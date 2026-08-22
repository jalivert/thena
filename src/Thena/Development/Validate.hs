-- | @revalidate@: is this development a valid state? (§5.3, thesis §2.3.)
--
-- **Its own module, above "Thena.Core.Typing" — decided by the user
-- 2026-08-22.** §2.5 had listed it in "Thena.Development.Partial", and it
-- cannot live there: it needs @infer@, so the data module that
-- "Thena.Development.Cursor" and the @.hs-boot@ both depend on would import the
-- whole core typechecker, and everything wanting the data type would pull
-- @Typing@, @Convert@, @Reduce@ and @Global.Env@ with it. No cycle — exactly
-- the shape @Global@ was split in two to avoid.
--
-- **Not the kernel** (§5.3's table). @certify@ takes a closed pure term and
-- lives outside the layer stack; this takes a whole 'Partial', holes and
-- guesses and constraints included, and lives in the core under the ops. The
-- two cannot be confused by accident, because @certify@'s signature will not
-- accept a 'Partial' — §3.1's two fragments making the distinction structural.
module Thena.Development.Validate
  ( revalidate
  ) where

import Thena.Core.Context (Context)
import Thena.Core.Convert (convert)
import Thena.Core.Reduce (whnf)
import Thena.Core.Term (Core (..), Ident, Var, instantiate)
import Thena.Core.Typing (check, sortOf)
import Thena.Development.Component (Component (..), forget)
import Thena.Development.Partial (Constraint (..), Partial (..))
import Thena.Errors (KernelError (..), Position (..), TypeError (..))
import Thena.Global.Env (GlobalEnv)

-- | Walk the chain, checking each link against what precedes it.
--
-- Thesis §2.3's validity judgment, one line per component:
--
-- * @λ x : S@ and @? x : S@ — @S@ must be a type in Γ.
-- * @x = s : S@ — @S@ must be a type, and @s@ must have it.
-- * @? x ≐ g : S@ — @S@ must be a type, and @g@ must itself be a valid
--   development /whose trailing term has type @S@/.
-- * @Ξ ⊢ s ≟ t : T@ — in Γ extended by Ξ, @T@ must be a type and both sides
--   must have it (§6.4).
-- * the trailing term — **nothing is checked against it at the top**, because
--   nothing written down says what it should be. Under a guess something does:
--   the guess's own type. That asymmetry is phase 5's @expectedType@, and this
--   is the same rule stated by the same distinction rather than a second time.
--
-- Γ is built by 'forget', and that is the point rather than a convenience: a
-- 'Guess' forgets to a hypothesis with no value, so nothing here can δ-unfold
-- a guess, and "guesses are invisible to the core" is kept by the code that
-- keeps it everywhere else instead of by a filter written again.
--
-- **Takes and returns the counter** (§7.4), for @infer@'s reason — opening a
-- 'Thena.Core.Term.Scope' mints variables, and they must not collide with the
-- session's.
--
-- The first failure stops it, carrying a 'Position' that names the component
-- the way the user wrote it.
revalidate :: GlobalEnv -> Context -> Int -> Partial -> (Either KernelError (), Int)
revalidate env ctx n = chain env ctx n Nothing

-- | The whole of 'revalidate', plus what the trailing term must have.
--
-- 'Nothing' at the top and @Just@ under a guess. One traversal with one extra
-- argument, rather than two that could come to disagree about a link.
chain
  :: GlobalEnv -> Context -> Int -> Maybe Core -> Partial
  -> (Either KernelError (), Int)
chain env ctx n0 expected p0 = case p0 of
  Trailing t -> case expected of
    Nothing -> (Right (), n0)
    Just ty -> at TheTerm (check env ctx n0 t ty)

  Pending k rest -> constraint k `andThen` \n1 ->
    chain env ctx n1 expected rest
    where
      -- Ξ's binders scope over the equation and over nothing else (§6.4), so
      -- they extend the context here and are gone from the recursive call.
      constraint (Equate xi s t ty) =
        isAType here inner n0 ty `andThen` \n1 ->
          at here (check env inner n1 s ty) `andThen` \n2 ->
            at here (check env inner n2 t ty)
        where
          inner = ctx ++ xi
          here  = ConstraintAt (1 + constraintsBefore p0 rest)

  Under c rest -> component c `andThen` \n1 ->
    case peeled c n1 of
      (Left e,      n2) -> (Left e, n2)
      (Right below, n2) -> chain env (ctx ++ [forget c]) n2 below rest
    where
      component (Assume x i s)   = isAType (TypeOf x i) ctx n0 s
      component (Claim  x i s)   = isAType (TypeOf x i) ctx n0 s
      component (Define x i v s) =
        isAType (TypeOf x i) ctx n0 s `andThen` \n1 ->
          at (ValueOf x i) (check env ctx n1 v s)
      component (Guess x i g s) =
        isAType (TypeOf x i) ctx n0 s `andThen` \n1 ->
          case chain env ctx n1 (Just s) g of
            (Left e,   n2) -> (Left (under x i e), n2)
            (Right (), n2) -> (Right (), n2)

      -- **Only an assumption consumes the expected type**, and that is thesis
      -- §2.3 read exactly: @assume@ adds @(λx:S)@, an abstraction, so the
      -- construction below it builds the codomain and not the whole thing. A
      -- hole and a guess are bindings that abstract nothing, and a local
      -- definition is a @let@ whose variable Γ already carries a value for —
      -- so conversion can δ-unfold it and the expected type passes through
      -- unchanged. 'Thena.Development.Partial.extract' folds the term the same
      -- way, one constructor at a time; the two agree because they are the
      -- same case split.
      --
      -- Without this the running example fails: @? id' ≐ (λ a : A . ? h : A .
      -- h) : A -> A@ has a trailing @h : A@, not @h : A -> A@.
      peeled :: Component -> Int -> (Either KernelError (Maybe Core), Int)
      peeled c' n = case (c', expected) of
        (Assume x i s, Just ty) -> case whnf env ctx ty of
          Pi _ dom cod -> case convert env ctx n dom s of
            (Nothing,  n') -> (Right (Just (instantiate (Free x) cod)), n')
            (Just why, n') -> (Left (Ill (TypeOf x i) (NotOfType ctx (Free x) dom s why)), n')
          other -> (Left (Overabstracted x i other), n)
        _ -> (Right expected, n)
  where
    isAType here ctx' n t = case sortOf env ctx' n t of
      (Left e,  n1) -> (Left (Ill here e), n1)
      (Right _, n1) -> (Right (), n1)

    at here (r, n) = case r of
      Left e   -> (Left (Ill here e), n)
      Right () -> (Right (), n)

-- | A failure inside a guess is reported inside it, not flattened: a guess's
-- body is a development in its own right and its positions mean nothing
-- outside it.
under :: Var -> Ident -> KernelError -> KernelError
under x i e = case e of
  Ill pos te -> Ill (Inside x i pos) te
  -- The other two carry no 'Position' to nest, and both already name the
  -- component they are about.
  Overabstracted {} -> e
  NotClosed {}      -> e   -- 'chain' never builds one

-- | Which constraint this is, counting from the front of the chain.
--
-- Recomputed rather than threaded, because a number the traversal carries and
-- a number the chain actually has are two encodings of the same fact.
constraintsBefore :: Partial -> Partial -> Int
constraintsBefore whole rest = count whole - count rest - 1
  where
    count p = case p of
      Trailing _      -> 0
      Pending _ q     -> 1 + count q
      Under _ q       -> count q

andThen :: (Either e (), Int) -> (Int -> (Either e (), Int)) -> (Either e (), Int)
andThen (Left e,   n) _ = (Left e, n)
andThen (Right (), n) k = k n
