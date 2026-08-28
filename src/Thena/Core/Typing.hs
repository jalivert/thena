-- | Typing: @infer@ and @check@ (§5.2, §7.4).
--
-- **Not bidirectional — decided by the user 2026-08-22.** @check@ is @infer@
-- followed by @convert@ and has no rules of its own. The argument is that
-- 'Core' is fully annotated: a 'Lam' carries its domain, a 'Let' its type, a
-- 'Pi' its domain, an 'Eliminate' its motive, and a 'Canonical' is saturated
-- and has a stored type. So every core term synthesises, and a pushed-in type
-- would have nothing left to supply. Bidirectionality earns its keep against
-- /un/annotated syntax and MS1 has no surface language (§9); the decision is
-- revisited when one arrives, and revisiting it means adding @check@ rules
-- beside this @infer@, not rewriting it.
--
-- **No cumulativity** (§5.2): a type is used at the universe it has, and
-- 'convert' is symmetric.
--
-- Takes and returns the name counter throughout, for the reason "Thena.Core.Convert"
-- does. §7.4's signatures are corrected to match — decided by the user
-- 2026-08-22, who also observed where this is heading: @infer@ is a large
-- instruction that will eventually be broken into smaller ones over an explicit
-- @fresh@ op, and the threading is the price of it being one instruction for
-- now.
module Thena.Core.Typing
  ( infer
  , check
    -- | Exported at phase 12 for "Thena.Development.Validate", which asks the
    -- same question of every component's stated type.
  , sortOf
  ) where

import Data.List (find)

import Thena.Core.Context (Context, Entry (..), entryType, entryVar)
import Thena.Core.Convert (convert)
import Thena.Core.Level (Level (..), levelMax, levelSuc)
import Thena.Core.Reduce (whnf)
import Thena.Core.Term
  ( Core (..)
  , GlobalName
  , close
  , fresh
  , instantiate
  , open
  )
import Thena.Errors (TypeError (..))
import Thena.Global.Env
  ( GlobalEnv
  , InductiveDefinition (..)
  , definitionType
  , eliminatorType
  , formerArity
  , lookupConstant
  , lookupDefinition
  , lookupInductive
  )

-- | The type of a term, or why it has none.
infer :: GlobalEnv -> Context -> Int -> Core -> (Either TypeError Core, Int)
infer env ctx n term = case term of
  Bound i -> (Left (LooseIndex i), n)

  Free x -> case find ((== x) . entryVar) ctx of
    Just e  -> (Right (entryType e), n)
    Nothing -> (Left (UnknownVariable ctx x), n)

  -- A definition first, then a constant. That order is δ's (§5.1): a former
  -- has an entry in both tables under one name, and what @g@ /means/ written
  -- as a term is the generated wrapper, not the type of the saturated
  -- 'Canonical' the wrapper's body builds.
  Global g _ -> case lookupDefinition g env of
    Just d  -> (Right (definitionType d), n)
    Nothing -> case lookupConstant g env of
      Just t  -> (Right t, n)
      Nothing -> (Left (UnknownGlobal g), n)

  Universe l -> (Right (Universe (levelSuc l)), n)

  -- @max@, not a subsumption: without cumulativity a Π lives at the larger of
  -- its two levels and nothing may be silently lifted into it (§5.2).
  --
  -- **Phase 28: this is now the algebra's @max@, and it is not evaluated.**
  -- @levelMax@ builds an @LMax@ and leaves it standing, because under
  -- polymorphism @max ℓ 0@ has no value until @ℓ@ does. Conversion compares up
  -- to the normal form, so nothing downstream notices — which is exactly what
  -- this phase's "the test suite does not move" check is testing.
  Pi i dom sc ->
    sortOf env ctx n dom `andThen` \k1 n1 ->
      let (x, n2) = fresh n1
       in sortOf env (ctx ++ [Hypothesis x i dom]) n2 (open x sc) `andThen` \k2 n3 ->
            (Right (Universe (levelMax k1 k2)), n3)

  Lam i dom sc ->
    sortOf env ctx n dom `andThen` \_ n1 ->
      let (x, n2) = fresh n1
       in infer env (ctx ++ [Hypothesis x i dom]) n2 (open x sc) `andThen` \b n3 ->
            (Right (Pi i dom (close x b)), n3)

  App f a ->
    infer env ctx n f `andThen` \fty n1 -> case whnf env ctx fty of
      Pi _ dom sc ->
        check env ctx n1 a dom `andThen` \() n2 -> (Right (instantiate a sc), n2)
      fty' -> (Left (NotAFunction ctx f fty'), n1)

  -- The body's type may mention the bound name, so the value is substituted
  -- back in — the same move @whnf@ makes on a term-level 'Let', and for the
  -- same reason (§5.1): there is no residual binding left to keep.
  Let i v ty sc ->
    sortOf env ctx n ty `andThen` \_ n1 ->
      check env ctx n1 v ty `andThen` \() n2 ->
        let (x, n3) = fresh n2
         in infer env (ctx ++ [Definition x i v ty]) n3 (open x sc) `andThen` \b n4 ->
              (Right (instantiate v (close x b)), n4)

  -- A saturated former. Its arity is read from the same place δ reads it, so
  -- the checker and the reducer cannot disagree about when one is complete.
  Canonical g _ as -> case formerArity g env of
    Nothing -> (Left (UnknownGlobal g), n)
    Just k
      | length as > k -> (Left (OverApplied g), n)
      | otherwise -> case lookupConstant g env of
          Nothing -> (Left (UnknownGlobal g), n)
          Just ty -> spine env ctx n MustSaturate g ty as

  -- The elimination rule, in full: build the eliminator's type at the level the
  -- motive is valued in, then walk the node's six field groups down it with the
  -- ordinary application rule. Nothing here is special to elimination except
  -- reading that level.
  --
  -- This is what the user's answer of 2026-08-22 collapses the rule to: the
  -- methods are terms, so they are inferred and converted against what the
  -- eliminator's type says their types are, exactly as every other argument is.
  -- 'eliminatorType''s binder order is 'Eliminate''s own field order, which is
  -- also the order §2.6 writes them in, so the walk needs no reshuffling.
  Eliminate d _ ps m ms is tgt -> case lookupInductive d env of
    Nothing  -> (Left (UnknownDatatype d), n)
    Just def ->
      motiveLevel env ctx n def m `andThen` \l n1 ->
        let (ety, n2) = eliminatorType def l n1
         in spine env ctx n2 MayBind d ety (ps ++ [m] ++ ms ++ is ++ [tgt])

-- | Does this term have this type? @infer@, then @convert@ (§5.2).
check :: GlobalEnv -> Context -> Int -> Core -> Core -> (Either TypeError (), Int)
check env ctx n t expected =
  infer env ctx n t `andThen` \actual n1 ->
    case convert env ctx n1 expected actual of
      (Nothing,  n2) -> (Right (), n2)
      (Just why, n2) -> (Left (NotOfType ctx t expected actual why), n2)

-- | The universe a type lives in: infer, reduce, and insist on a 'Universe'.
sortOf :: GlobalEnv -> Context -> Int -> Core -> (Either TypeError Level, Int)
sortOf env ctx n t =
  infer env ctx n t `andThen` \ty n1 -> case whnf env ctx ty of
    Universe l -> (Right l, n1)
    ty'        -> (Left (NotAType ctx t ty'), n1)

-- | What it means for the walk to end on a Π.
--
-- **Corrected phase 14.** Phase 8 rejected a leftover binder for both forms, on
-- the grounds that both are saturated by construction (§12 invariant 6). That
-- is right for 'Canonical', whose stored type ends at the datatype or a
-- universe, so a residual Π can only mean too few arguments. It is wrong for
-- 'Eliminate': every field group is supplied and the residue is @P indices
-- target@, which is whatever the motive says — and a motive valued in a
-- function type is the ordinary way to define a function by recursion.
-- @elim Nat () (λ t -> Nat -> Nat) (…) () n@, addition, was refused.
data Residue
  = MustSaturate  -- ^ a residual Π means arguments are missing
  | MayBind       -- ^ a residual Π is the motive's own value

-- | Apply a function type to a list of arguments, checking each against the
-- domain it lands in. The whole of the 'Canonical' and 'Eliminate' rules.
spine
  :: GlobalEnv -> Context -> Int -> Residue -> GlobalName -> Core -> [Core]
  -> (Either TypeError Core, Int)
spine env ctx n0 residue g = walk n0
  where
    walk n ty [] = case (residue, whnf env ctx ty) of
      (MustSaturate, Pi {}) -> (Left (Unsaturated g ty), n)
      _                     -> (Right ty, n)
    walk n ty (a : as) = case whnf env ctx ty of
      Pi _ dom sc ->
        check env ctx n a dom `andThen` \() n1 -> walk n1 (instantiate a sc) as
      _ -> (Left (OverApplied g), n)

-- | The universe the motive is valued in — §3.7's "the level is read from the
-- motive", which is how an eliminator serves every universe without the system
-- having universe polymorphism.
--
-- The read is deliberately **loose**: it peels one binder per index plus one
-- for the target and insists only that what is left is a universe. Whether the
-- motive's domains are actually the family's indices and target is not checked
-- here — 'spine' converts the motive against the eliminator type's own binder
-- for @P@, which is that check, stated once.
motiveLevel
  :: GlobalEnv -> Context -> Int -> InductiveDefinition -> Core
  -> (Either TypeError Level, Int)
motiveLevel env ctx n def m =
  infer env ctx n m `andThen` \ty n1 ->
    peel ctx n1 (length (inductiveIndices def) + 1) ty
  where
    peel c n' k ty = case (k :: Int, whnf env c ty) of
      (0, Universe l)   -> (Right l, n')
      (0, ty')          -> (Left (NotAMotive c m ty'), n')
      (_, Pi i dom sc)  ->
        let (x, n'') = fresh n'
         in peel (c ++ [Hypothesis x i dom]) n'' (k - 1) (open x sc)
      (_, ty')          -> (Left (NotAMotive c m ty'), n')

-- | Continue only on success, carrying the counter across either branch.
-- Written out rather than reached for as a monad, for the reason §3.5 gives:
-- the counter is an 'Int' in the outer state and there is no supply type.
andThen
  :: (Either TypeError a, Int) -> (a -> Int -> (Either TypeError b, Int))
  -> (Either TypeError b, Int)
andThen (Left e,  n) _ = (Left e, n)
andThen (Right a, n) k = k a n
infixl 1 `andThen`
