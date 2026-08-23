-- | Generating the @NoConfusion@ family and the @noConfusion@ lemma (§3.7
-- items 3 and 4).
--
-- These are what an elimination at specific indices uses to discharge the
-- equational hypotheses its motive carries: /injectivity/ of a former in each
-- argument, and /discrimination/ between distinct formers. MS1's target theorem
-- needs both — the matching branches the first, the impossible branches the
-- second.
--
-- **Its own module, not more of "Thena.Global.Declare".** Nothing forces the
-- split the way phase 12's did — @Declare@ already sits above @Typing@ — but
-- what is here is a different kind of code from what is there. @Declare@ asks
-- whether a declaration may be admitted; this /emits a proof term/, which is
-- the larger and riskier half of §3.7 and the one whose cost decides whether
-- the fallback (generating on demand inside the elimination tactic) is ever
-- reached.
--
-- **Everything emitted is checked before it is admitted** (§3.7): the two
-- definitions go through 'Thena.Core.Typing.check' in the environment they will
-- live in, and a failure is a 'Rejected', which "Thena.Global.Declare" turns
-- into a refusal. So unlike the eliminator, which is trusted derivation
-- (§5.3), this generator is verified.
--
-- == The shape, and why every case is CPS
--
-- §3.7 displays the family with @Unit@, @Empty@ and @Eq@ as its cases and
-- @Type₀@ as its result. That cannot be typed. The multi-argument case is
-- written CPS because MS1 has no product type, and @(C : Type₀) -> … -> C@
-- lives in @Type₁@ — 'Thena.Core.Typing.infer' gives a Π the @max@ of its two
-- levels, and the domain @Type₀@ is at level 1. With no cumulativity (§5.2) a
-- @Type₀@ case cannot sit beside a @Type₁@ one in a single family.
--
-- So **every case is CPS and the family lands in @Type₁@** — decided by the
-- user 2026-08-22. Only the level in §3.7 was wrong; the decision to encode the
-- conjunction in continuation-passing style, and @AGENDA.md@ item 13 as the one
-- place products change it, both stand. For @Nat@:
--
-- @
-- NoConfusionNat : Nat -> Nat -> Type₁
--   NoConfusionNat zero     zero     =  (C : Type₀) -> C -> C
--   NoConfusionNat zero     (succ b) =  (C : Type₀) -> C
--   NoConfusionNat (succ a) zero     =  (C : Type₀) -> C
--   NoConfusionNat (succ a) (succ b) =  (C : Type₀) -> (Eq Nat a b -> C) -> C
--
-- noConfusionNat : ∀ (x y : Nat) -> Eq Nat x y -> NoConfusionNat x y
-- @
--
-- @Unit@ and @Empty@ are therefore not used here at all; @Eq@ and @refl@ are
-- the only prelude names this module needs.
--
-- The family is two nested eliminations of the datatype — one to fix @x@'s
-- former, one to fix @y@'s. The lemma eliminates the equality first (its
-- eliminator is J), which fixes @y@ to be @x@, and then the datatype once, which
-- is why only the diagonal cases are ever proved: @λ C k . k refl … refl@.
module Thena.Global.NoConfusion
  ( Skipped (..)
  , Generated (..)
  , noConfusionNames
  , generateNoConfusion
  ) where

import Thena.Core.Context (Context, Entry (..), entryIdent, entryType, entryVar, lamOver, piOver)
import Thena.Core.Term
  ( Core (..)
  , GlobalName (..)
  , Ident (..)
  , Level (..)
  , close
  , fresh
  , freeVars
  , instantiate
  )
import Thena.Core.Typing (check)
import Thena.Errors (TypeError)
import Thena.Global.Env
  ( ConstructorDefinition (..)
  , Definition (..)
  , GlobalEnv
  , InductiveDefinition (..)
  , addDefinition
  , isDeclared
  , lookupInductive
  , recursiveArgument
  )

-- | Why a datatype gets no no-confusion. Structured, per §12 invariant 2.
--
-- The three are ordered by how much they are about the /user's/ declaration.
-- 'NoEquality' is about the environment and is reported to nobody (see
-- 'generateNoConfusion'); the other two are properties of what was just
-- written, and "Thena.Driver" says them.
data Skipped
  = NoEquality
    -- ^ no well-shaped @Eq@ is in scope, so no equation can be stated. Arises
    -- only before the prelude is loaded — @repl@ loads it at startup — which is
    -- why it is silent.
  | NotAtTypeZero Level
    -- ^ the datatype is not declared at @Type₀@, so @Eq (D params indices) x y@
    -- cannot be formed: the prelude's @Eq@ takes @A : Type₀@.
  | DependentArguments GlobalName Ident
    -- ^ this constructor's argument telescope is dependent, so the equation for
    -- the named argument is ill-typed. @cons : (n : Nat) (a : A) (as : Vec A n)
    -- -> Vec A (succ n)@ wants @Eq (Vec A n) as as'@ while @as' : Vec A n'@.
    -- An MS1 limit and not unsoundness — the way out is a transported chain of
    -- equations, which nothing in MS1 wants (@AGENDA.md@).
  deriving (Eq, Show)

-- | What generation did.
--
-- 'Rejected' is a **generator bug**, not a user error: it means the checker
-- refused a term this module built. It is a case rather than an @error@ call
-- because §12 invariant 2 wants the 'TypeError' carried out to where it can be
-- printed.
data Generated
  = Generated GlobalEnv Int
  | Declined Skipped
  | Clash GlobalName
    -- ^ a generated name is already taken (§3.6: one namespace, shared with
    -- generated names — the declaration is rejected rather than either name
    -- being hidden)
  | Rejected GlobalName TypeError

-- | The two names a datatype generates: @NoConfusionNat@ and @noConfusionNat@.
--
-- Concatenation, per §3.6's own example of the rule — @noConfusionTerm@ is a
-- name the user could have written, and if they do, the declaration that would
-- generate it is refused.
noConfusionNames :: GlobalName -> (GlobalName, GlobalName)
noConfusionNames (GlobalName d) =
  (GlobalName ("NoConfusion" ++ d), GlobalName ("noConfusion" ++ d))

-- | Generate, check and admit both definitions — or say why not.
--
-- Called from "Thena.Global.Declare" /after/ the wrappers are installed, so the
-- datatype's own former and constructors are already resolvable: @Eq Term a b@
-- and @succ a@ inside the generated terms are ordinary globals.
--
-- The preconditions are tested in this order deliberately. A prelude-free
-- script (the golden transcripts, phase 11's accepted divergence) fails the
-- first one and gets no message at all; a script with the prelude that declares
-- @Vec@ reaches the third and is told.
generateNoConfusion :: GlobalEnv -> Int -> InductiveDefinition -> Generated
generateNoConfusion env n0 d
  | not (equalityInScope env)          = Declined NoEquality
  | inductiveLevel d /= Level 0        = Declined (NotAtTypeZero (inductiveLevel d))
  | Just why <- dependentArgument d    = Declined why
  | isDeclared famName env             = Clash famName
  | isDeclared lemName env             = Clash lemName
  | otherwise =
      let (famTy,   n1) = familyType n0
          (famBody, n2) = family n1
       in case fst (check env [] n2 famBody famTy) of
            Left e   -> Rejected famName e
            Right () ->
              let env1          = addDefinition famName (MkDefinition famTy famBody) env
                  (lemTy,   n3) = lemmaType n2
                  (lemBody, n4) = lemma n3
               in case fst (check env1 [] n4 lemBody lemTy) of
                    Left e   -> Rejected lemName e
                    Right () ->
                      Generated (addDefinition lemName (MkDefinition lemTy lemBody) env1) n4
  where
    (famName, lemName) = noConfusionNames (inductiveName d)

    dn        = inductiveName d
    ps        = inductiveParameters d
    idx       = inductiveIndices d
    np        = length ps
    cs        = inductiveConstructors d
    paramVars = varsOf ps

    -- @D params indices@, as an application of the generated wrapper — the same
    -- spelling 'Thena.Global.Env.constructorTarget' builds, so nothing has to
    -- reduce to see the two agree.
    familyAt is = foldl App (Global dn) (paramVars ++ is)

    eqAt a x y = foldl App (Global (GlobalName "Eq")) [a, x, y]
    reflAt a x = foldl App (Global (GlobalName "refl")) [a, x]

    -- ----------------------------------------------------------------------
    -- The family
    -- ----------------------------------------------------------------------

    -- @∀ params indices (x y : D params indices) -> Type₁@
    familyType n =
      let (vx, n1) = fresh n
          (vy, n2) = fresh n1
          fam      = familyAt (varsOf idx)
       in ( piOver ps (piOver idx
              (Pi (Ident "x") fam (close vx
                (Pi (Ident "y") fam (close vy (Universe (Level 1)))))))
          , n2
          )

    -- @λ params indices x y . elim D params ‹motive› (‹methods›) indices x@
    --
    -- **@y@ is bound outside both eliminations, not consumed by the first.**
    -- The obvious reading of "eliminate @x@, then eliminate @y@" makes the
    -- first elimination compute a /function/ of @y@, and then its motive is
    -- Π-valued. That is well typed, but each method's body is a λ and the whole
    -- term is harder to read for no gain: with @y@ already in scope, the second
    -- elimination is simply what each method of the first returns, and both
    -- motives are the same constant.
    family n =
      let (vx, n1) = fresh n
          (vy, n2) = fresh n1
          (mt, n3) = typeMotive n2
          (ms, n4) = each (outerMethod mt (Free vy)) n3 cs
          fam      = familyAt (varsOf idx)
          body     = Eliminate dn paramVars mt ms (varsOf idx) (Free vx)
       in ( lamOver ps (lamOver idx
              (Lam (Ident "x") fam (close vx
                (Lam (Ident "y") fam (close vy body)))))
          , n4
          )

    -- @λ indices (t : D params indices) . Type₁@ — the motive of both
    -- eliminations, since both compute a type and neither result depends on
    -- what was eliminated. Valued in @Type₂@, which is the level
    -- 'Thena.Core.Typing.infer' reads off it.
    typeMotive n =
      let (is, n1) = freshen n idx
          (vt, n2) = fresh n1
       in ( lamOver is (Lam (Ident "t") (familyAt (varsOf is)) (close vt (Universe (Level 1))))
          , n2
          )

    -- One per constructor of @x@: @λ Δ . λ IHs . elim D … y@, the second
    -- elimination, at the indices @y@ was given.
    outerMethod mt y c n =
      let args       = constructorArguments c
          (ms, n1)   = each (innerMethod mt args c) n cs
          inner      = Eliminate dn paramVars mt ms (varsOf idx) y
          (body, n2) = withHypotheses mt args inner n1
       in (lamOver args body, n2)

    -- One per constructor of @y@, given the constructor @x@ turned out to be.
    -- The arguments are **freshened**: on the diagonal the two telescopes are
    -- the same 'Context', so reusing its variables would have the inner binder
    -- capture the outer one and every equation read @Eq A a a@.
    innerMethod mt args c c' n =
      let (args', n1) = freshen n (constructorArguments c')
          (payload, n2)
            | constructorName c' == constructorName c = diagonal args args' n1
            | otherwise                               = discriminate n1
          (body, n3) = withHypotheses mt args' payload n2
       in (lamOver args' body, n3)

    -- @(C : Type₀) -> C@ — the Church-encoded empty type. Applying it to the
    -- goal is how an impossible branch closes.
    discriminate n =
      let (vc, n1) = fresh n
       in (Pi (Ident "C") (Universe (Level 0)) (close vc (Free vc)), n1)

    -- @(C : Type₀) -> (Eq A₁ a₁ a\'₁ -> … -> C) -> C@. Well typed only because
    -- 'dependentArgument' has already refused telescopes where @Aᵢ@ mentions an
    -- earlier argument.
    diagonal args args' n =
      let (vc, n1) = fresh n
          (vk, n2) = fresh n1
          eqs = zipWith
                  (\e e' -> eqAt (entryType e) (Free (entryVar e)) (Free (entryVar e')))
                  args args'
          (kty, n3) = arrows eqs (Free vc) n2
       in ( Pi (Ident "C") (Universe (Level 0)) (close vc
              (Pi (Ident "k") kty (close vk (Free vc))))
          , n3
          )

    -- ----------------------------------------------------------------------
    -- The lemma
    -- ----------------------------------------------------------------------

    -- @∀ params indices (x y : D params indices) -> Eq (D params indices) x y
    --   -> NoConfusionD params indices x y@
    lemmaType n =
      let (vx, n1) = fresh n
          (vy, n2) = fresh n1
          (ve, n3) = fresh n2
          fam      = familyAt (varsOf idx)
          result   = foldl App (Global famName)
                       (paramVars ++ varsOf idx ++ [Free vx, Free vy])
       in ( piOver ps (piOver idx
              (Pi (Ident "x") fam (close vx
                (Pi (Ident "y") fam (close vy
                  (Pi (Ident "e") (eqAt fam (Free vx) (Free vy)) (close ve result)))))))
          , n3
          )

    -- @λ params indices x y e . elim Eq (D params indices) ‹motive› (‹refl›)
    --   (x, y) e@ — J, and the whole reason only diagonal cases are proved.
    lemma n =
      let (vx, n1) = fresh n
          (vy, n2) = fresh n1
          (ve, n3) = fresh n2
          fam      = familyAt (varsOf idx)
          (meq, n4)  = equalityMotive n3
          (mrfl, n5) = reflMethod n4
          body = Eliminate (GlobalName "Eq") [fam] meq [mrfl]
                   [Free vx, Free vy] (Free ve)
       in ( lamOver ps (lamOver idx
              (Lam (Ident "x") fam (close vx
                (Lam (Ident "y") fam (close vy
                  (Lam (Ident "e") (eqAt fam (Free vx) (Free vy)) (close ve body)))))))
          , n5
          )

    -- @λ u v (w : Eq (D …) u v) . NoConfusionD params indices u v@ — valued in
    -- @Type₁@, so J is used at level 1 here and the family's own eliminations
    -- at level 2.
    equalityMotive n =
      let (vu, n1) = fresh n
          (vv, n2) = fresh n1
          (vw, n3) = fresh n2
          fam      = familyAt (varsOf idx)
          result   = foldl App (Global famName)
                       (paramVars ++ varsOf idx ++ [Free vu, Free vv])
       in ( Lam (Ident "u") fam (close vu
              (Lam (Ident "v") fam (close vv
                (Lam (Ident "w") (eqAt fam (Free vu) (Free vv)) (close vw result)))))
          , n3
          )

    -- @λ a . elim D params ‹motive› (‹methods›) indices a@ — the one method J
    -- leaves, which is @NoConfusionD … a a@ for an arbitrary @a@.
    reflMethod n =
      let (va, n1)   = fresh n
          (mdg, n2)  = diagonalMotive n1
          (ms,  n3)  = each (diagonalMethod mdg) n2 cs
          body       = Eliminate dn paramVars mdg ms (varsOf idx) (Free va)
       in (Lam (Ident "a") (familyAt (varsOf idx)) (close va body), n3)

    -- @λ indices (z : D params indices) . NoConfusionD params indices z z@.
    diagonalMotive n =
      let (is, n1) = freshen n idx
          (vz, n2) = fresh n1
          result   = foldl App (Global famName)
                       (paramVars ++ varsOf is ++ [Free vz, Free vz])
       in ( lamOver is (Lam (Ident "z") (familyAt (varsOf is)) (close vz result))
          , n2
          )

    -- @λ Δ . λ IHs . λ C k . k (refl A₁ a₁) … (refl Aₖ aₖ)@ — the only proof
    -- this generator ever writes, and §3.7's own @λ C k . k refl … refl@.
    diagonalMethod mdg c n =
      let args     = constructorArguments c
          (vc, n1) = fresh n
          (vk, n2) = fresh n1
          eqs = map (\e -> eqAt (entryType e) (Free (entryVar e)) (Free (entryVar e))) args
          (kty, n3) = arrows eqs (Free vc) n2
          proof = foldl App (Free vk)
                    (map (\e -> reflAt (entryType e) (Free (entryVar e))) args)
          payload = Lam (Ident "C") (Universe (Level 0)) (close vc
                      (Lam (Ident "k") kty (close vk proof)))
          (body, n4) = withHypotheses mdg args payload n3
       in (lamOver args body, n4)

    -- ----------------------------------------------------------------------
    -- Shared shapes
    -- ----------------------------------------------------------------------

    -- One inductive hypothesis binder per recursive argument, in argument
    -- order — the same reading of the record 'Thena.Global.Env.eliminatorType'
    -- makes, through the same function, so a method cannot bind a telescope its
    -- own type does not have. Nothing generated here ever /uses/ one.
    withHypotheses mot tel body = go tel
      where
        go []       n = (body, n)
        go (e : es) n = case recursiveArgument dn np (entryType e) of
          Nothing -> go es n
          Just is ->
            let (hv, n1)    = fresh n
                (below, n2) = go es n1
             in (Lam (Ident "ih") (foldl App mot (is ++ [Free (entryVar e)])) (close hv below), n2)

    -- @S₁ -> … -> Sₙ -> T@. Each arrow is a Π whose scope binds nothing, but a
    -- 'Thena.Core.Term.Scope' still needs a variable to close over — the same
    -- spend 'Thena.Global.Env.eliminatorType' makes on inductive hypotheses.
    arrows []       t n = (t, n)
    arrows (s : ss) t n =
      let (v, n1)     = fresh n
          (below, n2) = arrows ss t n1
       in (Pi (Ident "_") s (close v below), n2)

-- --------------------------------------------------------------------------
-- Preconditions
-- --------------------------------------------------------------------------

-- | Is there an @Eq@ of the prelude's shape?
--
-- Matched structurally rather than by name alone. A user is free to declare
-- something else called @Eq@ — one namespace (§3.6) — and the cost of not
-- looking would be that every subsequent @data@ is refused with a type error
-- from a term the user never wrote.
equalityInScope :: GlobalEnv -> Bool
equalityInScope env = case lookupInductive (GlobalName "Eq") env of
  Nothing -> False
  Just e -> case (inductiveParameters e, inductiveIndices e, inductiveConstructors e) of
    ([a], [i, j], [c]) ->
      inductiveLevel e == Level 0
        && entryType a == Universe (Level 0)
        && entryType i == Free (entryVar a)
        && entryType j == Free (entryVar a)
        && constructorName c == GlobalName "refl"
        && case constructorArguments c of
             [x] -> entryType x == Free (entryVar a)
                      && constructorIndices c == [Free (entryVar x), Free (entryVar x)]
             _   -> False
    _ -> False

-- | The first constructor argument whose type mentions an argument before it.
--
-- That is exactly when the injectivity equations stop being statable: the
-- equation for such an argument relates two terms of two different types.
dependentArgument :: InductiveDefinition -> Maybe Skipped
dependentArgument d = firstJust (map perConstructor (inductiveConstructors d))
  where
    perConstructor c = go [] (constructorArguments c)
      where
        go _    []       = Nothing
        go seen (e : es)
          | any (`elem` seen) (freeVars (entryType e)) =
              Just (DependentArguments (constructorName c) (entryIdent e))
          | otherwise = go (entryVar e : seen) es

    firstJust xs = case [x | Just x <- xs] of
      x : _ -> Just x
      []    -> Nothing

-- --------------------------------------------------------------------------
-- Small helpers
-- --------------------------------------------------------------------------

varsOf :: Context -> [Core]
varsOf = map (Free . entryVar)

-- | A copy of a telescope under fresh variables, primed so a printed term does
-- not show two binders with one name.
--
-- Sound only because 'dependentArgument' has already refused telescopes whose
-- later types mention earlier entries: the types are carried across unchanged.
-- | A second copy of a telescope, with new variables.
--
-- **Every later entry is repointed at the new variable** — a telescope is
-- dependent in general, and an entry whose type still named the /old/ variable
-- would be a copy that silently refers back into the original. Phase 17 found
-- this the hard way: it is invisible for every telescope in the suite, because
-- none of them is dependent where this is used, and it made
-- @data Below : ∀ (n : Nat) (i : Fin n) -> Type₀@ generate a
-- @NoConfusionBelow@ that did not typecheck — reported as "the variables
-- Var 125 and Var 121 are different", which is exactly what it was.
--
-- 'close' then 'instantiate' is the only way to rewrite a variable (§3.4), and
-- it is safe here because both are free variables of the ambient context.
freshen :: Int -> Context -> (Context, Int)
freshen n0 = go n0
  where
    go n []       = ([], n)
    go n (e : es) =
      let (v, n1)    = fresh n
          (rest, n2) = go n1 (map (repoint (entryVar e) v) es)
       in (copy v e : rest, n2)

    copy v e = case e of
      Hypothesis _ (Ident i) t   -> Hypothesis v (Ident (i ++ "'")) t
      Definition _ (Ident i) s t -> Definition v (Ident (i ++ "'")) s t

    repoint old new e = case e of
      Hypothesis w i t   -> Hypothesis w i (swap t)
      Definition w i s t -> Definition w i (swap s) (swap t)
      where
        swap t = instantiate (Free new) (close old t)

-- | Map with the counter threaded, left to right.
each :: (a -> Int -> (b, Int)) -> Int -> [a] -> ([b], Int)
each f = go
  where
    go n []       = ([], n)
    go n (x : xs) =
      let (y,  n1) = f x n
          (ys, n2) = go n1 xs
       in (y : ys, n2)
