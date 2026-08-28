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
--   NoConfusionNat zero     zero     =  Unit
--   NoConfusionNat zero     (succ b) =  Empty
--   NoConfusionNat (succ a) zero     =  Empty
--   NoConfusionNat (succ a) (succ b) =  Eq Nat a b
--
-- noConfusionNat : ∀ (x y : Nat) -> Eq Nat x y -> NoConfusionNat x y
-- @
--
-- A constructor with several arguments conjoins one equation per argument,
-- right-nested: @both@'s @And (Eq A a a') (Eq B b b')@. **Phase 20 replaced a
-- continuation-passing encoding of that conjunction**, which phase 14 had been
-- forced into because @(C : Type₀) -> …@ is at @Type₁@ and no cumulativity
-- lets a @Type₀@ case sit beside it. With the products in the prelude the
-- table above is the one §3.7 always displayed, at @Type₀@.
--
-- The prelude names this module needs are therefore @Eq@ and @refl@, and
-- @And@, @both@, @Unit@, @unit@ and @Empty@.
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

import Thena.Core.Level (Level (..))
import Thena.Core.Context (Context, Entry (..), entryIdent, entryType, entryVar, lamOver, piOver)
import Thena.Core.Term
  ( Core (..)
  , GlobalName (..)
  , Ident (..)
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
  | NoProducts
    -- ^ a prelude type this datatype's own table would be written out of —
    -- @And@, @Unit@ or @Empty@ — is missing or misshapen. Silent for
    -- 'NoEquality'\'s reason and arising in the same situation, a prelude-free
    -- script, which is why the two are tested together.
    --
    -- **Asked per datatype, not once**, and that is load-bearing rather than
    -- fastidious: the prelude declares @Eq@ before @And@, so a blanket
    -- precondition would refuse @NoConfusionEq@ — which phase 14 generated —
    -- for a name it was never going to write. See 'productsInScope'.
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
  | not (productsInScope env d)        = Declined NoProducts
  | Just why <- dependentArgument d    = Declined why
  | isDeclared famName env             = Clash famName
  | isDeclared lemName env             = Clash lemName
  | otherwise =
      let (famTy,   n1) = familyType n0
          (famBody, n2) = family n1
       in case fst (check env [] n2 famBody famTy) of
            Left e   -> Rejected famName e
            Right () ->
              let env1          = addDefinition famName (MkDefinition (inductiveLevels d) famTy famBody) env
                  (lemTy,   n3) = lemmaType n2
                  (lemBody, n4) = lemma n3
               in case fst (check env1 [] n4 lemBody lemTy) of
                    Left e   -> Rejected lemName e
                    Right () ->
                      Generated (addDefinition lemName (MkDefinition (inductiveLevels d) lemTy lemBody) env1) n4
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
    -- **At the datatype's own level parameters**, like every other generated
    -- reference (phase 31g; the same fix `Thena.Global.Env` took in 31c).
    familyAt is = foldl App (Global dn (map LVar (inductiveLevels d))) (paramVars ++ is)

    -- **At level 0** (MS3 phase 31d). @Eq@ is level-polymorphic now, and
    -- no-confusion is generated only for a @Type₀@ datatype (the
    -- 'NotAtTypeZero' guard), whose constructor arguments therefore live at
    -- @Type₀@ too by the size restriction. So every equation this module
    -- writes is stated at @Eq {0}@.
    -- **Everything this module writes is stated at the datatype's own level**
    -- (MS3 phase 31g), and that is exactly what cumulativity buys.
    --
    -- A constructor argument's type lives at some @ℓ_arg ≤ dl@ (the size
    -- restriction), so @Eq {dl}@ applied to it is well typed: subsumption
    -- lifts a @Type ℓ_arg@ into @Type dl@. Before phase 32 the equations would
    -- have had to be stated each at its own argument's level, and then could
    -- not have been conjoined — @And@ takes two types at **one** level.
    dl = inductiveLevel d

    eqAt a x y = foldl App (Global (GlobalName "Eq") [dl]) [a, x, y]
    reflAt a x = foldl App (Global (GlobalName "refl") [dl]) [a, x]

    andAt p q        = foldl App (Global (GlobalName "And") [dl]) [p, q]
    bothAt p q x y   = foldl App (Global (GlobalName "both") [dl]) [p, q, x, y]

    -- ----------------------------------------------------------------------
    -- The family
    -- ----------------------------------------------------------------------

    -- @∀ params indices (x y : D params indices) -> Type₀@
    --
    -- **@Type₀@, not @Type₁@.** Phase 14 had every case CPS-encoded, and
    -- @(C : Type₀) -> C@ is itself at @Type₁@; with @Empty@, @Unit@ and @And@
    -- in the prelude every case is an ordinary @Type₀@ proposition and the
    -- family follows it down. Nothing else about the shape changed.
    familyType n =
      let (vx, n1) = fresh n
          (vy, n2) = fresh n1
          fam      = familyAt (varsOf idx)
       in ( piOver ps (piOver idx
              (Pi (Ident "x") fam (close vx
                (Pi (Ident "y") fam (close vy (Universe dl))))))
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
          body     = Eliminate dn (map LVar (inductiveLevels d)) paramVars mt ms (varsOf idx) (Free vx)
       in ( lamOver ps (lamOver idx
              (Lam (Ident "x") fam (close vx
                (Lam (Ident "y") fam (close vy body)))))
          , n4
          )

    -- @λ indices (t : D params indices) . Type₀@ — the motive of both
    -- eliminations, since both compute a type and neither result depends on
    -- what was eliminated. Valued in @Type₁@, which is the level
    -- 'Thena.Core.Typing.infer' reads off it.
    typeMotive n =
      let (is, n1) = freshen n idx
          (vt, n2) = fresh n1
       in ( lamOver is (Lam (Ident "t") (familyAt (varsOf is)) (close vt (Universe dl)))
          , n2
          )

    -- One per constructor of @x@: @λ Δ . λ IHs . elim D … y@, the second
    -- elimination, at the indices @y@ was given.
    outerMethod mt y c n =
      let args       = constructorArguments c
          (ms, n1)   = each (innerMethod mt args c) n cs
          inner      = Eliminate dn (map LVar (inductiveLevels d)) paramVars mt ms (varsOf idx) y
          (body, n2) = withHypotheses mt args inner n1
       in (lamOver args body, n2)

    -- One per constructor of @y@, given the constructor @x@ turned out to be.
    -- The arguments are **freshened**: on the diagonal the two telescopes are
    -- the same 'Context', so reusing its variables would have the inner binder
    -- capture the outer one and every equation read @Eq A a a@.
    innerMethod mt args c c' n =
      let (args', n1) = freshen n (constructorArguments c')
          payload
            | constructorName c' == constructorName c = diagonal args args'
            | otherwise                               = discriminate
          (body, n2) = withHypotheses mt args' payload n1
       in (lamOver args' body, n2)

    -- @Empty@ — the prelude's empty type, named rather than Church-encoded.
    -- Discharging an impossible branch is @elim Empty@ at whatever goal is
    -- wanted, which is a goal at /any/ level; the CPS form it replaces could
    -- only ever reach a @Type₀@ one.
    discriminate = Global (GlobalName "Empty") [dl]

    -- @And (Eq A₁ a₁ a\'₁) (… (Eq Aₙ aₙ a\'ₙ))@, right-nested, and @Unit@ for a
    -- constructor with no arguments. Well typed only because 'dependentArgument'
    -- has already refused telescopes where @Aᵢ@ mentions an earlier argument.
    diagonal args args' =
      conjoin (zipWith
                 (\e e' -> eqAt (entryType e) (Free (entryVar e)) (Free (entryVar e')))
                 args args')

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
          result   = foldl App (Global famName (map LVar (inductiveLevels d)))
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
          body = Eliminate (GlobalName "Eq") [dl] [fam] meq [mrfl]
                   [Free vx, Free vy] (Free ve)
       in ( lamOver ps (lamOver idx
              (Lam (Ident "x") fam (close vx
                (Lam (Ident "y") fam (close vy
                  (Lam (Ident "e") (eqAt fam (Free vx) (Free vy)) (close ve body)))))))
          , n5
          )

    -- @λ u v (w : Eq (D …) u v) . NoConfusionD params indices u v@ — valued in
    -- @Type₀@, so J is used at level 0 here and the family's own eliminations
    -- at level 1.
    equalityMotive n =
      let (vu, n1) = fresh n
          (vv, n2) = fresh n1
          (vw, n3) = fresh n2
          fam      = familyAt (varsOf idx)
          result   = foldl App (Global famName (map LVar (inductiveLevels d)))
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
          body       = Eliminate dn (map LVar (inductiveLevels d)) paramVars mdg ms (varsOf idx) (Free va)
       in (Lam (Ident "a") (familyAt (varsOf idx)) (close va body), n3)

    -- @λ indices (z : D params indices) . NoConfusionD params indices z z@.
    diagonalMotive n =
      let (is, n1) = freshen n idx
          (vz, n2) = fresh n1
          result   = foldl App (Global famName (map LVar (inductiveLevels d)))
                       (paramVars ++ varsOf is ++ [Free vz, Free vz])
       in ( lamOver is (Lam (Ident "z") (familyAt (varsOf is)) (close vz result))
          , n2
          )

    -- @λ Δ . λ IHs . both … (refl A₁ a₁) (both … (refl A₂ a₂) …)@ — the only
    -- proof this generator ever writes, nested exactly as 'conjoin' nests the
    -- type it inhabits, and @unit@ where that type is @Unit@.
    diagonalMethod mdg c n =
      let args    = constructorArguments c
          payload = conjoinProof
                      [ ( eqAt (entryType e) (Free (entryVar e)) (Free (entryVar e))
                        , reflAt (entryType e) (Free (entryVar e))
                        )
                      | e <- args
                      ]
          (body, n1) = withHypotheses mdg args payload n
       in (lamOver args body, n1)

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

    -- @P₁ ∧ (P₂ ∧ … ∧ Pₙ)@, right-nested, and @Unit@ when there is nothing to
    -- conjoin. Right-nested rather than left so that the one-argument case is
    -- the bare equation with no wrapper at all, which is the overwhelmingly
    -- common one.
    conjoin []       = Global (GlobalName "Unit") [dl]
    conjoin [t]      = t
    conjoin (t : ts) = andAt t (conjoin ts)

    -- The proof of 'conjoin' applied to the same list, given a proof of each
    -- conjunct. Taken as pairs so the two nestings cannot drift apart.
    conjoinProof []             = Global (GlobalName "unit") [dl]
    conjoinProof [(_, p)]       = p
    conjoinProof ((t, p) : tps) =
      bothAt t (conjoin (map fst tps)) p (conjoinProof tps)

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
    -- **@Eq@ is level-polymorphic in exactly one parameter** (MS3 phase 31d),
    -- and the shape check follows it: the carrier lives at that parameter, and
    -- so does the family. Everything this module generates is still stated at
    -- @Eq {0}@ — no-confusion is only produced for a @Type₀@ datatype (the
    -- guard below), whose constructor arguments live at @Type₀@ too by the size
    -- restriction.
    ([a], [i, j], [c]) | [lv] <- inductiveLevels e ->
      inductiveLevel e == LVar lv
        && entryType a == Universe (LVar lv)
        && entryType i == Free (entryVar a)
        && entryType j == Free (entryVar a)
        && constructorName c == GlobalName "refl"
        && case constructorArguments c of
             [x] -> entryType x == Free (entryVar a)
                      && constructorIndices c == [Free (entryVar x), Free (entryVar x)]
             _   -> False
    _ -> False

-- | Are the prelude types /this/ datatype's table is written out of in scope?
--
-- Matched structurally, for 'equalityInScope'\'s reason and by the same
-- technique, and reported the same way — silently.
--
-- **Only what the generator will actually write is required.** The three names
-- are each demanded by one shape of case and by nothing else:
--
-- * @Empty@ by an off-diagonal case, so only where there are two or more
--   constructors to be off the diagonal of;
-- * @Unit@ and @unit@ by a diagonal case for a constructor with no arguments;
-- * @And@ and @both@ by a diagonal case for a constructor with two or more,
--   since one argument needs no conjunction and 'conjoin' emits the bare
--   equation.
--
-- Asking for all three unconditionally would be simpler and wrong. The prelude
-- must declare @Eq@ before @And@ — @And@\'s own no-confusion needs the
-- equality — and @Eq@\'s single constructor @refl@ takes a single argument, so
-- its table mentions none of the three. Under a blanket check @NoConfusionEq@
-- would be silently lost at the very line that makes everything else possible.
productsInScope :: GlobalEnv -> InductiveDefinition -> Bool
productsInScope env d =
     (not needsEmpty || falsityInScope env)
  && (not needsUnit  || truthInScope env)
  && (not needsAnd   || conjunctionInScope env)
  where
    cs         = inductiveConstructors d
    arity      = length . constructorArguments
    needsEmpty = length cs >= 2
    needsUnit  = any ((== 0) . arity) cs
    needsAnd   = any ((>= 2) . arity) cs

-- | @And (A : Type₀) (B : Type₀) : Type₀ { both : ∀ (a : A) (b : B) -> And A B }@
conjunctionInScope :: GlobalEnv -> Bool
conjunctionInScope env = case lookupInductive (GlobalName "And") env of
  Nothing -> False
  Just e -> case (inductiveParameters e, inductiveIndices e, inductiveConstructors e) of
    ([a, b], [], [c]) | [lv] <- inductiveLevels e ->
      inductiveLevel e == LVar lv
        && entryType a == Universe (LVar lv)
        && entryType b == Universe (LVar lv)
        && constructorName c == GlobalName "both"
        && case constructorArguments c of
             [x, y] -> entryType x == Free (entryVar a)
                         && entryType y == Free (entryVar b)
                         && null (constructorIndices c)
             _      -> False
    _ -> False

-- | @Unit : Type₀ { unit : Unit }@ — @unit@ is checked because 'conjoinProof'
-- writes it, not only the type.
truthInScope :: GlobalEnv -> Bool
truthInScope env = case lookupInductive (GlobalName "Unit") env of
  Nothing -> False
  Just e -> case (inductiveParameters e, inductiveIndices e, inductiveConstructors e) of
    ([], [], [c]) | [lv] <- inductiveLevels e ->
      inductiveLevel e == LVar lv
        && constructorName c == GlobalName "unit"
        && null (constructorArguments c)
        && null (constructorIndices c)
    _ -> False

-- | @Empty : Type₀ { }@ — no constructor to check, which is the point of it.
falsityInScope :: GlobalEnv -> Bool
falsityInScope env = case lookupInductive (GlobalName "Empty") env of
  Nothing -> False
  Just e -> case inductiveLevels e of
    [lv] -> null (inductiveParameters e)
              && null (inductiveIndices e)
              && null (inductiveConstructors e)
              && inductiveLevel e == LVar lv
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

-- | A second copy of a telescope, with new variables — primed, so a printed
-- term does not show two binders with one name.
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
