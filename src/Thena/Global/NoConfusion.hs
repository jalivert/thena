-- | Generating the @NoConfusion@ family and the @noConfusion@ lemma (§3.7
-- items 3, 4 and 6).
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
-- levels, and the domain @Type₀@ is at level 1. **At the time there was no
-- cumulativity** — it arrived at MS3 phase 32 — so a @Type₀@ case could not sit
-- beside a @Type₁@ one in a single family.
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
-- == Each element has its own indices, and what relates them is a chain
--
-- **MS9 phases 218 and 222.** @Nat@ above is the whole story for a family with
-- no indices, and that is most of them. For an indexed family the pair is stated
-- over the telescope @(indices; element)@: the family takes an index group per
-- element, and the lemma takes the telescopic equality between the two
-- instantiations — §3.3 of /Pattern Matching Without K/, 'confusionChain' —
-- __curried__, one argument per equation.
--
-- @
-- NoConfusionEv : ∀ (n : N) -> Ev n -> ∀ (n' : N) -> Ev n' -> Type₀
-- noConfusionEv : ∀ (n : N) (a : Ev n) (n' : N) (b : Ev n') (q : Eq N n n')
--              -> Eq (Ev n') (transport q a) b -> NoConfusionEv n a n' b
-- @
--
-- **Why both sides need their own indices**: @noCycleD@'s last step assumes an
-- equation between two constructor applications whose indices are not visibly
-- the same, so a lemma stated at one index group cannot be /applied/ there,
-- whatever it says. "Thena.Global.NoCycle" is that caller.
--
-- **Curried and not packaged** because a split holds its equations as separate Π
-- binders, one per tied index, so a lemma it calls must take them that way;
-- packaging here would only be unpacked at every use site.
--
-- **The payload is unchanged, and that is why the replacement cost nothing at a
-- use site.** On the diagonal both sides are the same constructor, whose own
-- arguments determine both index groups, so the indices need no equations of
-- their own and what is left to say is still the telescopic equality of the
-- arguments. Where the family has no indices the chain /is/ the single @Eq@ the
-- homogeneous lemma took, argument for argument.
--
-- **It costs one precondition**: a dependent index telescope packages the index
-- with the element, so it wants @DPair@. See 'productsInScope'.
--
-- A constructor with several arguments pairs one equation per argument,
-- right-nested: @dpair@'s @DPair (Eq A a a') (λ _ . Eq B b b')@, and where an
-- argument's type mentions an earlier argument the later equation is stated
-- after transporting along the earlier one — see 'telescopic'. **Phase 20 replaced a
-- continuation-passing encoding of that conjunction**, which phase 14 had been
-- forced into because @(C : Type₀) -> …@ is at @Type₁@ and there was then no
-- cumulativity to let a @Type₀@ case sit beside it. With the products in the
-- prelude the table above is the one §3.7 always displayed, at @Type₀@.
--
-- The prelude names this module needs are therefore @Eq@ and @refl@, and
-- @DPair@, @dpair@, @Unit@, @unit@ and @Empty@.
--
-- The family is two nested eliminations of the datatype — one to fix @x@'s
-- former, one to fix @y@'s. The lemma eliminates the equality first (its
-- eliminator is J), which fixes @y@ to be @x@, and then the datatype once, which
-- is why only the diagonal cases are ever proved: @λ C k . k refl … refl@.
module Thena.Global.NoConfusion
  ( noConfusionNames
  , noConfusionInverseNames
  , generateNoConfusion
  ) where

import Thena.Core.Level (Level (..))
import Thena.Errors (Skipped (..))
import Thena.Core.Context (Entry (..), entryType, entryVar, lamOver, piOver)
import Thena.Core.Term
  ( Core (..)
  , GlobalName (..)
  , Ident (..)
  , close
  , fresh
  , freeVars
  )
import Thena.Core.Typing (check)
import Thena.Global.Env
  ( ConstructorDefinition (..)
  , Definition (..)
  , GlobalEnv
  , InductiveDefinition (..)
  , addDefinition
  , isDeclared
  , recursiveArgument
  )
import Thena.Global.Generate
  ( Chain (..)
  , Generated (..)
  , chainGoalType
  , chainProof
  , conjunctionInScope
  , dependentPairInScope
  , mentionsAnEarlierEntry
  , each
  , emptyType
  , eqAt
  , reflAt
  , curriedRefls
  , packageType
  , packageWith
  , rewriteStated
  , rewriting
  , stations
  , unpackChain
  , Stated (..)
  , equalityInScope
  , equipmentLevel
  , falsityInScope
  , freshen
  , telescopic
  , truthInScope
  , unitProof
  , varsOf
  )


-- | The two names a datatype generates: @NoConfusionNat@ and @noConfusionNat@.
--
-- Concatenation, per §3.6's own example of the rule — @noConfusionTerm@ is a
-- name the user could have written, and if they do, the declaration that would
-- generate it is refused.
noConfusionNames :: GlobalName -> (GlobalName, GlobalName)
noConfusionNames (GlobalName d) =
  (GlobalName ("NoConfusion" ++ d), GlobalName ("noConfusion" ++ d))

-- | The two names the backwards half generates: @noConfusionNatInv@ and
-- @isLeftInvNat@ — §3.5's @noConfD⁻¹@ and @isLeftInvD@.
--
-- **Named apart from 'noConfusionNames' because they are generated apart.** A
-- datatype whose forward pair is declined has no inverse either, and a caller
-- that only wants the forward lemma should not have to know these exist.
noConfusionInverseNames :: GlobalName -> (GlobalName, GlobalName)
noConfusionInverseNames (GlobalName d) =
  (GlobalName ("noConfusion" ++ d ++ "Inv"), GlobalName ("isLeftInv" ++ d))

-- | Generate, check and admit all four definitions — or say why not.
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
  | not (equalityInScope env)          = Declined NoEqInScope
  | not (productsInScope env d)        = Declined NoProducts
  | isDeclared famName env             = Clash famName
  | isDeclared lemName env             = Clash lemName
  | otherwise =
      let (famTy,   n1) = familyType n0
          (famBody, n2) = family n1
       in case verdict (check env [] n2 famBody famTy) of
            Left e   -> Rejected famName e
            Right () ->
              let env1          = addDefinition famName (MkDefinition (inductiveLevels d) [] famTy famBody) env
                  (lemTy,   n3) = lemmaType n2
                  (lemBody, n4) = lemma n3
               in case verdict (check env1 [] n4 lemBody lemTy) of
                    Left e   -> Rejected lemName e
                    Right () ->
                      backwards
                        (addDefinition lemName (MkDefinition (inductiveLevels d) [] lemTy lemBody) env1)
                        n4
  where
    -- __The backwards half__ — @noConfusionDInv@ and @isLeftInvD@, which is
    -- what injectivity over a transported chain needs: the forward lemma drops
    -- the binder it fired on, and only the round-trip law lets a later equation
    -- be restated along the proof rebuilt in its place.
    backwards env2 n
      -- __Its own precondition, and it is stricter than the forward pair's.__
      -- The forward lemma /takes/ the chain, one Π binder per equation, and so
      -- needs no product at all; the inverse /produces/ it, and a term cannot
      -- be a run of binders. So a datatype declared before the products exist —
      -- the prelude's own first few — keeps its forward pair and gets no
      -- inverse, which is exactly what a prelude-free script already gets.
      | not (backwardsInScope env2) = Generated env2 n
      | isDeclared invName env2 = Clash invName
      | isDeclared lawName env2 = Clash lawName
      | otherwise =
          let (invTy, n1) = inverseType n
              (invTm, n2) = inverseBody n1
           in case verdict (check env2 [] n2 invTm invTy) of
                Left e   -> Rejected invName e
                Right () ->
                  let env3        = addDefinition invName (MkDefinition (inductiveLevels d) [] invTy invTm) env2
                      (lawTy, n3) = lawType n2
                      (lawTm, n4) = lawBody n3
                   in case verdict (check env3 [] n4 lawTm lawTy) of
                        Left e   -> Rejected lawName e
                        Right () ->
                          Generated
                            (addDefinition lawName (MkDefinition (inductiveLevels d) [] lawTy lawTm) env3)
                            n4

    -- Everything checked here is /generated/, so it holds no level meta and
    -- can owe no obligation. The counter is not wanted either — these checks
    -- run in an empty context on closed terms.
    verdict (r, _, _) = r

    (famName, lemName) = noConfusionNames (inductiveName d)
    (invName, lawName) = noConfusionInverseNames (inductiveName d)
    lvls               = map LVar (inductiveLevels d)

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

    -- **Everything this module writes is stated at the datatype's own level**
    -- (MS3 phase 31g), and that is exactly what cumulativity buys.
    --
    -- A constructor argument's type lives at some @ℓ_arg ≤ dl@ (the size
    -- restriction), so @Eq {dl}@ applied to it is well typed: subsumption
    -- lifts a @Type ℓ_arg@ into @Type dl@. Before phase 32 the equations would
    -- have had to be stated each at its own argument's level, and then could
    -- not have been conjoined — @And@ takes two types at **one** level.
    --
    -- **AN INDEX IS NOT AN ARGUMENT AND NOTHING BOUNDS IT** (MS9 phase 227,
    -- @~3fj3k@), so the level is the datatype's own joined with every index
    -- type's — 'equipmentLevel' has why. For every family in the suite and the
    -- corpus that join /is/ the datatype's own level.
    dl = equipmentLevel env ps (inductiveLevel d) idx n0

    -- ----------------------------------------------------------------------
    -- The family
    -- ----------------------------------------------------------------------

    -- @∀ params indices (x y : D params indices) -> Type dl@
    --
    -- @λ indices (t : D params indices) . Type dl@ — the motive of both
    -- eliminations, since both compute a type and neither result depends on
    -- what was eliminated. Valued in @Type (suc dl)@, which is the level
    -- 'Thena.Core.Typing.infer' reads off it.
    typeMotive n =
      let (is, n1) = freshen n idx
          (vt, n2) = fresh n1
       in ( lamOver is (Lam (Ident "t") (familyAt (varsOf is)) (close vt (Universe dl)))
          , n2
          )

    -- One per constructor of @y@, given the constructor @x@ turned out to be.
    -- The arguments are **freshened**: on the diagonal the two telescopes are
    -- the same 'Context', so reusing its variables would have the inner binder
    -- capture the outer one and every equation read @Eq A a a@.
    innerMethod mt args c c' n =
      let (args', n1) = freshen n (constructorArguments c')
          (payload, n2)
            | constructorName c' == constructorName c = diagonal args args' n1
            | otherwise                               = (discriminate, n1)
          (body, n3) = withHypotheses mt args' payload n2
       in (lamOver args' body, n3)

    -- @Empty@ — the prelude's empty type, named rather than Church-encoded.
    -- Discharging an impossible branch is @elim Empty@ at whatever goal is
    -- wanted, which is a goal at /any/ level; the CPS form it replaces could
    -- only ever reach a @Type₀@ one.
    discriminate = emptyType dl

    -- The telescopic equality of @x@'s arguments with @y@'s, which is what
    -- injectivity says, and @Unit@ for a constructor with no arguments.
    diagonal args args' n =
      let (ty, _, n1) = telescopic dl args (map (Free . entryVar) args') n
       in (ty, n1)

    -- ----------------------------------------------------------------------
    -- The family — over the telescope (indices; element), MS9 phase 218
    -- ----------------------------------------------------------------------

    -- @∀ params is1 (x : D params is1) is2 (y : D params is2) -> Type dl@
    --
    -- **The one difference from 'familyType' is that @y@ has its OWN index
    -- group**, which is the whole point: the appendix\'s @noConfD@ is stated over
    -- the telescope @D̄ = (indices; element)@, and its @β@ step applies it to an
    -- equation whose two sides are at two different indices. The homogeneous
    -- family cannot be /applied/ there, whatever it says.
    --
    -- The payload is unchanged, and that is not an accident: on the diagonal
    -- both sides are the same constructor, whose own arguments determine both
    -- index groups, so the indices need no equations of their own and what is
    -- left to say is still the telescopic equality of the arguments.
    familyType n =
      let (vx,  n1) = fresh n
          (is2, n2) = freshen n1 idx
          (vy,  n3) = fresh n2
       in ( piOver ps (piOver idx
              (Pi (Ident "x") (familyAt (varsOf idx)) (close vx
                (piOver is2
                  (Pi (Ident "y") (familyAt (varsOf is2)) (close vy (Universe dl)))))))
          , n3
          )

    -- @λ params is1 x is2 y . elim D params ‹motive› (‹methods›) is1 x@, with the
    -- inner elimination at @is2@ rather than at the one group there used to be.
    family n =
      let (vx,  n1) = fresh n
          (is2, n2) = freshen n1 idx
          (vy,  n3) = fresh n2
          (mt,  n4) = typeMotive n3
          (ms,  n5) = each (outerMethod mt (varsOf is2) (Free vy)) n4 cs
          body      = Eliminate dn (map LVar (inductiveLevels d)) paramVars mt ms (varsOf idx) (Free vx)
       in ( lamOver ps (lamOver idx
              (Lam (Ident "x") (familyAt (varsOf idx)) (close vx
                (lamOver is2
                  (Lam (Ident "y") (familyAt (varsOf is2)) (close vy body))))))
          , n5
          )

    -- As 'outerMethod', but the second elimination is at @y@\'s own indices.
    -- 'innerMethod' is shared with the homogeneous family unchanged: it is
    -- about the two constructors and knows nothing about indices.
    outerMethod mt is2 y c n =
      let args         = constructorArguments c
          (ms, n1)     = each (innerMethod mt args c) n cs
          inner        = Eliminate dn (map LVar (inductiveLevels d)) paramVars mt ms is2 y
          (body, n2)   = withHypotheses mt args inner n1
       in (lamOver args body, n2)

    -- @λ Δ . λ IHs . dpair … (refl A₁ a₁) (dpair … (refl A₂ a₂) …)@ — the only
    -- proof this generator ever writes, built by the same function that builds
    -- the type it inhabits so that the two nestings cannot drift apart, and
    -- @unit@ where that type is @Unit@.
    --
    -- **Each equation is proved by @refl@ even where its type carries a
    -- transport**, because the proof supplies @refl@ for every earlier equation
    -- and a transport along @refl@ reduces away. That is the whole reason this
    -- generator is still as simple as it was before the telescopic case: the
    -- diagonal is where the paper's §3.3 construction costs nothing.
    diagonalMethod mdg c n =
      let args           = constructorArguments c
          (_, payload, n1) = telescopic dl args (map (Free . entryVar) args) n
          (body, n2)     = withHypotheses mdg args payload n1
       in (lamOver args body, n2)

    -- ----------------------------------------------------------------------
    -- The lemma — over the same telescope, MS9 phase 218
    -- ----------------------------------------------------------------------

    -- @∀ params is1 (x : D params is1) is2 (y : D params is2) -> ‹chain› ->
    --   NoConfusionD params is1 x is2 y@
    --
    -- **The chain is curried and not packaged**, which is the one place this
    -- departs from the homogeneous lemma's single @Eq@ argument. A specialiser
    -- holds its equations as separate Π binders, one per tied index, so a lemma
    -- it is going to call must take them that way; packaging them here would
    -- only be unpacked at every use site. 'Thena.Global.Generate.stations' and
    -- 'Thena.Global.Generate.package' are the same walk in the two shapes.
    --
    -- **The telescope is the indices /and/ the element, with nothing special
    -- about the element** (MS9 phase 220, where the walk became
    -- 'Thena.Global.Generate.Chain' and grew two more callers). The element
    -- used to be handled apart from the indices, its equation eliminated by a
    -- @transport@ in the base case rather than by the same J as every other
    -- position; it is one more entry of one telescope now, and the base case is
    -- the diagonal and nothing else.
    confusionChain n =
      let (vx, n1) = fresh n
          theta    = idx ++ [Hypothesis vx (Ident "x") (familyAt (varsOf idx))]
       in ( Chain
              { chainLevel     = dl
              , chainTelescope = theta
              , chainGoal      = \ls rs m ->
                  ( foldl App (Global famName (map LVar (inductiveLevels d)))
                      (paramVars ++ ls ++ rs)
                  , m
                  )
              , chainDiagonal  = \shared m ->
                  case splitAt (length idx) shared of
                    (is, [a]) -> diagonalProof is a m
                    _         -> (unitProof dl, m)
              }
          , n1
          )

    lemmaType n =
      let (ch, n1) = confusionChain n
          (t,  n2) = chainGoalType ch n1
       in (piOver ps t, n2)

    -- @λ params . ‹the nested J›@ — and the body /is/ the chain's proof, because
    -- that already abstracts @is1@, @x@, @is2@, @y@ and the chain in exactly the
    -- order the type quantifies them.
    lemma n =
      let (ch, n1)   = confusionChain n
          (body, n2) = chainProof ch n1
       in (lamOver ps body, n2)


    -- @NoConfusionD params shared a shared a@, by one elimination of @a@:
    -- the family's inner elimination lands on the same constructor, so the
    -- payload reduces to the telescopic equality of its arguments with
    -- themselves, which 'diagonalMethod' proves by @refl@.
    diagonalProof shared a n =
      let (mdg, n1) = diagonalProofMotive n
          (ms,  n2) = each (diagonalMethod mdg) n1 cs
       in (Eliminate dn (map LVar (inductiveLevels d)) paramVars mdg ms shared a, n2)

    -- @λ indices (z : D params indices) . NoConfusionD params indices z indices z@
    diagonalProofMotive n =
      let (is, n1) = freshen n idx
          (vz, n2) = fresh n1
          result   = foldl App (Global famName (map LVar (inductiveLevels d)))
                       (paramVars ++ varsOf is ++ [Free vz] ++ varsOf is ++ [Free vz])
       in ( lamOver is (Lam (Ident "z") (familyAt (varsOf is)) (close vz result))
          , n2
          )

    -- ----------------------------------------------------------------------
    -- The inverse, and its round-trip law — MS9, @~rqs39@
    -- ----------------------------------------------------------------------

    -- Everything the backwards half writes, whatever the datatype: the chain is
    -- packaged, so @DPair@, @And@ and @Unit@ are all reachable, and an
    -- off-diagonal method is @elim Empty@.
    backwardsInScope e =
      dependentPairInScope e && conjunctionInScope e
        && truthInScope e && falsityInScope e

    -- @(indices; element)@ — the telescope the lemma and its inverse are both
    -- stated over, with the datatype's own index variables.
    thetaOf n =
      let (vx, n1) = fresh n
       in (idx ++ [Hypothesis vx (Ident "x") (familyAt (varsOf idx))], n1)

    -- A fresh copy of it, for the right-hand side of a statement whose left
    -- already holds those variables.
    thetaFresh n = let (tel, n1) = thetaOf n in freshen n1 tel

    -- @NoConfusionD p̄ ⟨ls⟩ ⟨rs⟩@, both sides given as terms.
    noConfAt ls rs = foldl App (Global famName lvls) (paramVars ++ ls ++ rs)

    -- The chain between two instantiations of @(indices; element)@, both given
    -- as terms, as its stations — the type and any proof follow from those, and
    -- there is one walk so a type and a proof of it cannot drift.
    chainStations ls rs n =
      let (tel, n1) = thetaOf n
          (hs,  n2) = stations dl tel rs n1
       in (map (rewriteStated (zip (map entryVar tel) ls)) hs, n2)

    -- A constructor's target indices and the constructor applied, at @ts@ —
    -- the instantiation of @(indices; element)@ one of its methods sits at.
    sidesOf c ts =
      let ss = zip (map entryVar (constructorArguments c)) ts
       in map (rewriting ss) (constructorIndices c)
            ++ [foldl App (Global (constructorName c) lvls) (paramVars ++ ts)]

    -- @∀ p̄ ⟨ī; x⟩ ⟨j̄; y⟩ -> NoConfusionD p̄ ī x j̄ y -> ⟨the chain, packaged⟩@
    --
    -- **It is packaged where the forward lemma's is curried**, and it has to be:
    -- the inverse /produces/ the chain, and a term cannot be a run of Π binders.
    -- The law below is what reconciles the two shapes at a use site.
    inverseType m0 =
      let (tel,  n1) = thetaOf m0
          (tel2, n2) = freshen n1 tel
          (hs,   n3) = chainStations (varsOf tel) (varsOf tel2) n2
          (hv,   n4) = fresh n3
       in ( piOver ps (piOver tel (piOver tel2
              (Pi (Ident "h") (noConfAt (varsOf tel) (varsOf tel2))
                  (close hv (packageType dl hs)))))
          , n4
          )

    -- @λ p̄ ⟨ī; x⟩ ⟨j̄; y⟩ h . elim D p̄ ⟨motive⟩ ⟨methods⟩ ī x j̄ y h@ — the same
    -- two eliminations the family is, with the second under the first.
    inverseBody m0 =
      let (tel,  n1) = thetaOf m0
          (tel2, n2) = freshen n1 tel
          (mot,  n3) = inverseMotive n2
          (ms,   n4) = each (inverseOuter mot) n3 cs
          (hv,   n5) = fresh n4
          vx         = entryVar (last tel)
          body       = foldl App
                         (Eliminate dn lvls paramVars mot ms (varsOf idx) (Free vx))
                         (varsOf tel2 ++ [Free hv])
       in ( lamOver ps (lamOver tel (lamOver tel2
              (Lam (Ident "h") (noConfAt (varsOf tel) (varsOf tel2))
                   (close hv body))))
          , n5
          )

    -- @λ ī x . ∀ ⟨j̄; y⟩ -> NoConfusionD p̄ ī x j̄ y -> ⟨the chain⟩@
    inverseMotive m0 =
      let (is,   n1) = freshen m0 idx
          (vt,   n2) = fresh n1
          (tel2, n3) = thetaFresh n2
          ls         = varsOf is ++ [Free vt]
          (hs,   n4) = chainStations ls (varsOf tel2) n3
          (hv,   n5) = fresh n4
       in ( lamOver is (Lam (Ident "x") (familyAt (varsOf is)) (close vt
              (piOver tel2 (Pi (Ident "h") (noConfAt ls (varsOf tel2))
                               (close hv (packageType dl hs))))))
          , n5
          )

    -- @λ ā ⟨ihs⟩ ⟨j̄; y⟩ . elim D p̄ ⟨motive⟩ ⟨methods⟩ j̄ y@
    inverseOuter mot c m0 =
      let args       = constructorArguments c
          (tel2, n1) = thetaFresh m0
          (imot, n2) = inverseInner c args n1
          (ms,   n3) = each (inverseInnerMethod imot c args) n2 cs
          vy         = entryVar (last tel2)
          inner      = Eliminate dn lvls paramVars imot ms
                         (varsOf (init tel2)) (Free vy)
          (body, n4) = withHypotheses mot args (lamOver tel2 inner) n3
       in (lamOver args body, n4)

    -- @λ j̄ y . NoConfusionD p̄ ⟨c ā⟩ j̄ y -> ⟨the chain⟩@
    inverseInner c args m0 =
      let (is,  n1) = freshen m0 idx
          (vy,  n2) = fresh n1
          ls        = sidesOf c (varsOf args)
          rs        = varsOf is ++ [Free vy]
          (hs,  n3) = chainStations ls rs n2
          (hv,  n4) = fresh n3
       in ( lamOver is (Lam (Ident "y") (familyAt (varsOf is)) (close vy
              (Pi (Ident "h") (noConfAt ls rs) (close hv (packageType dl hs)))))
          , n4
          )

    -- One per constructor of @y@, given the constructor @x@ turned out to be:
    -- off the diagonal the hypothesis is @Empty@, and on it the argument chain
    -- has to become the chain between the two constructor applications.
    inverseInnerMethod imot c args c' m0 =
      let (args', n1) = freshen m0 (constructorArguments c')
          ls          = sidesOf c  (varsOf args)
          rs          = sidesOf c' (varsOf args')
          (hs,    n2) = chainStations ls rs n1
          goal        = packageType dl hs
          (hv,    n3) = fresh n2
          (payload, n4)
            | constructorName c' == constructorName c =
                inverseDiagonal c args args' goal (Free hv) n3
            | otherwise = absurdAt goal (Free hv) n3
          (body,  n5) = withHypotheses imot args'
                          (Lam (Ident "h") (noConfAt ls rs) (close hv payload)) n4
       in (lamOver args' body, n5)

    -- @elim Empty ⟨λ _ . goal⟩ h@ — an impossible branch, discharged by name.
    absurdAt goal h n =
      let (tv, n1) = fresh n
       in ( Eliminate (GlobalName "Empty") [dl] []
              (Lam (Ident "impossible") (emptyType dl) (close tv goal)) [] [] h
          , n1
          )

    -- __The diagonal, and the whole of what the inverse has to prove.__ The
    -- hypothesis is the telescopic equality of the constructor's own arguments,
    -- packaged; what is wanted is the chain between the two applications of it.
    -- Unpack the one, walk the other down to where the two sides coincide, and
    -- there the answer is reflexivity at every station — the same bargain the
    -- forward lemma's diagonal makes, read the other way round.
    --
    -- **THE PACKAGE IS BOUND, NOT PROJECTED, AND THE DIFFERENCE IS EXPONENTIAL.**
    -- A projection names the package it reads and the package names every
    -- station in it, so writing one projection per station puts two copies of
    -- the package's tail at every level: a constructor with eleven arguments —
    -- @judgment alike@'s @Tr@, five premises over six metavariables — took the
    -- suite past six gigabytes. 'unpackChain' is one constant-motive elimination
    -- per station with the walk underneath, which is linear, and it is also the
    -- walk 'package' is paired with, so an unpacking cannot disagree with the
    -- packing it reads.
    inverseDiagonal c args args' goal pkg m0 =
      let (hs, m1) = stations dl args (varsOf args') m0
          ch = Chain
                 { chainLevel     = dl
                 , chainTelescope = args
                 , chainGoal      = \l r m ->
                     let (hs', m') = chainStations (sidesOf c l) (sidesOf c r) m
                      in (packageType dl hs', m')
                 , chainDiagonal  = \shared m ->
                     let sides     = sidesOf c shared
                         (hs', m') = chainStations sides sides m
                      in (packageWith dl hs' (curriedRefls dl hs'), m')
                 }
          (walk, m2) = chainProof ch m1
          applied    = foldl App walk
                         (varsOf args ++ varsOf args'
                            ++ map (Free . statedProof) hs)
       in unpackChain dl hs goal pkg applied m2

    -- The statement of the law at one instantiation: the chain's index half is
    -- reflexivity and its element half is the equation itself.
    --
    -- **That is the whole reason the law is stated homogeneously.** The caller
    -- holds an equation whose two sides are at one index group and supplies
    -- @refl@ for every index position, so this is the instance it needs; the
    -- fully telescopic law would want an equation between two chains neither of
    -- whose index halves is known.
    lawStatement ls rs hs q =
      let qs  = take (length hs - 1) (curriedRefls dl hs) ++ [q]
          lhs = App (foldl App (Global invName lvls) (paramVars ++ ls ++ rs))
                    (foldl App (Global lemName lvls) (paramVars ++ ls ++ rs ++ qs))
       in eqAt dl (packageType dl hs) lhs (packageWith dl hs qs)

    -- @∀ p̄ ī (x y : D p̄ ī) (q : Eq (D p̄ ī) x y) -> ⟨the statement⟩@
    lawType m0 =
      let (is, n1) = freshen m0 idx
          (vx, n2) = fresh n1
          (vy, n3) = fresh n2
          (vq, n4) = fresh n3
          dty      = familyAt (varsOf is)
          ls       = varsOf is ++ [Free vx]
          rs       = varsOf is ++ [Free vy]
          (hs, n5) = chainStations ls rs n4
       in ( piOver ps (piOver is
              (Pi (Ident "x") dty (close vx
                (Pi (Ident "y") dty (close vy
                  (Pi (Ident "q") (eqAt dl dty (Free vx) (Free vy))
                      (close vq (lawStatement ls rs hs (Free vq)))))))))
          , n5
          )

    -- __J, and then one elimination of the datatype.__ J brings the two sides
    -- together; after it both sides of the statement are closed terms that
    -- reduce as soon as the former is known, and every method is @refl@.
    lawBody m0 =
      let (is,  n1) = freshen m0 idx
          (vx,  n2) = fresh n1
          (vy,  n3) = fresh n2
          (vq,  n4) = fresh n3
          dty       = familyAt (varsOf is)
          (mot, n5) = lawMotive is dty n4
          (mh,  n6) = lawMethod is dty n5
          body      = Eliminate (GlobalName "Eq") [dl] [dty] mot [mh]
                        [Free vx, Free vy] (Free vq)
       in ( lamOver ps (lamOver is
              (Lam (Ident "x") dty (close vx
                (Lam (Ident "y") dty (close vy
                  (Lam (Ident "q") (eqAt dl dty (Free vx) (Free vy))
                       (close vq body)))))))
          , n6
          )

    -- @λ u v w . ⟨the statement at u, v and w⟩@
    lawMotive is dty m0 =
      let (uv, n2) = fresh m0
          (vv, n3) = fresh n2
          (wv, n4) = fresh n3
          ls       = varsOf is ++ [Free uv]
          rs       = varsOf is ++ [Free vv]
          (hs, n5) = chainStations ls rs n4
       in ( Lam (Ident "u") dty (close uv
              (Lam (Ident "v") dty (close vv
                (Lam (Ident "w") (eqAt dl dty (Free uv) (Free vv))
                     (close wv (lawStatement ls rs hs (Free wv)))))))
          , n5
          )

    -- @λ c . elim D p̄ ⟨λ j̄ z . the statement at (j̄; z) and refl⟩ ⟨refls⟩ ī c@
    lawMethod is dty m0 =
      let (vc,  n1) = fresh m0
          (mot, n2) = lawDiagMotive n1
          (ms,  n3) = each (lawDiagMethod mot) n2 cs
       in ( Lam (Ident "c") dty (close vc
              (Eliminate dn lvls paramVars mot ms (varsOf is) (Free vc)))
          , n3
          )

    -- @λ j̄ z . ⟨the statement at (j̄; z), (j̄; z) and refl⟩@
    lawDiagMotive m0 =
      let (js, n1) = freshen m0 idx
          (vz, n2) = fresh n1
          zt       = familyAt (varsOf js)
          sides    = varsOf js ++ [Free vz]
          (hs, n3) = chainStations sides sides n2
       in ( lamOver js (Lam (Ident "z") zt (close vz
              (lawStatement sides sides hs (reflAt dl zt (Free vz)))))
          , n3
          )

    -- Both sides have reduced to the same packaged chain of reflexivities, so
    -- the method is @refl@ of it.
    lawDiagMethod mot c m0 =
      let args     = constructorArguments c
          sides    = sidesOf c (varsOf args)
          (hs, n1) = chainStations sides sides m0
          prf      = packageWith dl hs (curriedRefls dl hs)
          (body, n2) = withHypotheses mot args
                         (reflAt dl (packageType dl hs) prf) n1
       in (lamOver args body, n2)

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



-- --------------------------------------------------------------------------
-- Preconditions
-- --------------------------------------------------------------------------

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
--   since one argument needs no conjunction and 'telescopic' emits the bare
--   equation;
-- * @DPair@ and @dpair@ by a diagonal case for a /dependent/ telescope, and
--   only there — see 'telescopic'.
--
-- Asking for all three unconditionally would be simpler and wrong. The prelude
-- must declare @Eq@ before @DPair@ — @DPair@\'s own no-confusion needs the
-- equality — and @Eq@\'s single constructor @refl@ takes a single argument, so
-- its table mentions none of the three. Under a blanket check @NoConfusionEq@
-- would be silently lost at the very line that makes everything else possible.
--
-- **And it is why @DPair@ stands third in the prelude, before @And@ and
-- @Unit@** (MS9 phase 212). @both@ takes two arguments, so @And@\'s own table
-- wants a pair; declared after it, @NoConfusionAnd@ would be lost the same
-- silent way.
productsInScope :: GlobalEnv -> InductiveDefinition -> Bool
productsInScope env d =
     (not needsEmpty || falsityInScope env)
  && (not needsUnit  || truthInScope env)
  && (not needsAnd   || conjunctionInScope env)
  && (not needsPair  || dependentPairInScope env)
  where
    cs         = inductiveConstructors d
    arity      = length . constructorArguments
    needsEmpty = length cs >= 2
    needsUnit  = any ((== 0) . arity) cs
    -- **Per position and not per arity**, because the two answers are what
    -- break the prelude's ordering if they are approximated. @dpair@ has two
    -- arguments and needs no @And@ at all — its one pair is dependent — and
    -- asking for @And@ anyway declined @NoConfusionDPair@ silently, @And@ being
    -- declared after it. The converse approximation is worse: a pair demanded
    -- and absent is a generated term that does not typecheck.
    needsAnd   = any (elem False . pairKinds) cs
    -- **And one pair the argument telescopes may not ask for.** The chain is
    -- over the telescope @(indices; element)@, so where an index's type
    -- mentions an earlier index that index travels packaged with everything
    -- after it — the element included — and 'Thena.Global.Generate.packType' of
    -- two entries or more is a dependent pair. A non-dependent index telescope
    -- asks for nothing new, the element then being packaged alone: that is why
    -- @NoConfusionEq@ is still generated, @Eq@'s two indices mentioning neither
    -- each other nor anything else and @Eq@ being declared before @DPair@.
    needsPair  = any (elem True  . pairKinds) cs
              || mentionsAnEarlierEntry (inductiveIndices d)

-- | Is this argument mentioned by the type of any argument after it?
--
-- **This says which prelude types a constructor will need, and nothing more.**
-- @True@ means the equations after this one will be stated about a transport
-- along /this/ one's proof, so @DPair@ will be wanted; @False@ means an @And@
-- will be. Which pair each equation is actually held in is decided by
-- 'telescopic', from the type it has just built — a prediction from the
-- telescope is wrong for an argument interior to a package, which is the shape
-- phase 216 found and which 'telescopic' describes.
--
-- **It cannot under-predict @DPair@.** An interior member of a package only
-- exists where the package has a head, and a head is an argument some later
-- argument's type reaches back to — so @True@ here already.
mentionedLater :: Entry -> [Entry] -> Bool
mentionedLater e after =
  any ((entryVar e `elem`) . freeVars . entryType) after

-- | Which pair each of a constructor's equations will want, in argument order,
-- one entry shorter than the telescope — the last equation heads no pair.
--
-- **Read only by 'productsInScope'.** See 'mentionedLater' for why this is a
-- statement about what the prelude must hold rather than about what gets built.
pairKinds :: ConstructorDefinition -> [Bool]
pairKinds c = case constructorArguments c of
  []     -> []
  args   -> [ mentionedLater e after
            | (e, after) <- zip args (drop 1 (suffixes args))
            , not (null after) ]
  where
    suffixes xs = case xs of
      []      -> [[]]
      _ : rest -> xs : suffixes rest
