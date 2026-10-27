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
  , telescopicNoConfusionNames
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
  , equalityInScope
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

-- | The two the __telescopic__ lemma generates: @NoConfusionTelNat@ and
-- @noConfusionTelNat@ (MS9 phase 218).
--
-- **The name is temporary and says so.** The telescopic family subsumes the
-- homogeneous one — it degenerates to it where the two index groups coincide —
-- and phase 222 drops the homogeneous pair and gives these its names. Until
-- then the two live side by side, and nothing generated after this phase may
-- name the homogeneous pair, so that 222 is a rename and not a redesign.
telescopicNoConfusionNames :: GlobalName -> (GlobalName, GlobalName)
telescopicNoConfusionNames (GlobalName d) =
  (GlobalName ("NoConfusionTel" ++ d), GlobalName ("noConfusionTel" ++ d))

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
  | not (equalityInScope env)          = Declined NoEqInScope
  | not (productsInScope env d)        = Declined NoProducts
  | isDeclared famName env             = Clash famName
  | isDeclared lemName env             = Clash lemName
  | isDeclared telFamName env          = Clash telFamName
  | isDeclared telLemName env          = Clash telLemName
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
                      let env2          = addDefinition lemName (MkDefinition (inductiveLevels d) [] lemTy lemBody) env1
                          (tfTy,   n5)  = telFamilyType n4
                          (tfBody, n6)  = telFamily n5
                       in if not (telescopicInScope env2 d)
                            then Generated env2 n4
                            else case verdict (check env2 [] n6 tfBody tfTy) of
                            Left e   -> Rejected telFamName e
                            Right () ->
                              let env3         = addDefinition telFamName (MkDefinition (inductiveLevels d) [] tfTy tfBody) env2
                                  (tlTy,   n7) = telLemmaType n6
                                  (tlBody, n8) = telLemma n7
                               in case verdict (check env3 [] n8 tlBody tlTy) of
                                    Left e   -> Rejected telLemName e
                                    Right () ->
                                      Generated (addDefinition telLemName (MkDefinition (inductiveLevels d) [] tlTy tlBody) env3) n8
  where
    -- Everything checked here is /generated/, so it holds no level meta and
    -- can owe no obligation. The counter is not wanted either — these checks
    -- run in an empty context on closed terms.
    verdict (r, _, _) = r

    (famName, lemName) = noConfusionNames (inductiveName d)
    (telFamName, telLemName) = telescopicNoConfusionNames (inductiveName d)

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
    dl = inductiveLevel d

    -- ----------------------------------------------------------------------
    -- The family
    -- ----------------------------------------------------------------------

    -- @∀ params indices (x y : D params indices) -> Type dl@
    --
    -- **At the datatype's own level, not one above it.** Phase 14 had every
    -- case CPS-encoded, and @(C : Type l) -> C@ is itself at @Type (suc l)@;
    -- with @Empty@, @Unit@ and @And@ in the prelude every case is an ordinary
    -- proposition at @dl@ and the family follows it down. Phase 31g is what
    -- made @dl@ the datatype's own rather than @Type₀@; nothing else about the
    -- shape changed.
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
    -- The telescopic family (MS9 phase 218)
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
    telFamilyType n =
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
    telFamily n =
      let (vx,  n1) = fresh n
          (is2, n2) = freshen n1 idx
          (vy,  n3) = fresh n2
          (mt,  n4) = typeMotive n3
          (ms,  n5) = each (telOuterMethod mt (varsOf is2) (Free vy)) n4 cs
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
    telOuterMethod mt is2 y c n =
      let args         = constructorArguments c
          (ms, n1)     = each (innerMethod mt args c) n cs
          inner        = Eliminate dn (map LVar (inductiveLevels d)) paramVars mt ms is2 y
          (body, n2)   = withHypotheses mt args inner n1
       in (lamOver args body, n2)

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
                  (Pi (Ident "e") (eqAt dl fam (Free vx) (Free vy)) (close ve result)))))))
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
                  (Lam (Ident "e") (eqAt dl fam (Free vx) (Free vy)) (close ve body)))))))
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
                (Lam (Ident "w") (eqAt dl fam (Free vu) (Free vv)) (close vw result)))))
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
    -- The telescopic lemma (MS9 phase 218)
    -- ----------------------------------------------------------------------

    -- @∀ params is1 (x : D params is1) is2 (y : D params is2) -> ‹chain› ->
    --   NoConfusionTelD params is1 x is2 y@
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
    telChain n =
      let (vx, n1) = fresh n
          theta    = idx ++ [Hypothesis vx (Ident "x") (familyAt (varsOf idx))]
       in ( Chain
              { chainLevel     = dl
              , chainTelescope = theta
              , chainGoal      = \ls rs ->
                  foldl App (Global telFamName (map LVar (inductiveLevels d)))
                    (paramVars ++ ls ++ rs)
              , chainDiagonal  = \shared m ->
                  case splitAt (length idx) shared of
                    (is, [a]) -> telDiagonal is a m
                    _         -> (unitProof dl, m)
              }
          , n1
          )

    telLemmaType n =
      let (ch, n1) = telChain n
          (t,  n2) = chainGoalType ch n1
       in (piOver ps t, n2)

    -- @λ params . ‹the nested J›@ — and the body /is/ the chain's proof, because
    -- that already abstracts @is1@, @x@, @is2@, @y@ and the chain in exactly the
    -- order the type quantifies them.
    telLemma n =
      let (ch, n1)   = telChain n
          (body, n2) = chainProof ch n1
       in (lamOver ps body, n2)


    -- @NoConfusionTelD params shared a shared a@, by one elimination of @a@:
    -- the family's inner elimination lands on the same constructor, so the
    -- payload reduces to the telescopic equality of its arguments with
    -- themselves, which 'diagonalMethod' proves by @refl@.
    telDiagonal shared a n =
      let (mdg, n1) = telDiagonalMotive n
          (ms,  n2) = each (diagonalMethod mdg) n1 cs
       in (Eliminate dn (map LVar (inductiveLevels d)) paramVars mdg ms shared a, n2)

    -- @λ indices (z : D params indices) . NoConfusionTelD params indices z indices z@
    telDiagonalMotive n =
      let (is, n1) = freshen n idx
          (vz, n2) = fresh n1
          result   = foldl App (Global telFamName (map LVar (inductiveLevels d)))
                       (paramVars ++ varsOf is ++ [Free vz] ++ varsOf is ++ [Free vz])
       in ( lamOver is (Lam (Ident "z") (familyAt (varsOf is)) (close vz result))
          , n2
          )

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
    needsPair  = any (elem True  . pairKinds) cs

-- | Can the __telescopic__ pair be generated for this datatype (MS9 phase 218)?
--
-- **It asks for one pair the homogeneous one never did.** The telescopic chain
-- is over the telescope @(indices; element)@, so where an index's type mentions
-- an earlier index that index travels packaged with everything after it — the
-- element included — and 'packType' of two entries or more is a dependent pair.
--
-- **A non-dependent index telescope asks for nothing new**, because the element
-- is then packaged alone and 'packType' of one entry is the bare type. That is
-- not a detail: @Eq@'s own two indices mention neither each other nor anything
-- else, and @Eq@ is declared before @DPair@ is.
--
-- **Failing it skips the telescopic pair and keeps the homogeneous one**, rather
-- than declining the declaration's equipment altogether: the telescopic lemma
-- is additive until phase 222 replaces the homogeneous one with it.
telescopicInScope :: GlobalEnv -> InductiveDefinition -> Bool
telescopicInScope env d =
  not (mentionsAnEarlierEntry (inductiveIndices d)) || dependentPairInScope env


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
