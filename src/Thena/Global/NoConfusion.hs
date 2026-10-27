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
                      Generated (addDefinition lemName (MkDefinition (inductiveLevels d) [] lemTy lemBody) env1) n4
  where
    -- Everything checked here is /generated/, so it holds no level meta and
    -- can owe no obligation. The counter is not wanted either — these checks
    -- run in an empty context on closed terms.
    verdict (r, _, _) = r

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
              , chainGoal      = \ls rs ->
                  foldl App (Global famName (map LVar (inductiveLevels d)))
                    (paramVars ++ ls ++ rs)
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
