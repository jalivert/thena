-- | Generating the acyclicity equipment: @Below@, and the two relations the
-- appendix writes @≮@ and @≰@ (MS9 phase 219).
--
-- == What it is for
--
-- A split leaves one equation per tied index and one per constructor argument,
-- and four of @eliminating.pdf@'s five unification transitions discharge them.
-- The fifth is __cycle__: an equation between a variable and a term that
-- contains it structurally, @k ≃ s k@, which no substitution can satisfy and
-- which is therefore how a case the user correctly omitted is recognised as
-- impossible. Discharging it needs a proof that no term is structurally below
-- itself, and that proof is stated in terms of the tuple McBride's structural
-- recursion is built from — @Below@.
--
-- == The four definitions, for @N@
--
-- @
-- BelowN        : ∀ (P : N -> Type₀) (n : N) -> Type₀
-- NotEqN        : ∀ (x : N) (y : N) -> Type₀
-- NotBelowN     : ∀ (x : N) (y : N) -> Type₀
-- NotBelowEqN   : ∀ (x : N) (y : N) -> Type₀
-- @
--
-- @BelowN P n@ is the tuple asserting @P@ of everything structurally smaller
-- than @n@ — @Unit@ at a constructor with no recursive argument, and one
-- @And ‹the sub-tuple› (P a)@ per recursive argument @a@ otherwise. It is
-- __one elimination at a type-valued motive__, which is the whole of it: the
-- inductive hypothesis the eliminator hands each method /is/ the sub-tuple,
-- because the elimination computes a type rather than a proof.
--
-- @NotEqN x y@ is the appendix's @≢@, @NotBelowN@ its @≮ := Below (λ w . x ≢ w)@,
-- and @NotBelowEqN@ its @≰ := ≮ × ≢@. Phase 220 states the @Step@ lemmas and
-- @noCycle@ itself over them.
--
-- == What is __not__ generated, and it was measured
--
-- @belowD@ and @recD@ — the appendix's (59) and the structural recursor built
-- from it — are not generated, because @noCycle@ never mentions them: every
-- elimination the construction needs is an ordinary @elim D@ at a motive this
-- module writes. Measured 2026-10-27, by building the whole construction by
-- hand for a datatype with no indices;
-- @.jalivert\/reports\/2026-10-27-nocycle-against-the-generator.md@ has it.
--
-- == Indices, and why the relations take two index groups
--
-- @x@ and @y@ are at __two different index groups__, related by the telescopic
-- equality of §3.3 rather than by a single @Eq@: the cycle transition compares
-- a variable with a constructor application, and for an indexed family those sit
-- at different indices. So @NotEqN@ in general reads
--
-- @
-- NotEqD : ∀ ps ī (x : D ps ī) j̄ (y : D ps j̄) -> Type dl
--        = λ … . (q̄ : ī ≡ j̄) (q : q̄* x ≡ y) -> Empty
-- @
--
-- with the chain curried, one argument per equation —
-- 'Thena.Global.Generate.telescopicChain', the same walk the telescopic
-- no-confusion lemma is stated over.
--
-- == Its own precondition, and that is deliberate
--
-- The guard below is this bundle's and no other's. Folding its needs into the
-- no-confusion generator's precondition is what @.claude\/HAZARDS.md@ records as
-- /an additive artifact is not additive if it shares the bundle's up-front
-- guard/ — a fixture without @DPair@ lost a lemma that had worked for twenty
-- phases, and the failure named that lemma.
module Thena.Global.NoCycle
  ( noCycleNames
  , belowName
  , notEqName
  , notBelowName
  , notBelowEqName
  , generateNoCycle
  ) where

import Thena.Core.Context (Entry (..), entryType, entryVar, lamOver, piOver)
import Thena.Core.Level (Level (..))
import Thena.Core.Term
  ( Core (..)
  , GlobalName (..)
  , Ident (..)
  , close
  , fresh
  )
import Thena.Core.Typing (check)
import Thena.Errors (Skipped (..))
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
  ( Generated (..)
  , andAt
  , conjunctionInScope
  , dependentPairInScope
  , mentionsAnEarlierEntry
  , each
  , emptyType
  , equalityInScope
  , falsityInScope
  , freshen
  , telescopicChain
  , truthInScope
  , unitType
  , varsOf
  )
import Thena.Global.NoConfusion (telescopicNoConfusionNames)

-- | The names the acyclicity equipment reserves for one datatype, in the order
-- it is generated.
--
-- Concatenation, like 'Thena.Global.NoConfusion.noConfusionNames' and for §3.6's
-- reason: one namespace, shared with generated names, so @BelowNat@ is a name
-- the user could have written and the declaration that would generate it is
-- refused if they did.
noCycleNames :: GlobalName -> [GlobalName]
noCycleNames d = [belowName d, notEqName d, notBelowName d, notBelowEqName d]

-- | @BelowNat@ — the tuple of a motive at everything structurally smaller.
belowName :: GlobalName -> GlobalName
belowName (GlobalName d) = GlobalName ("Below" ++ d)

-- | @NotEqNat@ — the appendix's @≢@, over the telescope.
notEqName :: GlobalName -> GlobalName
notEqName (GlobalName d) = GlobalName ("NotEq" ++ d)

-- | @NotBelowNat@ — the appendix's @≮@.
notBelowName :: GlobalName -> GlobalName
notBelowName (GlobalName d) = GlobalName ("NotBelow" ++ d)

-- | @NotBelowEqNat@ — the appendix's @≰@.
notBelowEqName :: GlobalName -> GlobalName
notBelowEqName (GlobalName d) = GlobalName ("NotBelowEq" ++ d)

-- | Generate, check and admit the four definitions — or say why not.
--
-- Called from "Thena.Global.Declare" after 'Thena.Global.NoConfusion' has run,
-- which is what the last precondition is about: the bundle's final member
-- (phase 220's @noCycle@) calls the telescopic no-confusion lemma, so a
-- datatype that cannot have that one has no use for these four either, and
-- reserving their names would be reserving them for nothing.
generateNoCycle :: GlobalEnv -> Int -> InductiveDefinition -> Generated
generateNoCycle env n0 d
  | not (equalityInScope env)                = Declined NoEqInScope
  | not (falsityInScope env)                 = Declined NoProducts
  | not (conjunctionInScope env)             = Declined NoProducts
  | needsUnit && not (truthInScope env)      = Declined NoProducts
  | needsPair && not (dependentPairInScope env) = Declined NoProducts
  | not (isDeclared telLemName env)          = Declined NoProducts
  | otherwise = case filter (`isDeclared` env) (noCycleNames dn) of
      (g : _) -> Clash g
      []      ->
        admit env n0
          [ (belowName      dn, belowType,      belowBody)
          , (notEqName      dn, relationType,   notEqBody)
          , (notBelowName   dn, relationType,   notBelowBody)
          , (notBelowEqName dn, relationType,   notBelowEqBody)
          ]
  where
    -- | Each definition in turn, in the environment the ones before it left.
    -- **A 'Rejected' here is a generator bug**, like 'Thena.Global.NoConfusion'\'s,
    -- and carries the 'Thena.Errors.TypeError' out to where it can be printed.
    admit e n []                      = Generated e n
    admit e n ((g, ty, body) : rest) =
      let (t, n1) = ty n
          (b, n2) = body n1
       in case verdict (check e [] n2 b t) of
            Left err -> Rejected g err
            Right () ->
              admit (addDefinition g (MkDefinition (inductiveLevels d) [] t b) e) n2 rest

    -- Everything checked here is generated, so it holds no level meta and can
    -- owe no obligation; the checks run in an empty context on closed terms.
    verdict (r, _, _) = r

    (_, telLemName) = telescopicNoConfusionNames dn

    dn        = inductiveName d
    ps        = inductiveParameters d
    idx       = inductiveIndices d
    np        = length ps
    cs        = inductiveConstructors d
    paramVars = varsOf ps
    dl        = inductiveLevel d
    levels    = map LVar (inductiveLevels d)

    -- @Unit@ is written by a method for a constructor with no recursive
    -- argument, and by nothing else; @DPair@ by the chain, exactly where the
    -- index telescope is dependent — see 'mentionsAnEarlierEntry'.
    needsUnit = any (null . recursivesOf) cs
    needsPair = mentionsAnEarlierEntry idx

    -- @D params indices@, the same spelling
    -- 'Thena.Global.Env.constructorTarget' builds.
    familyAt is = foldl App (Global dn levels) (paramVars ++ is)

    -- One of this module's own globals, applied to the parameters and then to
    -- @args@ — at the datatype's own level parameters, like every other
    -- generated reference.
    at g args = foldl App (Global g levels) (paramVars ++ args)

    -- The constructor's recursive arguments, each with the indices it sits at.
    -- **Read through 'Thena.Global.Env.recursiveArgument'**, which is the same
    -- reading 'Thena.Global.Env.eliminatorType' makes of the record — so a
    -- method cannot bind a telescope its own type does not have.
    recursivesOf c =
      [ (e, is)
      | e <- constructorArguments c
      , Just is <- [recursiveArgument dn np (entryType e)]
      ]

    -- ----------------------------------------------------------------------
    -- Below
    -- ----------------------------------------------------------------------

    -- @∀ params (P : ∀ indices (t : D params indices) -> Type dl)
    --   indices (x : D params indices) -> Type dl@
    belowType n =
      let (mt, n1) = motiveType n
          (vp, n2) = fresh n1
          (vx, n3) = fresh n2
       in ( piOver ps (Pi (Ident "P") mt (close vp
              (piOver idx (Pi (Ident "x") (familyAt (varsOf idx)) (close vx
                (Universe dl))))))
          , n3
          )

    -- @λ params P indices x . elim D params (λ indices t . Type dl) (‹methods›)
    --   indices x@
    belowBody n =
      let (mt, n1) = motiveType n
          (vp, n2) = fresh n1
          (vx, n3) = fresh n2
          (em, n4) = typeMotive n3
          (ms, n5) = each (belowMethod em (Free vp)) n4 cs
          body     = Eliminate dn levels paramVars em ms (varsOf idx) (Free vx)
       in ( lamOver ps (Lam (Ident "P") mt (close vp
              (lamOver idx (Lam (Ident "x") (familyAt (varsOf idx)) (close vx
                body)))))
          , n5
          )

    -- @∀ indices (t : D params indices) -> Type dl@ — what @P@ is.
    motiveType n =
      let (is, n1) = freshen n idx
          (vt, n2) = fresh n1
       in ( piOver is (Pi (Ident "t") (familyAt (varsOf is)) (close vt (Universe dl)))
          , n2
          )

    -- @λ indices (t : D params indices) . Type dl@ — the elimination's own
    -- motive, which is constant because the tuple's /type/ does not depend on
    -- what was eliminated. Valued in @Type (suc dl)@, which is the level
    -- 'Thena.Core.Typing.infer' reads off it.
    typeMotive n =
      let (is, n1) = freshen n idx
          (vt, n2) = fresh n1
       in ( lamOver is (Lam (Ident "t") (familyAt (varsOf is)) (close vt (Universe dl)))
          , n2
          )

    -- One per constructor: @λ Δ . λ IHs . ‹the conjunction›@.
    --
    -- **The inductive hypothesis is the sub-tuple itself.** The elimination's
    -- motive is valued in @Type dl@, so what the eliminator hands a method for
    -- a recursive argument @a@ is a term of type @Type dl@ — namely
    -- @Below P ī a@ — and the method conjoins it with @P ī a@ rather than
    -- applying anything to it. That is why @belowD@ is not owed: this is the
    -- whole of (58).
    belowMethod em p c n =
      let args       = constructorArguments c
          recs       = recursivesOf c
          (ihs, n1)  = each (\_ m -> fresh m) n recs
          conjuncts  = [ andAt dl (Free h) (foldl App p (is ++ [Free (entryVar e)]))
                       | (h, (e, is)) <- zip ihs recs
                       ]
          body       = foldr bindIH (conjoin conjuncts) (zip ihs recs)
          bindIH (h, (e, is)) acc =
            Lam (Ident "ih") (foldl App em (is ++ [Free (entryVar e)])) (close h acc)
       in (lamOver args body, n1)

    -- @Unit@ for none, the conjunct itself for one, right-nested @And@ for more
    -- — the same convention 'Thena.Global.Generate.package' follows, so a
    -- constructor with one recursive argument costs no wrapper.
    conjoin ts = case ts of
      []      -> unitType dl
      [t]     -> t
      t : rest -> andAt dl t (conjoin rest)

    -- ----------------------------------------------------------------------
    -- The two relations
    -- ----------------------------------------------------------------------

    -- @∀ params indices (x : D params indices) indices' (y : D params indices')
    --   -> Type dl@ — the type all three relations share.
    relationType n =
      let (vx,  n1) = fresh n
          (is2, n2) = freshen n1 idx
          (vy,  n3) = fresh n2
       in ( piOver ps (piOver idx
              (Pi (Ident "x") (familyAt (varsOf idx)) (close vx
                (piOver is2
                  (Pi (Ident "y") (familyAt (varsOf is2)) (close vy (Universe dl)))))))
          , n3
          )

    -- @λ params ī x j̄ y . ‹the chain› -> Empty@.
    --
    -- **The chain is over the telescope @(indices; element)@ and is curried**,
    -- one Π per equation: the index equations in order, then the element
    -- equation stated after transporting @x@ along them. A specialiser holds
    -- its equations as separate binders, so this is the shape it can apply.
    notEqBody n =
      let (vx,  n1) = fresh n
          (is2, n2) = freshen n1 idx
          (vy,  n3) = fresh n2
          tel       = idx ++ [Hypothesis vx (Ident "x") (familyAt (varsOf idx))]
          rhs       = varsOf is2 ++ [Free vy]
          (ch, n4)  = telescopicChain dl tel rhs (emptyType dl) n3
       in (relationOver vx is2 vy ch, n4)

    -- @λ params ī x j̄ y . Below params (λ k̄ w . NotEq params ī x k̄ w) j̄ y@ —
    -- the appendix's @x ≮ y := (x ≢) below y@.
    notBelowBody n =
      let (vx,  n1) = fresh n
          (is2, n2) = freshen n1 idx
          (vy,  n3) = fresh n2
          (is3, n4) = freshen n3 idx
          (vw,  n5) = fresh n4
          apart     = lamOver is3 (Lam (Ident "w") (familyAt (varsOf is3)) (close vw
                        (at (notEqName dn)
                           (varsOf idx ++ [Free vx] ++ varsOf is3 ++ [Free vw]))))
          body      = at (belowName dn) (apart : varsOf is2 ++ [Free vy])
       in (relationOver vx is2 vy body, n5)

    -- @λ params ī x j̄ y . And (NotBelow …) (NotEq …)@ — the appendix's
    -- @x ≰ y := x ≮ y × x ≢ y@, which is what @noCycle@ will be proved at and
    -- what a use site projects: the left half for the recursion, the right half
    -- for the contradiction itself.
    notBelowEqBody n =
      let (vx,  n1) = fresh n
          (is2, n2) = freshen n1 idx
          (vy,  n3) = fresh n2
          sides g   = at g (varsOf idx ++ [Free vx] ++ varsOf is2 ++ [Free vy])
          body      = andAt dl (sides (notBelowName dn)) (sides (notEqName dn))
       in (relationOver vx is2 vy body, n3)

    -- The binders all three relations share, so none of them can bind them in a
    -- different order from the type they are checked against.
    relationOver vx is2 vy body =
      lamOver ps (lamOver idx
        (Lam (Ident "x") (familyAt (varsOf idx)) (close vx
          (lamOver is2
            (Lam (Ident "y") (familyAt (varsOf is2)) (close vy body))))))
