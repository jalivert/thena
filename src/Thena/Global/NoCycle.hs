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
  , noCycleDiagName
  , noCycleName
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
  ( Chain (..)
  , Generated (..)
  , andAt
  , andFirst
  , andSecond
  , bothAt
  , chainProof
  , chainGoalType
  , curriedRefls
  , conjunctionInScope
  , dependentPairInScope
  , mentionsAnEarlierEntry
  , each
  , emptyType
  , equalityInScope
  , falsityInScope
  , freshen
  , lamsOver
  , rewriteStated
  , rewriting
  , stations
  , statedProof
  , telescopicChain
  , truthInScope
  , unitProof
  , unitType
  , unpackChain
  , varsOf
  )
import Thena.Global.NoConfusion (noConfusionNames)

-- | The names the acyclicity equipment reserves for one datatype, in the order
-- it is generated.
--
-- Concatenation, like 'Thena.Global.NoConfusion.noConfusionNames' and for §3.6's
-- reason: one namespace, shared with generated names, so @BelowNat@ is a name
-- the user could have written and the declaration that would generate it is
-- refused if they did.
noCycleNames :: GlobalName -> [GlobalName]
noCycleNames d =
  [ belowName d, notEqName d, notBelowName d, notBelowEqName d
  , noCycleDiagName d, noCycleName d
  ]



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

-- | @noCycleDiagNat@ — no term is structurally below itself.
noCycleDiagName :: GlobalName -> GlobalName
noCycleDiagName (GlobalName d) = GlobalName ("noCycleDiag" ++ d)

-- | @noCycleNat@ — and so nothing equal to a term is below it either, which is
-- what the cycle transition applies.
noCycleName :: GlobalName -> GlobalName
noCycleName (GlobalName d) = GlobalName ("noCycle" ++ d)

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
  | otherwise = case filter ((`isDeclared` env) . fst3) (relations ++ nested) of
      ((g, _, _) : _) -> Clash g
      []              -> case admit env n0 relations of
        Generated e1 n1 -> case admit e1 n1 nested of
          Generated e2 n2 -> Generated e2 n2
          _               -> Generated e1 n1
        other           -> other
  where
    fst3 (g, _, _) = g

    -- The four relations, which are generated whatever the telescopes look
    -- like, and hold nothing that can be refused.
    relations =
      [ (belowName      dn, belowType,    belowBody)
      , (notEqName      dn, relationType, notEqBody)
      , (notBelowName   dn, relationType, notBelowBody)
      , (notBelowEqName dn, relationType, notBelowEqBody)
      ]

    -- **The two that go through the nested J, and whether they are generated
    -- is read off the kernel rather than predicted from the telescope** (MS9
    -- phase 223). Both are withheld together where the checker refuses
    -- either, which is a loss of the cycle transition for that family and
    -- never a wrong acceptance: @DECISIONS.md@, /When @noCycle@ is not
    -- generated/, is what a user reads.
    --
    -- **It used to be a predicate over the constructors' telescopes**, and
    -- phase 223 measured that predicate withholding the lemma from families
    -- whose generated term the kernel accepts. A question asked of the input
    -- stands no chance of staying exactly right as the walk improves, and
    -- the walk is the thing that decides: @.claude\/HAZARDS.md@, /a predicate
    -- over the input stands in for a fact about the output/.
    nested =
      [ (noCycleDiagName dn, diagType,  diagBody)
      , (noCycleName     dn, cycleType, cycleBody)
      ]

    -- | Each definition in turn, in the environment the ones before it left.
    -- **A 'Rejected' from 'relations' is a generator bug**, like
    -- 'Thena.Global.NoConfusion'\'s, and carries the 'Thena.Errors.TypeError'
    -- out to where it can be printed. **From 'nested' it is the family\'s
    -- answer**: the caller above withholds both and the datatype is declared
    -- without them.
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

    (_, telLemName) = noConfusionNames dn

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
    recursivesOf c = recursivesAmong (constructorArguments c)

    -- The same reading of an arbitrary telescope, for a /freshened/ copy of a
    -- constructor's arguments.
    recursivesAmong tel =
      [ (e, is)
      | e <- tel
      , Just is <- [recursiveArgument dn np (entryType e)]
      ]

    -- The constructor applied to the parameters and to the variables of @tel@ —
    -- the generated wrapper's own spelling, parameters first.
    appliedAt c tel =
      foldl App (Global (constructorName c) levels) (paramVars ++ varsOf tel)

    -- A constructor's target indices, read at a freshened copy of its
    -- arguments.
    indicesAt c tel =
      map (rewriting (zip (map entryVar (constructorArguments c)) (varsOf tel)))
          (constructorIndices c)

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

    -- ----------------------------------------------------------------------
    -- noCycleDiag — no term is structurally below itself
    -- ----------------------------------------------------------------------

    -- @∀ params indices (x : D params indices) -> NotBelowD params ī x ī x@
    diagType n =
      let (vx, n1) = fresh n
       in ( piOver ps (piOver idx (Pi (Ident "x") (familyAt (varsOf idx)) (close vx
              (at (notBelowName dn)
                 (varsOf idx ++ [Free vx] ++ varsOf idx ++ [Free vx])))))
          , n1
          )

    -- @λ params indices x . elim D params (λ ī y . NotBelowD ī y ī y) (‹methods›)
    --   indices x@
    diagBody n =
      let (vx, n1) = fresh n
          (mt, n2) = diagMotive n1
          (ms, n3) = each (diagMethod mt) n2 cs
          body     = Eliminate dn levels paramVars mt ms (varsOf idx) (Free vx)
       in ( lamOver ps (lamOver idx
              (Lam (Ident "x") (familyAt (varsOf idx)) (close vx body)))
          , n3
          )

    diagMotive n =
      let (is, n1) = freshen n idx
          (vy, n2) = fresh n1
          result   = at (notBelowName dn)
                       (varsOf is ++ [Free vy] ++ varsOf is ++ [Free vy])
       in (lamOver is (Lam (Ident "y") (familyAt (varsOf is)) (close vy result)), n2)

    -- | One per constructor: @λ Δ . λ IHs . ‹the tuple›@, with the component for
    -- each recursive argument given by that argument's __Step__ lemma applied to
    -- its own inductive hypothesis — (64), with every @Φ@ empty.
    --
    -- **The Step lemma is written inline and not generated under a name.** It is
    -- used exactly once, here, so a global would reserve a name per recursive
    -- argument of every constructor and buy nothing.
    diagMethod mt c n =
      let args        = constructorArguments c
          recs        = recursivesOf c
          (ihs, n1)   = each (\_ m -> fresh m) n recs
          target      = appliedAt c args
          tis         = constructorIndices c
          (comps, n2) = each (stepAt c args target tis) n1
                          (zip [0 ..] (zip ihs recs))
          compTys     = [ at (notBelowEqName dn)
                            (tis ++ [target] ++ is ++ [Free (entryVar e)])
                        | (e, is) <- recs
                        ]
          body        = tupleOf compTys comps
          wrapped     = foldr bindIH body (zip ihs recs)
          bindIH (h, (e, is)) acc =
            Lam (Ident "ih") (foldl App mt (is ++ [Free (entryVar e)])) (close h acc)
       in (lamOver args wrapped, n2)

    -- | The proof of a right-nested @And@, matching 'conjoin' level for level.
    tupleOf tys prfs = case (tys, prfs) of
      ([],     _)      -> unitProof dl
      ([_],    [p])    -> p
      (t : ts, p : qs) -> bothAt dl t (conjoin ts) p (tupleOf ts qs)
      _                -> unitProof dl

    -- ----------------------------------------------------------------------
    -- The Step lemma, (63)–(68)
    -- ----------------------------------------------------------------------

    -- | @stepij@ applied at @b := xⱼ@ and then to its inductive hypothesis,
    -- which is the only place it is ever used.
    --
    -- Its statement is (63): if the constructor's @j@-th recursive argument is
    -- not a proper subterm of @b@, the whole application is neither a proper
    -- subterm of @b@ nor equal to it. It is proved by eliminating @b@.
    stepAt c args target tis (q, (ihv, (e, is))) n =
      let (mt, n1) = stepMotive c args target tis e is n
          (ms, n2) = each (stepFor q c args target tis e is mt) n1 cs
       in ( App (Eliminate dn levels paramVars mt ms is (Free (entryVar e))) (Free ihv)
          , n2
          )

    -- @λ j̄ b . NotBelowD ī_a a j̄ b -> NotBelowEqD ū_c (c Δ) j̄ b@
    stepMotive _ _ target tis e is n =
      let (js, n1) = freshen n idx
          (vb, n2) = fresh n1
          (vh, n3) = fresh n2
          prem     = at (notBelowName dn)
                       (is ++ [Free (entryVar e)] ++ varsOf js ++ [Free vb])
          concl    = at (notBelowEqName dn) (tis ++ [target] ++ varsOf js ++ [Free vb])
       in ( lamOver js (Lam (Ident "b") (familyAt (varsOf js)) (close vb
              (Pi (Ident "H") prem (close vh concl))))
          , n3
          )

    -- | One method of that elimination, per constructor @c'@ of @b@ — (65), and
    -- its two halves are the paper's @α@ of (67) and @β@ of (68).
    --
    -- @H@ says @xⱼ@ is not a proper subterm of @c' Δ'@, which /reduces/ to one
    -- @xⱼ ≰ x'_q@ per recursive argument of @c'@; the goal reduces the same way
    -- with @c Δ@ in place of @xⱼ@. So @α@ is that tuple again, each component
    -- being the inner inductive hypothesis fed the matching half of @H@.
    stepFor q c args target tis e is mt c' n =
      let (args', n1) = freshen n (constructorArguments c')
          recs'       = recursivesAmong args'
          (ihs', n2)  = each (\_ m -> fresh m) n1 recs'
          target'     = appliedAt c' args'
          tis'        = indicesAt c' args'
          (vH, n3)    = fresh n2
          aTy         = at (notBelowName dn) (tis ++ [target] ++ tis' ++ [target'])
          bTy         = at (notEqName dn)    (tis ++ [target] ++ tis' ++ [target'])
          hTy         = at (notBelowName dn)
                          (is ++ [Free (entryVar e)] ++ tis' ++ [target'])
          belowSides  = [ (at (notBelowName dn) (lhs ++ rhs e' is')
                          , at (notEqName dn)   (lhs ++ rhs e' is'))
                        | (e', is') <- recs'
                        ]
          lhs         = is ++ [Free (entryVar e)]
          rhs e' is'  = is' ++ [Free (entryVar e')]
          hParts      = [ at (notBelowEqName dn) (lhs ++ rhs e' is') | (e', is') <- recs' ]
          aParts      = [ at (notBelowEqName dn) (tis ++ [target] ++ rhs e' is')
                        | (e', is') <- recs'
                        ]
          (alpha, n4) = each (stepBelow (Free vH) hParts belowSides) n3
                          (zip [0 ..] ihs')
          (beta,  n5) = stepApart q c args target tis e is c' args' recs'
                          (Free vH) hParts n4
       in ( lamOver args' (foldr bindIH
              (Lam (Ident "H") hTy (close vH
                 (bothAt dl aTy bTy (tupleOf aParts alpha) beta)))
              (zip ihs' recs'))
          , n5
          )
      where
        bindIH (h, (e', is')) acc =
          Lam (Ident "ih") (foldl App mt (is' ++ [Free (entryVar e')])) (close h acc)

    -- @αq = ihq (π₁ (Hq))@.
    stepBelow h hParts belowSides (q, ihv) n =
      let (part, n1) = componentOf hParts q h n
          (bl, bq)   = belowSides !! q
          (left, n2) = andFirst dl bl bq part n1
       in (App (Free ihv) left, n2)

    -- | The @q@-th component of a right-nested @And@ whose conjuncts are @tys@.
    componentOf tys q t n = go tys q t n
      where
        go [_]        _ term m = (term, m)
        go (a : rest) 0 term m = andFirst dl a (conjoin rest) term m
        go (a : rest) k term m =
          let (t', m1) = andSecond dl a (conjoin rest) term m
           in go rest (k - 1) t' m1
        go []         _ term m = (term, m)

    -- | @β@ of (68): the two applications cannot be equal.
    --
    -- Off the diagonal the telescopic no-confusion lemma /is/ the proof — its
    -- family reduces to @Empty@ for two different constructors, so the lemma
    -- applied to the chain already has the type wanted.
    --
    -- **On the diagonal it is the paper's \"it suffices to consider the case
    -- where @x̄ = x̄'@\", and that is a second chain.** No-confusion turns the
    -- chain between the two applications into the chain between their
    -- /arguments/; eliminating that one down to its diagonal makes @Δ'@ into
    -- @Δ@, and then @H@'s own @j@-th half says @xⱼ@ is not equal to itself,
    -- which reflexivity contradicts.
    --
    -- **The argument chain's equation for @xⱼ@ cannot simply be handed over.**
    -- It transports along an /argument/\'s equation — motive @λ z . D p̄ v̄ⱼ[z]@ —
    -- where @≢@\'s own chain transports along an /index/\'s, and the two are the
    -- same term only when @v̄ⱼ@ is a variable. Eliminating is what makes them
    -- agree, by making both sides one.
    stepApart q c args target tis e is c' args' recs' h hParts n
      | constructorName c' /= constructorName c =
          let (vz, n1)  = fresh n
              theta     = idx ++ [Hypothesis vz (Ident "x") (familyAt (varsOf idx))]
              (hs0, n2) = stations dl theta (indicesAt c' args' ++ [appliedAt c' args']) n1
              hs        = map (rewriteStated (zip (map entryVar theta) (tis ++ [target]))) hs0
              pay       = foldl App (Global telLemName levels)
                            (paramVars ++ tis ++ [target]
                               ++ indicesAt c' args' ++ [appliedAt c' args']
                               ++ map (Free . statedProof) hs)
           in (lamsOver dl hs pay, n2)
      | otherwise =
          let (vz, n1)   = fresh n
              theta      = idx ++ [Hypothesis vz (Ident "x") (familyAt (varsOf idx))]
              rightSide  = indicesAt c' args' ++ [appliedAt c' args']
              (hs0, n2)  = stations dl theta rightSide n1
              hs         = map (rewriteStated (zip (map entryVar theta) (tis ++ [target]))) hs0
              pay        = foldl App (Global telLemName levels)
                             (paramVars ++ tis ++ [target] ++ rightSide
                                ++ map (Free . statedProof) hs)
              (argHs, n3) = stations dl args (varsOf args') n2
              (part, n4)  = componentOf hParts q h n3
              (ne,   n5)  = andSecond dl
                              (at (notBelowName dn) (lhs ++ rhsAt q))
                              (at (notEqName dn)    (lhs ++ rhsAt q))
                              part n4
              (apart, n6) = chainProof (apartChain args e is) n5
              applied     = foldl App apart
                              (varsOf args ++ varsOf args'
                                 ++ map (Free . statedProof) argHs ++ [ne])
              (body, n7)  = unpackChain dl argHs (emptyType dl) pay applied n6
           in (lamsOver dl hs body, n7)
      where
        lhs      = is ++ [Free (entryVar e)]
        rhsAt k  = case drop k recs' of
                     ((e', is') : _) -> is' ++ [Free (entryVar e')]
                     []              -> []
        -- **On the diagonal the two argument telescopes are the same**, so the
        -- Step lemma's own position @q@ is also the position of @H@'s half about
        -- it. Off the diagonal this function is not reached.

    -- | @∀ Δ Δ' ⟨the argument chain⟩ -> xⱼ ≢ x'ⱼ -> Empty@ — the chain that
    -- makes @β@'s diagonal go through, eliminated by
    -- 'Thena.Global.Generate.chainProof'.
    apartChain args e is =
      Chain
        { chainLevel     = dl
        , chainTelescope = args
        , chainGoal      = \ls rs ->
            Pi (Ident "ne") (at (notEqName dn) (sidesAt ls ++ sidesAt rs))
               -- Nothing of @Empty@ mentions the binder, so any variable
               -- closes it; @e@'s is one that certainly exists.
               (close (entryVar e) (emptyType dl))
        , chainDiagonal  = \shared m ->
            let (vz, m1)  = fresh m
                theta     = idx ++ [Hypothesis vz (Ident "x") (familyAt (varsOf idx))]
                diag      = sidesAt shared
                (hs0, m2) = stations dl theta diag m1
                hs        = map (rewriteStated (zip (map entryVar theta) diag)) hs0
                (nev, m3) = fresh m2
             in ( Lam (Ident "ne") (at (notEqName dn) (diag ++ diag)) (close nev
                    (foldl App (Free nev) (curriedRefls dl hs)))
                , m3
                )
        }
      where
        sidesAt ts =
          let ss = zip (map entryVar args) ts
           in map (rewriting ss) is ++ [rewriting ss (Free (entryVar e))]

    -- ----------------------------------------------------------------------
    -- noCycleD
    -- ----------------------------------------------------------------------

    -- | @∀ p̄ ī x j̄ y -> ⟨chain⟩ -> NotBelowD p̄ ī x j̄ y@ — the same chain the
    -- telescopic no-confusion lemma takes, eliminated down to
    -- @noCycleDiagD@.
    cycleChain n =
      let (vx, n1) = fresh n
          theta    = idx ++ [Hypothesis vx (Ident "x") (familyAt (varsOf idx))]
       in ( Chain
              { chainLevel     = dl
              , chainTelescope = theta
              , chainGoal      = \ls rs -> at (notBelowName dn) (ls ++ rs)
              , chainDiagonal  = \shared m -> (at (noCycleDiagName dn) shared, m)
              }
          , n1
          )

    cycleType n =
      let (ch, n1) = cycleChain n
          (t,  n2) = chainGoalType ch n1
       in (piOver ps t, n2)

    cycleBody n =
      let (ch, n1) = cycleChain n
          (b,  n2) = chainProof ch n1
       in (lamOver ps b, n2)
