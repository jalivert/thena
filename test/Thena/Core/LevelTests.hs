-- | The level algebra and its normal form (MS3 phase 28).
--
-- **These tests carry more weight than usual.** Nothing in the REPL builds a
-- level variable before phase 29, so 'LVar' and every var-carrying branch of
-- 'normalise', 'levelLeq' and the printer are reached from here and nowhere
-- else. If this module is thin, that code is unexercised rather than merely
-- unreached.
--
-- The closed cases are covered a second time, from the outside, by the whole
-- of the rest of the suite continuing to pass — which is phase 28's done-when.
module Thena.Core.LevelTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

import Thena.Repl (renderLevel)

import Thena.Core.Level
  ( Level (..)
  , LevelUnification (..)
  , LevelVar (..)
  , Normal (..)
  , Obligation (..)
  , Unmet (..)
  , levelLeq
  , levelOfNat
  , normalise
  , solveLevels
  , unifyLevels
  )

tests :: TestTree
tests =
  testGroup
    "Thena.Core.Level"
    [ testGroup "normalising closed levels" closedTests
    , testGroup "normalising levels with variables" variableTests
    , testGroup "canonicity — the two invariants" canonTests
    , testGroup "equality is up to the normal form" equalityTests
    , testGroup "levelLeq decides, refuses, or postpones" leqTests
    , testGroup "rendering" renderTests
    , testGroup "solveLevels discharges, refutes, or gives up" solveTests
    , testGroup "unifyLevels solves, sticks, or clashes" unifyTests
    ]

-- | A second meta, for the constraints between two unknowns.
m2 :: LevelVar
m2 = LMeta 3

-- | Two rigid parameters and one meta. The rigid\/flexible split matters to
-- nothing in this module except the printer — normalisation is indifferent to
-- it, which is the reason the split lives on 'LevelVar' rather than on 'Level'.
a, b, m :: LevelVar
a = LRigid 0
b = LRigid 1
m = LMeta 2

-- --------------------------------------------------------------------------

closedTests :: [TestTree]
closedTests =
  [ testCase "zero" $
      normalise LZero @?= Normal 0 []
  , testCase "suc counts" $
      normalise (levelOfNat 3) @?= Normal 3 []
  , testCase "max of constants evaluates" $
      normalise (LMax (levelOfNat 2) (levelOfNat 5)) @?= Normal 5 []
  , testCase "suc distributes over max" $
      normalise (LSuc (LMax (levelOfNat 1) (levelOfNat 4))) @?= Normal 5 []
  , testCase "levelOfNat clamps at zero" $
      normalise (levelOfNat (-3)) @?= Normal 0 []
  ]

variableTests :: [TestTree]
variableTests =
  [ testCase "a bare variable" $
      normalise (LVar a) @?= Normal 0 [(a, 0)]
  , -- @max 1 (a+1)@ IS @a+1@, since @a >= 0@ — so canonicity drops the
    -- constant here. The constant survives only when some instantiation could
    -- put it on top; see the canonicity group below.
    testCase "suc raises the offset, and the constant it implies is redundant" $
      normalise (LSuc (LVar a)) @?= Normal 0 [(a, 1)]
  , testCase "two variables both survive" $
      normalise (LMax (LVar a) (LVar b)) @?= Normal 0 [(a, 0), (b, 0)]
  , testCase "the same variable twice keeps the larger offset" $
      normalise (LMax (LSuc (LVar a)) (LSuc (LSuc (LVar a))))
        @?= Normal 0 [(a, 2)]
  , testCase "and keeps it whichever side it is on" $
      normalise (LMax (LSuc (LSuc (LVar a))) (LSuc (LVar a)))
        @?= Normal 0 [(a, 2)]
  , testCase "variables come out sorted, so equality can be structural" $
      normalise (LMax (LVar b) (LVar a)) @?= normalise (LMax (LVar a) (LVar b))
  ]

canonTests :: [TestTree]
canonTests =
  [ -- @v + 5 >= 5 > 3@, so the constant cannot decide the max and is dropped.
    testCase "a constant no offset can fall below is dropped" $
      normalise (LMax (levelOfNat 3) (LSuc (LSuc (LSuc (LSuc (LSuc (LVar a)))))))
        @?= Normal 0 [(a, 5)]
  , -- @v + 0@ can be @0@, so @max 3 v@ genuinely needs the 3.
    testCase "but a constant that can still win is kept" $
      normalise (LMax (levelOfNat 3) (LVar a)) @?= Normal 3 [(a, 0)]
  , testCase "so those two are not the same level" $
      (LMax (levelOfNat 3) (LVar a) == LVar a) @?= False
  , testCase "while max 3 (v+5) and v+5 are" $
      (LMax (levelOfNat 3) (offset 5 (LVar a)) == offset 5 (LVar a)) @?= True
  ]
  where
    offset k l = iterate LSuc l !! k

equalityTests :: [TestTree]
equalityTests =
  [ testCase "max 0 (suc 0) is suc 0" $
      (LMax LZero (LSuc LZero) == LSuc LZero) @?= True
  , testCase "max is commutative up to equality" $
      (LMax (LVar a) (LVar b) == LMax (LVar b) (LVar a)) @?= True
  , testCase "max is idempotent" $
      (LMax (LVar a) (LVar a) == LVar a) @?= True
  , testCase "and different variables are different levels" $
      (LVar a == LVar b) @?= False
  ]

-- | Three answers, and **the sort of variable decides which reading applies**
-- (MS3 phase 31, his ruling of 2026-08-28).
--
-- A **rigid** is a definition's prenex parameter, universally quantified, so
-- the question is **validity** and it is decidable. A **meta** is an unknown, so
-- the question is a **constraint** and the answer is postponement.
--
-- **Phase 28 answered @Nothing@ for every variable**, which was right while
-- nothing could build one. The four cases below that changed answer are the
-- ones that had to: the size restriction is @levelLeq@'s only caller and treats
-- @Nothing@ as refusal, so under the old reading no polymorphic datatype could
-- be declared at all.
leqTests :: [TestTree]
leqTests =
  [ testGroup "closed levels decide, as they always did" closedLeq
  , testGroup "a rigid parameter is universally quantified, so: validity" rigidLeq
  , testGroup "a meta is an unknown, so: postpone" metaLeq
  ]

closedLeq :: [TestTree]
closedLeq =
  [ testCase "constants decide outright" $
      levelLeq (levelOfNat 2) (levelOfNat 5) @?= Just True
  , testCase "and refuse outright" $
      levelLeq (levelOfNat 5) (levelOfNat 2) @?= Just False
  , testCase "equal constants are within the order" $
      levelLeq (levelOfNat 4) (levelOfNat 4) @?= Just True
  , testCase "a max on the left decomposes" $
      levelLeq (LMax (levelOfNat 2) (levelOfNat 3)) (levelOfNat 5) @?= Just True
  , testCase "and one component that cannot fit refutes the whole" $
      levelLeq (LMax (levelOfNat 2) (levelOfNat 9)) (levelOfNat 5) @?= Just False
  ]

rigidLeq :: [TestTree]
rigidLeq =
  [ testCase "a parameter is below its own successor, for every instantiation" $
      levelLeq (LVar a) (LSuc (LVar a)) @?= Just True
  , testCase "and never above it" $
      levelLeq (LSuc (LVar a)) (LVar a) @?= Just False
  , testCase "a parameter is not bounded by any constant — it could be larger" $
      levelLeq (LVar a) (levelOfNat 3) @?= Just False
  , testCase "nor does a constant sit below one — it could be zero" $
      levelLeq (levelOfNat 3) (LVar a) @?= Just False
  , -- Only the SAME variable can dominate a variable. @b@ could be 0 while
    -- @a@ is huge, so no other parameter bounds it.
    testCase "and one parameter never bounds another" $
      levelLeq (LVar a) (LVar b) @?= Just False
  , testCase "but a max containing it does" $
      levelLeq (LVar a) (LMax (LVar b) (LVar a)) @?= Just True
  , testCase "offsets cancel the variable and decide on the numbers" $
      levelLeq (LSuc (LVar a)) (LSuc (LSuc (LVar a))) @?= Just True
  , -- The floor: every variable at zero. @3 <= max 0 (a+5)@ holds there and
    -- variables only grow, so it holds everywhere.
    testCase "a constant under a variable with a big enough offset is valid" $
      levelLeq (levelOfNat 3) (LMax LZero (offset 5 (LVar a))) @?= Just True
  , testCase "and invalid when the offset cannot carry it" $
      levelLeq (levelOfNat 3) (LMax LZero (LVar a)) @?= Just False
  ]
  where
    offset k l = iterate LSuc l !! k

metaLeq :: [TestTree]
metaLeq =
  [ testCase "a meta on the left postpones — it could yet be small" $
      levelLeq (LVar m) (levelOfNat 3) @?= Nothing
  , testCase "a meta on the right postpones — it could yet be large" $
      levelLeq (levelOfNat 3) (LVar m) @?= Nothing
  , testCase "the same meta both sides still decides, by cancellation" $
      levelLeq (LVar m) (LSuc (LVar m)) @?= Just True
  , testCase "a rigid against a meta postpones" $
      levelLeq (LVar a) (LVar m) @?= Nothing
  , -- Refutation beats postponement: one component that can never fit settles
    -- it however the metas are solved.
    testCase "but a refutation elsewhere beats an undecided component" $
      levelLeq (LMax (levelOfNat 9) (LVar m)) (levelOfNat 2) @?= Just False
  , testCase "and a validity elsewhere does not" $
      levelLeq (LMax (levelOfNat 1) (LVar m)) (levelOfNat 2) @?= Nothing
  ]

-- | The printer, whose variable branch is reached from here alone until the
-- REPL can build a level variable.
--
-- **A closed level must print exactly as it always did** — most of what phase
-- 28's "the existing suite does not move" check was checking, since
-- 'Thena.Core.Typing' hands the printer an unevaluated @LMax@ for every Π.
renderTests :: [TestTree]
renderTests =
  [ testCase "zero" $ renderLevel LZero @?= "Type₀"
  , testCase "a numeral" $ renderLevel (levelOfNat 12) @?= "Type₁₂"
  , testCase "an unevaluated max prints as its value — the Π rule's case" $
      renderLevel (LMax (levelOfNat 1) (levelOfNat 1)) @?= "Type₁"
  , testCase "and so does a lopsided one" $
      renderLevel (LMax (levelOfNat 2) (levelOfNat 7)) @?= "Type₇"
  , testCase "a bare rigid parameter" $ renderLevel (LVar a) @?= "Type (ℓ0)"
  , testCase "a meta wears the ? a hole wears" $
      renderLevel (LVar m) @?= "Type (?ℓ2)"
  , testCase "and the two are different levels" $
      (LVar (LRigid 0) == LVar (LMeta 0)) @?= False
  , testCase "a variable joined with a constant that can still win" $
      renderLevel (LMax (levelOfNat 3) (LVar a)) @?= "Type (3 ⊔ ℓ0)"
  , testCase "two variables" $
      renderLevel (LMax (LVar a) (LVar b)) @?= "Type (ℓ0 ⊔ ℓ1)"
  , testCase "a variable with an offset" $
      renderLevel (LSuc (LVar a)) @?= "Type (suc ℓ0)"
  ]

-- --------------------------------------------------------------------------
-- The collector's pass (phase 33)
-- --------------------------------------------------------------------------

-- | 'solveLevels' is the whole of what @qed@ does with the obligations
-- conversion handed back: discharge, refute, or hand back for generalisation.
--
-- **The fixpoint is what these test hardest.** A round that solves a meta
-- substitutes it into the rest and runs again, and it is that second round —
-- not the first — that turns a bound into a decision.
--
-- The second component is the **residue**: what is neither valid nor false, and
-- what phase 33b stores on the definition rather than refusing (phase 33 did
-- refuse it, which is the one behaviour these tests record as changed).
solveTests :: [TestTree]
solveTests =
  [ testCase "nothing owed is nothing to do" $
      solveLevels [] @?= Right ([], [])

  , testCase "a closed obligation that holds is discharged" $
      solveLevels [AtMost (levelOfNat 1) (levelOfNat 3)] @?= Right ([], [])

  , testCase "and one that does not is refuted, not postponed" $
      solveLevels [AtMost (levelOfNat 3) (levelOfNat 1)]
        @?= Left (Refuted (levelOfNat 3) (levelOfNat 1))

  , -- @0 <= anything@ holds at the floor, where every variable is zero, and
    -- variables only grow. So this needs no solving at all.
    testCase "zero fits under an unknown without pinning it down" $
      solveLevels [AtMost LZero (LVar m)] @?= Right ([], [])

  , -- The commonest shape there is: @try Type@ against a goal of @Type1@. The
    -- bound leaves one value, so it is the answer rather than a choice.
    testCase "an upper bound of zero pins the level at zero" $
      solveLevels [AtMost (LSuc (LVar m)) (levelOfNat 1)] @?= Right ([(m, LZero)], [])

  , -- **Nothing is defaulted.** A level with room left in it is not chosen, it
    -- is handed back — and generalisation makes it a parameter with this very
    -- relation as its constraint. Choosing the lower bound here would quietly
    -- turn every polymorphic theorem into its @Type₀@ copy.
    testCase "an upper bound with room left in it is residue, not a solution" $
      solveLevels [AtMost (LSuc (LVar m)) (levelOfNat 3)]
        @?= Right ([], [AtMost (LSuc (LVar m)) (levelOfNat 3)])

  , testCase "a lower bound alone is residue too" $
      solveLevels [AtMost (levelOfNat 1) (LVar m)]
        @?= Right ([], [AtMost (levelOfNat 1) (LVar m)])

  , testCase "bounds that meet force the one level there was" $
      solveLevels [AtMost (levelOfNat 2) (LVar m), AtMost (LVar m) (levelOfNat 2)]
        @?= Right ([(m, levelOfNat 2)], [])

  , -- Crossed bounds are reported as the false obligation they make, rather
    -- than as an undetermined one — which is why 'forced' solves to the lower
    -- bound even when it is above the upper.
    testCase "bounds that cross are refuted, and say which way" $
      solveLevels [AtMost (levelOfNat 3) (LVar m), AtMost (LVar m) (levelOfNat 1)]
        @?= Left (Refuted (levelOfNat 3) (levelOfNat 1))

  , -- The fixpoint. @?m <= max 2 a@ is undecidable on the first round — a meta
    -- against a rigid bounds nothing — and decides on the second, once the
    -- other two obligations have pinned @?m@ to a constant.
    testCase "a solution found in one round decides another obligation" $
      solveLevels
        [ AtMost (LVar m) (LMax (levelOfNat 2) (LVar a))
        , AtMost (levelOfNat 2) (LVar m)
        , AtMost (LVar m) (levelOfNat 2)
        ]
        @?= Right ([(m, levelOfNat 2)], [])

  , testCase "a relation between two unknowns bounds neither, and is residue" $
      solveLevels [AtMost (LVar m) (LVar m2)]
        @?= Right ([], [AtMost (LVar m) (LVar m2)])

  , -- **The shape @∀ (A : Type) -> A -> A@ makes**, and the reason 'equated'
    -- exists: conversion says an equality as two inequalities, and read back as
    -- one substitution it gives @foo {ℓ0}@ rather than @foo {ℓ0 ℓ1}@ with a
    -- mutual constraint.
    testCase "two unknowns each bounded by the other are one unknown" $
      solveLevels [AtMost (LVar m) (LVar m2), AtMost (LVar m2) (LVar m)]
        @?= Right ([(m, LVar m2)], [])

  , testCase "and the equality is read even with other obligations around" $
      solveLevels
        [ AtMost (LVar m) (LVar m2)
        , AtMost (levelOfNat 1) (LVar m2)
        , AtMost (LVar m2) (LVar m)
        ]
        @?= Right ([(m, LVar m2)], [AtMost (levelOfNat 1) (LVar m2)])

  , -- A rigid is universally quantified, so 'levelLeq' decides it outright and
    -- the solver never sees it.
    testCase "a rigid parameter is decided rather than solved" $
      solveLevels [AtMost (LVar a) (LSuc (LVar a))] @?= Right ([], [])
  ]

-- --------------------------------------------------------------------------
-- Level unification (phase 33)
-- --------------------------------------------------------------------------

-- | What "Thena.Core.Unify" does with two universes. **@LevelsStuck@ is not a
-- failure** — the user's decision of 2026-08-27, that a level obligation does
-- not block — and telling it apart from @LevelsClash@ is the whole point of the
-- three answers.
unifyTests :: [TestTree]
unifyTests =
  [ testCase "equal levels need no solution" $
      unifyLevels [(levelOfNat 2, LMax (levelOfNat 2) LZero)] @?= LevelsSolved []

  , testCase "a lone meta takes the other side" $
      unifyLevels [(LVar m, levelOfNat 3)] @?= LevelsSolved [(m, levelOfNat 3)]

  , testCase "from either side" $
      unifyLevels [(levelOfNat 3, LVar m)] @?= LevelsSolved [(m, levelOfNat 3)]

  , testCase "one meta may take another" $
      unifyLevels [(LVar m, LVar m2)] @?= LevelsSolved [(m, LVar m2)]

  , -- The Optimist's lemma in the small: the first pair solves and the second
    -- is then a check rather than a second solution.
    testCase "a solution is substituted into what is left" $
      unifyLevels [(LVar m, levelOfNat 3), (LVar m, levelOfNat 3)]
        @?= LevelsSolved [(m, levelOfNat 3)]

  , testCase "and a later pair may contradict it" $
      unifyLevels [(LVar m, levelOfNat 3), (LVar m, levelOfNat 1)]
        @?= LevelsClash (levelOfNat 3) (levelOfNat 1)

  , testCase "no variable at all, and different: a clash" $
      unifyLevels [(levelOfNat 0, levelOfNat 1)]
        @?= LevelsClash (levelOfNat 0) (levelOfNat 1)

  , testCase "two rigids that differ clash — neither may be instantiated" $
      unifyLevels [(LVar a, LVar b)] @?= LevelsClash (LVar a) (LVar b)

  , -- @max ?m ?m2 = 3@ has no most general solution, so nothing is chosen. The
    -- caller proceeds; @qed@ re-derives.
    testCase "a join against a constant is stuck, not a clash" $
      unifyLevels [(LMax (LVar m) (LVar m2), levelOfNat 3)] @?= LevelsStuck

  , testCase "the occurs check keeps a meta out of its own solution" $
      unifyLevels [(LVar m, LSuc (LVar m))] @?= LevelsStuck

  , testCase "one stuck pair does not lose the others' solutions — it reports stuck" $
      unifyLevels [(LVar m, levelOfNat 1), (LMax (LVar m2) (LVar a), levelOfNat 3)]
        @?= LevelsStuck
  ]
