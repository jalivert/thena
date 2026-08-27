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
  , LevelVar (..)
  , Normal (..)
  , levelLeq
  , levelOfNat
  , normalise
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
    ]

a, b :: LevelVar
a = LevelVar 0
b = LevelVar 1

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

-- | Two answers here and one deferral, which is exactly what phase 28 knows.
--
-- **The deferral is the point.** @levelLeq@ could compute more than this, and a
-- first draft did — and got it wrong, reporting @Just True@ for @?ℓ <= Type₃@,
-- which is unsound at @?ℓ := 4@. These tests are what caught it. Anything with
-- a variable in it postpones until phase 33 settles what the question even
-- means: validity over every instantiation, or a constraint to record.
leqTests :: [TestTree]
leqTests =
  [ testCase "constants decide outright" $
      levelLeq (levelOfNat 2) (levelOfNat 5) @?= Just True
  , testCase "and refuse outright" $
      levelLeq (levelOfNat 5) (levelOfNat 2) @?= Just False
  , testCase "equal constants are within the order" $
      levelLeq (levelOfNat 4) (levelOfNat 4) @?= Just True
  , testCase "a max of constants is still closed, so it still decides" $
      levelLeq (LMax (levelOfNat 2) (levelOfNat 3)) (levelOfNat 5) @?= Just True
  , testCase "and decides against" $
      levelLeq (LMax (levelOfNat 2) (levelOfNat 9)) (levelOfNat 5) @?= Just False
  , testCase "a variable on the left postpones" $
      levelLeq (LVar a) (levelOfNat 3) @?= Nothing
  , testCase "a variable on the right postpones" $
      levelLeq (levelOfNat 3) (LVar a) @?= Nothing
  , testCase "even when it is the same variable both sides" $
      levelLeq (LVar a) (LSuc (LVar a)) @?= Nothing
  , testCase "and even when the answer looks obvious" $
      levelLeq (LSuc (LVar a)) (LVar a) @?= Nothing
  ]

-- | The printer, whose variable branch is likewise reached from here alone.
--
-- **A closed level must print exactly as it always did** — that is most of what
-- phase 28's "the existing suite does not move" check is checking, since
-- 'Thena.Core.Typing' now hands the printer an unevaluated @LMax@ for every Π.
renderTests :: [TestTree]
renderTests =
  [ testCase "zero" $ renderLevel LZero @?= "Type₀"
  , testCase "a numeral" $ renderLevel (levelOfNat 12) @?= "Type₁₂"
  , testCase "an unevaluated max prints as its value — the Π rule's case" $
      renderLevel (LMax (levelOfNat 1) (levelOfNat 1)) @?= "Type₁"
  , testCase "and so does a lopsided one" $
      renderLevel (LMax (levelOfNat 2) (levelOfNat 7)) @?= "Type₇"
  , testCase "a bare variable" $ renderLevel (LVar a) @?= "Type (?ℓ0)"
  , testCase "a variable joined with a constant that can still win" $
      renderLevel (LMax (levelOfNat 3) (LVar a)) @?= "Type (3 ⊔ ?ℓ0)"
  , testCase "two variables" $
      renderLevel (LMax (LVar a) (LVar b)) @?= "Type (?ℓ0 ⊔ ?ℓ1)"
  , testCase "a variable with an offset" $
      renderLevel (LSuc (LVar a)) @?= "Type (suc ?ℓ0)"
  ]
