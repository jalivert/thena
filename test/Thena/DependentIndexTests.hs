-- | A family with a dependent index telescope, proved and admitted (phase 19).
--
-- @examples\/dependent-index.thena@ declares
-- @Below : ∀ (n : Nat) (i : Fin n) -> Type₀@ — two indices, the second typed by
-- the first — and proves a theorem about it by induction. Before phase 19 the
-- elimination was refused outright, on a condition that only a /tied/ index can
-- violate; both of @Below@'s indices are plain variables here, so the dependent
-- one is friendly and states no equation.
--
-- **This is the check that the motive's dependent telescope is right**, and it
-- is the one the unit suite cannot make: @Thena.EliminateTests@ pins the
-- motive as a string, which says it has the shape intended, while @qed@ runs
-- 'Thena.Kernel.certify' and says the kernel accepts the term built from it.
-- Same pattern as "Thena.DeterminacyTests", and for the same reason.
module Thena.DependentIndexTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Term (GlobalName (..))
import Thena.Driver (Session (..))
import Thena.Engine (Machine (..))
import Thena.Global.Env (Definition (..), lookupDefinition)
import Thena.Repl (startingSession, loadFile, renderCore)

-- | Relative to the package root, which is where the suite runs.
target :: FilePath
target = "examples/dependent-index.thena"

tests :: TestTree
tests =
  testGroup
    "a dependent index telescope, proved end to end (phase 19)"
    [ testCase "the file runs to the end" $ do
        (s, _) <- startingSession
        (_, _, stopped) <- loadFile s target
        stopped @?= []

    , testCase "and the theorem is a global with the statement it should have" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadFile s target
        case lookupDefinition (GlobalName "belowRefl") (globals (sessionMachine s')) of
          Nothing -> assertFailure "belowRefl was not admitted"
          Just d  ->
            renderCore (names (sessionMachine s')) [] (definitionType d)
              @?= "∀ (n : Nat) (i : Fin n) -> Below n i -> Eq {0} (Fin n) i i"
    ]
