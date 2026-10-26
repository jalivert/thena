-- | A family with a dependent index telescope — proved and admitted at a
-- /friendly/ index (phase 19), and split at a /tied/ one (MS9 phase 214).
--
-- @examples\/dependent-index.thena.script@ declares
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
--
-- __And the tied case, which is the one that states an equation — MS9 phase
-- 214, @~7gmvr@ step three.__ @examples\/tied-index-chain.thena@ declares
-- @Q : ∀ (n : N) -> Fin n -> Type₀@ and splits a @Q (s m) (fz m)@. Both indices
-- are tied there, the second's type mentions the first, so the motive states the
-- second equation only after transporting its side along the first — and the
-- second equation is stated about the first one's __proof__. Solving the first
-- removes the binder that proof is, so the solution transition supplies @refl@
-- for it and the transports ι-contract.
--
-- __It is a module and not a tactic script__, because the thing being exercised
-- is the surface split: @case … of@ is what reaches
-- "Thena.Tactics.Specialise", and a hand-driven @eliminate-core@ never does.
-- The declaration is elaborated and then type-checked whole, which is the
-- independent judge here — "Thena.SpecialiseTests" asserts the specialised
-- method type, and this says the term built from it is accepted.
module Thena.DependentIndexTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=), assertBool)

import Thena.Core.Term (GlobalName (..))
import Thena.Driver
  ( machineOf
  )
import Thena.Engine (Machine (..))
import Thena.Global.Env (Definition (..), lookupDefinition)
import Thena.Files (loadFile, loadProofFile, startingSession)
import Thena.Render ( Rendering (..)
  ,renderCore)

-- | Relative to the package root, which is where the suite runs.
target :: FilePath
target = "examples/dependent-index.thena.script"

tiedTarget :: FilePath
tiedTarget = "examples/tied-index-chain.thena"

tests :: TestTree
tests =
  testGroup
    "a dependent index telescope, end to end"
    [ testCase "the tied file runs to the end" $ do
        (s, _) <- startingSession
        (_, _, stopped) <- loadProofFile s tiedTarget
        assertBool (unlines (map show stopped)) (null stopped)

      -- The split discharged both equations, so the arm bound the
      -- constructor's two arguments and nothing else. Were either equation
      -- kept, the arm would have been handed a hypothesis it does not bind and
      -- the declaration would not be here at all.
    , testCase "and the split's definition is admitted at its written type" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadProofFile s tiedTarget
        case lookupDefinition (GlobalName "tied") (globals (machineOf s')) of
          Nothing -> assertFailure "tied was not admitted"
          Just d  ->
            renderCore (Rendering [] (names (machineOf s'))) [] (definitionType d)
              @?= "\8704 (m : N) -> Q (s m) (fz m) -> N"

    , testCase "the file runs to the end" $ do
        (s, _) <- startingSession
        (_, _, stopped) <- loadFile s target
        assertBool (unlines (map show stopped)) (null stopped)

    , testCase "and the theorem is a global with the statement it should have" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadFile s target
        case lookupDefinition (GlobalName "belowRefl") (globals (machineOf s')) of
          Nothing -> assertFailure "belowRefl was not admitted"
          Just d  ->
            renderCore (Rendering [] (names (machineOf s'))) [] (definitionType d)
              @?= "∀ (n : Nat) (i : Fin n) -> Below n i -> Eq {0} (Fin n) i i"
    ]
