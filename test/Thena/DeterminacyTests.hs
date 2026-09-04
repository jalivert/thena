-- | MS1's target — determinacy of one-step evaluation (§9, phase 18).
--
-- @examples\/determinacy-tactics.thena.script@ is the deliverable: TAPL chapter 3's language,
-- its numeric-value predicate, its ten-rule evaluation relation, and twenty-one
-- theorems ending in Theorem 3.5.4. It is a script of command lines, so it is
-- run the way phase 11 runs any file — through 'loadFile', which is the same
-- path @:load@ takes at the prompt.
--
-- **The golden is the load's own output**, which for this file is one line per
-- declaration and three per theorem. That is deliberately not a transcript of
-- all 1190 lines: the lines that matter are the statements the kernel admitted,
-- and a proof of the wrong statement is the failure mode a transcript of moves
-- would hide.
--
-- The two cases beside it are what a golden cannot say — that the load ran to
-- the end rather than stopping, and that @determinacy@ is a global with the
-- statement it is supposed to have.
--
-- == Two versions, and they must prove the same theorem
--
-- **@examples\/determinacy-surface.thena@ is the same proof in the surface
-- language** (MS4 tier 3): a proof module of 278 lines where the script is
-- 1190, because the script\'s @back@ / @along@ navigation is gone and the
-- elimination tactic\'s motive is written out instead of derived. Both come
-- from @examples\/determinacy.py@ — one generator, two targets — so the proof
-- itself is stated once.
--
-- **The assertion that ties them together is the statement**: each is checked
-- against the /same/ rendered type for @determinacy@, so a version that proved
-- something weaker would fail here rather than pass quietly.
module Thena.DeterminacyTests (tests) where

import Data.ByteString.Builder (stringUtf8, toLazyByteString)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit (testCase, (@?=))

import Thena.Core.Term (GlobalName (..))
import Thena.Driver (Session (..))
import Thena.Engine (Machine (..))
import Thena.Global.Env (Definition (..), lookupDefinition)
import Thena.Repl (startingSession, loadFile, loadProofFile, renderCore)

-- | Relative to the package root, which is where the suite runs — the same
-- assumption @test\/golden@ already makes.
target :: FilePath
target = "examples/determinacy-tactics.thena.script"

surfaceTarget :: FilePath
surfaceTarget = "examples/determinacy-surface.thena"

tests :: TestTree
tests =
  testGroup
    "MS1's target — determinacy of evaluation (§9, phase 18)"
    [ goldenVsString "determinacy" "test/golden/determinacy.golden" $ do
        (s, problems) <- startingSession
        (_, out, _) <- loadFile s target
        pure (toLazyByteString (stringUtf8 (unlines (problems ++ out))))

    , testCase "the file runs to the end" $ do
        (s, _) <- startingSession
        (_, _, stopped) <- loadFile s target
        stopped @?= []

    , testCase "and TAPL 3.5.4 is a global with the statement it should have" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadFile s target
        statementOf s' @?= Just theorem

      -- **The same proof, in the surface language** (MS4 tier 3). A proof
      -- module is one program rather than a sequence of command lines, so it
      -- goes through 'loadProofFile' — and its failure, if it had one, is in
      -- the response rather than in a stopped-line count.
    , goldenVsString "determinacy-surface" "test/golden/determinacy-surface.golden" $ do
        (s, problems) <- startingSession
        (_, out) <- loadProofFile s surfaceTarget
        pure (toLazyByteString (stringUtf8 (unlines (problems ++ out))))

    , testCase "and the surface version proves the same statement" $ do
        (s, _) <- startingSession
        (s', _) <- loadProofFile s surfaceTarget
        statementOf s' @?= Just theorem
    ]
  where
    statementOf s' =
      renderCore (names (sessionMachine s')) [] . definitionType
        <$> lookupDefinition (GlobalName "determinacy") (globals (sessionMachine s'))

    theorem = "∀ (t : Term) (t1 : Term) -> Step t t1 \
              \-> ∀ (t2 : Term) -> Step t t2 -> Eq {0} Term t1 t2"
