-- | MS1's target — determinacy of one-step evaluation (§9, phase 18).
--
-- @examples\/determinacy.thena.script@ is the deliverable: TAPL chapter 3's language,
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
module Thena.DeterminacyTests (tests) where

import Data.ByteString.Builder (stringUtf8, toLazyByteString)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Term (GlobalName (..))
import Thena.Driver (Session (..))
import Thena.Engine (Machine (..))
import Thena.Global.Env (Definition (..), lookupDefinition)
import Thena.Repl (startingSession, loadFile, renderCore)

-- | Relative to the package root, which is where the suite runs — the same
-- assumption @test\/golden@ already makes.
target :: FilePath
target = "examples/determinacy.thena.script"

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
        case lookupDefinition (GlobalName "determinacy") (globals (sessionMachine s')) of
          Nothing -> assertFailure "determinacy was not admitted"
          Just d  ->
            renderCore (names (sessionMachine s')) [] (definitionType d)
              @?= "∀ (t : Term) (t1 : Term) -> Step t t1 \
                  \-> ∀ (t2 : Term) -> Step t t2 -> Eq {0} Term t1 t2"
    ]
