-- | A value is a normal form — the companion to progress.
--
-- **Why it is worth a file.** @progress@ concludes @Or (Value t) (Steps t)@, and
-- an @Or@ is not by itself exclusive: without this, nothing in the development
-- ruled out a term that is both a value and able to step. This says the two
-- halves cannot overlap.
module Thena.NormalTests (tests) where

import Data.Maybe (isJust)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

import Thena.Core.Term (GlobalName (..))
import Thena.Driver (Session (..))
import Thena.Engine (Machine (..))
import Thena.Global.Env (Definition (..), lookupDefinition)
import Thena.Repl (startingSession, loadProofFile, renderCore)

tests :: TestTree
tests =
  testGroup
    "a value is a normal form"
    [ testCase "a value takes no step" $ do
        st <- statementOf "valueNoStep"
        st @?= Just "∀ (v : Term) -> Value v -> ∀ (u : Term) -> Step v u -> Empty {0}"

      -- **It holds of any value, not only a well-typed one** — the statement
      -- mentions no typing at all, which is what makes it the exclusivity half
      -- of progress rather than a corollary of it.
    , testCase "and it says nothing about typing" $ do
        st <- statementOf "nvNoStep"
        st @?= Just "∀ (t : Term) -> NV t -> ∀ (u : Term) -> Step t u -> Empty {0}"

    , testCase "the three inversions underneath are there" $ do
        s <- loaded
        map (isJust . flip lookupDefinition (globals (sessionMachine s)) . GlobalName)
            ["trueNoStep", "falseNoStep", "zeroNoStep"]
          @?= [True, True, True]
    ]
  where
    loaded = do
      (s, _)  <- startingSession
      (s1, _) <- loadProofFile s  "examples/canonical.thena"
      (s2, _) <- loadProofFile s1 "examples/progress.thena"
      (s3, _) <- loadProofFile s2 "examples/normal.thena"
      pure s3

    statementOf n = do
      s <- loaded
      pure ( renderCore (names (sessionMachine s)) [] . definitionType
               <$> lookupDefinition (GlobalName n) (globals (sessionMachine s)) )
