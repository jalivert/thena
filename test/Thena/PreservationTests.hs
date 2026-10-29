-- | Preservation — TAPL Theorem 8.3.3, and with @progress@ beside it, type
-- safety for the language.
--
-- **Three modules loaded in sequence.** @canonical.thena@ declares the terms,
-- the typing relation and canonical forms; @progress.thena@ adds the step
-- relation and 8.3.2; this one takes the typing derivation apart at each term
-- shape and proves 8.3.3. Thena has no imports, so the chain is the session's
-- globals — which is what keeps each file to what it actually contributes.
--
-- **The nine inversion lemmas are gone as of MS9** and the theorem is the only
-- thing the file declares: taking the typing derivation apart is an inner
-- @case d of@ in the arm that needs it. Their absence is asserted below,
-- because a phase that pastes one back in has moved the boundary this file
-- exists to show.
module Thena.PreservationTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

import Data.List (isInfixOf, isPrefixOf)
import Data.Maybe (isJust)
import Thena.Core.Term (GlobalName (..))
import Thena.Driver
  ( machineOf
  )
import Thena.Engine (Machine (..))
import Thena.Global.Env (Definition (..), lookupDefinition)
import Thena.Files (loadProofFile, startingSession)
import Thena.Render ( Rendering (..)
  ,renderCore)

target :: FilePath
target = "examples/preservation.thena"

tests :: TestTree
tests =
  testGroup
    "preservation — TAPL 8.3.3"
    [ -- **The theorem.** Evaluation does not change a term's type.
      testCase "a step preserves the type" $ do
        st <- statementOf "preservation"
        st @?= Just "∀ (t : Term) (t' : Term) -> Step t t' \
                    \-> ∀ (U : Ty) -> HasType t U -> HasType t' U"

      -- **Type safety is the pair**, and this asserts the other half is still
      -- the theorem it was two modules ago.
    , testCase "and progress is still there beside it" $ do
        st <- statementOf "progress"
        st @?= Just "∀ (t : Term) (T : Ty) -> HasType t T -> Or (Value t) (Steps t)"

      -- **The nine lemmas the proof used to need.** Six took the derivation
      -- apart at a term shape; three more — @succAtNat@, @predAtNat@,
      -- @isZeroAtBool@ — existed only to move the goal's type to @nat@ or
      -- @bool@ without an equation to rewrite along. A split solves that
      -- equation itself, so none of them has anything left to do.
    , testCase "the nine inversion lemmas are gone" $ do
        s <- loaded
        map (isJust . flip lookupDefinition (globals (machineOf s)) . GlobalName)
            [ "ifGuard", "ifThen", "ifElse"
            , "succArg", "predArg", "isZeroArg"
            , "succAtNat", "predAtNat", "isZeroAtBool"
            ]
          @?= replicate 9 False

    , testCase "and the proof is a split throughout" $ do
        src <- code <$> readFile target
        (any ("elim" `isInfixOf`) src, any ("noConfusion" `isInfixOf`) src)
          @?= (False, False)
    ]
  where
    -- The file without its prose, which names what the splits replaced.
    code = filter (not . isPrefixOf "--" . dropWhile (== ' ')) . lines

    -- **Three modules, in order** — each reads what the ones before it declared.
    loaded = do
      (s, _)  <- startingSession
      (s1, _, _) <- loadProofFile s  "examples/canonical.thena"
      (s2, _, _) <- loadProofFile s1 "examples/progress.thena"
      (s3, _, _) <- loadProofFile s2 target
      pure s3

    statementOf n = do
      s <- loaded
      pure ( renderCore (Rendering [] (names (machineOf s))) [] . definitionType
               <$> lookupDefinition (GlobalName n) (globals (machineOf s)) )
