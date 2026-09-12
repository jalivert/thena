-- | Preservation — TAPL Theorem 8.3.3, and with @progress@ beside it, type
-- safety for the language.
--
-- **Three modules loaded in sequence.** @canonical.thena@ declares the terms,
-- the typing relation and canonical forms; @progress.thena@ adds the step
-- relation and 8.3.2; this one takes the typing derivation apart at each term
-- shape and proves 8.3.3. Thena has no imports, so the chain is the session's
-- globals — which is what keeps each file to what it actually contributes.
module Thena.PreservationTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

import Data.Maybe (isJust)
import Thena.Core.Term (GlobalName (..))
import Thena.Driver (Session (..))
import Thena.Engine (Machine (..))
import Thena.Global.Env (Definition (..), lookupDefinition)
import Thena.Repl (startingSession, loadProofFile, renderCore)

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

      -- The nine inversion lemmas. Asserted as present rather than by their
      -- types, for @ProgressTests@' reason: several conclude with a Π whose
      -- body carries the elaborator's @let@ scaffolding.
    , testCase "the nine inversion lemmas are all there" $ do
        s <- loaded
        map (isJust . flip lookupDefinition (globals (sessionMachine s)) . GlobalName)
            [ "ifGuard", "ifThen", "ifElse"
            , "succArg", "predArg", "isZeroArg"
            , "succAtNat", "predAtNat", "isZeroAtBool"
            ]
          @?= replicate 9 True
    ]
  where
    -- **Three modules, in order** — each reads what the ones before it declared.
    loaded = do
      (s, _)  <- startingSession
      (s1, _) <- loadProofFile s  "examples/canonical.thena"
      (s2, _) <- loadProofFile s1 "examples/progress.thena"
      (s3, _) <- loadProofFile s2 "examples/preservation.thena"
      pure s3

    statementOf n = do
      s <- loaded
      pure ( renderCore (names (sessionMachine s)) [] . definitionType
               <$> lookupDefinition (GlobalName n) (globals (sessionMachine s)) )
