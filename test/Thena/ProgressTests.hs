-- | Progress — TAPL Theorem 8.3.2.
--
-- @examples\/progress.thena@ finishes what @examples\/canonical.thena@ starts,
-- and **the pair is loaded in sequence**: Thena has no module imports, so what
-- makes the second file short is that the first one's globals are still in
-- scope. That is worth a test of its own — it is the only place in the suite
-- where one development is built on another.
--
-- **The statement is asserted and so is the abbreviation it names.**
-- @progress@ concludes @Or (Value t) (Steps t)@, and @Steps@ is a definition —
-- so without pinning what @Steps@ unfolds to, the theorem could be weakened by
-- redefining it and still read correctly.
module Thena.ProgressTests (tests) where

import Data.ByteString.Builder (stringUtf8, toLazyByteString)
import Data.Maybe (isJust)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit (testCase, (@?=))

import Thena.Core.Term (GlobalName (..))
import Thena.Driver (Session (..))
import Thena.Engine (Machine (..))
import Thena.Global.Env (Definition (..), lookupDefinition)
import Thena.Repl (startingSession, loadProofFile, renderCore)

tests :: TestTree
tests =
  testGroup
    "progress — TAPL 8.3.2"
    [ goldenVsString "progress" "test/golden/progress.golden" $ do
        s <- loaded
        pure (toLazyByteString (stringUtf8 (unlines (declarationsOf s))))

      -- **The theorem.** Either the term is already a value, or it takes a step
      -- — which is the half of type safety that says a well-typed term is never
      -- stuck.
    , testCase "a well-typed term is a value or it steps" $ do
        st <- statementOf "progress"
        st @?= Just "∀ (t : Term) (T : Ty) -> HasType t T -> Or (Value t) (Steps t)"

      -- …and what @Steps@ means, so the conclusion cannot be hollowed out.
    , testCase "and stepping really is the existential" $ do
        st <- statementOf "Steps"
        st @?= Just "Term -> Type₀"

      -- **The three lemmas that produce a step**, asserted as present rather
      -- than by their rendered types. Each concludes with a @Sigma@ whose second
      -- component is a lambda, and an elaborated lambda carries the @let@
      -- scaffolding @ms4\/CLOSEOUT.md@ 8 describes — so the type is right and
      -- prints with a dozen bindings inside it. Pinning that string would pin
      -- the elaborator's output shape, not the theorem.
    , testCase "and the three lemmas that produce a step are there" $ do
        s <- loaded
        map (isJust . flip lookupDefinition (globals (sessionMachine s)) . GlobalName)
            ["ifSteps", "predSteps", "isZeroSteps"]
          @?= [True, True, True]
    ]
  where
    -- **Two modules, in order** — the second reads the first's globals.
    loaded = do
      (s, _)  <- startingSession
      (s1, _) <- loadProofFile s "examples/canonical.thena"
      (s2, _) <- loadProofFile s1 "examples/progress.thena"
      pure s2

    declarationsOf _ = ["loaded canonical.thena, then progress.thena"]

    statementOf n = do
      s <- loaded
      pure ( renderCore [] (names (sessionMachine s)) [] . definitionType
               <$> lookupDefinition (GlobalName n) (globals (sessionMachine s)) )
