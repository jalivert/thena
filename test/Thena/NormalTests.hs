-- | A value is a normal form — the companion to progress.
--
-- **Why it is worth a file.** @progress@ concludes @Or (Value t) (Steps t)@, and
-- an @Or@ is not by itself exclusive: without this, nothing in the development
-- ruled out a term that is both a value and able to step. This says the two
-- halves cannot overlap.
--
-- **Every proof in it is a split as of MS9**, and the last test here is that
-- claim rather than the file's word for it: the header says there is no @elim@
-- and no appeal to no-confusion in it, and a phase that pastes one back in
-- fails this.
module Thena.NormalTests (tests) where

import Data.List (isInfixOf, isPrefixOf)
import Data.Maybe (isJust)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

import Thena.Core.Level (Level (..), instantiateLevels)
import Thena.Core.Term (GlobalName (..), substLevelsIn)
import Thena.Driver
  ( machineOf
  )
import Thena.Engine (Machine (..))
import Thena.Global.Env (Definition (..), lookupDefinition)
import Thena.Files (loadProofFile, startingSession)
import Thena.Render ( Rendering (..)
  ,renderCore)

target :: FilePath
target = "examples/normal.thena"

tests :: TestTree
tests =
  testGroup
    "a value is a normal form"
    [ -- **Level-polymorphic since MS9, and that is the intended behaviour.** A
      -- declared type's level is generalised when nothing pins it, and no proof
      -- here passes @Empty@ to @absurd@ any more. 'statementOf' answers with how
      -- many level parameters there are and with the statement read at level 0 —
      -- the parameter's printed name carries the session counter and is not what
      -- to assert. @CanonicalTests@ has the same pair for the same reason.
      testCase "a value takes no step" $ do
        st <- statementOf "valueNoStep"
        st @?= Just (1, "∀ (v : Term) -> Value v -> ∀ (u : Term) -> Step v u -> Empty {0}")

      -- **It holds of any value, not only a well-typed one** — the statement
      -- mentions no typing at all, which is what makes it the exclusivity half
      -- of progress rather than a corollary of it.
    , testCase "and it says nothing about typing" $ do
        st <- statementOf "nvNoStep"
        st @?= Just (1, "∀ (t : Term) -> NV t -> ∀ (u : Term) -> Step t u -> Empty {0}")

    , testCase "the three inversions underneath are there" $ do
        s <- loaded
        map (isJust . flip lookupDefinition (globals (machineOf s)) . GlobalName)
            ["trueNoStep", "falseNoStep", "zeroNoStep"]
          @?= [True, True, True]

      -- **The claim the rewrite is for**, asserted of the source: three of these
      -- proofs have no cases at all, and the file used to write out ten methods
      -- and ten appeals to no-confusion for each of them.
    , testCase "and every proof in it is a split" $ do
        src <- code <$> readFile target
        (any ("elim" `isInfixOf`) src, any ("noConfusion" `isInfixOf`) src)
          @?= (False, False)
    ]
  where
    -- The file without its prose, which says @elim Step@ and @noConfusionTerm@
    -- in describing what the splits replaced.
    code = filter (not . isPrefixOf "--" . dropWhile (== ' ')) . lines

    loaded = do
      (s, _)  <- startingSession
      (s1, _, _) <- loadProofFile s  "examples/canonical.thena"
      (s2, _, _) <- loadProofFile s1 "examples/progress.thena"
      (s3, _, _) <- loadProofFile s2 target
      pure s3

    statementOf n = do
      s <- loaded
      pure (atZero (machineOf s) <$>
              lookupDefinition (GlobalName n) (globals (machineOf s)))

    -- Every prenex level parameter read at 0, with how many there were.
    atZero m d =
      let ps  = definitionLevels d
          sub = maybe [] id (instantiateLevels ps (map (const LZero) ps))
       in ( length ps
          , renderCore (Rendering [] (names m)) []
              (substLevelsIn sub (definitionType d)) )
