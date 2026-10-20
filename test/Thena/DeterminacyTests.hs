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
-- == Three versions, and they must prove the same theorem
--
-- **@examples\/determinacy-surface.thena@ is the same proof in the surface
-- language** (MS4 tier 3): a proof module of 278 lines where the script is
-- 1190, because the script\'s @back@ / @along@ navigation is gone and the
-- elimination tactic\'s motive is written out instead of derived. Both come
-- from @examples\/determinacy.py@ — one generator, two targets — so the proof
-- itself is stated once.
--
-- **@examples\/determinacy-patterns.thena@ is the same theorem by dependent
-- pattern matching** (MS9), written by hand — and it exists to be read beside
-- the generated one, which is why it is in the suite rather than in a report.
-- Eleven of its thirteen lemmas are splits, and the generated proof's 148
-- appeals to @noConfusionTerm@ become 27.
--
-- **THE OTHER TWO ARE THE GENERATED PROOF'S OWN LEMMAS, PASTED UNCHANGED**, and
-- the file says why: @invPredSucc@ and @invIsZeroSucc@ eliminate at
-- @pred (succ v)@, which nests a constructor around the generalised variable,
-- so injectivity against @ePred@'s @pred c1@ leaves @Eq Term c1 (succ v9)@ —
-- and the copy @v9@ is quantified after the method's own binder @c1@, so
-- solving @c1@ to a term mentioning it is not a telescope move the specialiser
-- has. The arm can be written to take the leftover equation instead; **his
-- ruling of 2026-10-20 is that a proof which does that is not correctly
-- proved**, because an arm whose right-hand side is a function of an
-- unpredictable equation is the elaboration leaking into the surface. **So this
-- file shrinking further is the measure of that being fixed.**
--
-- **AND A RECURSION MAY NOT CROSS A GENERALISING SPLIT**, which is why the four
-- congruence inversions are lemmas rather than arms of @determinacy@: a
-- recursive call is tied to an induction hypothesis by the argument it names,
-- and inside such a split that name means the entry's refined copy rather than
-- the entry. Each takes the hypothesis as a parameter and the caller passes the
-- recursive call from outside the split.
--
-- **The assertion that ties all three together is the statement**: each is
-- checked against the /same/ rendered type for @determinacy@, so a version that
-- proved something weaker would fail here rather than pass quietly.
module Thena.DeterminacyTests (tests) where

import Data.Char (isAlpha)
import Data.List (isPrefixOf)
import Data.ByteString.Builder (stringUtf8, toLazyByteString)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit (testCase, (@?=), assertBool)

import Thena.Core.Term (GlobalName (..))
import Thena.Driver
  ( machineOf
  )
import Thena.Engine (Machine (..))
import Thena.Global.Env (Definition (..), lookupDefinition)
import Thena.Files (loadFile, loadProofFile, startingSession)
import Thena.Render ( Rendering (..)
  ,renderCore, renderTrouble, renderResponse)

-- | Relative to the package root, which is where the suite runs — the same
-- assumption @test\/golden@ already makes.
target :: FilePath
target = "examples/determinacy-tactics.thena.script"

surfaceTarget :: FilePath
surfaceTarget = "examples/determinacy-surface.thena"

patternTarget :: FilePath
patternTarget = "examples/determinacy-patterns.thena"

tests :: TestTree
tests =
  testGroup
    "MS1's target — determinacy of evaluation (§9, phase 18)"
    [ goldenVsString "determinacy" "test/golden/determinacy.golden" $ do
        (s, trouble) <- startingSession
        (s', out, _) <- loadFile s target
        pure (toLazyByteString (stringUtf8 (unlines
          (concatMap (renderTrouble s) trouble ++ concatMap (renderResponse s') out))))

    , testCase "the file runs to the end" $ do
        (s, _) <- startingSession
        (_, _, stopped) <- loadFile s target
        assertBool (unlines (map show stopped)) (null stopped)

    , testCase "and TAPL 3.5.4 is a global with the statement it should have" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadFile s target
        statementOf s' @?= Just theorem

      -- **The same proof, in the surface language** (MS4 tier 3). A proof
      -- module is one program rather than a sequence of command lines, so it
      -- goes through 'loadProofFile' — and its failure, if it had one, is in
      -- the response rather than in a stopped-line count.
    , goldenVsString "determinacy-surface" "test/golden/determinacy-surface.golden" $ do
        (s, trouble) <- startingSession
        (s', out, _) <- loadProofFile s surfaceTarget
        pure (toLazyByteString (stringUtf8 (unlines
          (concatMap (renderTrouble s) trouble ++ concatMap (renderResponse s') out))))

    , testCase "and the surface version proves the same statement" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadProofFile s surfaceTarget
        statementOf s' @?= Just theorem

      -- **The same theorem by pattern matching** (MS9). A proof module like the
      -- one above, so the same path loads it; the golden is what the splitter
      -- let the user get away with not writing.
    , goldenVsString "determinacy-patterns" "test/golden/determinacy-patterns.golden" $ do
        (s, trouble) <- startingSession
        (s', out, _) <- loadProofFile s patternTarget
        pure (toLazyByteString (stringUtf8 (unlines
          (concatMap (renderTrouble s) trouble ++ concatMap (renderResponse s') out))))

    , testCase "and the pattern version proves the same statement" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadProofFile s patternTarget
        statementOf s' @?= Just theorem

      -- **The style, not the theorem** — and it is here because 'HAZARDS.md'
      -- asked for it after a green suite said nothing while six of this file's
      -- arms were written in the one style the project had just ruled out. A
      -- suite that checks the statement and the trust level cannot see how a
      -- proof is written, and this file exists to demonstrate how it is
      -- written. So the header's claim is an assertion: every lemma is a split
      -- except the ones named here, which a split cannot reach and which are
      -- @determinacy.py@'s own.
      --
      -- **It fails when the boundary moves, which is the point**: a phase that
      -- makes one of these two writable, or that pastes a third one back in,
      -- changes this line and the header together.
    , testCase "and every lemma is a split but the two the header names" $ do
        src <- readFile patternTarget
        [ n | (n, body) <- definitions src, any ("elim " `isPrefixOf`) (tails' body) ]
          @?= ["invPredSucc", "invIsZeroSucc"]
    ]
  where
    -- The file's top-level equations, as (name, text). An equation begins at a
    -- line @‹name› = @ in the first column and runs to the next such line or to
    -- the next signature; everything before the first one is the preamble.
    -- **Comment lines are dropped**, or the prose between two lemmas — which
    -- says the words @elim Step@ — would be read as part of the lemma above it.
    definitions src =
      [ (n, unlines [ l | l <- ls, not (comment l) ])
      | (n, ls) <- chunks (lines src)
      ]
      where
        comment = isPrefixOf "--" . dropWhile (== ' ')
        chunks [] = []
        chunks (l : rest) = case equationName l of
          Nothing -> chunks rest
          Just n  ->
            let (mine, more) = break (\x -> headed x && not (indented x)) rest
             in (n, l : mine) : chunks more
        headed x = case x of
          c : _ -> isAlpha c
          []    -> False
        indented x = " " `isPrefixOf` x
        equationName l = case span (\c -> isAlpha c || c `elem` "'0123456789") l of
          (n@(_ : _), rest) | " = " `isPrefixOf` rest -> Just n
          _                                           -> Nothing

    tails' xs = case xs of
      []       -> [[]]
      _ : rest -> xs : tails' rest

    statementOf s' =
      renderCore (Rendering [] (names (machineOf s'))) [] . definitionType
        <$> lookupDefinition (GlobalName "determinacy") (globals (machineOf s'))

    theorem = "∀ (t : Term) (t1 : Term) -> Step t t1 \
              \-> ∀ (t2 : Term) -> Step t t2 -> Eq {0} Term t1 t2"
