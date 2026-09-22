-- | The numbered example programs load, in order (his request, 2026-09-21).
--
-- @examples/NN-*.thena@ and @examples/NN-*.thena.rules@ are the series he reads
-- to see what the language can do as each feature lands, so a file that has
-- gone stale is a false picture of the language. **The directory is walked, not
-- listed here**, so a new example is loaded by this test the day it is written
-- and nobody has to remember to add it.
--
-- Modules are loaded into one session, in name order, because that is how the
-- README tells a reader to load them and because a later one uses what an
-- earlier one declared. A rule file is loaded beside the shipped base and
-- every numbered rule file before it, as @:load rules@ would be — a load
-- replaces the list.
--
-- A numbered file of any other kind is a failure rather than a skip, so that a
-- new kind of example is a decision somebody makes.
module Thena.ExamplesTests (tests) where

import Data.Char (isDigit)
import Data.List (isSuffixOf, sort)
import System.Directory (listDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Driver (Response (..), Session, command, loadProofSource, loadRuleBases)
import Thena.Repl (renderResponse, rulesPath, startingSession)

tests :: TestTree
tests =
  testGroup
    "the example programs"
    [ testCase "every numbered example loads, in order" $ do
        files <- sort . filter numbered <$> listDirectory "examples"
        if null files then assertFailure "no numbered examples were found" else pure ()
        (s0, _) <- startingSession
        standard <- rulesPath >>= \p -> (,) p <$> readFile p
        go s0 [standard] files
    -- **MS6's done-when** (phase 109b): preservation for STLC, proved in the
    -- surface language over the language 01–03 declare, and stated as it is
    -- here — for closed terms (his choice, ms6/CLOSEOUT.md 32).
    , testCase "preservation for STLC is proved, at its statement" $ do
        (s0, _) <- startingSession
        s <- foldl (\ms p -> ms >>= \s1 -> readFile p >>= \src -> case loadProofSource s1 src of
                               (s2, ProofLoaded {}) -> pure s2
                               (s2, other) -> refused p s2 other)
               (pure s0)
               [ "examples/01-stlc-syntax.thena", "examples/02-contexts.thena"
               , "examples/03-typing-and-reduction.thena", "examples/07-preservation.thena" ]
        let (s', r) = command s ":infer preservation"
        renderResponse s' r @?=
          [ "preservation : \8704 (M : LC) (M1 : LC) (T : Ty) -> typing empty M T -> step M M1 -> typing empty M1 T" ]
    ]
  where
    numbered f = case f of
      a : b : '-' : _ -> isDigit a && isDigit b
      _ -> False

    go :: Session -> [(FilePath, String)] -> [FilePath] -> IO ()
    go _ _ [] = pure ()
    go s bases (f : more) = do
      let path = "examples/" ++ f
      src <- readFile path
      if ".thena.rules" `isSuffixOf` f
        then do
          let bases' = bases ++ [(path, src)]
          case loadRuleBases s bases' of
            (s', BasesLoaded _) -> go s' bases' more
            (s', other) -> refused path s' other
        else if ".thena" `isSuffixOf` f
          then case loadProofSource s src of
            (s', ProofLoaded {}) -> go s' bases more
            (s', other) -> refused path s' other
          else assertFailure (path ++ " is a numbered example of a kind this test does not load")

refused :: FilePath -> Session -> Response -> IO a
refused path s r = assertFailure (unlines ((path ++ " did not load:") : renderResponse s r))
