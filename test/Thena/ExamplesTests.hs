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
import Test.Tasty.HUnit (assertFailure, testCase)

import Thena.Driver (Response (..), Session, loadProofSource, loadRuleBases)
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

    refused path s r = assertFailure (unlines ((path ++ " did not load:") : renderResponse s r))
