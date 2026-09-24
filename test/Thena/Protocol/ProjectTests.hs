-- | A stored project (phase 112b).
--
-- **The second test is the one that matters**, and it is MS7's fourth done-when
-- for the JSON half: the shipped project, loaded from stored trees, gives the
-- same session as the shipped project loaded from its text. Not the same tree —
-- the same /session/, which is globals, rule bases, development and all.
--
-- **The labels are made to match deliberately.** A rule base records the file it
-- came from, so a text load saying @rules\/standard.thena.rules@ and a stored
-- load saying @000.json@ would differ in a field that has nothing to do with
-- whether the two doors agree. Giving the text load the stored names makes the
-- comparison total rather than partial — everything is compared, including the
-- paths, and nothing is excused.
module Thena.Protocol.ProjectTests (tests) where

import Data.List (isSuffixOf, sort)
import System.Directory (listDirectory)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Driver
  ( loadProofSource
  , loadRuleBases
  , newSession
  , parseSurfaceModule
  , rawRuleDecls
  )
import Thena.Protocol.Project
  ( Project (..)
  , ProjectError (..)
  , StoredModule (..)
  , loadInto
  , manifestName
  , readStoredProject
  , storeProject
  )

tests :: TestTree
tests =
  testGroup
    "Thena.Protocol.Project"
    [ testCase "a project survives being stored and read back" storageRoundTrip
    , testCase "and loads to the same session as its text does" sameSession
    , testCase "a missing module file is named" missingNamed
    , testCase "the manifest has the name the format says" manifestIsNamed
    ]

-- | The shipped project: the standard base, the prelude, then the numbered
-- examples in order — which is the order a session is built in.
shipped :: IO [(FilePath, String)]
shipped = do
  es <- sort . filter numbered <$> listDirectory "examples"
  let ps = ["rules/standard.thena.rules", "prelude/prelude.thena"]
             <> map ("examples/" <>) es
  mapM (\p -> (,) p <$> readFile p) ps
  where
    numbered f = ".thena" `isSuffixOf` f && take 1 f `elem` map (: []) ['0' .. '9']

-- | Parse each file into the module it stores.
projectOf :: [(FilePath, String)] -> Either String Project
projectOf files = Project "shipped" <$> traverse one files
  where
    one (p, src)
      | ".thena.rules" `isSuffixOf` p = case rawRuleDecls src of
          Left e -> Left (p <> ": " <> take 120 (show e))
          Right (nm, desc, ds) -> Right (StoredRules nm desc ds)
      | otherwise = case parseSurfaceModule src of
          Left e -> Left (p <> ": " <> take 120 (show e))
          Right (nm, items) -> Right (StoredSurface nm items)

storageRoundTrip :: IO ()
storageRoundTrip = do
  fs <- shipped
  case projectOf fs of
    Left e -> assertFailure e
    Right p -> readStoredProject (storeProject p) @?= Right p

-- | The two doors, compared on the whole session.
sameSession :: IO ()
sameSession = do
  fs <- shipped
  case projectOf fs of
    Left e -> assertFailure e
    Right p -> do
      let stored = fst (loadInto newSession p)
          viaText = fst (foldl step (newSession, 0 :: Int) fs)
      if stored == viaText
        then pure ()
        else assertFailure "a stored project and its text gave different sessions"
  where
    -- The text load is given the stored project's own file names, so that the
    -- one field that records where a base came from cannot make the comparison
    -- fail for a reason that is not about the two doors.
    step (s, i) (p, src)
      | ".thena.rules" `isSuffixOf` p = (fst (loadRuleBases s [(name i, src)]), i + 1)
      | otherwise = (fst (loadProofSource s src), i + 1)
    name i = pad (show i) <> ".json"
    pad s = replicate (max 0 (3 - length s)) '0' <> s

-- | A project is many files, so "it did not read" has to say which one.
missingNamed :: IO ()
missingNamed = do
  fs <- shipped
  case projectOf fs of
    Left e -> assertFailure e
    Right p -> case storeProject p of
      (m : _first : rest) -> readStoredProject (m : rest) @?= Left (ModuleMissing "000.json")
      _ -> assertFailure "the shipped project stored too few files"

-- | The manifest's name is part of the format, so it is pinned rather than left
-- to whatever the implementation happens to use.
manifestIsNamed :: IO ()
manifestIsNamed = manifestName @?= "project.json"
