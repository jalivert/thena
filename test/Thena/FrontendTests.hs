-- | @.jalivert\/FRONTEND.md@, crossed against the boundary it describes (MS7
-- phase 129).
--
-- **The document is his and is not in this repository** — @.jalivert@ is his
-- notes directory, shared with the editor worktree by @.\/jlv@ and gitignored
-- here. So the crossing runs wherever the file is and passes where it is absent,
-- which is the only honest thing a test can do about a file it does not own: a
-- clean clone has no document to be wrong about.
--
-- **A document is a mirror, and a mirror nothing crosses drifts.** This one
-- tells a frontend what it may import and call, so the two ways it can go wrong
-- are a module or a view that exists and is not in it, and a name in it that the
-- library does not have. Both are read off the sources rather than from a
-- hand-written list here — `thena.cabal`\'s @reexported-modules@ and
-- "Thena.View"\'s own export list are the oracles, so this cannot agree with the
-- document by copying it.
--
-- It is deliberately not a check that the document is /correct/: prose is not
-- testable and the walls it describes are enforced by cabal and by @Session@
-- being opaque, which @thena-boundary@ asserts by compiling at all. What is
-- testable is that nothing has been added to the boundary without being written
-- down, which is the failure that would make the document worse than nothing.
module Thena.FrontendTests (tests) where

import Data.Char (isAlphaNum)
import Data.List (isPrefixOf, isSuffixOf)
import System.Directory (doesFileExist)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

document :: FilePath
document = ".jalivert/FRONTEND.md"

tests :: TestTree
tests =
  testGroup
    "the frontend document describes the boundary it has"
    [ testCase "every module the view sublibrary re-exports is in it" $ do
        doc  <- theDocument
        cbl  <- readFile "thena.cabal"
        let missing = [ m | Just d <- [doc], m <- reexported cbl, not (m `mentionedIn` d) ]
        missing @?= []
    , testCase "and every view Thena.View exports is in it" $ do
        doc <- theDocument
        src <- readFile "src/Thena/View.hs"
        let missing = [ n | Just d <- [doc], n <- exportsOf src, not (n `mentionedIn` d) ]
        missing @?= []
      -- **Both lists above pass when they are empty**, which is what an
      -- extractor that stopped matching its source would give. Two anchors that
      -- cannot be absent while there is a boundary at all say the sources were
      -- really read.
    , testCase "and both lists were really read off the sources" $ do
        cbl <- readFile "thena.cabal"
        src <- readFile "src/Thena/View.hs"
        ( "Thena.View" `elem` reexported cbl
          -- **'Thena.Files' since MS7 phase 130**, when 'Thena.Repl' left the
          -- list. The anchor has to be a module a frontend cannot do without,
          -- and starting a session is that.
          , "Thena.Files" `elem` reexported cbl
          , "developmentView" `elem` exportsOf src
          , "Budget" `elem` exportsOf src
          , "Session" `elem` exportsOf src ) @?= (True, True, True, True, True)
    ]

-- | The document, if this checkout has it.
theDocument :: IO (Maybe String)
theDocument = do
  there <- doesFileExist document
  if there then fmap Just (readFile document) else pure Nothing

-- | The modules named in @thena.cabal@\'s @reexported-modules@ stanza.
--
-- The stanza runs from that keyword to the first line that is not a comment, a
-- blank line or an indented module name — which is how cabal reads it too.
reexported :: String -> [String]
reexported src =
  [ l
  | l <- takeWhile inStanza (drop 1 (dropWhile (not . isKeyword) (map strip (lines src))))
  , "Thena." `isPrefixOf` l
  ]
  where
    isKeyword l = "reexported-modules:" `isPrefixOf` l
    strip = trim . filter (/= ',')
    -- **The comments have to be taken /through/, not stopped at** — the stanza
    -- opens with one, so a @takeWhile@ that only admits module names returns
    -- nothing at all. It did, and the first test passed on an empty list until
    -- the anchor below caught it.
    inStanza l = null l || "--" `isPrefixOf` l || "Thena." `isPrefixOf` l

-- | The names in a module's export list: from @module X (@ to the @) where@.
--
-- Constructor lists are dropped — @Budget (..)@ contributes @Budget@ — and so
-- are the section headings, which are Haddock comments.
exportsOf :: String -> [String]
exportsOf src =
  [ name
  | l <- takeWhile (not . isEnd) (drop 1 (dropWhile (not . isStart) (map trim (lines src))))
  , not ("--" `isPrefixOf` l)
  , let name = takeWhile ok (dropWhile (`elem` ("(, " :: String)) l)
  , not (null name)
  ]
  where
    isStart l = "module Thena.View" `isPrefixOf` l
    isEnd l = ") where" `isSuffixOf` l
    ok c = isAlphaNum c || c == '\'' || c == '_'

-- | Does the document name it, as a word rather than as part of one?
--
-- Backticks and the table pipes are separators, as they are in
-- 'Thena.ManualTests.mentionedIn' — and for the same reason: a name is written
-- @`oneLine`@ in prose and @| `oneLine` |@ in a table.
mentionedIn :: String -> String -> Bool
mentionedIn w doc = w `elem` concatMap (words . map plain) (lines doc)
  where
    plain c = if c `elem` ("`|(),:" :: String) then ' ' else c

trim :: String -> String
trim = dropWhile (== ' ') . reverse . dropWhile (`elem` (" \t" :: String)) . reverse
