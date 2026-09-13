-- | @docs\/MANUAL.md@, re-driven.
--
-- **The standing rule is that the manual's transcripts are captured output**,
-- and that a hand-patched one is a lie waiting to happen. It was captured by
-- hand twice — phase 36, and again 2026-09-08 — and by 2026-09-13 twenty-six of
-- its forty-three transcript blocks no longer replayed: level metas renumber
-- whenever the prelude grows, and two examples had become outright fiction (an
-- annotated λ binder, refused by name since MS4, and a level argument that
-- phase 44 made unnecessary and the parser now rejects).
--
-- **It is a golden test, and the manual is its own golden file.** What the
-- generator produces is *the manual with every transcript re-driven*, so
-- @cabal test --test-options=--accept@ is the re-capture — no second harness to
-- keep in step with this one. The standing hazard applies with full force:
-- @--accept@ records whatever happened, so **read the diff before accepting
-- it**, and if a block now shows an error, that is a change to the program or
-- to the manual's prose and not something to write down.
--
-- Three conventions, and the manual's own header states all three to the
-- reader, which is what keeps them honest:
--
--   * chapters continue one session, because that is what typing along does;
--   * **/From a fresh session./** above a block restarts it — some chapters load
--     a file that declares its own @Nat@;
--   * @…@ elides output, either a whole run of lines or the tail of one. Some
--     of it is a single four-hundred-character term.
module Thena.ManualTests (tests) where

import Data.ByteString.Builder (stringUtf8, toLazyByteString)
import Data.List (isPrefixOf, isSuffixOf)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString)

import Thena.Repl (startingSession, transcriptIO)

manual :: FilePath
manual = "docs/MANUAL.md"

tests :: TestTree
tests =
  testGroup
    "the manual is what the program prints"
    [ goldenVsString "MANUAL.md" manual $ do
        src <- readFile manual
        rewritten <- redrive (lines src)
        pure (toLazyByteString (stringUtf8 (unlines rewritten)))
    ]

-- | A fenced block: where it starts and ends, its body, and whether the
-- sentence above it says to restart the session.
data Block = Block
  { blockStart :: Int
  , blockEnd   :: Int
  , blockBody  :: [String]
  , blockFresh :: Bool
  }

fresh :: String
fresh = "*From a fresh session.*"

prompts :: [String]
prompts = ["thena spine> ", "thena core> ", "         ... ", "> "]

isPrompt :: String -> Bool
isPrompt l = any (`isPrefixOf` l) prompts

-- | The line a prompt introduces, if this is one. **`> ` counts**: it is the
-- prompt an asking op puts up, so the line under one is an input, and missing
-- that desynchronises every block after the first @claim@.
inputOf :: String -> Maybe String
inputOf l = case [ drop (length p) l | p <- prompts, p `isPrefixOf` l ] of
  x : _ -> Just x
  []    -> Nothing

blocksIn :: [String] -> [Block]
blocksIn = go 0 "" Nothing []
  where
    go _ _ Nothing  acc [] = reverse acc
    go _ _ (Just _) acc [] = reverse acc
    go n prev open acc (l : ls)
      | "```" `isPrefixOf` l = case open of
          Just (start, body, f) ->
            go (n + 1) prev Nothing (Block start n (reverse body) f : acc) ls
          Nothing -> go (n + 1) prev (Just (n, [], prev == fresh)) acc ls
      | otherwise = case open of
          Just (start, body, f) -> go (n + 1) prev (Just (start, l : body, f)) acc ls
          Nothing -> go (n + 1) (if null (words l) then prev else l) Nothing acc ls

-- | Run the manual's inputs and splice what came back into its blocks.
redrive :: [String] -> IO [String]
redrive src = do
  replayed <- runSegments (segmentsOf shown)
  let edits =
        [ (blockStart b, blockEnd b, if matches (blockBody b) new then blockBody b else new)
        | (b, new) <- zip shown (carve replayed shown)
        ]
  pure (apply edits src)
  where
    shown = [ b | b <- blocksIn src, any isPrompt (blockBody b) ]

-- | The inputs, cut into the sessions the manual asks for: a new one at a block
-- that says so, and a new one after @:quit@.
segmentsOf :: [Block] -> [[String]]
segmentsOf bs = filter (not . null) (go [] [] bs)
  where
    go done cur [] = done ++ [cur]
    go done cur (b : rest) =
      let (done', cur') = if blockFresh b then (done ++ [cur], []) else (done, cur)
       in uncurry (\d c -> go d c rest)
            (foldl afterQuit (done', cur')
               [ i | l <- blockBody b, Just i <- [inputOf l] ])

    afterQuit (done, cur) i
      | i == ":quit" = (done ++ [cur ++ [i]], [])
      | otherwise    = (done, cur ++ [i])

runSegments :: [[String]] -> IO [String]
runSegments segs = concat <$> mapM one segs
  where
    one seg = do
      (s, _) <- startingSession
      lines <$> transcriptIO s seg

-- | Cut the replayed transcript back into blocks: one input line produces
-- exactly one prompt line, so a block that took @k@ inputs owns everything up
-- to the @k+1@th.
carve :: [String] -> [Block] -> [[String]]
carve _  []       = []
carve ls (b : bs) =
  let want = length [ () | l <- blockBody b, isPrompt l ]
      (mine, rest) = grab want 0 [] ls
   in mine : carve rest bs

grab :: Int -> Int -> [String] -> [String] -> ([String], [String])
grab _    _    acc []         = (reverse acc, [])
grab want seen acc (l : ls)
  | isPrompt l, seen == want = (reverse acc, l : ls)
  | isPrompt l               = grab want (seen + 1) (l : acc) ls
  | otherwise                = grab want seen (l : acc) ls

-- | Put each block's body back where it came from.
apply :: [(Int, Int, [String])] -> [String] -> [String]
apply edits = go 0
  where
    go _ [] = []
    go n (l : ls) = case [ e | e@(start, _, _) <- edits, start == n ] of
      (_, end, body) : _ -> l : body ++ ["```"] ++ go (end + 1) (drop (end - n) ls)
      []                 -> l : go (n + 1) ls

-- | Does the replayed block match, allowing the manual's @…@?
matches :: [String] -> [String] -> Bool
matches []       have = null have
matches (w : ws) have
  | trim w == "…" = any (matches ws) (suffixes have)
  | otherwise = case have of
      []     -> False
      h : hs
        | "…" `isSuffixOf` trim w -> trim (dropLast (trim w)) `isPrefixOf` h && matches ws hs
        | otherwise               -> w == h && matches ws hs

suffixes :: [a] -> [[a]]
suffixes xs = xs : case xs of { [] -> []; _ : r -> suffixes r }

dropLast :: String -> String
dropLast = reverse . drop 1 . reverse

trim :: String -> String
trim = dropWhile (== ' ') . reverse . dropWhile (== ' ') . reverse
