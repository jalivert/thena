-- | **The project database** — `~22qjj`, and the frontend's alone: the engine
-- writes none of it, because writing it needs the project root and the root is
-- the frontend's (§12 invariant 4).
--
-- **Its shape is his, 2026-11-11, and it is two things and not one.**
--
--   * **A proof-script per session**, under @.thena\/sessions\/@, holding the
--     transcript — *"It was never intended that the transcript would be stored
--     in the json. "* It is the format Thena already reads, so a stored session
--     replays with @:replay@ and no frontend in front of it.
--   * **One json index**, @.thena\/sessions.json@, holding what a transcript
--     cannot say about itself: the session's readable name, where its caret
--     stood, the files it read with their digests, and which theorems it proved
--     and where in the transcript each proof is.
--
-- **Nothing here is load-bearing.** Lose the database and every transcript
-- still replays; what is lost is the caret and the warning that a file moved.
-- So every read and every write swallows its own trouble, as 'Tui.Config'
-- does: a frontend's cache is not worth a crash, and a half-written index must
-- not stop the TUI starting.
--
-- **A file the user opened is never written to.** Opening
-- @examples\/Foo.thena.script@ copies its lines into a session of its own and
-- records where they came from; the original is touched only by an explicit
-- @:script save@. Persisting happens on every committed line and every caret
-- move — his, 2026-11-06: *"it happens automatically line by line… nowadays
-- editors write even more often"* — and auto-writing over somebody's corpus
-- file is not what he agreed to.
module Tui.Database
  ( Stored (..)
  , databaseDir
  , indexPath
  , scriptPathFor
  , loadIndex
  , saveIndex
  , writeTranscript
  , readTranscript
  , freshStored
  , clockStem
  , clockName
  , storedNamed
  ) where

import Control.Exception (IOException, try)
import Data.Char (isAlphaNum, toLower)
import Data.List (isPrefixOf)
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Time (defaultTimeLocale, formatTime, getZonedTime)
import System.Directory (createDirectoryIfMissing, doesFileExist)
import System.FilePath ((<.>), (</>))
import System.IO (readFile')

import Tui.Json

-- | One session as the index records it. **The transcript is not in here** —
-- 'stSlug' names the file beside it that holds the lines.
data Stored = Stored
  { stSlug :: String
    -- ^ the stem of its proof-script under @.thena\/sessions\/@, and the handle
    -- @:script resume@ takes. Minted off the clock, so it sorts by date.
  , stName :: String
    -- ^ the readable name — his own example, *"like `Friday 12:25 6.11.2026`,
    -- so that later you can list through it and it kind of makes sense"*. It is
    -- in the index rather than in the filename because a filename with spaces
    -- in it is a filename nobody can type.
  , stCaret :: Int
    -- ^ which line the caret stood on, zero-based. **This is why the database
    -- exists at all** — resuming goes to the stored caret, which is his ruling,
    -- and is what makes opening a file, resuming a session and reloading one
    -- operation at three speeds.
  , stLines :: Int
    -- ^ how many lines the transcript has, so the listing can say @12\/500@
    -- without reading every script file.
  , stRead :: [(FilePath, String)]
    -- ^ every file the session read, with its digest as sixteen hex digits —
    -- 'Thena.Driver.digestText', because a new process has no `Digest` left to
    -- compare against. The shipped prelude and standard base are in here too,
    -- so an engine upgrade shows up as a changed hash.
  , stFrom :: Maybe FilePath
    -- ^ where the lines came from, if they were opened from a path rather than
    -- typed. Provenance for the listing, and never a destination.
  , stProofs :: [(String, Int, Int)]
    -- ^ each theorem the session proved and the slice of the transcript that
    -- proves it — @:theorem@ through @qed@, as line indices. **A stored proof
    -- is a slice of a transcript and not a second kind of artifact**, which is
    -- what `~xq9m2` will read when he unparks it.
  } deriving (Eq, Show)

-- * Where it lives

-- | @.thena@ under the working directory. **The project root is the
-- frontend's**, and this is a per-project cache, which is why it is not beside
-- the per-user preferences in @~\/.config\/thena@.
databaseDir :: FilePath
databaseDir = ".thena"

indexPath :: FilePath
indexPath = databaseDir </> "sessions.json"

scriptPathFor :: String -> FilePath
scriptPathFor slug = databaseDir </> "sessions" </> slug <.> "thena.script"

-- * The index

loadIndex :: IO [Stored]
loadIndex = do
  there <- doesFileExist indexPath
  if not there
    then pure []
    else do
      -- **`readFile'` and not `readFile`, and it is not a style choice.** The
      -- index is read and then written back in the same breath (every save
      -- re-reads it so two TUIs do not drop each other's sessions), and lazy
      -- IO leaves the read handle open until the string is forced — so the
      -- write failed with the file locked, silently, and the index stopped
      -- updating after its first line. Found by probe, 2026-11-11.
      result <- try (readFile' indexPath) :: IO (Either IOException String)
      pure $ case result of
        Left _ -> []
        Right src -> fromMaybe [] (readIndex src)

readIndex :: String -> Maybe [Stored]
readIndex src = do
  top <- parseJson src
  sessions <- objectField "sessions" top >>= arrayOf
  pure (mapMaybe storedOf sessions)

-- | **A session the index cannot make sense of is dropped, not fatal.** The
-- four fields below are the ones without which an entry says nothing; the rest
-- default, so an index written by an older build still reads.
storedOf :: Json -> Maybe Stored
storedOf j = do
  slug <- objectField "slug" j >>= stringOf
  name <- objectField "name" j >>= stringOf
  caret <- objectField "caret" j >>= intOf
  count <- objectField "lines" j >>= intOf
  pure
    Stored
      { stSlug = slug
      , stName = name
      , stCaret = caret
      , stLines = count
      , stRead = maybe [] (mapMaybe readPair) (objectField "read" j >>= arrayOf)
      , stFrom = objectField "from" j >>= stringOf
      , stProofs = maybe [] (mapMaybe proofTriple) (objectField "proofs" j >>= arrayOf)
      }
  where
    readPair p = do
      path <- objectField "path" p >>= stringOf
      digest <- objectField "digest" p >>= stringOf
      pure (path, digest)
    proofTriple p = do
      name <- objectField "name" p >>= stringOf
      from <- objectField "from" p >>= intOf
      to <- objectField "to" p >>= intOf
      pure (name, from, to)

saveIndex :: [Stored] -> IO ()
saveIndex sessions = do
  _ <- try (write) :: IO (Either IOException ())
  pure ()
  where
    write = do
      createDirectoryIfMissing True (databaseDir </> "sessions")
      writeFile indexPath (renderJson (indexJson sessions) <> "\n")

indexJson :: [Stored] -> Json
indexJson sessions =
  JObj
    [ ("version", JInt 1)
    , ("sessions", JArr (map one sessions))
    ]
  where
    one s =
      JObj
        ( [ ("slug", JStr (stSlug s))
          , ("name", JStr (stName s))
          , ("caret", JInt (stCaret s))
          , ("lines", JInt (stLines s))
          ]
            <> [("from", JStr p) | Just p <- [stFrom s]]
            <> [ ("read", JArr [JObj [("path", JStr p), ("digest", JStr d)] | (p, d) <- stRead s])
               | not (null (stRead s))
               ]
            <> [ ( "proofs"
                 , JArr [JObj [("name", JStr n), ("from", JInt a), ("to", JInt b)] | (n, a, b) <- stProofs s]
                 )
               | not (null (stProofs s))
               ]
        )

-- * The transcripts

writeTranscript :: String -> [String] -> IO ()
writeTranscript slug ls = do
  _ <- try (write) :: IO (Either IOException ())
  pure ()
  where
    write = do
      createDirectoryIfMissing True (databaseDir </> "sessions")
      writeFile (scriptPathFor slug) (unlines ls)

readTranscript :: String -> IO (Maybe [String])
readTranscript slug = do
  there <- doesFileExist (scriptPathFor slug)
  if not there
    then pure Nothing
    else do
      result <- try (readFile' (scriptPathFor slug)) :: IO (Either IOException String)
      pure $ case result of
        Left _ -> Nothing
        Right src -> Just (lines src)

-- * Minting one

-- | A session named and slugged off the clock, with the slug stepped until it
-- is not one the index already holds — two sessions in one minute is a thing
-- that happens.
freshStored :: [Stored] -> Maybe FilePath -> IO Stored
freshStored existing from = do
  now <- getZonedTime
  stem <- clockStem
  let name = formatTime defaultTimeLocale "%A %H:%M %-d.%-m.%Y" now
      taken s = s `elem` map stSlug existing
      stepped = [stem <> "-" <> show n | n <- [2 .. 99 :: Int]]
      slug = case filter (not . taken) (stem : stepped) of
        (free : _) -> free
        -- A hundred sessions in one minute is not a state to have a plan for,
        -- and overwriting the first is better than refusing to start.
        [] -> stem
  pure
    Stored
      { stSlug = slug
      , stName = name
      , stCaret = 0
      , stLines = 0
      , stRead = []
      , stFrom = from
      , stProofs = []
      }

-- | **A session's slug off the clock**: @2026-11-11-2215@. This one is a
-- HANDLE, not prose — `:script resume 2026-11-11` takes a prefix of it, and
-- prefix-matching is why it stays year-first: a date is what you remember a
-- session by and what narrows the list. It also names the transcript file
-- inside @.thena\/sessions\/@, which nobody reads by eye.
--
-- **It is deliberately not 'clockName'.** A slug you type a prefix of and a
-- filename you read are different jobs, and his ruling of 2026-11-11 is about
-- the second: a weekday-first slug would prefix-match every Wednesday ever
-- and would not match the year at all.
clockStem :: IO String
clockStem = formatTime defaultTimeLocale "%Y-%m-%d-%H%M" <$> getZonedTime

-- | **The name a saved proof-script gets: readable, and one word**:
-- @Wednesday-11-11-2026-at-22-15@. His, 2026-11-11, and the sketch is his
-- too: *"I would much prefer it it read something like: \"Wednesday Evening
-- (11-11-2026-at-22-15)\""*, answering the *"later I would like something
-- better"* that the five random letters stood in for.
--
-- **Three things it is not, each ruled rather than guessed.** No day-part
-- word — @Evening@ says what @22-15@ beside it already says, and every
-- boundary (17:00, 12:00, 23:00) is a judgment that will read wrong to
-- somebody. No spaces or parentheses, because the bar's open command matches
-- two words, so a saved file has to be typeable back in. And it does not
-- sort chronologically, which he was told and chose: these are files named
-- and reopened by name, not a log to scan.
clockName :: IO String
clockName = formatTime defaultTimeLocale "%A-%d-%m-%Y-at-%H-%M" <$> getZonedTime

-- | **The session a handle names: its slug, by prefix, case ignored.** The
-- readable name is not a handle — it has spaces in it, and `:script resume` is
-- a word-split command line. 'Left' says why when it is not exactly one.
storedNamed :: String -> [Stored] -> Either String Stored
storedNamed handle sessions = case matches of
  [one] -> Right one
  [] -> Left ("no stored session starts with " <> handle)
  many -> Left (show (length many) <> " sessions start with " <> handle <> ": " <> unwords (map stSlug many))
  where
    wanted = map toLower (filter keep handle)
    keep c = isAlphaNum c || c == '-'
    matches = [s | s <- sessions, wanted `isPrefixOf` map toLower (stSlug s)]
