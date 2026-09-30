-- | Persists the TUI-local standing preferences — 'Tui.Theme.themeName',
-- `:preselect`, `:whisper` — across sessions. A dotfile under the user's own
-- config directory, not this worktree: these are per-user taste, not
-- per-project state, so they follow him rather than living under
-- @thena_datadir@ the way rules/prelude do.
--
-- **Deliberately not the engine's business.** Nothing here touches
-- @Thena.*@ or the wire — a TUI-local preference file is squarely inside
-- what this track owns on its own authority (see this worktree's
-- @CLAUDE.md@, "who works here").
module Tui.Config
  ( Config (..)
  , defaultConfig
  , loadConfig
  , saveConfig
  ) where

import Control.Exception (IOException, try)
import System.Directory (XdgDirectory (XdgConfig), createDirectoryIfMissing, doesFileExist, getXdgDirectory)
import System.FilePath ((</>))

import Tui.Theme (neonPinkDark, themeName)

data Config = Config
  { cfgTheme      :: String
  , cfgAutoSelect :: Bool
  , cfgWhisperOn  :: Bool
  } deriving (Show, Eq)

-- | The standing defaults as they already are in 'Tui.App.runTui' —
-- 'loadConfig' falls back to this whenever there is no file yet, or the
-- file on disk doesn't parse.
defaultConfig :: Config
defaultConfig = Config
  { cfgTheme      = themeName neonPinkDark
  , cfgAutoSelect = True
  , cfgWhisperOn  = True
  }

-- | @~\/.config\/thena@ — not @thena-tui@: the TUI is the only frontend
-- today, but the directory name shouldn't say so, since more than these
-- three fields is likely to live here eventually (his ask, 2026-09-30).
configDir :: IO FilePath
configDir = getXdgDirectory XdgConfig "thena"

configPath :: IO FilePath
configPath = do
  dir <- configDir
  pure (dir </> "config")

-- | Reads the dotfile if it's there and parses; 'defaultConfig' for
-- anything else — no file, an unreadable one, a line that doesn't parse.
-- A frontend's own preferences are not worth a crash over, so trouble here
-- is silent and simply falls back, unlike 'Thena.Files' 'Trouble', which is
-- surfaced because a rule file failing to load is something he needs to
-- know about.
loadConfig :: IO Config
loadConfig = do
  path <- configPath
  exists <- doesFileExist path
  if not exists
    then pure defaultConfig
    else do
      result <- try (readFile path) :: IO (Either IOException String)
      pure $ case result of
        Left _         -> defaultConfig
        Right contents -> foldl applyLine defaultConfig (lines contents)

applyLine :: Config -> String -> Config
applyLine cfg line = case break (== '=') line of
  ("theme", '=' : v)     -> cfg { cfgTheme = v }
  ("preselect", '=' : v) | Just b <- parseBool v -> cfg { cfgAutoSelect = b }
  ("whisper", '=' : v)   | Just b <- parseBool v -> cfg { cfgWhisperOn = b }
  _                      -> cfg

parseBool :: String -> Maybe Bool
parseBool "on"  = Just True
parseBool "off" = Just False
parseBool _     = Nothing

-- | Overwrites the whole file with the current preferences — called after
-- every `:theme`/`:preselect`/`:whisper` command, not batched, so the
-- dotfile never lags what a session just set. A failed write (a read-only
-- home, a missing config directory that can't be created) is swallowed the
-- same way a failed read is: the toggle still takes effect for this
-- session, it just won't have persisted.
saveConfig :: Config -> IO ()
saveConfig cfg = do
  path <- configPath
  _ <- try (writeConfig path cfg) :: IO (Either IOException ())
  pure ()

writeConfig :: FilePath -> Config -> IO ()
writeConfig path cfg = do
  dir <- configDir
  createDirectoryIfMissing True dir
  writeFile path $ unlines
    [ "theme=" <> cfgTheme cfg
    , "preselect=" <> (if cfgAutoSelect cfg then "on" else "off")
    , "whisper=" <> (if cfgWhisperOn cfg then "on" else "off")
    ]
