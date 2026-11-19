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
import Data.Char (isDigit)
import Data.List (intercalate)
import Data.Maybe (mapMaybe)
import System.Directory (XdgDirectory (XdgConfig), createDirectoryIfMissing, doesFileExist, getXdgDirectory)
import System.FilePath ((</>))

import Tui.Layout
  ( Layout
  , Pane
  , Position
  , Strip (..)
  , defaultLayout
  , defaultStrip
  , layoutFrom
  , layoutPairs
  , paneByName
  , paneName
  , stripSized
  )
import qualified Data.Text as Text

import Tui.Hint (defaultModelId)
import Tui.Theme (neonPinkDark, themeName)

data Config = Config
  { cfgTheme      :: String
  , cfgAutoSelect :: Bool
  , cfgWhisperOn  :: Bool
  , cfgConfirmQuit :: Bool
    -- ^ `:confirm-quit on|off`, his instruction of 2026-11-18 — whether
    -- quitting with an unsaved (or changed-since-save) script session is
    -- caught and asked about first, same shape as 'cfgAutoSelect' and
    -- 'cfgWhisperOn'.
  , cfgLayout     :: Layout
    -- ^ **which panes are on screen and where** — `~fxc89`'s half of
    -- `~vqsd8`, and the two take one answer because they were put to him as
    -- one question.
  , cfgWidths     :: [(Pane, Int)]
    -- ^ **the width he pulled each pane to, in columns** — `~vqsd8`. A list
    -- and not a total map: **only a pane he has actually pulled belongs here**,
    -- so a pane he has never touched keeps taking its width from the terminal's
    -- own, which is what 'Tui.App.appStart' computes and what makes an unwritten
    -- dotfile indistinguishable from no feature.
  , cfgStrip      :: Strip
    -- ^ **whether the suggestion strip is on screen and how tall** —
    -- `~w2tk2` slice 1, two keys in the file (@suggestions@ and
    -- @suggestion-rows@) and one field here, because they are one pane.
  , cfgDropdownOn :: Bool
    -- ^ @:dropdown on|off@ — `~492hq`. Same shape as 'cfgAutoSelect'.
  , cfgJevOn      :: Bool
    -- ^ **@:jev on|off@ — `~zttnz`, his instruction of 2026-11-19.** Off
    -- means no request is ever sent and the suggestion pane falls back to
    -- its own candidates in alphabetical order. Same shape as the three
    -- above; defaults to on, so a dotfile that has never heard of it behaves
    -- as before.
  , cfgModel      :: String
    -- ^ **which OpenRouter model answers the hint region** — `~w2tk2`
    -- slice 6, set by @:model ‹id›@ or by Enter in the @:models@ picker.
    --
    -- **An id and not an enumeration**, because the catalogue is 479 rows
    -- and moves without us: a model this build has never heard of is still
    -- a model he may have chosen, so what is stored is whatever string
    -- OpenRouter answers to. 'Tui.Hint.defaultModelId' is the fallback and
    -- the only name this code knows.
  } deriving (Show, Eq)

-- | The standing defaults as they already are in 'Tui.App.runTui' —
-- 'loadConfig' falls back to this whenever there is no file yet, or the
-- file on disk doesn't parse.
defaultConfig :: Config
defaultConfig = Config
  { cfgTheme      = themeName neonPinkDark
  , cfgAutoSelect = True
  , cfgWhisperOn  = True
  , cfgConfirmQuit = True
  , cfgLayout     = defaultLayout
  , cfgWidths     = []
  , cfgStrip      = defaultStrip
  -- **OFF, which is `~492hq` applied rather than deferred.** His ruling of
  -- 2026-11-19 was that the dropdown is /"disabled pretty much immediately as
  -- we start working"/ on the suggestion pane; it shipped on while the strip
  -- could not yet accept anything, and that was recorded as a deviation. The
  -- strip accepts, is Jev-authored and has a switch of its own now, and he
  -- reaffirmed the direction on 2026-11-19 — /"I am literally designing this
  -- so that the dropdown is replaced"/. **Nothing is deleted**: `:dropdown
  -- on` brings it back, which is the second half of his ruling.
  , cfgDropdownOn = False
  , cfgJevOn      = True
  , cfgModel      = Text.unpack defaultModelId
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
  ("confirm-quit", '=' : v) | Just b <- parseBool v -> cfg { cfgConfirmQuit = b }
  ("panes", '=' : v)     -> cfg { cfgLayout = layoutFrom (mapMaybe parsePane (commas v)) }
  ("widths", '=' : v)    -> cfg { cfgWidths = mapMaybe parseWidth (commas v) }
  ("suggestions", '=' : v) | Just b <- parseBool v ->
    cfg { cfgStrip = (cfgStrip cfg) { stripOpen = b } }
  -- | **A height out of range is clamped and not dropped**, unlike a bad
  -- @widths@ entry: 'stripSized' has a floor and a nonsense number there is
  -- still a number he meant as a height, where @globals:banana@ is not a
  -- width at all.
  ("suggestion-rows", '=' : v) | Just n <- readInt v ->
    cfg { cfgStrip = stripSized n (cfgStrip cfg) }
  ("dropdown", '=' : v) | Just b <- parseBool v -> cfg { cfgDropdownOn = b }
  ("jev", '=' : v)      | Just b <- parseBool v -> cfg { cfgJevOn = b }
  -- | **Not validated against anything, and deliberately so** — see
  -- 'cfgModel'. An empty value falls back to the default rather than
  -- storing a model id of @""@, which would come back as a 400 on his
  -- first ask with nothing on screen to explain it.
  ("model", '=' : v)    -> cfg { cfgModel = if null v then Text.unpack defaultModelId else v }
  _                      -> cfg

parseBool :: String -> Maybe Bool
parseBool "on"  = Just True
parseBool "off" = Just False
parseBool _     = Nothing

-- | **A bad entry is dropped and the rest of the line still counts**, which is
-- one step more forgiving than 'applyLine''s own rule of dropping the whole
-- line — deliberately. A @panes=@ line is six entries, and a frontend's
-- preference file is not worth losing five good ones over a typo in the sixth.
commas :: String -> [String]
commas v = case break (== ',') v of
  (a, [])       -> [a]
  (a, _ : rest) -> a : commas rest

-- | @1:globals@ — the position, then the name the pane already goes by.
--
-- **Position first, because the file is read in position order** and anyone
-- editing it by hand is reading down a column of 1 to 6.
-- 'Tui.Layout.layoutFrom' is what rejects a position outside that range, not
-- this: keeping the range in one place is why it is built out of
-- 'Tui.Layout.openPane'.
parsePane :: String -> Maybe (Position, Pane)
parsePane entry = case break (== ':') entry of
  (n, ':' : name) -> (,) <$> readInt n <*> paneByName name
  _               -> Nothing

-- | @globals:60@ — the pane, then its width in columns.
--
-- **Name first here and position first above, because these are different
-- keys**: a width belongs to a pane whatever position it sits at, which is the
-- whole reason the two are separate lines rather than one list of triples.
parseWidth :: String -> Maybe (Pane, Int)
parseWidth entry = case break (== ':') entry of
  (name, ':' : n) -> (,) <$> paneByName name <*> readInt n
  _               -> Nothing

-- | **Digits and nothing else.** 'reads' would take @"60 junk"@ and a leading
-- sign, and neither is a width or a position.
readInt :: String -> Maybe Int
readInt t
  | not (null t), all isDigit t = Just (read t)
  | otherwise = Nothing

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
    , "confirm-quit=" <> (if cfgConfirmQuit cfg then "on" else "off")
    , "panes=" <> intercalate ","
        [show n <> ":" <> paneName p | (n, p) <- layoutPairs (cfgLayout cfg)]
    , "widths=" <> intercalate ","
        [paneName p <> ":" <> show w | (p, w) <- cfgWidths cfg]
    , "suggestions=" <> (if stripOpen (cfgStrip cfg) then "on" else "off")
    , "suggestion-rows=" <> show (stripRows (cfgStrip cfg))
    , "dropdown=" <> (if cfgDropdownOn cfg then "on" else "off")
    , "jev=" <> (if cfgJevOn cfg then "on" else "off")
    , "model=" <> cfgModel cfg
    ]
