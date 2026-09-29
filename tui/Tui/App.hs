-- | The TUI's entry point.
--
-- **Four panes, no borders** — a wide REPL on the left, proof-term/goals/
-- machine stacked narrower on the right (geometry from `MS7-CLI`, his
-- instruction: the layout only, never its code). Separation is a dark
-- panel fill plus one neon accent as a left edge, never a border glyph and
-- never a full-pane fill — his correction, 2026-09-29, after the first
-- pass used pale tints across the whole pane.
--
-- **Views are pulled, not pushed** — `developmentView`/`machineView` are
-- recomputed from `stSession` on every draw, never stored.
--
-- **Not yet built, so as not to pretend otherwise**: the rules dropdown and
-- the object-term offer dropdown (both need positioned-popup machinery,
-- next slice); clicking a proof-term/goal line to move the cursor there
-- (agreed to stay, not yet wired — needs per-line extents).
--
-- Drives the engine through `Thena.Driver` and `Thena.Files`/`Thena.Render`
-- for bootstrap and status text only — panes render through `Thena.View.*`.
-- Never `Thena.Repl`: off `thena:view` entirely since MS7 phase 130.
module Tui.App (runTui) where

import Brick
import Brick.Widgets.Edit
  ( Editor
  , getEditContents
  , handleEditorEvent
  , renderEditor
  )
import qualified Brick.Widgets.Edit as E
import Control.Monad.IO.Class (liftIO)
import Data.List (isPrefixOf)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Graphics.Vty as V
import Graphics.Vty.Platform.Unix (mkVty)
import Lens.Micro (Lens', lens)
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath (takeDirectory, takeFileName, (</>))

import Thena.Driver (Response (Quit), Session, oneLine)
import Thena.Files (startingSession)
import Thena.Render (renderResponse, renderTrouble)
import Thena.View (developmentView, focusAddress, machineView)
import Thena.View.Core (Budget (..))

import Tui.Render
  ( Fold (..)
  , foldAttr
  , renderDevelopment
  , renderGoals
  , renderMachineView
  , spliceAttr
  )
import Tui.Theme (Theme (..), neonPinkDark, themeByName)

data Name
  = Input
  | HistoryVP
  | ProofTermVP
  | GoalsVP
  | MachineVP
  deriving (Eq, Ord, Show)

data St = St
  { stHistory :: [String]
  , stInput   :: Editor Text Name
  , stSession :: Session
  , stTheme   :: Theme
  , stFoldOn  :: Bool
  }

stInputL :: Lens' St (Editor Text Name)
stInputL = lens stInput (\st i -> st { stInput = i })

emptyInput :: Editor Text Name
emptyInput = E.editorText Input (Just 1) Text.empty

runTui :: IO ()
runTui = do
  (s0, trouble) <- startingSession
  let st0 = St
        { stHistory = concatMap (renderTrouble s0) trouble
        , stInput   = emptyInput
        , stSession = s0
        , stTheme   = neonPinkDark
        , stFoldOn  = True
        }
  vty <- mkVty V.defaultConfig
  _ <- customMain vty (mkVty V.defaultConfig) Nothing app st0
  pure ()

app :: App St e Name
app = App
  { appDraw         = draw
  , appChooseCursor = showFirstCursor
  , appHandleEvent  = handleEvent
  , appStartEvent   = enableMouse
  , appAttrMap      = attrs . stTheme
  }

-- | Wheel-scroll works on whichever pane the pointer is over, "no matter
-- where the focus is" — his words, 2026-09-29 — which needs mouse mode on
-- at the terminal, not just clickable widgets.
enableMouse :: EventM Name St ()
enableMouse = do
  vty <- getVtyHandle
  liftIO (V.setMode (V.outputIface vty) V.Mouse True)

-- | One dark panel fill, one neon accent per pane (edge and title text,
-- never a fill), plus the fold/splice attrs the reading-flow feature uses.
-- 'V.linearColor', always — 'V.rgbColor' quantizes to 256 colors at
-- construction in vty 6 and is why the first pass came out as two
-- indistinguishable pale blobs instead of four panes (`.claude/LOG.md`,
-- 2026-09-29).
attrs :: Theme -> AttrMap
attrs th = attrMap (surface (themeStage th) (themeInk th))
  [ (attrName "panel",          surface (themePanel th) (themeInk th))
  , (attrName "edge.repl",      surface (themeRepl th) (themeRepl th))
  , (attrName "edge.proofterm", surface (themeProof th) (themeProof th))
  , (attrName "edge.goals",     surface (themeGoals th) (themeGoals th))
  , (attrName "edge.machine",   surface (themeMachine th) (themeMachine th))
  , (attrName "title.repl",     ink (themeRepl th))
  , (attrName "title.proofterm", ink (themeProof th))
  , (attrName "title.goals",    ink (themeGoals th))
  , (attrName "title.machine",  ink (themeMachine th))
  , (attrName "dim",            ink (themeDim th))
  , (foldAttr,   V.withStyle (surface (themeFold th) (themeInk th)) V.italic)
  , (spliceAttr, V.withStyle (surface (themeSplice th) (themeInk th)) V.bold)
  ]
  where
    surface bgC fgC = V.withBackColor (V.withForeColor V.defAttr fgC) bgC
    ink fgC = V.withForeColor V.defAttr fgC

draw :: St -> [Widget Name]
draw st = [hBox [replColumn, sideColumn]]
  where
    budget = Budget 200
    s = stSession st
    links = developmentView budget s
    machine = machineView budget s
    fold = if stFoldOn st then Fold (focusAddress s) else NoFold

    replColumn =
      withAttr (attrName "panel") $
        vBox
          [ pane "repl" HistoryVP
              (padAll 1 (vBox (map str (reverse (stHistory st)))))
          , padLeftRight 1
              (str "> " <+> renderEditor (str . concatMap Text.unpack) True (stInput st))
          ]

    sideColumn =
      hLimitPercent 38 $
        withAttr (attrName "panel") $
          vBox
            [ pane "proofterm" ProofTermVP (padAll 1 (renderDevelopment fold links))
            , pane "goals"     GoalsVP     (padAll 1 (renderGoals fold links))
            , pane "machine"   MachineVP   (padAll 1 (vBox (map str (renderMachineView machine))))
            ]

    -- | The accent edge, a title strip, then the content — never a full
    -- fill, per his correction. 'clickable' so a scroll-wheel event over
    -- this pane resolves to its own 'Name', not the row under it.
    --
    -- **The edge bar sits outside the 'viewport', not inside it.** 'fill'
    -- is infinite in both directions; a 'Vertical' viewport has to know
    -- its content's real height to manage a scroll offset, and refuses at
    -- runtime — "tried to embed an infinite-height widget in vertical
    -- viewport" — if anything inside it reports infinite height, which
    -- 'fill' always does regardless of 'hLimit' pinning its width. Only
    -- the scrollable part (title + content) goes inside the viewport; the
    -- edge is a plain sibling, sized by the outer box like any other
    -- widget.
    pane key vp content =
      clickable vp $
        hBox
          [ withAttr (attrName ("edge." <> key)) (hLimit 1 (fill ' '))
          , viewport vp Vertical $
              vBox
                [ withAttr (attrName ("title." <> key)) (padLeftRight 1 (str key))
                , content
                ]
          ]

-- | A line, run against the session, and its 'Response' rendered as lines
-- via 'Thena.Render.renderResponse' — a status-line-shaped placeholder for
-- the REPL pane's own output; the side panes render through 'Thena.View'.
--
-- **Two TUI-local pseudo-commands, intercepted before 'oneLine' ever sees
-- them**: `:theme <name>` and `:fold on|off`. Neither is instral syntax —
-- same standing as `:load`'s path completion, his ruling 2026-09-28:
-- *"it is not instral. Therefore special casing it in our TUI's repl is
-- ok."*
handleEvent :: BrickEvent Name e -> EventM Name St ()
handleEvent (VtyEvent (V.EvKey V.KEnter [])) = do
  st <- get
  let line = concatMap Text.unpack (getEditContents (stInput st))
  case words line of
    [":theme", name] | Just th <- themeByName name ->
      put st { stInput = emptyInput, stTheme = th, stHistory = ("theme: " <> name) : stHistory st }
    [":fold", mode] | mode `elem` ["on", "off"] ->
      put st { stInput = emptyInput, stFoldOn = mode == "on", stHistory = ("fold: " <> mode) : stHistory st }
    _ -> do
      let (s', resp) = oneLine (stSession st) line
      put st
        { stInput   = emptyInput
        , stHistory = reverse (renderResponse s' resp) <> [("> " <> line)] <> stHistory st
        , stSession = s'
        }
      if resp == Quit then halt else pure ()
handleEvent (VtyEvent (V.EvKey V.KEsc [])) = halt
handleEvent (VtyEvent (V.EvKey (V.KChar '\t') [])) = completeLoadPath
handleEvent (MouseDown n V.BScrollUp _ _) = vScrollBy (viewportScroll n) (-1)
handleEvent (MouseDown n V.BScrollDown _ _) = vScrollBy (viewportScroll n) 1
handleEvent ev = Brick.zoom stInputL (handleEditorEvent ev)

-- | Tab-completion for `:load`'s path only — his ruling, 2026-09-29:
-- *"it is not instral. Therefore special casing it in our TUI's repl is
-- ok."* Scoped to a single trailing path (several comma/space-separated
-- paths completing independently is the old experiment's finer-grained
-- version of this and not built here yet — narrower, not a hack).
completeLoadPath :: EventM Name St ()
completeLoadPath = do
  st <- get
  let line = concatMap Text.unpack (getEditContents (stInput st))
  case loadPathPrefix line of
    Nothing -> pure ()
    Just prefix -> do
      matched <- liftIO (completePath prefix)
      case matched of
        Nothing -> pure ()
        Just full ->
          let line' = replacePathPrefix line full
           in put st { stInput = E.editorText Input (Just 1) (Text.pack line') }

loadPathPrefix :: String -> Maybe String
loadPathPrefix line
  | ":load " `isPrefixOf` line = Just (lastWord line)
  | otherwise = Nothing

lastWord :: String -> String
lastWord = reverse . takeWhile (/= ' ') . reverse

replacePathPrefix :: String -> String -> String
replacePathPrefix line completed = take (length line - length (lastWord line)) line <> completed

-- | The directory a prefix's last path segment sits in, listed and
-- filtered by what's typed so far; extended only as far as every match
-- agrees (ordinary shell-style completion) — genuinely ambiguous prefixes
-- are left alone rather than guessed at (a dropdown listing them is the
-- next slice, same as the object-term offers').
completePath :: String -> IO (Maybe String)
completePath prefix = do
  let dir  = takeDirectory prefix
      name = takeFileName prefix
  exists <- doesDirectoryExist dir
  if not exists
    then pure Nothing
    else do
      entries <- listDirectory dir
      let shown = if "." `isPrefixOf` name then entries else filter (not . isPrefixOf ".") entries
          matches = filter (name `isPrefixOf`) shown
      pure $ case matches of
        [] -> Nothing
        _  ->
          let common = longestCommonPrefix matches
           in if length common > length name then Just (joinDir dir common) else Nothing

joinDir :: FilePath -> String -> String
joinDir "." name = name
joinDir dir  name = dir </> name

longestCommonPrefix :: [String] -> String
longestCommonPrefix [] = ""
longestCommonPrefix (x : xs) = foldl agree x xs
  where
    agree a b = map fst (takeWhile (uncurry (==)) (zip a b))
