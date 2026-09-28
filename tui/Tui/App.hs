-- | The TUI's entry point — `SP1`'s first skeleton.
--
-- **One pane, no borders.** A scrollback above an input line, the two
-- separated by a background tint rather than a border glyph (`MS7-CLI`'s
-- parked experiment showed brick can do this cleanly; nothing of its
-- architecture is reused here, only the visual finding). Drives the engine
-- through `Thena.Driver` (`oneLine`, `Session`, `Response`) and
-- `Thena.Files` (`startingSession`, the load-bearing IO bootstrap) — never
-- `Thena.Repl`, which MS7 phase 130 took off `thena:view` entirely for
-- exactly this reason: it's the terminal REPL's own line protocol, not a
-- frontend's. See `REPORT.md`'s 2026-09-28 entries.
module Tui.App (runTui) where

import Brick
import Brick.Widgets.Edit
  ( Editor
  , getEditContents
  , handleEditorEvent
  , renderEditor
  )
import qualified Brick.Widgets.Edit as E
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Graphics.Vty as V
import Graphics.Vty.Platform.Unix (mkVty)
import Lens.Micro (Lens', lens)

import Thena.Driver (Session, oneLine)
import Thena.Files (startingSession)
import Thena.Render (renderResponse, renderTrouble)

data Name = Input
  deriving (Eq, Ord, Show)

data St = St
  { stHistory :: [String]
  , stInput   :: Editor Text Name
  , stSession :: Session
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
        }
  vty <- mkVty V.defaultConfig
  _ <- customMain vty (mkVty V.defaultConfig) Nothing app st0
  pure ()

app :: App St e Name
app = App
  { appDraw         = draw
  , appChooseCursor = showFirstCursor
  , appHandleEvent  = handleEvent
  , appStartEvent   = pure ()
  , appAttrMap      = const attrs
  }

attrs :: AttrMap
attrs = attrMap V.defAttr
  [ (attrName "history", bg (tint 255 235 205))
  , (attrName "input",   bg (tint 255 255 255))
  ]
  where
    tint :: Int -> Int -> Int -> V.Color
    tint = V.rgbColor

draw :: St -> [Widget Name]
draw st =
  [ vBox
      [ withAttr (attrName "history")
          (padAll 1 (vBox (map str (reverse (stHistory st)))))
      , withAttr (attrName "input")
          (padLeftRight 1
            (str "> " <+> renderEditor (str . concatMap Text.unpack) True (stInput st)))
      ]
  ]

-- | A line, run against the session, and its 'Response' rendered as lines
-- via 'Thena.Render.renderResponse' — a status-line-shaped placeholder;
-- real pane content waits on 'Thena.View', once the pane layout is decided.
handleEvent :: BrickEvent Name e -> EventM Name St ()
handleEvent (VtyEvent (V.EvKey V.KEnter [])) = do
  st <- get
  let line       = concatMap Text.unpack (getEditContents (stInput st))
      (s', resp) = oneLine (stSession st) line
  put st
    { stInput   = emptyInput
    , stHistory = reverse (renderResponse s' resp) <> [("> " <> line)] <> stHistory st
    , stSession = s'
    }
handleEvent (VtyEvent (V.EvKey V.KEsc [])) = halt
handleEvent ev = Brick.zoom stInputL (handleEditorEvent ev)
