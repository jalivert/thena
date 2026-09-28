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

import Thena.Driver (Response, Session, oneLine)
import Thena.Files (Trouble, startingSession)

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
        { stHistory = map showTrouble trouble
        , stInput   = emptyInput
        , stSession = s0
        }
  vty <- mkVty V.defaultConfig
  _ <- customMain vty (mkVty V.defaultConfig) Nothing app st0
  pure ()

-- | Placeholder rendering — real 'Trouble' display waits on the pane layout,
-- same as 'Response' below. Empty on an ordinary run, since the shipped
-- prelude and rule base load cleanly.
showTrouble :: Trouble -> String
showTrouble = show

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

-- | A line, run against the (now properly booted) session, and its raw
-- 'Response' dumped with 'show' — a placeholder for real rendering through
-- 'Thena.View', which wants a pane layout that hasn't been decided yet.
handleEvent :: BrickEvent Name e -> EventM Name St ()
handleEvent (VtyEvent (V.EvKey V.KEnter [])) = do
  st <- get
  let line          = concatMap Text.unpack (getEditContents (stInput st))
      (s', resp)    = oneLine (stSession st) line
      shown :: Response -> String
      shown         = show
  put st
    { stInput   = emptyInput
    , stHistory = shown resp : ("> " <> line) : stHistory st
    , stSession = s'
    }
handleEvent (VtyEvent (V.EvKey V.KEsc [])) = halt
handleEvent ev = Brick.zoom stInputL (handleEditorEvent ev)
