-- | The TUI's entry point — `SP1`'s first skeleton.
--
-- **One pane, no borders.** A scrollback above an input line, the two
-- separated by a background tint rather than a border glyph (`MS7-CLI`'s
-- parked experiment showed brick can do this cleanly; nothing of its
-- architecture is reused here, only the visual finding). Drives the engine
-- through `Thena.Driver` alone — `oneLine`, `Session`, `Response` — never
-- `Thena.Repl`: that module is the terminal REPL's own rendering layer
-- (prompts, plain-text transcripts), not part of what a structured-view TUI
-- should depend on. See `REPORT.md`'s 2026-09-28 entry.
--
-- **Known temporary gap, blocked on Opus**: booting a session needs the
-- prelude and the standard rule base loaded, in that order, which needs IO —
-- and the only place that logic exists right now is `Thena.Repl.startingSession`,
-- which this module is not allowed to use. Until the bootstrap is split out
-- into its own module, this starts from `Thena.Driver.newSession` instead —
-- a session with neither loaded, so nothing that depends on the standard
-- rule base will elaborate. That is the whole reason this skeleton does not
-- render real views yet either: there is nothing meaningful to view.
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

import Thena.Driver (Response, Session, newSession, oneLine)

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
  let st0 = St
        { stHistory =
            [ "temporary bootstrap: no prelude, no rule base loaded"
            , "(blocked on splitting Thena.Repl.startingSession out — see REPORT.md)"
            ]
        , stInput   = emptyInput
        , stSession = newSession
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

-- | A line, run against the (currently prelude-less) session, and its raw
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
