-- | The TUI's entry point — `SP1`'s first skeleton.
--
-- **One pane, no borders.** A scrollback of turns above an input line, with
-- the two separated by a background tint rather than a border glyph
-- (`MS7-CLI`'s parked experiment showed brick can do this cleanly; nothing
-- of its architecture is reused here, only the visual finding). It drives
-- the engine through 'Thena.Repl.turn' alone, which is 'thena:view''s
-- surface — nothing here imports `Thena.Engine`, `Thena.Core`, or anything
-- else outside that boundary.
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

import Thena.Driver (Session)
import Thena.Repl (Turn (..), prompt, startingSession, turn)

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
  (s0, warnings) <- startingSession
  let st0 = St { stHistory = warnings, stInput = emptyInput, stSession = s0 }
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
            (str (prompt (stSession st) <> " ")
              <+> renderEditor (str . concatMap Text.unpack) True (stInput st)))
      ]
  ]

handleEvent :: BrickEvent Name e -> EventM Name St ()
handleEvent (VtyEvent (V.EvKey V.KEnter [])) = do
  st <- get
  let line     = concatMap Text.unpack (getEditContents (stInput st))
      t        = turn (stSession st) line
      entered  = prompt (stSession st) <> " " <> line
  put st
    { stInput   = emptyInput
    , stHistory = reverse (turnOutput t) <> (entered : stHistory st)
    , stSession = turnSession t
    }
  if turnQuit t then halt else pure ()
handleEvent (VtyEvent (V.EvKey V.KEsc [])) = halt
handleEvent ev = Brick.zoom stInputL (handleEditorEvent ev)
