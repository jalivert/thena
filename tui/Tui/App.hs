-- | The TUI's entry point — `SP1`'s pane layout, first pass.
--
-- **Four panes, no borders, from the `MS7-CLI` experiment's geometry only**
-- (his instruction: take the layout, not the code) — a wide REPL on the
-- left, a narrower column on the right stacked proof-term / goals /
-- machine. Separation is background tint, never a border glyph.
--
-- **Views are pulled, not pushed** — `developmentView`/`machineView` are
-- recomputed from `stSession` on every draw, never stored, so the panes
-- follow the cursor for free.
--
-- **What this pass does not yet do**: real colors (a `Theme` value comes
-- later), keyboard actions on the side panes (no click-to-focus either —
-- his ruling — so those need dedicated bindings, not built yet), and the
-- reading-flow literal fold (`Tui.Render` always prints the expanded form).
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
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Graphics.Vty as V
import Graphics.Vty.Platform.Unix (mkVty)
import Lens.Micro (Lens', lens)

import Thena.Driver (Session, oneLine)
import Thena.Files (startingSession)
import Thena.Render (renderResponse, renderTrouble)
import Thena.View (developmentView, machineView)
import Thena.View.Core (Budget (..))

import Tui.Render (goalLines, renderLinkViews, renderMachineView)

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

-- | Placeholder tints, one per pane, distinct enough to tell them apart —
-- not the real `Theme` (a later slice); pick better values there, not here.
attrs :: AttrMap
attrs = attrMap V.defAttr
  [ (attrName "history",   surface 255 235 205)
  , (attrName "input",     surface 255 255 255)
  , (attrName "proofterm", surface 235 245 255)
  , (attrName "goals",     surface 235 255 235)
  , (attrName "machine",   surface 245 235 255)
  ]
  where
    -- **True 24-bit color, and an explicit foreground.** 'V.rgbColor' is a
    -- lossy synonym for 'V.color240' in vty 6 — it quantizes to a 256-color
    -- palette at construction, which is exactly how close pale tints
    -- collapsed into each other on screen. 'V.linearColor' passes the color
    -- through on a truecolor terminal instead. And 'bg' alone leaves the
    -- foreground at the terminal's own default, which is not guaranteed to
    -- read against a pale background — every surface sets both.
    surface :: Int -> Int -> Int -> V.Attr
    surface r g b = V.withBackColor (V.withForeColor V.defAttr ink) (tint r g b)
    ink = tint 46 40 32
    tint :: Int -> Int -> Int -> V.Color
    tint = V.linearColor

draw :: St -> [Widget Name]
draw st = [hBox [replColumn, sideColumn]]
  where
    budget = Budget 200
    links  = developmentView budget (stSession st)
    machine = machineView budget (stSession st)

    replColumn =
      vBox
        [ withAttr (attrName "history")
            (viewport HistoryVP Vertical
              (padAll 1 (vBox (map str (reverse (stHistory st))))))
        , withAttr (attrName "input")
            (padLeftRight 1
              (str "> " <+> renderEditor (str . concatMap Text.unpack) True (stInput st)))
        ]

    sideColumn =
      hLimitPercent 38
        (vBox
          [ pane "proofterm" ProofTermVP (renderLinkViews links)
          , pane "goals"     GoalsVP     (goalLines links)
          , pane "machine"   MachineVP   (renderMachineView machine)
          ])

    pane attrKey vp lns =
      withAttr (attrName attrKey)
        (viewport vp Vertical
          (padAll 1 (vBox (map str (if null lns then [" "] else lns)))))

-- | A line, run against the session, and its 'Response' rendered as lines
-- via 'Thena.Render.renderResponse' — a status-line-shaped placeholder for
-- the REPL pane's own output; the side panes render through 'Thena.View'.
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
