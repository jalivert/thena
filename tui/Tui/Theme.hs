-- | Color, as a value — never a literal `V.Color` scattered through
-- `Tui.App`. Dark stage, one neon accent per pane as a left edge and a
-- title, never as a fill: `Tui.App`'s first attempt filled whole panes with
-- pale tints, which is backwards from what was asked for.
--
-- **`V.linearColor`, always.** `V.rgbColor` is a lossy synonym for
-- `V.color240` in vty 6 — see `Tui.App`'s attr-building comment, and
-- `.claude/LOG.md`'s 2026-09-29 entry for the bug it caused here once
-- already.
module Tui.Theme
  ( Theme (..)
  , neonPinkDark
  , gruyere
  , synthwave84
  , themes
  , themeByName
  ) where

import Data.List (find)
import qualified Graphics.Vty as V

data Theme = Theme
  { themeName    :: String
  , themeStage   :: V.Color -- ^ the gap between panes — pure, darkest
  , themePanel   :: V.Color -- ^ a pane's own fill, one step up from the stage
  , themeInk     :: V.Color -- ^ body text
  , themeDim     :: V.Color -- ^ secondary text — headers, hints
  , themeRepl    :: V.Color -- ^ the repl pane's accent
  , themeProof   :: V.Color -- ^ the proof-term pane's accent
  , themeGoals   :: V.Color -- ^ the goals pane's accent
  , themeMachine :: V.Color -- ^ the machine pane's accent
  , themeFold    :: V.Color -- ^ a folded literal's background tint
  , themeSplice  :: V.Color -- ^ a folded splice's background tint — distinct
                             -- from a literal's, his ruling, 2026-09-28
  }

rgb :: Int -> Int -> Int -> V.Color
rgb = V.linearColor

-- | His pick, 2026-09-29, over the other two — *"Neon pink … the original
-- one"* — and the default. Pure black stage; every accent is a shade of the
-- one neon pink/magenta family, no blue, no yellow.
--
-- **`themePanel` lifted off near-neutral, 2026-09-29**: `(10, 10, 10)`
-- against a `(0, 0, 0)` stage read as too close to separate as its own
-- surface, his punch list. Warm and pink-tinted (R and B raised more than
-- G) rather than a neutral gray lift, so the step reads as *this* theme's
-- panel, not a generic dark-mode one.
neonPinkDark :: Theme
neonPinkDark = Theme
  { themeName    = "neon-pink-dark"
  , themeStage   = rgb 0 0 0
  , themePanel   = rgb 28 14 22
  , themeInk     = rgb 255 230 255
  , themeDim     = rgb 150 90 130
  , themeRepl    = rgb 255 45 190
  , themeProof   = rgb 255 140 240
  , themeGoals   = rgb 255 85 195
  , themeMachine = rgb 255 94 196
  , themeFold    = rgb 40 12 32
  , themeSplice  = rgb 30 20 14
  }

-- | Ranked second. Accents confirmed from the real source
-- (`savannahostrowski/gruyere`, `gruyere/main.py`) — `#EE6FF8` is its one
-- named accent; the rest is the title-gradient's three corners, repurposed
-- as pane accents since the source has no others. Not active unless asked
-- for.
gruyere :: Theme
gruyere = Theme
  { themeName    = "gruyere"
  , themeStage   = rgb 24 20 44
  , themePanel   = rgb 34 29 58
  , themeInk     = rgb 240 233 255
  , themeDim     = rgb 139 132 168
  , themeRepl    = rgb 238 111 248
  , themeProof   = rgb 237 255 130
  , themeGoals   = rgb 100 58 255
  , themeMachine = rgb 20 249 213
  , themeFold    = rgb 44 36 74
  , themeSplice  = rgb 34 44 40
  }

-- | Ranked third. `editor.background` confirmed from the shipped theme JSON
-- (`robb0wen/synthwave-vscode`); accents are its own named tokens
-- (`#ff7edb`, `#36f9f6`, `#72f1b8`, `#fede5d`). Not active unless asked for.
synthwave84 :: Theme
synthwave84 = Theme
  { themeName    = "synthwave-84"
  , themeStage   = rgb 38 35 53
  , themePanel   = rgb 52 46 71
  , themeInk     = rgb 255 255 255
  , themeDim     = rgb 168 155 194
  , themeRepl    = rgb 255 126 219
  , themeProof   = rgb 54 249 246
  , themeGoals   = rgb 114 241 184
  , themeMachine = rgb 254 222 93
  , themeFold    = rgb 52 41 79
  , themeSplice  = rgb 40 50 46
  }

themes :: [Theme]
themes = [neonPinkDark, gruyere, synthwave84]

themeByName :: String -> Maybe Theme
themeByName n = find ((== n) . themeName) themes
