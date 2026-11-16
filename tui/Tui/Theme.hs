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
  , themeGlobals :: V.Color -- ^ the globals pane's accent (`~5d35q`)
  , themeModules :: V.Color -- ^ the modules pane's accent (`~t7wc8`)
  , themeOutput  :: V.Color -- ^ the output pane's accent (`~wx6m3`). **The
                             -- second column gets three accents of its own
                             -- rather than borrowing the first column's** —
                             -- one accent per pane is this theme's whole
                             -- idea, and two panes wearing one colour would
                             -- say they are one thing in two places
  , themeChoices :: V.Color -- ^ the choice-points pane's accent (`~396c8`).
                             -- A provisional pick, same family as the rest of
                             -- its theme — his to retune, same as any other
                             -- accent here.
  , themeFold    :: V.Color -- ^ a folded literal's background tint
  , themeSplice  :: V.Color -- ^ a folded splice's background tint — distinct
                             -- from a literal's, his ruling, 2026-09-28
  , themePopup   :: V.Color -- ^ a floating dropdown's background. **Set by
                             -- chroma, not by lightness** — @~bmgr7@, his
                             -- report, 2026-10-21: *"its background color is almost
                             -- the same as the editor … I can't see whether
                             -- that's a dropdown showing 3 things or my
                             -- editor has three lines."* It was true and
                             -- measurable: against 'themePanel' the default
                             -- theme's popup stood at a 1.06 contrast ratio,
                             -- which is no edge at all. The earlier attempt
                             -- to fix that by lifting it — `(56, 26, 42)`,
                             -- `.jalivert/TUI.md` #22, *"like someone put a
                             -- dim purple filter over my eyes"* — failed
                             -- because it was a **desaturated** lift: a
                             -- gray-purple wash over a large area. So this
                             -- is saturated and still dark, deep in the
                             -- theme's own accent family, which separates it
                             -- from the panel without becoming the brightest
                             -- thing on the screen
  , themePopupInk :: V.Color -- ^ body text on 'themePopup', paired with it
                             -- here rather than borrowing 'themeInk' — the
                             -- two halves of one surface, so a theme cannot
                             -- retune the background and leave the text
                             -- behind on it
  , themeSoft    :: V.Color -- ^ the lightest accent, for the latest turn's
                             -- thin marker — present, not prominent. A field
                             -- of its own rather than reusing whichever pane
                             -- accent happens to be lightest, so retuning a
                             -- pane never moves the marker with it.
  , themeJevPick :: V.Color -- ^ background for a dropdown row Jev floated
                             -- to the top, read with 'themeStage' — see below.
  , themePaneBar :: V.Color
    -- ^ **the filled background of one chip in the pane bar** — `~7tfhd`, his
    -- instruction of 2026-11-13: /"a pink accent background around the text
    -- (get the contrast right)"/.
    --
    -- **A field of its own rather than a pane's accent reused**, because this
    -- is a decision each theme has to answer: the bar names all six panes at
    -- once, so borrowing any one pane's accent would make the bar look like it
    -- belonged to that pane.
    --
    -- **The text on it is 'themeStage', the theme's own darkest.** That is what
    -- /"get the contrast right"/ comes to: a bright accent cannot carry
    -- 'themeInk' — neon-pink-dark's ink on its pink is 2.8:1, which fails for
    -- body text — while the stage colour on the same pink is **6.4:1**. The
    -- other two themes are 7.0:1 and 6.7:1 on the same pairing, all computed
    -- rather than eyeballed.
                             -- to the top ('floatJevPicks') — paired with
                             -- 'themeStage', the theme's own darkest, not white.
                             -- White on the old teal was 3.7:1, unreadable on a
                             -- weak projector; the brightened teal on stage is
                             -- 9.9/8.4/7.2 across the three themes, computed
                             -- rather than eyeballed — the same bright-accent/
                             -- darkest-text pairing 'themePaneBar' already uses.
                             -- His correction, 2026-10-29, still stands: the
                             -- first cut set this as *text* colour on the popup's
                             -- own background and he called it "a horrible idea"
                             -- — green on pink is a legibility problem, not a
                             -- highlight. A fixed blue-green across all three
                             -- themes rather than drawn from each theme's own
                             -- accent family: it means "Jev said so," which should
                             -- read the same regardless of theme.
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
--
-- **Darkened and desaturated, 2026-09-30**: `(28, 14, 22)` read distinctly
-- purple and strained his eyes — same family, roughly half the lift and
-- half the chroma, still hue-separated from the black stage rather than
-- merely lighter.
neonPinkDark :: Theme
neonPinkDark = Theme
  { themeName    = "neon-pink-dark"
  , themeStage   = rgb 0 0 0
  , themePanel   = rgb 16 10 14
  , themeInk     = rgb 255 230 255
  , themeDim     = rgb 150 90 130
  , themeRepl    = rgb 255 45 190
  , themeProof   = rgb 255 140 240
  , themeGoals   = rgb 255 85 195
  , themeMachine = rgb 255 94 196
  , themeGlobals = rgb 255 170 225
  , themeModules = rgb 230 60 165
  , themeOutput  = rgb 255 115 215
  , themeChoices = rgb 255 70 150
  , themeFold    = rgb 40 12 32
  , themeSplice  = rgb 30 20 14
  -- **Deep magenta, 2026-10-21 (@~bmgr7@)**, replacing the `(28, 16, 22)` this was
  -- darkened to on 2026-09-30. That darkening answered #22's purple wash
  -- and overshot: at a 1.06 contrast ratio against the panel the popup had
  -- no visible edge, so three rows of it read as three lines of the editor.
  -- `(112, 8, 64)` is 1.68 against the panel at 0.93 saturation, where the
  -- rejected `(56, 26, 42)` was 1.26 at 0.43 — more separation *and* less
  -- of the gray cast that made the old one a filter rather than a surface.
  -- Green is the channel held down, since green carries most of perceived
  -- luminance: this is chromatic, not bright.
  , themePopup   = rgb 112 8 64
  , themePopupInk = rgb 255 232 248
  , themeSoft    = rgb 255 140 240
  , themeJevPick = rgb 0 200 180
  -- **The theme's own neon pink.** Same value as 'themeRepl' here and that is
  -- this theme's answer, not a rule: the repl's accent is one column of `▎`
  -- at the far left and a chip at the top rhymes with it rather than competing.
  , themePaneBar = rgb 255 45 190
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
  , themeGlobals = rgb 255 176 102
  , themeModules = rgb 130 255 170
  , themeOutput  = rgb 255 110 150
  , themeChoices = rgb 140 180 255
  , themeFold    = rgb 44 36 74
  , themeSplice  = rgb 34 44 40
  , themePopup   = rgb 86 34 136
  , themePopupInk = rgb 248 238 255
  , themeSoft    = rgb 237 255 130
  , themeJevPick = rgb 0 200 180
  -- Its one named accent, which is also the pinkest thing it has.
  , themePaneBar = rgb 238 111 248
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
  , themeGlobals = rgb 184 148 255
  , themeModules = rgb 54 206 255
  , themeOutput  = rgb 255 152 102
  , themeChoices = rgb 255 90 140
  , themeFold    = rgb 52 41 79
  , themeSplice  = rgb 40 50 46
  , themePopup   = rgb 112 50 152
  , themePopupInk = rgb 255 244 255
  , themeSoft    = rgb 254 222 93
  , themeJevPick = rgb 0 200 180
  -- `#ff7edb`, the shipped theme's own pink.
  , themePaneBar = rgb 255 126 219
  }

themes :: [Theme]
themes = [neonPinkDark, gruyere, synthwave84]

themeByName :: String -> Maybe Theme
themeByName n = find ((== n) . themeName) themes
