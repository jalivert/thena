-- | __The live choice points, as a pane of their own__ (MS12).
--
-- His ruling, 2026-11-16, when the alternative was to teach the machine pane's
-- frame rows to tell a choice from a call: /"let's not complicate things by
-- doing the harder thing when we can literally do the simpler and principled
-- thing — we make it possible for the TUI to have a standalone pane for
-- choice-points."/ So this is its own module and not a field on
-- 'Thena.View.Machine.FrameView': the frame rows keep the fidelity
-- 'Thena.Render.renderMachine' has, and the choice points get a reader that
-- says only what they are.
--
-- **This is exposure and not new design.** @:choices@ has printed exactly these
-- three things since MS4 — 'Thena.Render.renderChoices' — and what was missing
-- was a read a frontend could reach: 'Thena.Engine.choicePoints' takes a
-- 'Thena.Engine.Machine', and a frontend holds a session.
module Thena.View.Choices
  ( ChoiceView (..)
  , displayChoice
  ) where

import Thena.Core.Term (Spelling, spelledIn)
import Thena.Engine (ChoicePoint (..))

-- | One live choice point: the identifier @retry ‹n›@ names it by, the rule it
-- is running now, and the rules still untried, in dispatch order.
--
-- **Every choice point here is live**, which is the peek's own invariant — a
-- 'Thena.Engine.Choice' frame is unbuilt the moment its last alternative is
-- taken — so there is no \"exhausted\" field and 'choiceViewUntried' is never
-- empty.
--
-- **There is no term in here**, which is why 'Thena.View.Choices' is the one
-- view module that needs no 'Thena.View.Core.Budget': a depth to print to has
-- nothing to bound.
data ChoiceView = ChoiceView
  { choiceViewId      :: Int
    -- ^ **what @retry ‹n›@ takes.** Minted from the session's name counter
    -- (his choice, 2026-08-23), so it is stable and unique but not
    -- consecutive — every binder minted in between spends the counter too, and
    -- a pane that numbers its own rows instead would hand the user a number
    -- @retry@ refuses.
  , choiceViewRunning :: String
    -- ^ the alternative being run now.
  , choiceViewUntried :: [String]
    -- ^ the ones still to try, in dispatch order, which is the order @retry@
    -- with no argument walks.
  }
  deriving (Eq, Show)

-- | **The names are spelled, not dotted.** 'Thena.Core.Term.spelledIn' is the
-- shortest ending that still resolves to the name under what is open, and it is
-- the same function 'Thena.Render.nameString' prints @:choices@ through — so a
-- pane and the prompt agree without the pane choosing a printer policy.
--
-- Handing over 'Thena.Core.Term.GlobalName' instead would make every row carry
-- the whole module path, which is the defect he reported of the offer's
-- production labels at phase 316: the shape beside the name was pushed off a
-- capped popup.
displayChoice :: Spelling -> ChoicePoint -> ChoiceView
displayChoice sp cp =
  ChoiceView
    (pointId cp)
    (spelledIn sp (pointRule cp))
    (map (spelledIn sp) (pointAlts cp))
