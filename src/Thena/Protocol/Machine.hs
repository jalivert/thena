-- | What a running machine looks like to the editor (MS7 phase 115f;
-- @discussion\/editor-display.md@ §7's other half — "the frames, what is
-- underneath" — and 115d's own "what is not here").
--
-- **At the fidelity the terminal already has, and no further.**
-- 'Thena.Repl.renderMachine' draws a frame from two fields shared by both
-- 'Frame' constructors — how many instructions it resumes with, and
-- whether it has already returned — never asking whether the frame is a
-- plain 'Call' or a 'Choice' with a rule and untried alternatives of its
-- own. A 'Choice' frame's own richness has a printer nowhere in the
-- terminal today; exposing it here would be new design, not exposure of
-- what exists, so 'FrameView' matches 'renderMachine' exactly and no more —
-- see the phase's own plan for where that is recorded.
module Thena.Protocol.Machine
  ( FrameView (..)
  , MachineView (..)
  , displayFrame
  , displayMachine
  ) where

import Thena.Core.Term (Var)
import Thena.Engine (Exec (..), Frame (..), Machine (..))
import Thena.Language.Grammar (Grammar)
import Thena.Protocol.Address (Address)
import Thena.Protocol.Display (Budget)
import Thena.Protocol.Instral (StatementView, ValueView, displayBlock, displayValue)
import Thena.Syntax.Print (Env)

-- | One frame of the call stack, at 'Thena.Repl.renderMachine's own
-- fidelity: how much of it is left to resume, and whether control has
-- already passed back out.
data FrameView = FrameView
  { frameResumeCount :: Int
  , frameReturned    :: Bool
  }
  deriving (Eq, Show)

displayFrame :: Frame -> FrameView
displayFrame fr = FrameView (length (resume fr)) (returned fr)

-- | The three panes 'Thena.Repl.renderMachine' draws: the program still to
-- run, the bindings in scope, and the calls standing underneath it.
data MachineView = MachineView
  { machinePc    :: [StatementView]
  , machineEnv   :: [(String, ValueView)]
  , machineStack :: [FrameView]
  }
  deriving (Eq, Show)

-- | 'displayBlock' already answers "is this the head of a live @pc@" given
-- which index is live (115d) — for a running machine that is always index
-- @0@ when there is a @pc@ left to run at all, and no index when there is
-- not.
displayMachine :: [Grammar] -> Budget -> Env -> [(Var, Address)] -> Int -> Address -> Machine -> MachineView
displayMachine gs budget penv bs n at m =
  MachineView
    (displayBlock gs budget penv bs n at headOfPc (pc ex))
    [ (x, displayValue gs budget penv bs n at v) | (x, v) <- env ex ]
    (map displayFrame (stack ex))
  where
    ex = exec m
    headOfPc = if null (pc ex) then Nothing else Just 0
