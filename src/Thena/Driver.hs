-- | The session, and the commands that act on it.
--
-- Nothing in this module or below it may assume a terminal, block on 'getLine',
-- or write to stdout (@PLAN.md@ §2.1, §12 invariant 4). The terminal lives in
-- "Thena.Repl" and nowhere else. That is why 'command' is a pure function and
-- why the phase-0 tests need no terminal to run.
--
-- Phase 0 only. At phase 4 this module is rewritten around the loop of §7.8:
-- a command compiles to @[Instr]@, is loaded into the current machine's @pc@,
-- and the driver dispatches on the five 'Outcome' cases.
module Thena.Driver
  ( Session
  , newSession
  , Response (..)
  , command
  ) where

-- | Everything the session holds. It is empty at phase 0 and grows into the
-- proof list, the global environment, the per-proof undo stacks and the
-- session-global name counter (§2.4).
data Session = Session

-- | The empty session. 'Session'\'s constructor is exported — Level 1 is spent
-- on 'Scope', 'Var' and 'Cursor' and nowhere else (§3.4) — but "Thena.Repl"
-- should still go through this, so that gaining a field here is not a change
-- to the frontend.
newSession :: Session
newSession = Session

-- | What the driver hands back for a frontend to render.
--
-- A datatype rather than a 'String', even with two cases, because §12
-- invariant 2 says replies carry structure and phase 2's renderer will copy
-- whatever shape it finds here.
data Response
  = Echoed String  -- ^ the line, to be shown back
  | Quit           -- ^ leave the loop
  deriving (Eq, Show)

-- | Phase 0's entire driver: @:quit@ leaves, anything else echoes.
command :: Session -> String -> (Session, Response)
command s ":quit" = (s, Quit)
command s line    = (s, Echoed line)
