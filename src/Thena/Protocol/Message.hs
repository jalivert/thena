-- | What crosses between a client and the server (phase 111).
--
-- **The channel already existed.** @PLAN-machine.md@ §7.5 is the rule the
-- machine has always followed — /anything the machine cannot do itself, it
-- yields/ — and "Thena.Driver" is the far side of it, already pure: it takes a
-- session and a line and returns a session and a structured 'Response', with no
-- IO and no rendering. "Thena.Repl" turns that into text. **A client is the same
-- far side reached over a wire**, so this module wraps what the driver already
-- says rather than inventing a second vocabulary beside it.
--
-- That is deliberate and it is the reason 'Turn' carries a 'Response' whole. A
-- parallel enum mirroring 'Response'\'s constructors would be one more
-- hand-written mirror to keep in step, and the ones this project already has are
-- the things that cost a phase when they drift.
--
-- **The server does not know about panes** (his ruling, 2026-09-23). It says
-- what happened; the client decides what to draw. So there is no message here
-- for /give me the contents of pane four/, and there is not meant to be one.
module Thena.Protocol.Message
  ( -- * The two directions
    FromClient (..)
  , FromServer (..)
  , ProtocolError (..)
  , JobId (..)

    -- * Driving a session
  , turn
  , focusing
  , opOf
  ) where

import Thena.Driver (Response, Session, oneLine)
import Thena.Engine (Question)
import Thena.Instral.Ops (Instr (..), Op (..))
import Thena.Protocol.Address (Address (..), AddressError, Move (..))

-- | A running job, named by the server because nothing else can name it.
--
-- **The one thing here that is minted**, and it is minted because a job has no
-- structure to be addressed by: it is not in the development, it has no name in
-- any scope, and there is nothing to walk to reach it. Everything else a client
-- points at is either already named ('Thena.Core.Term.GlobalName', a rule, a
-- theorem) or addressed by 'Address'.
newtype JobId = JobId Int
  deriving (Eq, Ord, Show)

-- | What a client sends.
--
-- **Almost everything is a line**, and that is his ruling of 2026-09-23: a
-- question is answered at the REPL, a choice is picked at the REPL, a yield is
-- returned at the REPL, and @:undo@, @retry@, @:suspend@ and @:resume@ are
-- ordinary commands. So there is no session protocol beside the language — the
-- editor types what a person would type.
--
-- The rest are the things a person at a terminal cannot express: a click at a
-- position with no name, and the client-lifecycle words.
data FromClient
  = Line String
    -- ^ one REPL line. 'Thena.Driver.oneLine' already routes it to the pending
    -- question when there is one, so answering needs no message of its own.
  | Focus Address
    -- ^ put the cursor at a position — a click.
    --
    -- **It is not a side door.** 'focusing' compiles it into exactly the
    -- movement instructions the line would have produced, and they run through
    -- the machine like any others: visible in the program, undoable, and on the
    -- one path. A click that moved the cursor behind the machine's back would be
    -- the hidden state the first design principle refuses.
  | ClaimKeys
    -- ^ ask for the wheel (phase 117). Granted, never taken.
  | ReleaseKeys
    -- ^ give the wheel up (phase 117).
  | Terminate JobId
    -- ^ stop a running job (phase 118).
  | Save
    -- ^ write the project to disk (phase 112).
  deriving (Eq, Show)

-- | What the server sends.
--
-- **Three shapes now, and later phases add their own**: the full state (115),
-- events during a run (116), who holds the keys (117) and what is running
-- (118). They are not stubbed here — a constructor with a payload nobody can
-- fill yet is the lateral validity §4.0 I1 refuses, and adding one later is a
-- compile error at every match, which is exactly the reminder we want.
data FromServer
  = Welcome Int
    -- ^ the protocol version this server speaks, sent on connect and before
    -- anything else.
  | Turn Response (Maybe Question)
    -- ^ what a line did, and the question it left pending if it left one.
    --
    -- The 'Response' is the driver's own, unchanged. **Do not mirror it.**
  | Refused ProtocolError
  deriving (Eq, Show)

-- | Why the server would not do what a client asked.
--
-- Structured, never a string (§12) — a client has to be able to branch on these,
-- and 'BadAddress' in particular carries how far the walk got, which is what
-- lets an editor tell a stale click from a wrong one.
data ProtocolError
  = NotAtTheWheel
    -- ^ this client is an observer; another holds the keys (phase 117).
  | BadAddress AddressError
    -- ^ the address led nowhere. Ordinary, not a bug: the client drew a
    -- development, it changed underneath, and the click arrived late.
  | VersionMismatch Int Int
    -- ^ what the client asked for, and what this server speaks.
  | NoSuchJob JobId
  | NotServedYet
    -- ^ this server does not answer that message yet. **Not a stub payload and
    -- not a lie about the request**: phases 117 and 118 add the keys and the
    -- jobs, and until they do the honest answer is that this one does not serve
    -- them.
  deriving (Eq, Show)

-- | Run one line, and say what happened.
--
-- The whole of the mapping, and it is this short on purpose: 'oneLine' already
-- did the work, and everything this adds is the name of the shape it comes back
-- in.
turn :: Session -> Maybe Question -> String -> (Session, FromServer, Maybe Question)
turn s pending line = (s', Turn resp asking, asking)
  where
    (s', resp, asking) = oneLine s pending line

-- | Compile an address into the movement instructions that reach it.
--
-- One instruction per move, in order, from wherever the cursor stands — so this
-- is only correct from the root, which is where 'Thena.Protocol.Address.follow'
-- also starts. The caller returns to the root first.
focusing :: Address -> [Instr]
focusing (Address ms) = map (Do . opOf) ms

-- | The op a move is.
--
-- **One to one, and that is the finding rather than a convenience**: the five
-- moves an address can name are exactly the five movement ops that take no
-- operand, so an address is a program the user could have typed. Nothing had to
-- be added to the language to make clicking work.
opOf :: Move -> Op
opOf m = case m of
  GoAlong      -> Along
  GoInto       -> Into
  GoCrossType  -> CrossType
  GoCrossValue -> CrossValue
  GoDown part  -> Down part
