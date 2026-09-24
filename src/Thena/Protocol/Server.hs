-- | The server, as a pure state machine over messages (MS7 phase 113).
--
-- **This is the far side of the driver, reached by messages instead of by a
-- function call.** @PLAN-machine.md@ §7.5's channel has always ended at
-- "Thena.Driver", which is pure and hands back structured data; this module is
-- the same place with the wire's shape in front of it, and "Thena.Repl" is now
-- a client of it rather than a caller of the driver.
--
-- **It is pure, and that is not an accident.** Nothing here reads a file or
-- writes one: §12 invariant 4 keeps IO at the frontend, and the driver already
-- says /I need this file/ by answering 'Thena.Driver.LoadRequested' rather than
-- reading it. So a session is a fold of 'serve' over the messages that were
-- sent, which is what makes it testable, replayable, and later carried over a
-- socket without anything here changing.
module Thena.Protocol.Server
  ( Server (..)
  , newServer
  , serverOn
  , serve
  ) where

import Thena.Driver (Session, newSession, oneLine, oneProgram)
import Thena.Engine (Question)
import Thena.Protocol.Message (FromClient (..), FromServer (..), ProtocolError (..), focusing)

-- | What the server holds between messages.
--
-- The session, and whether a question is outstanding. **The pending question is
-- the server's, not the client's**: 'Thena.Driver.oneLine' routes a line to the
-- answer or to the command depending on it, so a client keeping its own copy
-- could disagree with the machine about what its next line means.
data Server = Server
  { serverSession :: Session
  , serverPending :: Maybe Question
  }
  deriving (Eq, Show)

-- | A server on a bare session.
newServer :: Server
newServer = serverOn newSession

-- | A server on a session someone else prepared — the prelude and the standard
-- base, for instance, which 'Thena.Repl.startingSession' builds.
serverOn :: Session -> Server
serverOn s = Server s Nothing

-- | One message in, and what the server says about it.
--
-- A list out rather than one message, because a client message can produce more
-- than one and because the event stream (phase 116) is this shape with more in
-- it.
serve :: Server -> FromClient -> (Server, [FromServer])
serve srv msg = case msg of
  Line line -> ran (oneLine (serverSession srv) (serverPending srv) line)

  -- **Through the machine, not around it.** The address compiles to the
  -- ordinary movement instructions and they are run exactly as a typed line's
  -- are — snapshotted for @:undo@, rewound if they fail. A click that moved the
  -- cursor by a private route would be a second way into the machine.
  Focus addr -> ran (oneProgram (serverSession srv) (focusing addr))

  -- **Refused because this server does not serve them yet**, not because of
  -- anything about the request. Keys are phase 117, jobs 118, and saving needs
  -- the server to hold a project, which it does not. Answering with a plausible
  -- error would be worse than saying so.
  ClaimKeys   -> unserved
  ReleaseKeys -> unserved
  Terminate _ -> unserved
  Save        -> unserved
  where
    ran (s', resp, pending) = (Server s' pending, [Turn resp pending])
    unserved = (srv, [Refused NotServedYet])
