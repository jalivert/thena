-- | Carrying the protocol over a WebSocket (MS7 phase 114).
--
-- **The transport, and nothing else.** Everything about what a message /means/
-- is "Thena.Protocol.Server", which is pure; this module turns bytes into
-- messages and back and owns the one piece of state a connection needs. That
-- split is what lets the whole suite exercise the protocol in one process at
-- full speed while this file is exercised by a socket.
--
-- **A WebSocket and not a pipe, by his decision of 2026-09-23** — *"we are doing
-- web UI so we do sockets"* — with stdio left open for a future LSP-style
-- integration. Nothing in "Thena.Protocol.Server" or below would change for it.
module Thena.Protocol.Socket
  ( runSocketServer
  , Port
  , answer
  , sendable
  ) where

import Control.Concurrent.MVar (MVar, modifyMVar, newMVar)
import Control.Monad (forever)
import qualified Data.Text as T
import qualified Network.WebSockets as WS

import Thena.Driver (Session)
import Thena.Protocol.Codec (FromJson (..), ToJson (..), tagged)
import Thena.Protocol.Json (Json, decode, encode)
import Thena.Protocol.Message (FromClient, FromServer (..), ProtocolError (..))
import Thena.Protocol.Server (Server, serve, serverOn)
import Thena.Protocol.Wire ()

type Port = Int

-- | The protocol version this server speaks.
--
-- Sent before anything else, so a client that expects another one finds out at
-- once rather than at the first message it cannot read. It is the whole of the
-- versioning story until there is a second version to disagree with.
version :: Int
version = 1

-- | Serve a session on a port, forever.
--
-- **One 'Server' behind an 'MVar', shared by every connection.** There is one
-- machine, so there is one server state; a second connection sees the same
-- session, which is what his two-tabs requirement asks for. **Who is allowed to
-- drive is phase 117** — until the keys exist, every connection may send, and
-- the interleaving that permits is exactly the race the keys are for.
runSocketServer :: Port -> Session -> IO ()
runSocketServer port sess = do
  shared <- newMVar (serverOn sess)
  WS.runServer "127.0.0.1" port (application shared)

-- | **Loopback only.** A Thena session can define anything and run anything the
-- rule base can express, so it is not something to expose on a network
-- interface by default. A deployment that wants otherwise can say so; a default
-- that listens everywhere is a decision nobody made.
application :: MVar Server -> WS.ServerApp
application shared pending = do
  conn <- WS.acceptRequest pending
  send conn (Welcome version)
  forever $ do
    raw <- WS.receiveData conn
    mapM_ (send conn) =<< modifyMVar shared (pure . answer (T.unpack raw))

-- | One frame in, the new server state and what to say back.
--
-- **Pure, and separately testable** — the socket loop above is three lines
-- precisely so that everything worth testing is here and needs no network.
answer :: String -> Server -> (Server, [FromServer])
answer raw srv = case decode raw of
  Left e -> (srv, [Refused (Unreadable e)])
  Right j -> case fromJson j of
    Left e  -> (srv, [Refused (Malformed e)])
    Right m -> serve srv (m :: FromClient)

-- | What a message looks like on the wire, or nothing if it has no wire form
-- yet.
--
-- **'Turn' has none, and that is phase 115's work, not an oversight.** It
-- carries a 'Thena.Driver.Response', which carries terms, and what a term looks
-- like on the wire is settled in @discussion\/editor-display.md@ but not yet
-- built. Returning 'Nothing' here is what keeps that visible: the socket answers
-- 'NotServedYet' rather than inventing an encoding that would have to be
-- replaced.
sendable :: FromServer -> Maybe Json
sendable m = case m of
  Welcome v -> Just (tagged "Welcome" [toJson v])
  Refused e -> Just (tagged "Refused" [toJson e])
  Turn {}   -> Nothing

-- | Send one message, or say that it has no wire form.
send :: WS.Connection -> FromServer -> IO ()
send conn m =
  WS.sendTextData conn (T.pack (encode (maybe unserved id (sendable m))))
  where
    unserved = tagged "Refused" [toJson NotServedYet]
