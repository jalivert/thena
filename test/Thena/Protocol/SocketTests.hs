-- | The socket (MS7 phase 114).
--
-- **Almost everything here is pure**, because 'Thena.Protocol.Socket.answer' is
-- where the work is and the socket loop around it is three lines. The one test
-- that really opens a port is the last, and it exists because a transport that
-- has never carried a byte is not a transport.
module Thena.Protocol.SocketTests (tests) where

import Control.Concurrent (forkIO, killThread, threadDelay)
import Control.Exception (bracket)
import qualified Data.Text as T
import qualified Network.WebSockets as WS

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Protocol.Codec (CodecError (..), ToJson (..))
import Thena.Protocol.Json (JsonError (..), decode, encode)
import Thena.Protocol.Message (FromClient (..), FromServer (..), ProtocolError (..))
import Thena.Protocol.Server (newServer)
import Thena.Protocol.Socket (answer, runSocketServer, sendable)
import Thena.Protocol.Wire ()
import Thena.Repl (startingSession)

tests :: TestTree
tests =
  testGroup
    "Thena.Protocol.Socket"
    [ testCase "a frame that is not JSON is refused, and says where" notJson
    , testCase "JSON that is not a message is refused, and says what" notAMessage
    , testCase "a line is served" aLine
    , testCase "what has no wire form says so rather than inventing one" noWireForm
    , testCase "a client connects, is greeted, and is answered" endToEnd
    ]

notJson :: IO ()
notJson = case snd (answer "{oops" newServer) of
  [Refused (Unreadable (Unexpected 1 'o'))] -> pure ()
  other -> assertFailure ("expected an unreadable-frame refusal, got " <> show other)

notAMessage :: IO ()
notAMessage = case snd (answer "[\"Nope\"]" newServer) of
  [Refused (Malformed (NoSuchCase "FromClient" "Nope" 0))] -> pure ()
  other -> assertFailure ("expected a malformed-message refusal, got " <> show other)

aLine :: IO ()
aLine = case snd (answer (encode (toJson (Line ":theorem t : Type₀"))) newServer) of
  [Turn _ Nothing] -> pure ()
  other -> assertFailure ("expected a turn, got " <> take 120 (show other))

-- | 'Turn' carries a response, a response carries terms, and what a term looks
-- like on the wire is @discussion\/editor-display.md@ — designed, not built. The
-- absence is deliberate and this pins it, so that phase 115 removes a failing
-- expectation rather than quietly filling a gap nobody was watching.
noWireForm :: IO ()
noWireForm = do
  (sendable (Welcome 1) == Nothing) @?= False
  (sendable (Refused NotServedYet) == Nothing) @?= False
  case snd (answer (encode (toJson (Line "attack"))) newServer) of
    [m] -> (sendable m == Nothing) @?= True
    other -> assertFailure ("expected one message, got " <> take 120 (show other))

-- | The transport, actually carrying bytes.
--
-- A high port, the server on its own thread, and the client doing what a real
-- one would: read the greeting, send a message, read the answer.
endToEnd :: IO ()
endToEnd = do
  (sess, _) <- startingSession
  bracket (forkIO (runSocketServer port sess)) killThread $ \_ -> do
    threadDelay 400000
    WS.runClient "127.0.0.1" port "/" $ \conn -> do
      greeting <- WS.receiveData conn
      case decode (T.unpack greeting) of
        Right j | Just j == sendable (Welcome 1) -> pure ()
        other -> assertFailure ("expected a greeting, got " <> take 120 (show other))
      WS.sendTextData conn (T.pack (encode (toJson ClaimKeys)))
      reply <- WS.receiveData conn
      case decode (T.unpack reply) of
        Right j | Just j == sendable (Refused NotServedYet) -> pure ()
        other -> assertFailure ("expected a refusal, got " <> take 120 (show other))
  where
    port = 47893 :: Int
