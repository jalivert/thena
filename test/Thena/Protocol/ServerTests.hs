-- | The server as a client sees it (MS7 phase 113).
--
-- **The golden transcripts are this phase's real regression test** and they are
-- not here: 'Thena.Repl.turn' now goes through 'serve', so every transcript in
-- the suite is a protocol test, and they had to come out byte-identical. What is
-- here is the part the transcripts cannot reach — 'Msg.Focus', which no typed
-- line produces.
module Thena.Protocol.ServerTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Development.Cursor (Cursor, Part (..), focus)
import Thena.Driver (Session (..))
import Thena.Engine (Machine (..), cursor, development, names)
import Thena.Protocol.Address (Address (..), Move (..), follow)
import qualified Thena.Protocol.Message as Msg
import Thena.Protocol.Server (Server (..), newServer, serve)

tests :: TestTree
tests =
  testGroup
    "Thena.Protocol.Server"
    [ testCase "a click lands where the address says" focusTests
    , testCase "and it can be taken back like any line" focusUndoes
    , testCase "a message this server does not serve says so" unserved
    ]

-- | Run lines through the server, as a client would.
after :: [String] -> Server
after = foldl (\srv l -> fst (serve srv (Msg.Line l))) newServer

cursorOf :: Server -> Cursor
cursorOf = cursor . development . sessionMachine . serverSession

counterOf :: Server -> Int
counterOf = names . sessionMachine . serverSession

-- | A development with a binder and a body to walk into.
started :: Server
started = after [":theorem t : ∀ (A : Type₀) -> A", "attack", "intro A"]

-- | Every candidate address this development actually has.
--
-- **Which addresses exist is a fact about the fixture, not something to guess**
-- — the first draft asserted @[GoAlong, GoCrossType]@ and the /walk/ refused it,
-- because one @along@ leaves the spine here. So the candidates are filtered by
-- 'follow' and the surviving ones are what 'serve' is held to, with a floor so
-- that a fixture which stopped having positions could not pass silently.
focusTests :: IO ()
focusTests = do
  let candidates =
        [ Address ms
        | ms <-
            [ [], [GoAlong], [GoCrossType], [GoInto]
            , [GoCrossType, GoDown Cod], [GoCrossType, GoDown Dom]
            , [GoInto, GoAlong], [GoInto, GoCrossType]
            ]
        ]
      live = [a | a <- candidates, isRight (follow a (counterOf started) (cursorOf started))]
  if length live >= 3
    then mapM_ landsWhere live
    else assertFailure ("only " <> show (length live) <> " addresses were live in the fixture")
  where
    isRight = either (const False) (const True)

-- | Serve a click, and compare where it landed with where the cursor walk says
-- it should have.
--
-- **Two different routes to one position**: 'follow' walks the cursor API, and
-- 'serve' compiles the address into movement instructions and lets the machine
-- run them. This is the address module's crossing again, now with the whole
-- driver in the middle — so it also checks that a click is snapshotted, typed
-- and dispatched like a line rather than by a private route.
landsWhere :: Address -> IO ()
landsWhere addr = case follow addr (counterOf started) (cursorOf started) of
  Left e -> assertFailure ("the walk refused " <> show addr <> ": " <> show e)
  Right (walked, _) ->
    case serve started (Msg.Focus addr) of
      (srv', [Msg.Turn _ Nothing])
        | focus (cursorOf srv') == focus walked -> pure ()
        | otherwise -> assertFailure ("the click landed elsewhere for " <> show addr)
      (_, other) -> assertFailure ("the server said " <> take 160 (show other))

-- | A click is a line, so taking it back is @:undo@ and nothing special.
focusUndoes :: IO ()
focusUndoes = do
  let before = cursorOf started
      (moved, _) = serve started (Msg.Focus (Address [GoAlong]))
      (back, _) = serve moved (Msg.Line ":undo")
  if focus (cursorOf moved) == focus before
    then assertFailure "the click did not move the cursor, so undoing it proves nothing"
    else focus (cursorOf back) @?= focus before

unserved :: IO ()
unserved = snd (serve newServer Msg.ClaimKeys) @?= [Msg.Refused Msg.NotServedYet]
