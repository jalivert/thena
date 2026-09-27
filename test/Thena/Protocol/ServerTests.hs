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
import Thena.Protocol.Address (Address (..), Move (..), addressOf, follow)
import qualified Thena.Protocol.Message as Msg
import Thena.Protocol.Server (Server (..), newServer, serve)

tests :: TestTree
tests =
  testGroup
    "Thena.Protocol.Server"
    [ testCase "a click lands where the address says" focusTests
    , testCase "and it does so wherever the cursor stood" focusFromOffRoot
    , testCase "a click on the root goes to the root" focusRoot
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

-- | The same shape, with the cursor left standing **inside the guess, on the
-- assumption** rather than at the root (MS7 phase 121).
--
-- **This is the fixture the phase turned on.** 'started' stands at the root, so
-- an address run relatively and an address run absolutely agree there and the
-- crossing below passed while 'Thena.Protocol.Message.focusing' was compiling
-- addresses that only worked from the root. Here they disagree: the hole is at
-- @[GoInto, GoAlong]@ and the cursor is at @[GoInto]@, so a relative run takes
-- @into@ at the assumption and refuses with @NotAGuess@ — which is the error
-- the editor experiment reported (@reports\/2026-09-27-the-address-anchor.md@).
--
-- **Prelude-free, like every other fixture here**, so the primitives are
-- written out: @attack@ and @intro@ are rules and this server has no base.
standingOffRoot :: Server
standingOffRoot =
  after
    [ ":theorem t : ∀ (A : Type₀) -> A -> A"
    , "prim-attack"
    , "prim-lambda \"A\""
    , "into"
    ]

-- | Every candidate address this development actually has.
--
-- **Which addresses exist is a fact about the fixture, not something to guess**
-- — the first draft asserted @[GoAlong, GoCrossType]@ and the /walk/ refused it,
-- because one @along@ leaves the spine here. So the candidates are filtered by
-- 'follow' and the surviving ones are what 'serve' is held to, with a floor so
-- that a fixture which stopped having positions could not pass silently.
focusTests :: IO ()
focusTests = everyLiveAddress started

-- | The same sweep from a cursor that is **not** at the root.
--
-- 'standingOffRoot' says why this is a separate case rather than more
-- candidates: it is the one that fails when an address is run relatively.
focusFromOffRoot :: IO ()
focusFromOffRoot = everyLiveAddress standingOffRoot

everyLiveAddress :: Server -> IO ()
everyLiveAddress srv = do
  let candidates =
        [ Address ms
        | ms <-
            [ [], [GoAlong], [GoCrossType], [GoInto]
            , [GoCrossType, GoDown Cod], [GoCrossType, GoDown Dom]
            , [GoInto, GoAlong], [GoInto, GoCrossType]
            ]
        ]
      live = [a | a <- candidates, isRight (follow a (counterOf srv) (cursorOf srv))]
  if length live >= 3
    then mapM_ (landsWhere srv) live
    else assertFailure ("only " <> show (length live) <> " addresses were live in the fixture")
  where
    isRight = either (const False) (const True)

-- | The empty address is the root, and clicking it **moves**.
--
-- It compiled to an empty program until phase 121, so a client that asked to go
-- back to the root was answered @Completed@ and left where it was — a silent
-- no-op rather than a refusal, which is the worse of the two.
focusRoot :: IO ()
focusRoot = do
  let (moved, _) = serve standingOffRoot (Msg.Focus (Address []))
  if focus (cursorOf standingOffRoot) == focus (cursorOf moved)
    then assertFailure "the fixture already stood at the root, so this proves nothing"
    else addressOf (cursorOf moved) @?= Address []

-- | Serve a click, and compare where it landed with where the cursor walk says
-- it should have.
--
-- **Two different routes to one position**: 'follow' walks the cursor API, and
-- 'serve' compiles the address into movement instructions and lets the machine
-- run them. This is the address module's crossing again, now with the whole
-- driver in the middle — so it also checks that a click is snapshotted, typed
-- and dispatched like a line rather than by a private route.
landsWhere :: Server -> Address -> IO ()
landsWhere srv addr = case follow addr (counterOf srv) (cursorOf srv) of
  Left e -> assertFailure ("the walk refused " <> show addr <> ": " <> show e)
  Right (walked, _) ->
    case serve srv (Msg.Focus addr) of
      (srv'', [Msg.Turn _ Nothing])
        | focus (cursorOf srv'') == focus walked -> pure ()
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
