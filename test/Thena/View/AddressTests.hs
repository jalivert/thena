-- | Addresses (phase 111).
--
-- **The round trip is the weak test and it is here for completeness only.**
-- 'addressOf' and 'follow' are two readings of the same table, so a move
-- mis-mapped in both directions would agree with itself and pass — the same
-- trap 'Thena.CursorTests' names at the top of its own file.
--
-- **What does the work is Γ and the focus.** After following an address the
-- position must have the same 'focus' — the actual component or subterm, not a
-- description of it — and the same 'context', which §4.5 derives from the prefix
-- by a rule the moves never run. An address that lands one component early
-- passes neither.
--
-- **And the exact assertions are the second crossing**: for hand-picked
-- positions the address is written out move by move, so a systematic off-by-one
-- in the positional parts cannot hide behind a self-consistent walk.
module Thena.View.AddressTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import Test.Tasty.QuickCheck (counterexample, forAll, property, testProperty)

import Thena.Development.Cursor
  ( Cursor
  , Part (..)
  , along
  , context
  , crossType
  , crossValue
  , down
  , enter
  , focus
  , into
  )
import Thena.Development.Partial (Partial)
import Thena.DevelopmentTests (genDevelopment)
import Thena.Driver
  ( Session
  , machineOf
  , newSession
  , oneLine
  , oneProgram
  , parseDevelopment
  )
import Thena.Global.Env (emptyGlobals)
import Thena.Fixtures (allFour, guessShadowing, richTypes, withConstraint)
import Thena.Engine
  ( Development (..)
  , Exec (..)
  , Machine (..)
  , Outcome (..)
  , cursor
  , development
  , load
  , names
  , step
  )
import Thena.Standard (expectedBase)
import Thena.View.Address
  ( Address (..)
  , AddressError (..)
  , Move (..)
  , addressOf
  , focusing
  , follow
  )

tests :: TestTree
tests =
  testGroup
    "Thena.View.Address"
    [ testGroup "every position round trips" roundTripTests
    , testGroup "the address, written out" exactTests
    , testGroup "a stale address is refused" refusalTests
    , testGroup "a compiled click lands where the walk lands" clickTests
    , testGroup "and it does through the driver, like a typed line" drivenTests
    ]

-- | The name counter every walk in this file starts from.
--
-- **Not zero, and the reason is a bug this file caught in its own helper.**
-- Descending into a binder mints a fresh variable; the fixtures already contain
-- @Var 0@, @Var 1@ and so on. Walking from zero therefore opens a binder as a
-- variable the term already uses, and rebuilding closes over /both/ occurrences
-- — so the position is not the position it claims to be. Every walk here starts
-- above anything a fixture can contain.
startCounter :: Int
startCounter = 1000

-- | Every cursor reachable from the root by at most @d@ moves.
--
-- Breadth first and duplicate-tolerant: the point is coverage of shapes, not a
-- minimal set. The name counter threads through because 'down' mints.
reachable :: Int -> Cursor -> [Cursor]
reachable d root = map fst (go d [(root, startCounter)])
  where
    go 0 cs = cs
    go k cs = cs <> go (k - 1) (concatMap next cs)

    next (c, n) = [x | Right x <- map (\f -> f c n) movesFrom]

    movesFrom =
      [ \c n -> fmap (\x -> (x, n)) (along c)
      , \c n -> fmap (\x -> (x, n)) (into c)
      , \c n -> fmap (\x -> (x, n)) (crossType c)
      , \c n -> fmap (\x -> (x, n)) (crossValue c)
      ]
        <> [\c n -> down p n c | p <- parts]

    parts =
      [ Fun, Arg, Dom, Cod, Val, Type, Body, Motive, Target
      , Param 1, Method 1, Index 1, CanonArg 1, CanonArg 2
      ]

-- | Follow a cursor's own address and compare where you land.
--
-- Focus first, because it carries the thing itself; then Γ, which is derived by
-- a different rule and is what catches a step pushed in the wrong place.
agrees :: Cursor -> Either String ()
agrees c = case follow (addressOf c) startCounter c of
  Left e -> Left ("refused: " <> show e <> " for " <> show (addressOf c))
  Right (c', _)
    | focus c' /= focus c     -> Left ("focus differs at " <> show (addressOf c))
    | context c' /= context c -> Left ("context differs at " <> show (addressOf c))
    | otherwise               -> Right ()

failures :: Int -> Partial -> [String]
failures d p = [e | Left e <- map agrees (reachable d (enter p))]

roundTripTests :: [TestTree]
roundTripTests =
  [ testCase (name <> ": every position") $
      case failures 4 p of
        []    -> pure ()
        e : _ -> assertFailure e
  | (name, p) <-
      [ ("allFour", allFour)
      , ("richTypes", richTypes)
      , ("guessShadowing", guessShadowing)
      , ("withConstraint", withConstraint)
      ]
  ]
    <> [ testProperty "a generated development, every position" $
           forAll (genDevelopment [] 4) $ \src ->
             case parseDevelopment [] emptyGlobals [] 500 src of
               Left _       -> property True
               Right (p, _) -> case failures 3 p of
                 []    -> property True
                 e : _ -> counterexample (src <> "\n  " <> e) (property False)
       ]

-- | The address of a position, spelled out.
--
-- These are the crossing that the round trip cannot be: each expected list was
-- read off the development by hand, not produced by the code under test.
exactTests :: [TestTree]
exactTests =
  [ testCase "the root is the empty address" $
      addressOf (enter allFour) @?= Address []
  , testCase "one component along" $
      at allFour [along] @?= Address [GoAlong]
  , testCase "two components along" $
      at allFour [along, along] @?= Address [GoAlong, GoAlong]
  , testCase "crossing to a component's type" $
      at allFour [crossType] @?= Address [GoCrossType]
  , testCase "along, then into that component's type" $
      at allFour [along, crossType] @?= Address [GoAlong, GoCrossType]
  , testCase "into a guess" $
      at guessShadowing [into] @?= Address [GoInto]
  ]
  where
    at p fs = addressOf (foldl move (enter p) fs)
    move c f = either (error . show) id (f c)

refusalTests :: [TestTree]
refusalTests =
  [ testCase "walking past the end of the chain says how far it got" $
      case follow (Address (replicate 99 GoAlong)) startCounter (enter allFour) of
        Left (NoSuchPosition k _) | k > 0 -> pure ()
        other -> assertFailure ("expected a refusal with a count, got " <> show other)
  , testCase "a core descent on the spine is refused at move zero" $
      case follow (Address [GoDown Fun]) startCounter (enter allFour) of
        Left (NoSuchPosition 0 _) -> pure ()
        other -> assertFailure ("expected a refusal at 0, got " <> show other)
  ]

-- --------------------------------------------------------------------------
-- Clicking (MS7 phase 111 and 113, merged here at 124)
--
-- **These followed 'focusing' into this module.** They lived in
-- @Thena.View.MessageTests@ and @Thena.View.ServerTests@, beside a
-- request type and an envelope that phase 124 deleted; what they test is an
-- 'Address', so they belong with the other two readings of one.
-- --------------------------------------------------------------------------

-- | The crossing the round trip above cannot do.
--
-- 'follow' walks the cursor API; 'focusing' compiles the same address into
-- movement instructions and the /engine/ runs them. Two code paths, one
-- position — so a move mapped to the wrong op is caught, which reading one
-- table twice can never catch.
--
-- It is also the check that a click is not a side door: if the compiled
-- instructions did not land where the walk lands, a frontend would be moving
-- the cursor behind the machine's back.
clickAgrees :: Partial -> Cursor -> Either String ()
clickAgrees p c =
  case follow addr startCounter c of
    Left e -> Left ("the walk refused " <> show addr <> ": " <> show e)
    Right (walked, _) ->
      case runTo (load (focusing addr) (machineAt p)) of
        Finished m
          | focus (cursor (development m)) == focus walked -> Right ()
          | otherwise -> Left ("the click landed elsewhere for " <> show addr)
        other -> Left ("the click did not finish for " <> show addr <> ": " <> take 120 (show other))
  where
    addr = addressOf c

runTo :: Machine -> Outcome
runTo m = case step m of
  Continue m' -> runTo m'
  outcome     -> outcome

-- | A machine at the root of @p@.
machineAt :: Partial -> Machine
machineAt p =
  Machine (Exec [] [] []) (Development (enter p)) [] emptyGlobals expectedBase [] [] startCounter 0

clickTests :: [TestTree]
clickTests =
  [ testCase (name <> ": every position") $
      case [e | Left e <- map (clickAgrees p) (reachable 3 (enter p))] of
        []    -> pure ()
        e : _ -> assertFailure e
  | (name, p) <-
      [ ("allFour", allFour)
      , ("richTypes", richTypes)
      , ("guessShadowing", guessShadowing)
      , ("withConstraint", withConstraint)
      ]
  ]

-- | The same, with the whole driver in the middle.
--
-- A click is @oneProgram (focusing addr)@ and nothing else, so it is
-- snapshotted for @:undo@ and rewound if it fails, exactly as a typed line is.
drivenTests :: [TestTree]
drivenTests =
  [ testCase "from a cursor at the root" (everyLiveAddress started)
  , testCase "and from one that is not" (everyLiveAddress standingOffRoot)
  , testCase "a click on the root goes to the root" focusRoot
  , testCase "and a click can be taken back like any line" focusUndoes
  ]

-- | Run lines through the driver, as a frontend would.
after :: [String] -> Session
after = foldl (\s l -> fst (oneLine s l)) newSession

cursorOf :: Session -> Cursor
cursorOf = cursor . development . machineOf

counterOf :: Session -> Int
counterOf = names . machineOf

clickAt :: Session -> Address -> Session
clickAt s addr = fst (oneProgram s (focusing addr))

-- | A development with a binder and a body to walk into.
started :: Session
started = after [":theorem t : \8704 (A : Type\8320) -> A", "attack", "intro A"]

-- | The same shape, with the cursor left standing **inside the guess, on the
-- assumption** rather than at the root (MS7 phase 121).
--
-- **This is the fixture that phase turned on.** 'started' stands at the root,
-- so an address run relatively and an address run absolutely agree there, and
-- the crossing passed while 'focusing' was compiling addresses that only
-- worked from the root. Here they disagree: the hole is at
-- @[GoInto, GoAlong]@ and the cursor is at @[GoInto]@, so a relative run takes
-- @into@ at the assumption and refuses with @NotAGuess@ — which is the error
-- the editor experiment reported
-- (@reports\/2026-09-27-the-address-anchor.md@).
--
-- **Prelude-free, like its sibling**, so the primitives are written out:
-- @attack@ and @intro@ are rules and this session has no base.
standingOffRoot :: Session
standingOffRoot =
  after
    [ ":theorem t : \8704 (A : Type\8320) -> A -> A"
    , "prim-attack"
    , "prim-lambda \"A\""
    , "into"
    ]

-- | Every candidate address this session actually has, crossed.
--
-- **Which addresses exist is a fact about the fixture, not something to
-- guess** — the first draft asserted @[GoAlong, GoCrossType]@ and the walk
-- refused it. So the candidates are filtered by 'follow' and the survivors are
-- what the driver is held to, with a floor so a fixture that stopped having
-- positions could not pass silently.
everyLiveAddress :: Session -> IO ()
everyLiveAddress s = do
  let candidates =
        [ Address ms
        | ms <-
            [ [], [GoAlong], [GoCrossType], [GoInto]
            , [GoCrossType, GoDown Cod], [GoCrossType, GoDown Dom]
            , [GoInto, GoAlong], [GoInto, GoCrossType]
            ]
        ]
      live = [a | a <- candidates, isRight (follow a (counterOf s) (cursorOf s))]
  if length live >= 3
    then mapM_ (landsWhere s) live
    else assertFailure ("only " <> show (length live) <> " addresses were live in the fixture")
  where
    isRight = either (const False) (const True)

landsWhere :: Session -> Address -> IO ()
landsWhere s addr = case follow addr (counterOf s) (cursorOf s) of
  Left e -> assertFailure ("the walk refused " <> show addr <> ": " <> show e)
  Right (walked, _)
    | focus (cursorOf (clickAt s addr)) == focus walked -> pure ()
    | otherwise -> assertFailure ("the click landed elsewhere for " <> show addr)

-- | The empty address is the root, and clicking it **moves**.
--
-- It compiled to an empty program until phase 121, so a frontend asking to go
-- back to the root was told the program completed and left where it was — a
-- silent no-op rather than a refusal, which is the worse of the two.
focusRoot :: IO ()
focusRoot = do
  let moved = clickAt standingOffRoot (Address [])
  if focus (cursorOf standingOffRoot) == focus (cursorOf moved)
    then assertFailure "the fixture already stood at the root, so this proves nothing"
    else addressOf (cursorOf moved) @?= Address []

-- | A click is a line, so taking it back is @:undo@ and nothing special.
focusUndoes :: IO ()
focusUndoes = do
  let before = cursorOf started
      moved  = clickAt started (Address [GoAlong])
      back   = fst (oneLine moved ":undo")
  if focus (cursorOf moved) == focus before
    then assertFailure "the click did not move the cursor, so undoing it proves nothing"
    else focus (cursorOf back) @?= focus before
