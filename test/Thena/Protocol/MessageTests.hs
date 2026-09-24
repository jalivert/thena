-- | The protocol's messages (phase 111).
--
-- **The test worth having is the crossing, and it is 'clickAgrees'.**
-- "Thena.Protocol.Address"'s @follow@ walks the cursor API directly;
-- 'Thena.Protocol.Message.focusing' compiles the same address into movement
-- instructions and the /engine/ runs them. Two different code paths reach the
-- same position, so a move mapped to the wrong op is caught — which the address
-- module's own round trip cannot do, since it reads one table twice.
--
-- It is also the check that a click is not a side door: if the compiled
-- instructions did not land where the walk lands, the editor would be moving the
-- cursor behind the machine's back.
module Thena.Protocol.MessageTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase)

import Thena.Development.Cursor
  ( Cursor
  , Part (..)
  , along
  , crossType
  , crossValue
  , down
  , enter
  , focus
  , into
  )
import Thena.Development.Partial (Partial)
import Thena.Engine
  ( Development (..)
  , Exec (..)
  , Machine (..)
  , Outcome (..)
  , load
  , step
  )
import Thena.Fixtures (allFour, guessShadowing, richTypes, withConstraint)
import Thena.Global.Env (emptyGlobals)
import Thena.Protocol.Address (addressOf, follow)
import Thena.Protocol.Message (focusing)
import Thena.Standard (expectedBase)

tests :: TestTree
tests =
  testGroup
    "Thena.Protocol.Message"
    [ testGroup "a compiled click lands where the walk lands" clickTests ]

-- | Every cursor reachable from the root by at most @d@ moves.
reachable :: Int -> Cursor -> [Cursor]
reachable d root = map fst (go d [(root, startCounter)])
  where
    go 0 cs = cs
    go k cs = cs <> go (k - 1) (concatMap next cs)
    next (c, n) = [x | Right x <- map (\f -> f c n) moves]
    moves =
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

runTo :: Machine -> Outcome
runTo m = case step m of
  Continue m' -> runTo m'
  outcome     -> outcome

-- | Compile a cursor's address, run it through the engine, and compare.
clickAgrees :: Partial -> Cursor -> Either String ()
clickAgrees p c =
  case follow addr startCounter c of
    Left e -> Left ("the walk refused " <> show addr <> ": " <> show e)
    Right (walked, _) ->
      case runTo (load (focusing addr) (start p)) of
        Finished m
          | focus (cursor (development m)) == focus walked -> Right ()
          | otherwise -> Left ("the click landed elsewhere for " <> show addr)
        other -> Left ("the click did not finish for " <> show addr <> ": " <> take 120 (show other))
  where
    addr = addressOf c

-- | The name counter every walk here starts from.
--
-- **It has to be the same number on both sides, and it has to be above the
-- fixtures.** Both matter and this test found both. Same on both sides, because
-- descending into a binder mints and the opened term mentions what was minted.
-- Above the fixtures, because a walk from zero opens a binder as a variable the
-- term already uses, and rebuilding then closes over both occurrences — the
-- cursor is no longer at the position it names. That was this test\'s first
-- failure and the fault was in the walk, not in what it was testing.
startCounter :: Int
startCounter = 1000

-- | A machine at the root of @p@.
start :: Partial -> Machine
start p =
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
