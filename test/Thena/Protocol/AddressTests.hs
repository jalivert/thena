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
module Thena.Protocol.AddressTests (tests) where

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
import Thena.Driver (parseDevelopment)
import Thena.Global.Env (emptyGlobals)
import Thena.Fixtures (allFour, guessShadowing, richTypes, withConstraint)
import Thena.Protocol.Address
  ( Address (..)
  , AddressError (..)
  , Move (..)
  , addressOf
  , follow
  )

tests :: TestTree
tests =
  testGroup
    "Thena.Protocol.Address"
    [ testGroup "every position round trips" roundTripTests
    , testGroup "the address, written out" exactTests
    , testGroup "a stale address is refused" refusalTests
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
    at p fs = addressOf (foldl step (enter p) fs)
    step c f = either (error . show) id (f c)

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
