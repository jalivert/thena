-- | The seam: the views, computed from a session (MS7 phase 125).
--
-- **What is under test is the plumbing, not the views.** Each view module has
-- its own crossing against 'Thena.Repl' already; what "Thena.View" adds is where
-- the six arguments in front of every @display@ come from — the installed
-- grammars, the name counter, the display names at the focus, the binder
-- addresses, the cursor's route, and the address a view starts at. A seam that
-- passed the wrong counter, or the route of the wrong cursor, would build a
-- perfectly well-formed view of the wrong thing and every existing test would
-- still pass.
--
-- **So the crossing is the terminal's own whole command**, driven through
-- 'Thena.Driver.oneLine': @:show@ for the chain, @:matches@ for the match list.
-- Neither goes through any part of this module, and both see the same session.
--
-- **'Thena.View.binderAddresses' is the invariant the phase establishes**, so it
-- is asserted rather than assumed: every pair must be a variable and the address
-- of the link that binds it, checked by following the address with
-- 'Thena.View.Address.follow' — the reader the driver itself moves by, not a
-- second walk of the chain.
module Thena.ViewTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

import Thena.Core.Term (Var)
import Thena.Development.Component (Component (..))
import Thena.Development.Cursor (Focus (..), focus)
import Thena.Driver
  ( Session
  , newSession
  , oneLine
  , withRuleBases
  )
import Thena.Render (renderCursor)
import Thena.Repl (Turn (..), turn)
import Thena.Standard (expectedBase)
import Thena.View
  ( Budget (..)
  , binderAddresses
  , developmentView
  , focusTypeView
  , matchesView
  , sessionCursor
  , sessionGrammars
  , sessionNames
  )
import Thena.View.Address (follow)
import Thena.View.Redraw (markedChainText, redraw, redrawChain)
import Thena.View.Rules (RuleView (..))

tests :: TestTree
tests =
  testGroup
    "Thena.View"
    [ testGroup "the chain, against :show" (map chainCase fixtures)
    , testGroup "every binder address lands on its own link" (map binderCase fixtures)
    , testGroup "the focus's type, against :where" (map typeCase fixtures)
    , testGroup "the match list, against :matches" (map matchCase fixtures)
    , testGroup "and the fixtures really exercise it" notVacuous
    ]

-- ---------------------------------------------------------------------------
-- Sessions to look at
-- ---------------------------------------------------------------------------

-- | Lines through the driver, as a frontend would, over the shipped base — so
-- that @attack@ and @intro@ are there to run and 'matchesView' has something to
-- match.
after :: [String] -> Session
after = foldl (\s l -> fst (oneLine s l)) (withRuleBases expectedBase newSession)

-- | A name and a session: a development, and the cursor left somewhere in it.
--
-- **Where the cursor stands is the point of the list.** A seam that read the
-- route off the wrong cursor still draws a chain; it draws it with the wrong
-- link marked, and only a fixture standing somewhere other than the root can
-- show that.
fixtures :: [(String, Session)]
fixtures =
  [ ("nothing proved yet", after [])
  , ("a theorem, attacked, cursor at the root", after (theorem <> ["attack"]))
  , ("the cursor moved along, off the first link", after (theorem <> ["attack", "along"]))
  , ("along twice, then back to the root", after (theorem <> ["attack", "along", "goto-root"]))
  , ("inside the guess's own body", after (theorem <> ["attack", "into"]))
  ]
  where
    theorem = [":theorem t : \8704 (A : Type\8320) -> A -> A"]

-- ---------------------------------------------------------------------------
-- The chain
-- ---------------------------------------------------------------------------

-- | 'developmentView' takes every one of 'displayDevelopment's arguments off the
-- session; @:show@ hands 'Thena.Repl.renderCursor' its own. If the two draw the
-- same chain with the same link marked, the seam read the session the way the
-- terminal does.
chainCase :: (String, Session) -> TestTree
chainCase (name, s) =
  testCase name $
    markedChainText (developmentView (Budget 200) s)
      @?= renderCursor (sessionGrammars s) (sessionNames s) (sessionCursor s)

-- ---------------------------------------------------------------------------
-- Binder addresses
-- ---------------------------------------------------------------------------

binderCase :: (String, Session) -> TestTree
binderCase (name, s) =
  testCase name $ mapM_ one (binderAddresses s)
  where
    one (v, at) = case follow at (sessionNames s) (sessionCursor s) of
      Left e -> assertFailure (show at <> " does not follow: " <> show e)
      Right (cur, _) -> case focus cur of
        OnComponent c
          | boundBy c == v -> pure ()
          | otherwise ->
              assertFailure (show at <> " binds " <> show (boundBy c) <> ", not " <> show v)
        other -> assertFailure (show at <> " is not a component: " <> show other)

boundBy :: Component -> Var
boundBy c = case c of
  Assume   x _ _   -> x
  Define   x _ _ _ -> x
  Claim    x _ _   -> x
  Guess    x _ _ _ -> x
  Quantify x _ _   -> x

-- ---------------------------------------------------------------------------
-- The focus's type
-- ---------------------------------------------------------------------------

-- | 'focusTypeView' against @:where@'s own \"type\" section (MS7 phase 126).
--
-- **The naming is the part that could go wrong.** @:where@ builds its display
-- names by walking the prefix from the root and then into the term
-- ('Thena.Repl.walkSteps'\/@walkTerm@); the seam builds them by folding
-- 'Thena.View.sessionContext'. Those are two derivations of Γ at the focus, and
-- if they ever disagree the type prints with a different variable name on each
-- side — which is exactly what this compares.
typeCase :: (String, Session) -> TestTree
typeCase (name, s) = testCase name (drawn @?= typed)
  where
    drawn = fmap redraw (focusTypeView (Budget 200) s)
    typed = case dropWhile (/= "type") (turnOutput (turn s ":where")) of
      _ : line : _ -> Just (dropWhile (== ' ') line)
      _            -> Nothing

-- ---------------------------------------------------------------------------
-- The match list
-- ---------------------------------------------------------------------------

-- | 'matchesView' against @:matches@, which is 'Thena.Rules.matches' plus
-- 'Thena.Repl.renderMatches' and no part of this module — including the order,
-- which is dispatch order and the reason the seam drains the iterator rather
-- than sorting anything.
matchCase :: (String, Session) -> TestTree
matchCase (name, s) = testCase name (drawn @?= turnOutput (turn s ":matches"))
  where
    drawn = case map line (matchesView (Budget 200) s) of
      [] -> ["no rule applies here"]
      ls -> ls
    line rv = unwords (ruleViewName rv : ruleViewParams rv)

-- ---------------------------------------------------------------------------
-- Non-vacuity
-- ---------------------------------------------------------------------------

-- | **A green crossing over nothing is the failure @CLAUDE.md@ records three
-- goldens once having.** Every case above compares two drawings of the same
-- session, and two drawings of an empty development agree trivially — so what
-- the fixtures contain is asserted, not assumed. The numbers are floors.
notVacuous :: [TestTree]
notVacuous =
  [ testCase "some fixture has binders to address" $
      assertBool (show counts) (maximum counts >= 2)
  , testCase "some fixture has rules that match" $
      assertBool (show matched) (maximum matched >= 1)
  , testCase "some fixture has a marked link that is not the first" $
      assertBool (show marks) (any (\ms -> True `elem` drop 1 ms) marks)
  , testCase "some fixture has a type at the focus, and some has none" $
      -- Both sides of 'typeCase' answer 'Nothing' at a bare root, so the
      -- crossing there is trivially green; what makes it a test is a fixture
      -- that does have a type.
      assertBool (show types) (Just True `elem` types && Just False `elem` types)
  ]
  where
    counts = [ length (binderAddresses s) | (_, s) <- fixtures ]
    matched = [ length (matchesView (Budget 200) s) | (_, s) <- fixtures ]
    marks = [ map fst (redrawChain (developmentView (Budget 200) s)) | (_, s) <- fixtures ]
    types = [ Just (maybe False (const True) (focusTypeView (Budget 200) s)) | (_, s) <- fixtures ]
