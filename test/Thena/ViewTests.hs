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
-- 'Thena.Driver.oneLine': @:show@ for the chain, @:matches@ for the match list,
-- @:choices@ for the live choice points. None goes through any part of this
-- module, and all see the same session.
--
-- **'Thena.View.binderAddresses' is the invariant the phase establishes**, so it
-- is asserted rather than assumed: every pair must be a variable and the address
-- of the link that binds it, checked by following the address with
-- 'Thena.View.Address.follow' — the reader the driver itself moves by, not a
-- second walk of the chain.
module Thena.ViewTests (tests) where

import Data.List (intercalate)

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
import Thena.Engine (goalEnv)
import Thena.Render
  ( rendering
  ,renderCursor)
import Thena.Repl (Turn (..), turn)
import Thena.Standard (expectedBase)
import Thena.View
  ( Budget (..)
  , binderAddresses
  , developmentView
  , focusTypeView
  , goalsView
  , GoalKind (..)
  , GoalView (..)
  , machineOf
  , choicesView
  , matchesView
  , sessionCursor
  , sessionGrammars
  , sessionNames
  )
import Thena.View.Address (follow)
import Thena.View.Choices (AltView (..), ChoiceView (..))
import Thena.Syntax.Lexer (Pos (..))
import Thena.View.Redraw (markedChainText, redraw, redrawChain)
import Thena.View.Matches (MatchView (..))
import Thena.View.TypeTests (redrawSignature)

tests :: TestTree
tests =
  testGroup
    "Thena.View"
    [ testGroup "the chain, against :show" (map chainCase fixtures)
    , testGroup "every binder address lands on its own link" (map binderCase fixtures)
    , testGroup "the focus's type, against :where" (map typeCase fixtures)
    , testGroup "the match list, against :matches" (map matchCase fixtures)
    , testGroup "the choice points, against :choices" (map choiceCase choiceFixtures)
    , testGroup "the goals, against what a line is given" (map goalCase fixtures)
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
-- The goals
-- ---------------------------------------------------------------------------

-- | __The one way the goals pane can lie.__ 'goalsView' hands a frontend a word
-- per goal for the reader to type; 'Thena.Engine.goalEnv' is what a typed line is
-- actually given. If they disagree, a pane draws a move that does not run — or,
-- worse, one that runs and goes somewhere else.
--
-- Both are derived from the same walk ('Thena.Development.Cursor.goalsIn' and the
-- chain the development view prints), which is why this is an equality and not a
-- subset: the order has to match too, since the pane's first row is the
-- development's first goal.
goalCase :: (String, Session) -> TestTree
goalCase (name, s) =
  testCase name $
    map goalViewVar (goalsView (Budget 200) s) @?= map fst (goalEnv (machineOf s))

-- ---------------------------------------------------------------------------
-- The chain
-- ---------------------------------------------------------------------------

-- | 'developmentView' takes every one of 'displayDevelopment's arguments off the
-- session; @:show@ hands 'Thena.Render.renderCursor' its own. If the two draw the
-- same chain with the same link marked, the seam read the session the way the
-- terminal does.
chainCase :: (String, Session) -> TestTree
chainCase (name, s) =
  testCase name $
    markedChainText (developmentView (Budget 200) s)
      @?= renderCursor (rendering (sessionGrammars s) (sessionNames s)) (sessionCursor s)

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
-- ('Thena.Render.walkSteps'\/@walkTerm@); the seam builds them by folding
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

-- | 'matchesView' against @:matches@, which is 'Thena.Rules.matchingRules' plus
-- 'Thena.Render.renderMatches' and no part of this module — including the
-- order, which is dispatch order by each name's first matching clause.
--
-- **The type is part of the line now** (2026-11-19), so this redraws it the way
-- @Thena.View.TypeTests@ does: a view that dropped the signature, or carried a
-- different one from the one the prompt prints, would pass a name-only check.
matchCase :: (String, Session) -> TestTree
matchCase (name, s) = testCase name (drawn @?= turnOutput (turn s ":matches"))
  where
    drawn = case map line (matchesView (Budget 200) s) of
      [] -> ["no rule applies here"]
      ls -> ls
    line mv =
      unwords (matchViewName mv : map corners (matchViewParams mv))
        ++ maybe "" ((" : " ++) . redrawSignature) (matchViewType mv)
    corners p = "‹" ++ p ++ "›"

-- ---------------------------------------------------------------------------
-- The choice points
-- ---------------------------------------------------------------------------

-- | __A live choice point needs a machine standing still inside a rule__, and
-- the fixtures above never have one: a command at the prompt runs to
-- completion, and choice points are discarded at a proof boundary (his ruling
-- of 2026-09-03). So this list is its own, and @:step@ is what holds the
-- machine open.
--
-- @prove@ at a bare hole dispatches to @intro@ with @solve@, @regret@ and
-- @prove@ behind it — four clauses whose heads all hold — so two instructions
-- of fuel is enough to have built the 'Thena.Engine.Choice' frame and not
-- enough to have left it.
choiceFixtures :: [(String, Session)]
choiceFixtures =
  [ ("a settled prompt, where there is nothing to retry", after [])
  , ("paused inside prove, one choice point live", after paused)
  ]
  where
    paused =
      [":theorem t : \8704 (A : Type\8320) -> A -> A", "attack", ":step 2", "prove"]

-- | 'choicesView' against @:choices@, which is 'Thena.Engine.choicePoints' plus
-- 'Thena.Render.renderChoices' and no part of this module.
--
-- **The spelling is the half that can go wrong silently.** Both sides reach
-- 'Thena.Core.Term.shortestEnding', but only through a scope each side built
-- for itself — the view's from 'Thena.View.spellingOf', the terminal's from its
-- own 'Thena.Render.Rendering' — so a seam that read the scope off the wrong
-- machine would print a longer name here and nowhere else.
choiceCase :: (String, Session) -> TestTree
choiceCase (name, s) = testCase name (drawn @?= turnOutput (turn s ":choices"))
  where
    drawn = case map line (choicesView s) of
      [] -> ["no choice points"]
      ls -> ls
    line cv =
      show (choiceViewId cv) <> "  " <> alt (choiceViewRunning cv)
        <> "   untried: " <> intercalate ", " (map alt (choiceViewUntried cv))

    -- **The line and the paths are part of the row since MS12 phase 342**
    -- (@~mhz7j@), so they are part of what this crossing holds to one
    -- spelling: a pane that drew the name alone would now say less than the
    -- prompt does.
    alt a = case (altViewPath a, altViewAt a) of
      (Just f, Just p) ->
        altViewName a <> " (" <> reverse (takeWhile (/= '/') (reverse f))
                      <> ":" <> show (posLine p) <> ")"
      _ -> altViewName a

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
  , testCase "a choice fixture really has a live choice point" $
      -- Both sides of 'choiceCase' say "no choice points" at a settled prompt,
      -- so that case is trivially green; what makes it a test is the paused
      -- one, and that it has untried alternatives to list.
      assertBool (show chosen) (chosen == [0, 1] && untried >= 3)
  , testCase "some fixture has both a guess and a hole to list" $
      -- 'goalCase' is an equality between two empty lists before a theorem is
      -- started, so what makes it a test is a fixture that has goals of both
      -- kinds — which is also the half of his 2026-11-19 request that the
      -- development view could not answer, a guess being a goal.
      assertBool (show kinds) ([AGuess, AHole] `elem` kinds)
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
    kinds = [ map goalViewKind (goalsView (Budget 200) s) | (_, s) <- fixtures ]
    chosen = [ length (choicesView s) | (_, s) <- choiceFixtures ]
    untried =
      maximum (0 : [ length (choiceViewUntried c) | (_, s) <- choiceFixtures, c <- choicesView s ])
