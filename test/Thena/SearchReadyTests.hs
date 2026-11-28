-- | A rule that reads its own goal — @by-induction@ in the shipped base
-- (MS12).
--
-- @examples\/SearchReadyInduction.thena.script@ is the file. It proves
-- @natRefl@ by a case split that no command and no rule argument names: the
-- rule is nullary, its head matches that the goal is a universal, and the
-- subject of the split is the binder that head bound.
--
-- __The end-to-end judge is @qed@__, which runs 'Thena.Kernel.certify' over
-- the finished development, so a goal the rule shaped wrongly could not be
-- proved past.
--
-- __What is pinned here that the script alone does not say.__ That the head
-- /discriminates/ — the rule is offered at a universal goal and absent at one
-- that is not — because a clause that matched everywhere would pass the script
-- just as well while telling the search nothing. And that the subject really
-- is the parameter the head bound: the split refines @n@ to each constructor,
-- which a split over anything else would not do.
module Thena.SearchReadyTests (tests) where

import Data.List (isInfixOf)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

import Thena.Core.Term (rootName)
import Thena.Driver (Leniency (..), Session, command, machineOf)
import Thena.Engine (Machine (..))
import Thena.Files (loadFile, startingSession)
import Thena.Global.Env (Definition (..), lookupDefinition)
import Thena.Render (rendering, renderCore, renderResponse)

-- | Relative to the package root, which is where the suite runs.
target :: FilePath
target = "examples/SearchReadyInduction.thena.script"

-- | One command, and what the session said back.
step :: Session -> String -> (Session, [String])
step s cmd = let (s', r) = command s cmd in (s', renderResponse s' r)

-- | A run of commands, keeping only the last one's output.
run :: Session -> [String] -> (Session, [String])
run s = foldl (\(s', _) cmd -> step s' cmd) (s, [])

-- | A session with @Nat@ declared, and nothing else done.
withNat :: Session -> (Session, [String])
withNat s =
  run s
    [ "data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
    , "open Nat"
    ]

-- | The warning every split through a re-binding arm prints: the arm binds the
-- author's word for the scrutinee again, which costs the outer binder its
-- word. Deliberate, and part of what a split says.
shadowedByTheArm :: String
shadowedByTheArm =
  "warning: n shadows an outer binder of the same word, which no word reaches \
  \now \8212 walk up to that binder and rename it to give it one"

tests :: TestTree
tests =
  testGroup
    "a rule that reads its own goal"
    [ testCase "the script runs to the end" $ do
        (s, _) <- startingSession
        (_, _, stopped) <- loadFile Strict s target
        assertBool (unlines (map show stopped)) (null stopped)

      -- __@qed@ is what makes this an acceptance test.__ The theorem is
      -- admitted at the type it was stated at, so the eliminator the rule
      -- built, its motive and its two methods all type-check in the kernel.
    , testCase "and the theorem it proves is admitted at its written type" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadFile Strict s target
        case lookupDefinition (rootName "natRefl") (globals (machineOf s')) of
          Nothing -> assertFailure "natRefl was not admitted"
          Just d ->
            renderCore (rendering [] (names (machineOf s'))) [] (definitionType d)
              @?= "\8704 (n : Nat.Nat) -> Eq.Eq {0} Nat.Nat n n"

      -- __THE HEAD DISCRIMINATES, which is the landing in one assertion.__
      -- The rule is a candidate at a universal goal and not at one that is
      -- not, and the question is asked of a /core/ term — nothing in the
      -- vocabulary could have asked it before a pattern could stand there.
    , testCase "it is offered at a universal goal" $ do
        (s0, _) <- startingSession
        let (s1, _) = withNat s0
            (s2, _) = run s1 [":theorem p : \8704 (n : Nat) -> Nat", "attack"]
            (_, out) = step s2 ":matches"
        assertBool (unlines out) (any ("by-induction" `isInfixOf`) out)

    , testCase "and not at a goal that is not one" $ do
        (s0, _) <- startingSession
        let (s1, _) = withNat s0
            (s2, _) = run s1 [":theorem q : Nat", "attack"]
            (_, out) = step s2 ":matches"
        assertBool (unlines out) (not (any ("by-induction" `isInfixOf`) out))

      -- __And it is offered to a bare @step@__, which is what /search-ready/
      -- means: nullary, so the search can reach it with nothing written down.
      -- It sits below @intro@, so @step@ takes the cheaper move and the case
      -- split is the next alternative at that very choice point.
    , testCase "a bare step leaves it as the next alternative" $ do
        (s0, _) <- startingSession
        let (s1, _) = withNat s0
            (s2, _) = run s1 [":theorem p : \8704 (n : Nat) -> Nat", "attack", "step"]
            (_, out) = step s2 "retry"
        assertBool (unlines out)
          (any ("retrying" `isInfixOf`) out && any ("by-induction" `isInfixOf`) out)

      -- __One hole per constructor, from a call with no argument.__ The same
      -- shape @induction-core@ gives an author who names the scrutinee — which
      -- is the comparison @examples\/SplitAtAHole.thena.script@ is there for.
    , testCase "and calling it splits with no argument given" $ do
        (s0, _) <- startingSession
        let (s1, _) = withNat s0
            (s2, _) = run s1 [":theorem p : \8704 (n : Nat) -> Nat", "attack"]
            (_, out) = step s2 "by-induction"
        out
          @?= [ "subgoals: zeroMethod, succMethod"
              , "subgoals: zeroCase"
              , "subgoals: succCase"
              , shadowedByTheArm
              ]

      -- __THE SUBJECT IS THE PARAMETER THE HEAD BOUND__, and this is what says
      -- so: each case refines @n@ to that constructor, so @zero@ stands where
      -- the parameter was. A split over anything else would leave @n@ alone.
    , testCase "and each case refines the parameter the head bound" $ do
        (s0, _) <- startingSession
        let (s1, _) = withNat s0
            (s2, _) =
              run s1
                [ ":theorem p : \8704 (n : Nat) -> Eq {0} Nat n n"
                , "attack", "by-induction", "goto-named \"zeroCase1\""
                ]
            (_, out) = step s2 ":where"
        -- The context says it outright: the parameter is a /definition/ in
        -- this case, standing at the constructor the case is for.
        assertBool (unlines out) (any ("n = zero : Nat" `isInfixOf`) out)
        assertBool (unlines out) (any ("Eq {0} Nat zero zero" `isInfixOf`) out)

      -- __AND IT CATCHES A GOAL THAT ONLY UNFOLDS TO A UNIVERSAL.__ A pattern
      -- is tried as written and then reduced and tried again — his rule of
      -- 2026-09-20, one rule for every pattern — so a goal written as a
      -- definition is matched and the split runs. @spec\/machine.md@ §8 said
      -- the opposite until MS12 phase 360 measured it; this is the measurement.
    , testCase "and a goal that only unfolds to a universal still splits" $ do
        (s0, _) <- startingSession
        let (s1, _) = withNat s0
            (s2, _) =
              run s1
                [ "declare P : Type\8320 ; P = \8704 (n : Nat) -> Nat"
                , ":theorem viaDefinition : P"
                , "attack"
                ]
            (_, out) = step s2 "by-induction"
        out
          @?= [ "subgoals: zeroMethod, succMethod"
              , "subgoals: zeroCase"
              , "subgoals: succCase"
              , shadowedByTheArm
              ]

      -- __AND THE OP REFUSES A WORD THAT BINDS NOTHING__, which is the half of
      -- @ident-term@ the base does not reach: a written literal stands at an
      -- identifier's type and carries no token, so it names no variable. The
      -- alternative would be to mint one — which is what @intro@ reads the
      -- same absence as — and the term would then mention a binder that is not
      -- there.
    , testCase "and the op refuses a word that was never bound" $ do
        (s0, _) <- startingSession
        let (s1, _) = withNat s0
            (s2, _) = run s1 [":theorem p : \8704 (n : Nat) -> Nat", "attack"]
            (_, out) = step s2 "do { v = ident-term \"a\" ; say \"reached\" }"
        out
          @?= [ "stuck: a is a word and nothing more, so there is no variable \
                \it means\n  a term can be made only from an identifier a \
                \binder was opened at \8212 a binder position in a pattern, or \
                \the one `intro` adopted"
              ]
    ]
