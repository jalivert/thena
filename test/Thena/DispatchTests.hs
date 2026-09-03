-- | Dispatch, frames and backtracking (§7.3, §7.7).
--
-- Driven by a **synthetic ambiguous rule set** — aspect M's first concrete
-- task, and the reason it is synthetic rather than 'Thena.Rules.standardRules':
-- a test wants an alternative that fails on purpose, at a chosen instruction,
-- and no honest rule does that.
--
-- The three rules below are built from ops the engine already runs, so nothing
-- here is a mock: @works@ attacks, @messes@ attacks and then fails, and
-- @fails@ fails at once. All three match a hole.
module Thena.DispatchTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Level (Level (..))
import Thena.Core.Term (Core (..), GlobalName (..), Ident (..), fresh)
import Thena.Development.Component (Component (..))
import Thena.Development.Cursor (Cursor, enter, focus)
import qualified Thena.Development.Cursor as Cursor
import Thena.Development.Partial (Partial (..))
import Thena.Engine
  ( ChoicePoint (..)
  , Exec (..)
  , Frame (..)
  , Machine (..)
  , Outcome (..)
  , Development (..)
  , RetryError (..)
  , choicePoints
  , load
  , retryFrom
  , step
  )
import Thena.Errors (FailReason (..))
import Thena.Global.Env (emptyGlobals)
import Thena.Ops (Instr (..), Rule (..), Test (..))
import qualified Thena.Ops as Ops
import qualified Thena.Rules
import Thena.Rules (RuleBase, dispatch, matches, ruleBase)
import Thena.Standard (expectedBase)

tests :: TestTree
tests =
  testGroup
    "dispatch"
    [ peekTests
    , backtrackTests
    , retryTests
    , dispatchableTests
    ]

-- --------------------------------------------------------------------------
-- Fixtures
-- --------------------------------------------------------------------------

type0 :: Core
type0 = Universe (LZero)

-- | @? x : Type₀ . x@.
hole :: Cursor
hole = enter (Under (Claim v (Ident "goal") type0) (Trailing (Free v)))
  where v = fst (fresh 0)

rule :: String -> [Instr] -> Rule
rule n = Rule (GlobalName n) [] [FocusIsHole]

-- | Succeeds, and changes the development: the hole becomes a guess.
works :: Rule
works = rule "works" [Do Ops.Attack]

-- | Changes the development and /then/ fails, so restoring @saved@ has
-- something to undo: @solve@ needs a guess whose body is pure, and @attack@
-- leaves one whose body is a hole.
messes :: Rule
messes = rule "messes" [Do Ops.Attack, Do Ops.Solve]

-- | Fails at its first instruction: @solve@ at a hole is not a guess.
fails :: Rule
fails = rule "fails" [Do Ops.Solve]

-- | Succeeds and leaves the focus on a /hole/ again, so a second dispatch has
-- something to match. That is what makes a nested choice point buildable
-- without a rule that dispatches itself, which would not terminate.
descends :: Rule
descends = rule "descends" [Do Ops.Attack, Do Ops.Into]

-- | One anonymous base holding these rules. Phase 22 made the machine carry a
-- /list/ of named bases; these tests are about search order within one, so they
-- build exactly one and give it no interesting name or path.
bases :: [Rule] -> [RuleBase]
bases rs = [ruleBase "test" Nothing "" rs]

only :: Rule -> [RuleBase]
only r = bases [r]

machine :: [RuleBase] -> Cursor -> [Instr] -> Machine
machine base cur is =
  load is (Machine (Exec [] [] []) (Development cur) [] emptyGlobals base [] 1000)

-- | Run as the driver does, following every channel, and keep the messages.
runOut :: Machine -> ([String], Either FailReason Machine)
runOut m = case step m of
  Continue m'       -> runOut m'
  Saying msg m'     -> let (ms, r) = runOut m' in (msg : ms, r)
  Declaring _ m'    -> runOut m'
  Defining _ _ _ _ m' -> runOut m'
  Certifying _ _ m' -> runOut m'
  Asking _ m'       -> ([], Right m')
  Yielding _ m'     -> ([], Right m')
  Finished m'       -> ([], Right m')
  Stuck r _         -> ([], Left r)

ranTo :: Machine -> Machine
ranTo m = case snd (runOut m) of
  Right m' -> m'
  Left r   -> error ("the program did not run: " ++ show r)

isGuess :: Machine -> Bool
isGuess m = case focus (cursor (development m)) of
  Cursor.OnComponent (Guess {}) -> True
  _                             -> False

isHole :: Machine -> Bool
isHole m = case focus (cursor (development m)) of
  Cursor.OnComponent (Claim {}) -> True
  _                             -> False

-- --------------------------------------------------------------------------
-- The peek (§7.3)
-- --------------------------------------------------------------------------

peekTests :: TestTree
peekTests =
  testGroup
    "the peek"
    [ -- Prolog's determinism detection: one candidate costs a two-field frame
      -- and no snapshot.
      testCase "a deterministic dispatch builds a Call, not a Choice" $ do
        let m = ranTo (machine (only works) hole [Do Ops.Prove])
        choicePoints m @?= []
        isGuess m @?= True

    , testCase "and says nothing, because there was no decision" $
        fst (runOut (machine (only works) hole [Do Ops.Prove])) @?= []

    , testCase "an ambiguous dispatch builds a Choice, and says so" $ do
        let base = bases [works, fails]
            (msgs, _) = runOut (machine base hole [Do Ops.Prove])
        msgs @?= ["chose 1000: works"]

      -- §7.3, DECIDED 2026-08-20: kept on success, Prolog-style, so the user
      -- can ask for a different solution after one has been found.
    , testCase "the frame survives the program running out" $
        map pointAlts (choicePoints (ranTo (machine (bases [works, fails]) hole [Do Ops.Prove])))
          @?= [[GlobalName "fails"]]

      -- No Choice frame ever exists without a live alternative (§7.3): taking
      -- the last one demotes the frame on the spot, so "that choice is
      -- exhausted" is a state that cannot arise.
    , testCase "taking the last alternative leaves no choice point" $
        choicePoints (ranTo (machine (bases [fails, works]) hole [Do Ops.Prove]))
          @?= []

    , testCase "no rule at all is a definite failure, not a suspension" $
        case snd (runOut (machine (bases []) hole [Do Ops.Prove])) of
          Left NoRuleMatched -> pure ()
          other              -> assertFailure ("expected NoRuleMatched, got " ++ show other)
    ]

-- --------------------------------------------------------------------------
-- Unwinding (§7.3)
-- --------------------------------------------------------------------------

backtrackTests :: TestTree
backtrackTests =
  testGroup
    "backtracking"
    [ testCase "a failing alternative is followed by the next one" $ do
        let (msgs, out) = runOut (machine (bases [fails, works]) hole [Do Ops.Prove])
        msgs @?= ["chose 1000: fails", "backtracking to 1000: works"]
        case out of
          Right m -> isGuess m @?= True
          Left r  -> assertFailure ("expected success, got " ++ show r)

      -- The whole point of 'saved': a body that has already changed the
      -- development needs no cleanup, because the snapshot restores it (§7.2).
    , testCase "and what the failing one changed is undone first" $ do
        let m = ranTo (machine (bases [messes, fails, works]) hole [Do Ops.Prove])
        -- @messes@ attacked and then failed; @fails@ failed; @works@ attacked.
        -- One attack deep, not two, which is what says @saved@ was restored.
        isGuess m @?= True
        case cursor (development m) of
          cur -> case Cursor.focus cur of
            Cursor.OnComponent (Guess _ _ (Under (Claim {}) (Trailing _)) _) -> pure ()
            other -> assertFailure ("the failing branch was not undone: " ++ show other)

      -- §7.4: the counter keeps counting across a rewind. If it were rolled
      -- back, a retried branch would hand out names the abandoned one used.
    , testCase "the name counter is not rewound" $ do
        let m = ranTo (machine (bases [messes, works]) hole [Do Ops.Prove])
        (names m > 1000) @?= True

    , testCase "every alternative failing is Stuck, with the last reason" $
        case snd (runOut (machine (bases [fails, fails]) hole [Do Ops.Prove])) of
          Left NotAGuessHere -> pure ()
          other              -> assertFailure ("expected NotAGuessHere, got " ++ show other)
    ]

-- --------------------------------------------------------------------------
-- retry (§7.7)
-- --------------------------------------------------------------------------

retryTests :: TestTree
retryTests =
  testGroup
    "retry"
    [ testCase "nothing on the stack" $
        case retryFrom Nothing (machine (only works) hole []) of
          Left NoChoicePoint -> pure ()
          other              -> assertFailure ("expected NoChoicePoint, got " ++ show other)

    , testCase "an identifier that is not there" $
        case retryFrom (Just 5) (ranTo (machine (bases [works, fails]) hole [Do Ops.Prove])) of
          Left (UnknownChoice 5) -> pure ()
          other                  -> assertFailure ("expected UnknownChoice, got " ++ show other)

      -- §7.7: a solution found is not the last word. This is the deliverable
      -- in one test — a goal solved one way, then the other on request.
    , testCase "takes the next alternative and restores what the first did" $ do
        let m0 = ranTo (machine (bases [works, fails]) hole [Do Ops.Prove])
        isGuess m0 @?= True
        case retryFrom Nothing m0 of
          Left e -> assertFailure ("expected a retry, got " ++ show e)
          Right (m1, note) -> do
            note @?= "retrying 1000: fails"
            -- @fails@ fails, nothing is left, so the whole thing is Stuck —
            -- and the development is back where @works@ found it.
            case snd (runOut m1) of
              Left NotAGuessHere -> pure ()
              other -> assertFailure ("expected the alternative to fail, got " ++ show other)
            isHole m1 @?= True

    , testCase "the note says how far it popped" $ do
        let base = bases [works, fails]
            -- A Call frame between the choice point and the top of the stack.
            m0 = (ranTo (machine base hole [Do Ops.Prove]))
            m1 = m0 { exec = (exec m0) { stack = Call [] [] : stack (exec m0) } }
        case retryFrom Nothing m1 of
          Right (_, note) -> note @?= "retrying 1000: fails (1 frame(s) dropped)"
          Left e          -> assertFailure ("expected a retry, got " ++ show e)

      -- Nearest first, which is what "inner choice points are tried before
      -- outer ones" means, and what 'resumeFrom' preserves by stepping over a
      -- returned frame rather than popping it.
    , testCase "with no argument it takes the nearest" $ do
        let base = bases [descends, fails]
            m0   = ranTo (machine base hole [Do Ops.Prove, Do Ops.Prove])
        -- 1002 and not 1001: identifiers are minted from the session's name
        -- counter (decided by the user 2026-08-23), and @attack@ spent it in
        -- between. They are unique and stable, not consecutive.
        map pointId (choicePoints m0) @?= [1002, 1000]
        case retryFrom Nothing m0 of
          Right (_, note) -> note @?= "retrying 1002: fails"
          Left e          -> assertFailure ("expected a retry, got " ++ show e)

    , testCase "with an argument it takes that one, dropping what is above" $ do
        let base = bases [descends, fails]
            m0   = ranTo (machine base hole [Do Ops.Prove, Do Ops.Prove])
        case retryFrom (Just 1000) m0 of
          Right (m1, note) -> do
            note @?= "retrying 1000: fails (1 frame(s) dropped)"
            map pointId (choicePoints m1) @?= []
          Left e -> assertFailure ("expected a retry, got " ++ show e)

      -- Two dispatches in one program means the first returned before the
      -- second ran: the returned frame must still be on the stack, below the
      -- newer one, or 'retry' could not reach it at all.
    , testCase "a returned choice point is still reachable" $
        length (choicePoints (ranTo (machine (bases [descends, fails]) hole
                                       [Do Ops.Prove, Do Ops.Prove])))
          @?= 2
    ]

-- --------------------------------------------------------------------------
-- What dispatch will and will not run (§8)
-- --------------------------------------------------------------------------

dispatchableTests :: TestTree
dispatchableTests =
  testGroup
    "dispatch skips parameterised rules"
    [ testCase "matches shows try, dispatch does not" $ do
        let std = expectedBase
        names' (matches std emptyGlobals hole)
          @?= ["attack", "try-core", "abandon", "eliminate-core", "prove", "fill"
             , "unify-refine-core", "apply-core"]
               ++ replicate 15 "elaborate" ++ replicate 2 "enter-binders"
        names' (dispatch std emptyGlobals hole)
          @?= ["attack", "abandon", "prove"]

      -- And that is what the engine actually runs: @try@ would have been first
      -- past @attack@, so a dispatch that did not skip it would fail on an
      -- unbound @Ref@ rather than offering @abandon@.
    , testCase "so the alternative after attack is abandon" $
        map pointAlts (choicePoints (ranTo (machine expectedBase hole [Do Ops.Prove])))
          @?= [[GlobalName "abandon", GlobalName "prove"]]
    ]
  where
    names' it = [ n | r <- drainIt it, let GlobalName n = ruleName r ]
    drainIt it = case Thena.Rules.next it of
      Nothing        -> []
      Just (r, rest) -> r : drainIt rest
