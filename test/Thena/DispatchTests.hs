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
import Thena.Core.Term (Core (..), Ident (..), fresh, rootName, rootScope, nameDotted)
import Thena.Development.Component (Component (..))
import Thena.Development.Cursor (Cursor, enter, focus)
import qualified Thena.Development.Cursor as Cursor
import Thena.Development.Partial (Partial (..))
import Thena.Core.Trust (TrustLevel (..))
import Thena.Engine
  ( ChoiceAlt (..)
  , ChoicePoint (..)
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
  , splicing
  )
import Thena.Errors (FailReason (..))
import Thena.Global.Env (emptyGlobals)
import Thena.Instral.Ops (Instr (..), Rule (..))
import qualified Thena.Instral.Ops as Ops
import Thena.Rules (RuleBase, dispatch, iterRules, matches, ruleBase)
import Thena.Standard (atRule, atHole, expectedBase)

tests :: TestTree
tests =
  testGroup
    "dispatch"
    [ peekTests
    , backtrackTests
    , answeredBeforeTheForkTests
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
rule n = atRule atHole (rootName n) [] []

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
bases rs = [ruleBase "test" Nothing "" [] [] rs]

only :: Rule -> [RuleBase]
only r = bases [r]

machine :: [RuleBase] -> Cursor -> [Instr] -> Machine
machine base cur is =
  load is (Machine (Exec [] [] [] []) (Development cur) [] emptyGlobals base [] [] [] [] rootScope 1000 [] 0
                   NoUndischargeableTrust)

-- | Run as the driver does, following every channel, and keep the messages.
runOut :: Machine -> ([String], Either FailReason Machine)
runOut m = case step m of
  Continue m'       -> runOut m'
  Saying msg m'     -> let (ms, r) = runOut m' in (msg : ms, r)
  Declaring _ _ m'    -> runOut m'
  Defining _ _ _ _ m' -> runOut m'
  Primitively _ _ m' -> runOut m'
  DeclaringGrammar _ m' -> runOut m'
  -- A block the driver would have typed; the harness splices and runs it.
  Playing is m' -> runOut (splicing is m')
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
        let m = ranTo (machine (only works) hole [Do Ops.Dispatch])
        choicePoints m @?= []
        isGuess m @?= True

    , testCase "and says nothing, because there was no decision" $
        fst (runOut (machine (only works) hole [Do Ops.Dispatch])) @?= []

    , testCase "an ambiguous dispatch builds a Choice, and says so" $ do
        let base = bases [works, fails]
            (msgs, _) = runOut (machine base hole [Do Ops.Dispatch])
        msgs @?= ["chose 1000: works"]

      -- §7.3, DECIDED 2026-08-20: kept on success, Prolog-style, so the user
      -- can ask for a different solution after one has been found.
    , testCase "the frame survives the program running out" $
        map (map altRule . pointAlts)
            (choicePoints (ranTo (machine (bases [works, fails]) hole [Do Ops.Dispatch])))
          @?= [[rootName "fails"]]

      -- No Choice frame ever exists without a live alternative (§7.3): taking
      -- the last one demotes the frame on the spot, so "that choice is
      -- exhausted" is a state that cannot arise.
    , testCase "taking the last alternative leaves no choice point" $
        choicePoints (ranTo (machine (bases [fails, works]) hole [Do Ops.Dispatch]))
          @?= []

    , testCase "no rule at all is a definite failure, not a suspension" $
        case snd (runOut (machine (bases []) hole [Do Ops.Dispatch])) of
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
        let (msgs, out) = runOut (machine (bases [fails, works]) hole [Do Ops.Dispatch])
        msgs @?= ["chose 1000: fails", "backtracking to 1000: works"]
        case out of
          Right m -> isGuess m @?= True
          Left r  -> assertFailure ("expected success, got " ++ show r)

      -- The whole point of 'saved': a body that has already changed the
      -- development needs no cleanup, because the snapshot restores it (§7.2).
    , testCase "and what the failing one changed is undone first" $ do
        let m = ranTo (machine (bases [messes, fails, works]) hole [Do Ops.Dispatch])
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
        let m = ranTo (machine (bases [messes, works]) hole [Do Ops.Dispatch])
        (names m > 1000) @?= True

    , testCase "every alternative failing is Stuck, with the last reason" $
        case snd (runOut (machine (bases [fails, fails]) hole [Do Ops.Dispatch])) of
          Left NotAGuessHere -> pure ()
          other              -> assertFailure ("expected NotAGuessHere, got " ++ show other)
    ]

-- --------------------------------------------------------------------------
-- An answer given before the fork survives the backtracking (MS12)
-- --------------------------------------------------------------------------

-- | Hands back a word, so a caller has something to keep.
gives :: Rule
gives = rule "gives" [Do (Ops.Return (Ops.Lit (Ops.VText "hello")))]

-- | Two clauses under one name, the first of which fails: this is what builds
-- a choice point in the middle of a body rather than at the top of it.
forkedFails, forkedWorks :: Rule
forkedFails = rule "forked" [Do Ops.Solve]
forkedWorks = rule "forked" [Do (Ops.Say (Ops.Lit (Ops.VText "second clause")))]

-- | A body that gets a value, keeps it, /then/ forks, and uses the value at
-- its last instruction.
keepsThenForks :: Rule
keepsThenForks =
  rule "keeps-then-forks"
    [ Bind (Ops.PVar "x") Nothing (Ops.Call "gives" [])
    , Do (Ops.Call "forked" [])
    , Do (Ops.Say (Ops.Ref "x"))
    ]

-- | The same two calls the other way round, which always worked.
forksThenKeeps :: Rule
forksThenKeeps =
  rule "forks-then-keeps"
    [ Do (Ops.Call "forked" [])
    , Bind (Ops.PVar "x") Nothing (Ops.Call "gives" [])
    , Do (Ops.Say (Ops.Ref "x"))
    ]

-- | A call that keeps nothing, and then a fork — the same ordering as
-- 'keepsThenForks' with the binding taken out.
--
-- It is the second half of the defect and it shows up as duplicated work
-- rather than as a failure: a frame with no destination cannot report
-- 'NothingReturned', so reviving it simply ran the rest of the body again.
saysNothing :: Rule
saysNothing = rule "says-nothing" [Do (Ops.Say (Ops.Lit (Ops.VText "first call")))]

quietThenForks :: Rule
quietThenForks =
  rule "quiet-then-forks"
    [ Do (Ops.Call "says-nothing" [])
    , Do (Ops.Call "forked" [])
    ]

-- | **A call that has already returned is not un-returned by a later
-- backtracking** (MS12).
--
-- A 'Choice' frame restores the stack it was built on ('savedBelow') rather
-- than clearing @returned@ on everything below it. The difference is exactly
-- this body: @gives@ returns, and then @forked@ forks. Clearing the flags
-- revived @gives@\'s frame, so after the second clause of @forked@ ran, the
-- @Bind@ that had already been satisfied was entered a second time and the
-- body — which had printed its answer and reached its last instruction — failed
-- with 'NothingReturned'. Every visible sign said it had worked.
--
-- The same omission the other way is what MS4 phase 57 fixed, so both
-- directions are pinned here: a frame that returned /inside/ the branch being
-- abandoned must still come back to life, which is the nested-choice test at
-- the end of 'retryTests'.
answeredBeforeTheForkTests :: TestTree
answeredBeforeTheForkTests =
  testGroup
    "an answer given before a fork"
    [ testCase "survives the fork backtracking, and the body finishes" $ do
        let base = bases [gives, forkedFails, forkedWorks, keepsThenForks]
            (msgs, out) = runOut (machine base hole [Do (Ops.Call "keeps-then-forks" [])])
        case out of
          Left r  -> assertFailure ("the body did not finish: " ++ show r)
          Right _ -> pure ()
        -- The last message is the kept value, printed once.
        filter (== "hello") msgs @?= ["hello"]

    , testCase "and the alternative really did run" $ do
        let base = bases [gives, forkedFails, forkedWorks, keepsThenForks]
            (msgs, _) = runOut (machine base hole [Do (Ops.Call "keeps-then-forks" [])])
        ("second clause" `elem` msgs) @?= True

      -- The control, and it is the whole argument that this is about ordering:
      -- the same two calls with the fork first were never affected.
    , testCase "the other order was always fine, and still is" $ do
        let base = bases [gives, forkedFails, forkedWorks, forksThenKeeps]
            (msgs, out) = runOut (machine base hole [Do (Ops.Call "forks-then-keeps" [])])
        case out of
          Left r  -> assertFailure ("the body did not finish: " ++ show r)
          Right _ -> pure ()
        filter (== "hello") msgs @?= ["hello"]

      -- A body's instruction is run once. Reviving a frame that had returned
      -- before the fork re-ran everything the body had left after that call,
      -- and with no binding to fail on that is silent: the fork was taken
      -- again, and again, and the line did not come back at all.
      --
      -- **Bounded on purpose.** 'runOut' builds its messages lazily, so a
      -- prefix of them is answerable even by a machine that never finishes —
      -- which is what this one did. Forcing the outcome here would hang the
      -- suite instead of failing it.
    , testCase "nothing after the returning call is run twice" $ do
        let base = bases [saysNothing, forkedFails, forkedWorks, quietThenForks]
            msgs = fst (runOut (machine base hole [Do (Ops.Call "quiet-then-forks" [])]))
        take 8 msgs
          @?= [ "first call"
              , "chose 1000: forked"
              , "backtracking to 1000: forked"
              , "second clause"
              ]
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
        case retryFrom (Just 5) (ranTo (machine (bases [works, fails]) hole [Do Ops.Dispatch])) of
          Left (UnknownChoice 5) -> pure ()
          other                  -> assertFailure ("expected UnknownChoice, got " ++ show other)

      -- §7.7: a solution found is not the last word. This is the deliverable
      -- in one test — a goal solved one way, then the other on request.
    , testCase "takes the next alternative and restores what the first did" $ do
        let m0 = ranTo (machine (bases [works, fails]) hole [Do Ops.Dispatch])
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
            m0 = (ranTo (machine base hole [Do Ops.Dispatch]))
            m1 = m0 { exec = (exec m0) { stack = Call [] [] Nothing [] False : stack (exec m0) } }
        case retryFrom Nothing m1 of
          Right (_, note) -> note @?= "retrying 1000: fails (1 frame(s) dropped)"
          Left e          -> assertFailure ("expected a retry, got " ++ show e)

      -- Nearest first, which is what "inner choice points are tried before
      -- outer ones" means, and what 'resumeFrom' preserves by stepping over a
      -- returned frame rather than popping it.
    , testCase "with no argument it takes the nearest" $ do
        let base = bases [descends, fails]
            m0   = ranTo (machine base hole [Do Ops.Dispatch, Do Ops.Dispatch])
        -- 1002 and not 1001: identifiers are minted from the session's name
        -- counter (decided by the user 2026-08-23), and @attack@ spent it in
        -- between. They are unique and stable, not consecutive.
        map pointId (choicePoints m0) @?= [1002, 1000]
        case retryFrom Nothing m0 of
          Right (_, note) -> note @?= "retrying 1002: fails"
          Left e          -> assertFailure ("expected a retry, got " ++ show e)

    , testCase "with an argument it takes that one, dropping what is above" $ do
        let base = bases [descends, fails]
            m0   = ranTo (machine base hole [Do Ops.Dispatch, Do Ops.Dispatch])
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
                                       [Do Ops.Dispatch, Do Ops.Dispatch])))
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
        names' (matches std emptyGlobals 0 hole)
          @?= [ -- **@try-in-scope@ is nullary and dispatch DOES run it** (MS12):
               -- it finds its own term, so it is the one candidate in this list
               -- that can close the goal. **It is ABOVE @attack@** (his
               -- instruction of 2026-11-23), so it is what a bare @prove@ tries
               -- first; @attack@ never fails, and below it this rule was never
               -- reached at all. @fit-in-scope@ is the same walk for a
               -- hypothesis that has to be applied to something.
               "try-in-scope", "fit-in-scope"
             , "attack", "try-core", "abandon"
               -- **@rename@ is offered here too** (MS12 phase 330): its focus
               -- is @at _@, and dispatch runs it no more than it runs
               -- @try-core@ — it takes a parameter.
             , "rename", "eliminate-core"
             , "eliminate-generalising-core", "step", "step", "step", "fill"
             , "unify-refine-core", "apply-core"
               -- **@fit-core@'s two clauses both pass, and dispatch runs
               -- neither** (MS2 phase 27) — it takes a parameter, exactly like
               -- @try-core@ above, which is what this test is about.
             , "fit-core", "fit-core"
             , "claim", "assume", "quantify"]
               ++ replicate 7 "elaborate"
               ++ [ "no-nesting", "ihs-for", "ihs-for"
                  , "reverse-onto", "reverse-onto", "any-of", "any-of"
               , "apply-all", "apply-all"
                  , "instantiate-with"
                  , "name-or-stem", "name-or-stem" ]
               ++ replicate 6 "intro-arm-binders"
               ++ ["dotted-position-is-forced"]
               ++ replicate 3 "intro-arm-binders"
               ++ [ "bind-friendlies", "bind-friendlies", "bind-solved", "bind-solved"
                  , "same-length", "same-length"
                  , "arm-for", "arm-for", "pick", "pick", "arm-needs-body"
                  , "arm-needs-body"
                  , "elaborate-arm", "case-needs-an-arm", "case-needs-an-arm"
                  , "vanished-case-takes-no-body", "vanished-case-takes-no-body"
                  , "case-must-vanish", "case-must-vanish"
                  , "one-case", "one-case", "one-case"
                  , "arm-must-be-for-this-datatype"
                  , "arms-are-for-this-datatype", "arms-are-for-this-datatype"
                  , "one-arm-per-constructor"
                  , "arm-not-repeated", "arm-not-repeated"
                  , "arms-are-distinct", "arms-are-distinct"
                  , "split-cases", "split-cases", "split-over"
                  , "split-claim", "split-claim", "split-elaborate"
                  ]
               -- **The interactive spelling** (MS9 phase 231). @induction-core@
               -- and @case-core@ take a parameter, so dispatch runs neither —
               -- which is this test's own subject, one tactic on.
               ++ replicate 4 "argument-patterns"
               ++ [ "argument-pattern"
                  , "open-case", "open-case"
                  , "split-holes", "split-holes", "split-holes-over"
                  , "with-hypotheses", "with-hypotheses"
                  , "without-hypotheses", "without-hypotheses"
                  , "induction-core", "case-core"
                  ]
               ++ replicate 15 "elaborate"
               ++ ["run-block"]
               -- @intro-binders@ is written @at ? _ : _@ as of MS12 phase 357.
               ++ replicate 4 "intro-binders"
               ++ replicate 2 "spine-arguments"
        names' (dispatch std emptyGlobals 0 hole)
          @?= ["try-in-scope", "fit-in-scope", "attack", "abandon", "step"]

      -- And that is what the engine actually runs: @try-core@ would have been
      -- in the list, so a dispatch that did not skip it would fail on an
      -- unbound @Ref@ rather than offering @abandon@.
      --
      -- **This hole has nothing in scope, so the two closing rules above
      -- @attack@ are taken and fail before it** (MS12 phase 340): @any-of []@
      -- matches no clause and @apply-next@ has no candidate to apply. Neither
      -- leaves a frame behind — 'demote' unbuilds a 'Choice' as its last
      -- alternative is taken — so what stands is @attack@'s one choice point
      -- with @abandon@ and @prove@ left, which is what this assertion reads.
    , testCase "so the alternative after attack is abandon" $
        map (map altRule . pointAlts)
            (choicePoints (ranTo (machine expectedBase hole [Do Ops.Dispatch])))
          @?= [[rootName "abandon", rootName "step"]]
    ]
  where
    names' it = [ nameDotted (ruleName r) | r <- drainIt it ]
    drainIt = iterRules
