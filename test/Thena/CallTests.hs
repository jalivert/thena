-- | Calling a rule by name (§8, phase 23).
--
-- **A call is the same search as a dispatch over a narrower candidate list**,
-- and these tests are written to show that rather than to assert it: the same
-- @Choice@ frame, the same peek, the same @retry@, the same @:choices@.
--
-- The user's framing, 2026-08-25, which the whole phase is:
--
-- > @Prove@ means \"search any rule that fits and wants to try solving the
-- > goal\" and @Call@ means \"see if any rules named like this can succeed\".
-- > Calling is not that different from searching. Calling is essentially what
-- > Prolog does.
module Thena.CallTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Level (Level (..), levelOfNat)
import Thena.Core.Term (Core (..), GlobalName (..), Ident (..), fresh)
import qualified Thena.Development.Component as Component
import qualified Thena.Development.Cursor as Cursor
import Thena.Development.Cursor (Cursor, enter, focus)
import Thena.Development.Partial (Partial (..))
import Thena.Engine
  ( ChoicePoint (..)
  , Exec (..)
  , Machine (..)
  , Outcome (..)
  , Development (..)
  , choicePoints
  , cursor
  , load
  , development
  , retryFrom
  , step
  )
import Thena.Errors (FailReason (..))
import Thena.Global.Env (emptyGlobals)
import Thena.Ops (Instr (..), Op (..), Operand (..), Rule (..), Test (..), Value (..))
import qualified Thena.Ops as Ops
import Thena.Rules (RuleBase, ruleBase)

tests :: TestTree
tests = testGroup "call by name (§8)" [finding, backtracking, arity, recursion]

-- --------------------------------------------------------------------------
-- Fixtures
-- --------------------------------------------------------------------------

type0, type1 :: Core
type0 = Universe (LZero)
type1 = Universe (levelOfNat 1)

-- **The goal is at @Type₁@** (phase 25b): the clauses below @try@ their
-- argument, that argument is @Type₀@, and @try@ now checks it — so the hole
-- must be at the universe @Type₀@ actually inhabits. It was @type0@ while the
-- side condition went unenforced.
hole :: Cursor
hole = enter (Under (Component.Claim v (Ident "goal") type1) (Trailing (Free v)))
  where v = fst (fresh 0)

bases :: [Rule] -> [RuleBase]
bases rs = [ruleBase "test" Nothing "" rs]

machine :: [RuleBase] -> [Instr] -> Machine
machine base is =
  load is (Machine (Exec [] [] []) (Development hole) [] emptyGlobals base [] 1000)

runOut :: Machine -> ([String], Either FailReason Machine)
runOut m = case step m of
  Continue m'       -> runOut m'
  Saying msg m'     -> let (ms, r) = runOut m' in (msg : ms, r)
  Declaring _ m'    -> runOut m'
  Defining _ _ _ _ m' -> runOut m'
  Certifying _ _ m' -> runOut m'
  Asking _ m'       -> ([], Right m')
  Finished m'       -> ([], Right m')
  Stuck r _         -> ([], Left r)

ranTo :: Machine -> Machine
ranTo m = case snd (runOut m) of
  Right m' -> m'
  Left r   -> error ("the program did not run: " ++ show r)

isGuess :: Machine -> Bool
isGuess m = case focus (cursor (development m)) of
  Cursor.OnComponent (Component.Guess {}) -> True
  _                             -> False

-- | Two clauses of one name. The first fails in its body — @solve@ at a hole
-- is not a guess — and the second succeeds, so a call over them is exactly the
-- state @retry@ and @:choices@ were built for.
--
-- **They do not share a parameter name**, deliberately: each clause binds the
-- arguments to its own, which is why the @Choice@ frame keeps the argument
-- /values/ rather than a ready-made environment.
badClause, goodClause :: Rule
badClause  = Rule (GlobalName "step") ["x"] [FocusIsHole] [Do Solve]
goodClause = Rule (GlobalName "step") ["y"] [FocusIsHole] [Do (Try (Ref "y"))]

-- | Same name, one argument fewer. Never a candidate for a two-argument call.
nullary :: Rule
nullary = Rule (GlobalName "step") [] [FocusIsHole] [Do Attack]

-- | Same name and arity, but a head that cannot pass at a hole.
guessOnly :: Rule
guessOnly = Rule (GlobalName "step") ["x"] [FocusIsGuess] [Do Solve]

callStep :: [Instr]
callStep = [Do (Ops.Call (GlobalName "step") [Lit (VTerm (Trailing type0))])]

-- --------------------------------------------------------------------------
-- Finding the clauses
-- --------------------------------------------------------------------------

finding :: TestTree
finding =
  testGroup
    "finding a clause"
    [ testCase "one clause runs, and its parameter is bound" $
        isGuess (ranTo (machine (bases [goodClause]) callStep)) @?= True

    , -- The peek, unchanged from phase 16 and now reaching calls: one
      -- candidate is not a decision, so no choice point and no message.
      testCase "one candidate builds no choice point" $
        let (msgs, out) = runOut (machine (bases [goodClause]) callStep)
         in do msgs @?= []
               fmap choicePoints out @?= Right []

    , testCase "two candidates do" $
        let (msgs, out) = runOut (machine (bases [badClause, goodClause]) callStep)
         in do msgs @?= ["chose 1000: step", "backtracking to 1000: step"]
               fmap (map pointAlts . choicePoints) out @?= Right []

    , -- **The head is tested**, which is what phase 15's note reversed.
      testCase "a clause whose head fails is not a candidate" $
        case snd (runOut (machine (bases [guessOnly]) callStep)) of
          Left (NoClauseMatched (GlobalName "step") 1 [1]) -> pure ()
          other -> assertFailure ("expected NoClauseMatched, got " ++ show other)

    , testCase "no rule of that name at all" $
        case snd (runOut (machine (bases []) callStep)) of
          Left (NoClauseMatched (GlobalName "step") 1 []) -> pure ()
          other -> assertFailure ("expected NoClauseMatched, got " ++ show other)
    ]

-- --------------------------------------------------------------------------
-- Backtracking
-- --------------------------------------------------------------------------

-- | **The phase's deliverable**: two clauses of one name, the second reached by
-- backtracking, and visible in @:choices@ while it happens.
backtracking :: TestTree
backtracking =
  testGroup
    "backtracking over clauses"
    [ testCase "the first clause fails and the second is tried" $ do
        let m = ranTo (machine (bases [badClause, goodClause]) callStep)
        isGuess m @?= True

    , testCase "and each clause binds the argument to its own parameter" $ do
        -- @goodClause@ names it @y@ where @badClause@ named it @x@; had the
        -- frame carried a ready-made environment the retry would have entered
        -- with @y@ unbound.
        let m = ranTo (machine (bases [badClause, goodClause]) callStep)
        isGuess m @?= True

    , -- §7.7: a choice-point frame **survives success**, so an alternative that
      -- was never needed is still there to @retry@ into. That is what makes
      -- \"like Prolog\" an argument the system can make out loud, and it now
      -- holds for a call and not only for a dispatch.
      testCase "an untried clause survives the call succeeding" $
        map (\p -> (pointId p, pointRule p, pointAlts p))
            (choicePoints (ranTo (machine (bases [goodClause, badClause]) callStep)))
          @?= [(1000, GlobalName "step", [GlobalName "step"])]

    , testCase "retry reaches the next clause by hand" $
        case retryFrom Nothing (ranTo (machine (bases [goodClause, goodClause]) callStep)) of
          Right (_, note) -> note @?= "retrying 1000: step"
          Left e          -> assertFailure ("no choice point: " ++ show e)

    , testCase "every clause failing fails the call" $
        case snd (runOut (machine (bases [badClause, badClause]) callStep)) of
          Left NotAGuessHere -> pure ()
          other          -> assertFailure ("expected the body to fail, got " ++ show other)
    ]

-- --------------------------------------------------------------------------
-- Arity
-- --------------------------------------------------------------------------

-- | **Clauses of one name need not share arity** — the user, 2026-08-25, and
-- the reason @MS2.md@'s proposed load-time check was dropped rather than added.
arity :: TestTree
arity =
  testGroup
    "arity filters, it does not fail"
    [ testCase "a clause of another arity is skipped, not an error" $
        isGuess (ranTo (machine (bases [nullary, goodClause]) callStep)) @?= True

    , testCase "and a call with no clause of its arity says which arities exist" $
        case snd (runOut (machine (bases [nullary]) callStep)) of
          Left (NoClauseMatched (GlobalName "step") 1 [0]) -> pure ()
          other -> assertFailure ("expected NoClauseMatched, got " ++ show other)

    , testCase "the arities are reported in search order" $
        case snd (runOut (machine (bases [nullary, guessOnly, nullary]) callStep)) of
          Left (NoClauseMatched _ 1 as) -> as @?= [0, 1, 0]
          other -> assertFailure ("expected NoClauseMatched, got " ++ show other)
    ]

-- --------------------------------------------------------------------------
-- Recursion
-- --------------------------------------------------------------------------

-- | **A rule may call itself**, which phases 21 and 22 could not express: the
-- callee was baked in when the rule was read, so a name had to already exist.
-- Phase 27's @fit@ is the reason this matters.
recursion :: TestTree
recursion =
  testGroup
    "a rule may call itself"
    [ testCase "the recursive call reaches the clause that stops" $
        -- @attack@ makes the focus a guess, so the recursive call reaches the
        -- /other/ clause, which @regret@s back to a hole and ends. Reaching it
        -- at all proves the call resolved a name that was still being defined
        -- when the calling clause was read — phases 21 and 22 could not.
        isGuess (ranTo (machine (bases [recurses, stops]) callDown)) @?= False

    , testCase "a call to a name defined below it also resolves" $
        isGuess (ranTo (machine (bases [callsLater, later]) callFirst)) @?= True
    ]
  where
    -- @attack@ turns the hole into a guess, so the recursive call reaches the
    -- /other/ clause and stops. A clause that recursed without changing the
    -- state would not terminate, and would not in Prolog either.
    recurses = Rule (GlobalName "down") [] [FocusIsHole]
                 [Do Attack, Do (Ops.Call (GlobalName "down") [])]
    stops    = Rule (GlobalName "down") [] [FocusIsGuess] [Do Regret]
    callDown = [Do (Ops.Call (GlobalName "down") [])]

    callsLater = Rule (GlobalName "first") [] [FocusIsHole]
                   [Do (Ops.Call (GlobalName "later") [])]
    later      = Rule (GlobalName "later") [] [FocusIsHole] [Do Attack]
    callFirst  = [Do (Ops.Call (GlobalName "first") [])]
