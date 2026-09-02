{-# LANGUAGE OverloadedLists #-}

-- | Elaboration (MS4 phase 41), and @Call@ (§8, phase 17b).
--
-- **The partition is gone and so are its tests.** Until this phase a hint split
-- the rule base in two, and this module's first group checked that
-- @:matches@ and @:matches ‹hint›@ were two questions with two answers. There
-- is no hint now: elaboration is a rule called by name, so every rule whose
-- head passes is a candidate and there is one question.
--
-- What is checked here instead:
--
--   * **the elaborator's leaves** — a name, a universe, and the two
--     placeholders — end to end, through the machine;
--   * **that a node it has no case for FAILS**, which is phase 41b's list;
--   * **@Call@** — arity, what binds in the callee, and what survives the
--     return.
module Thena.ElaborateTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Level (Level (..))
import Thena.Core.Term (Core (..), GlobalName (..), Ident (..), Var, fresh)
import Thena.Development.Component (Component (..))
import Thena.Development.Cursor (Cursor, enter, focus)
import qualified Thena.Development.Cursor as Cursor
import Thena.Development.Partial (Partial (..))
import Thena.Engine
  ( Exec (..)
  , Machine (..)
  , Outcome (..)
  , Development (..)
  , load
  , step
  )
import Thena.Errors (FailReason (..), ResolveError (..), SyntaxError (..))
import Thena.Global.Env (emptyGlobals)
import Thena.Ops
  ( Instr (..)
  , Operand (..)
  , Rule (..)
  , Value (..)
  )
import qualified Thena.Ops as Ops
import Thena.Rules
  ( RuleBase
  , RuleIter
  , matches
  , next
  )
import Thena.Standard (expectedBase)
import Thena.Surface.Concrete (Plicity (..), Surface (..), SurfaceArg (..), SurfaceBinder (..))

tests :: TestTree
tests =
  testGroup
    "elaboration"
    [ leafTests
    , unsupportedTests
    , baseTests
    ]

-- --------------------------------------------------------------------------
-- Fixtures
-- --------------------------------------------------------------------------

type0 :: Core
type0 = Universe LZero

goalVar, hypVar :: Var
goalVar = fst (fresh 0)
hypVar  = fst (fresh 1)

-- | @λ a : Type₀ . ? goal : Type₀ . goal@, focused on the hole — so there is
-- something in scope at the focus for a surface name to denote (§4.5).
hole :: Cursor
hole = case Cursor.along top of
  Right cur -> cur
  Left e    -> error ("fixture will not move: " ++ show e)
  where
    top =
      enter
        ( Under (Assume hypVar (Ident "a") type0)
            (Under (Claim goalVar (Ident "goal") type0) (Trailing (Free goalVar)))
        )

machine :: [RuleBase] -> [Instr] -> Machine
machine base is =
  load is (Machine (Exec [] [] []) (Development hole) emptyGlobals base 1000)

runOut :: Machine -> ([String], Either FailReason Machine)
runOut m = case step m of
  Continue m'       -> runOut m'
  Saying msg m'     -> let (ms, r) = runOut m' in (msg : ms, r)
  Declaring _ m'    -> runOut m'
  Certifying _ _ m' -> runOut m'
  Asking _ m'       -> ([], Right m')
  Finished m'       -> ([], Right m')
  Stuck r _         -> ([], Left r)

-- | Elaborate one surface term into the fixture's hole.
elaborating :: Surface -> Either FailReason Machine
elaborating s = snd (runOut (machine [] [Do (Ops.Elaborate (Lit (VSurface s)))]))

isGuess :: Machine -> Bool
isGuess m = case focus (cursor (development m)) of
  Cursor.OnComponent (Guess {}) -> True
  _                             -> False

isHole :: Machine -> Bool
isHole m = case focus (cursor (development m)) of
  Cursor.OnComponent (Claim {}) -> True
  _                             -> False

drain :: RuleIter -> [Rule]
drain it = case next it of
  Nothing        -> []
  Just (r, rest) -> r : drain rest

-- --------------------------------------------------------------------------
-- The leaves
-- --------------------------------------------------------------------------

leafTests :: TestTree
leafTests =
  testGroup
    "the leaves elaborate"
    [ -- @E⟦x⟧ = FILL x; SOLVE@ — Brady's variable case. What @elab-var@ did
      -- with a hint, one op does with a surface term.
      testCase "a name in scope is attached and committed" $
        case elaborating (SurfaceName "a") of
          Left r  -> assertFailure ("did not elaborate: " ++ show r)
          Right m -> isGuess m @?= False   -- solved, so it is a definition now

    , testCase "a name that is not in scope says so" $
        case elaborating (SurfaceName "nope") of
          Left (CannotRead (ResolveFailed (NotInScope x))) -> x @?= "nope"
          other -> assertFailure ("expected a scope error: " ++ show other)

      -- **The emitted program really is @try; solve@**, and this is how that is
      -- visible: the fixture's goal is @Type₀@, so attaching @Type₀@ to it is
      -- ill-typed, and the failure that comes back is @try@'s own side
      -- condition (phase 25b) rather than anything the elaborator checked.
    , testCase "a universe goes through try, and try still checks it" $
        case elaborating (SurfaceUniverse 0) of
          Left (GuessIllTyped _) -> pure ()
          other -> assertFailure ("expected try's check to fire: " ++ show other)

      -- **The placeholder elaborates by not elaborating** — his words. The
      -- hole is still a hole afterwards, which is the whole of the behaviour
      -- and the only way to see it.
    , testCase "_ leaves the hole exactly as it was" $
        case elaborating SurfacePlaceholder of
          Left r  -> assertFailure ("did not elaborate: " ++ show r)
          Right m -> isHole m @?= True

    , testCase "and so does a named placeholder, for now" $
        case elaborating (SurfaceHole "goal") of
          Left r  -> assertFailure ("did not elaborate: " ++ show r)
          Right m -> isHole m @?= True
    ]

-- --------------------------------------------------------------------------
-- What phase 41 does not do
-- --------------------------------------------------------------------------

-- | **A node with no case fails, and that is deliberate.**
--
-- Phase 41 compiles the leaves; these are phase 41b's list, and each needs
-- something the op vocabulary does not have. An elaborator that quietly did
-- nothing here would leave a hole that looked elaborated — which is the one
-- outcome worse than refusing.
unsupportedTests :: TestTree
unsupportedTests =
  testGroup
    "a node with no case is refused, not ignored"
    [ refused "an application"
        (SurfaceApp (SurfaceName "a") [SurfaceArg Explicit (SurfaceName "a")])
    , refused "a lambda"      (SurfaceLam [binder] (SurfaceName "a"))
    , refused "a ∀"           (SurfacePi [binder] (SurfaceName "a"))
    , refused "an arrow"      (SurfaceArrow (SurfaceName "a") (SurfaceName "a"))
    , refused "a let"         (SurfaceLet "x" Nothing (SurfaceName "a") (SurfaceName "x"))
    , refused "an ascription" (SurfaceAnnot (SurfaceName "a") (SurfaceUniverse 0))
    ]
  where
    binder = SurfaceBinder Explicit "x" Nothing
    refused what s = testCase what $
      case elaborating s of
        Left (NoElaborationRule w) -> w @?= what
        other -> assertFailure ("expected a refusal: " ++ show other)

-- --------------------------------------------------------------------------
-- The shipped base
-- --------------------------------------------------------------------------

baseTests :: TestTree
baseTests =
  testGroup
    "the shipped base"
    [ -- Every rule whose head passes, and no partition to divide them.
      testCase "every rule whose head passes is a candidate" $
        [ n | Rule (GlobalName n) _ _ _ <- drain (matches expectedBase emptyGlobals hole) ]
          @?= [ "attack", "try-core", "abandon", "eliminate-core"
              , "prove", "elaborate", "unify-refine-core", "apply-core"
              ]

    , testCase "prove is a rule over prim-prove" $
        case [ r | r@(Rule (GlobalName "prove") _ _ _) <- drain (matches expectedBase emptyGlobals hole) ] of
          [Rule _ ps _ b] -> (ps, b) @?= ([], [Do Ops.Prove])
          other           -> assertFailure ("expected one clause: " ++ show other)
    ]
