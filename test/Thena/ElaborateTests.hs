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
import qualified Thena.Core.Term
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
import Thena.Errors (FailReason (..), MoveError (..), ResolveError (..), SyntaxError (..))
import Thena.Global.Env (emptyGlobals)
import Thena.Ops
  ( Instr (..)
  , Operand (..)
  , Rule (..)
  , Value (..)
  )
import qualified Thena.Ops as Ops
import Thena.Rules
  ( RuleIter
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
    , hereTests
    , lambdaTests
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
elaborating = elaboratingAt hole

-- | The same, at a cursor of your own.
elaboratingAt :: Cursor -> Surface -> Either FailReason Machine
elaboratingAt cur s = snd (runOut (machineAt cur [Do (Ops.Elaborate (Lit (VSurface s)))]))

-- | A machine at a cursor, loaded with a program.
machineAt :: Cursor -> [Instr] -> Machine
machineAt cur is =
  load is (Machine (Exec [] [] []) (Development cur) emptyGlobals [] 1000)

-- | @? goal : ∀ (a : Type₀) (b : Type₀) -> Type₀@ — two binders, so a miscount
-- would show.
piGoal2 :: Cursor
piGoal2 = enter (Under (Claim goalVar (Ident "goal") ty) (Trailing (Free goalVar)))
  where
    inner = Pi (Ident "b") type0 (Thena.Core.Term.close hypVar type0)
    ty    = Pi (Ident "a") type0 (Thena.Core.Term.close hypVar inner)

-- | @? goal : ∀ (a : Type₀) -> Type₀@ — a hole a lambda can be elaborated into.
--
-- **The Π's binder is @a@ and the surface will say @y@**, which is the whole
-- point of the test that uses it.
piGoal :: Cursor
piGoal = enter (Under (Claim goalVar (Ident "goal") ty) (Trailing (Free goalVar)))
  where
    ty = Pi (Ident "a") type0 (Thena.Core.Term.close hypVar type0)

-- | The λ binders of the term the development has built, outermost first.
--
-- **In the term and not in the chain**: @attack@ opens a guess, @intro@ binds
-- inside it, and @solve@ commits the lot into one component whose /value/ is a
-- @Lam@. So the surface name that has to survive ends up as a
-- 'Thena.Core.Term.Lam' binder, which is where this looks for it.
identsBound :: Machine -> [String]
identsBound m = chain (Cursor.rebuild (cursor (development m)))
  where
    chain (Under (Define _ _ v _) _) = lams v
    chain (Under _ rest)             = chain rest
    chain (Trailing t)               = lams t
    chain _                          = []

    lams (Lam (Ident i) _ b) = i : lams (Thena.Core.Term.instantiate (Universe LZero) b)
    lams _                   = []

-- | The variable of the component the focus is on.
--
-- **What "the focus came back" actually means**, and it is what @here@ itself
-- answers — so the assertions below say /this component/ rather than /some
-- property of the path/. An earlier version asked whether @back@ failed, which
-- is a different question and passed for the wrong reason.
focusedVar :: Machine -> Maybe Var
focusedVar m = case focus (cursor (development m)) of
  Cursor.OnComponent (Assume v _ _)   -> Just v
  Cursor.OnComponent (Define v _ _ _) -> Just v
  Cursor.OnComponent (Claim  v _ _)   -> Just v
  Cursor.OnComponent (Guess  v _ _ _) -> Just v
  _                                   -> Nothing

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
-- The λ case (MS4 phase 41b)
-- --------------------------------------------------------------------------

lambdaTests :: TestTree
lambdaTests =
  testGroup
    "a lambda elaborates"
    [ -- **The binder takes the SURFACE name, not the type\'s**, which is the
      -- whole reason @prim-intro@ gained an operand. The fixture\'s goal binds
      -- @a@; the surface says @y@; the development must say @y@, or the body\'s
      -- @y@ resolves to nothing.
      testCase "the binder takes the surface name" $
        case elaboratingAt piGoal (SurfaceLam [SurfaceBinder Explicit "y" Nothing]
                                     (SurfaceName "y")) of
          Left r  -> assertFailure ("did not elaborate: " ++ show r)
          Right m -> identsBound m @?= ["y"]

      -- **@here@ is what makes this exact rather than careful** (phase 41c).
      -- Before it, the clause counted its own @into@/@along@ and undid them
      -- with matching @back@s; now it parks the component it was called at and
      -- @goto@es it. Two binders rather than one, because a miscount only shows
      -- when the counts differ.
    , testCase "two binders, and the focus still comes back" $
        case elaboratingAt piGoal2 (SurfaceLam [ SurfaceBinder Explicit "y" Nothing
                                               , SurfaceBinder Explicit "z" Nothing ]
                                      (SurfaceName "z")) of
          Left r  -> assertFailure ("did not elaborate: " ++ show r)
          Right m -> (identsBound m, focusedVar m) @?= (["y", "z"], Just goalVar)

      -- **The invariant every later case leans on**: an @Elaborate@ leaves the
      -- focus where it found it. The λ case makes moves and must undo them, or
      -- its own @prim-solve@ lands somewhere else.
    , testCase "and the focus comes back to where it started" $
        case elaboratingAt piGoal (SurfaceLam [SurfaceBinder Explicit "y" Nothing]
                                     (SurfaceName "y")) of
          Left r  -> assertFailure ("did not elaborate: " ++ show r)
          Right m -> focusedVar m @?= Just goalVar

      -- An annotation is **refused rather than ignored**: checking it against
      -- the goal\'s domain needs the ascription machinery, which is a later
      -- phase, and accepting it silently would be a check that is not happening.
    , refused "a lambda binder with a type or braces"
        (SurfaceLam [SurfaceBinder Explicit "x" (Just (SurfaceUniverse 0))]
           (SurfaceName "x"))
    , refused "a lambda binder with a type or braces"
        (SurfaceLam [SurfaceBinder Implicit "x" Nothing] (SurfaceName "x"))
    ]
  where
    refused what s = testCase what $
      case elaboratingAt piGoal s of
        Left (NoElaborationRule w) -> w @?= what
        other -> assertFailure ("expected a refusal: " ++ show other)

-- --------------------------------------------------------------------------
-- here (MS4 phase 41c)
-- --------------------------------------------------------------------------

hereTests :: TestTree
hereTests =
  testGroup
    "here answers which component the focus is on"
    [ -- The companion to @goal@, which answers what it is claimed /at/. Nothing
      -- could answer this before: @claim@ and @define@ yield the variables of
      -- holes they make, and @goal@ gives a type.
      testCase "it yields the focused component's variable" $
        case snd (runOut (machineAt hole [Bind "h" Ops.Here])) of
          Left r  -> assertFailure ("did not run: " ++ show r)
          Right m -> lookup "h" (env (exec m))
                       @?= Just (VTerm (Trailing (Free goalVar)))

      -- **It survives @attack@**, which is the whole reason the λ case can use
      -- it: @attack@ turns @? x : S@ into a guess binding the /same/ variable,
      -- so a @goto@ afterwards finds what @here@ named.
    , testCase "and goto finds it again after attack" $
        case snd (runOut (machineAt hole [ Bind "h" Ops.Here
                                         , Do Ops.Attack
                                         , Do Ops.Into
                                         , Do (Ops.Goto (Ref "h"))
                                         ])) of
          Left r  -> assertFailure ("did not run: " ++ show r)
          Right m -> focusedVar m @?= Just goalVar

      -- Off the spine there is no component and no variable, which is the same
      -- refusal every component op gives.
    , testCase "and it is refused in the core fragment" $
        case snd (runOut (machineAt hole [Do Ops.CrossType, Bind "h" Ops.Here])) of
          Left (CannotMove NotOnTheSpine) -> pure ()
          other -> assertFailure ("expected a refusal: " ++ show other)
    ]

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
