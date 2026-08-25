-- | The three ops that read the development (§7.2, phase 24).
--
-- @goal@, @typeof@ and @define@ are gap 2 closing: before them, six ops
-- produced a value and not one of them looked at the proof state.
--
-- Driven as instructions rather than through the REPL, for
-- "Thena.EngineTests"' reason — the interesting states include ones no REPL
-- line can reach, such as a focus with nothing written down.
module Thena.ReadTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Context (Entry (..))
import Thena.Core.Term (Core (..), Ident (..), Level (..), Var, fresh)
import qualified Thena.Development.Component as Component
import Thena.Development.Cursor
  (Cursor, Focus (..), along, context, enter, focus, rebuild)
import Thena.Development.Partial (Partial (..))
import Thena.Engine
  ( Exec (..)
  , Machine (..)
  , Outcome (..)
  , ProofState (..)
  , cursor
  , load
  , proof
  , step
  )
import Thena.Errors (FailReason (..), MoveError (..))
import Thena.Global.Env (GlobalEnv, emptyGlobals)
import Thena.Declared (nat)
import Thena.Ops (Instr (..), Op (..), Operand (..), Value (..))

tests :: TestTree
tests =
  testGroup
    "reading the development (§7.2)"
    [goalTests, typeofTests, defineTests, gotoTests]

type0 :: Core
type0 = Universe (Level 0)

goalVar :: Var
goalVar = fst (fresh 0)

-- | @? goal : Type₀ . goal@ — a hole, focused.
hole :: Cursor
hole = enter (Under (Component.Claim goalVar (Ident "goal") type0) (Trailing (Free goalVar)))

machine :: Cursor -> [Instr] -> Machine
machine = machineIn emptyGlobals

machineIn :: GlobalEnv -> Cursor -> [Instr] -> Machine
machineIn env' cur is =
  load is (Machine (Exec [] [] []) (ProofState cur) env' [] 1000)

-- | Run to a stop, and hand back the environment or the reason.
run :: Cursor -> [Instr] -> Either FailReason Machine
run cur is = go (machine cur is)

-- | Run a machine to a stop. Top level, so a test that needs a non-empty
-- global environment can build its own machine and still use it.
go :: Machine -> Either FailReason Machine
go m = case step m of
  Continue m'       -> go m'
  Saying _ m'       -> go m'
  Declaring _ m'    -> go m'
  Certifying _ _ m' -> go m'
  Asking _ m'       -> Right m'
  Finished m'       -> Right m'
  Stuck r _         -> Left r

bound :: String -> Machine -> Maybe Value
bound n m = lookup n (env (exec m))

expectBound :: Cursor -> [Instr] -> String -> IO Value
expectBound cur is n = case run cur is of
  Left r  -> assertFailure ("did not run: " ++ show r)
  Right m -> maybe (assertFailure (n ++ " is unbound")) pure (bound n m)

goalTests :: TestTree
goalTests =
  testGroup
    "goal"
    [ testCase "is the type the focus is claimed at" $ do
        v <- expectBound hole [Bind "g" Goal] "g"
        v @?= VTerm (Trailing type0)

      -- §4.5: the goal is what the development /writes down/, never what
      -- @infer@ derives. The trailing term of a chain claims nothing.
    , testCase "and a focus with nothing written down has none" $
        case along hole >>= \c -> Right (run c [Do Goal]) of
          Right (Left NoGoalHere) -> pure ()
          other -> assertFailure ("expected NoGoalHere, got " ++ show (fmap (fmap (const ())) other))
    ]

typeofTests :: TestTree
typeofTests =
  testGroup
    "typeof"
    [ testCase "infers in the context at the focus" $ do
        v <- expectBound hole [Bind "t" (Typing (Lit (VTerm (Trailing type0))))] "t"
        v @?= VTerm (Trailing (Universe (Level 1)))

    , testCase "a variable gets its type from the context" $ do
        v <- expectBound hole
               [ Bind "x" (Claim (Lit (VText "x")) (Lit (VTerm (Trailing type0))))
               , Bind "t" (Typing (Ref "x"))
               ] "t"
        v @?= VTerm (Trailing type0)

    , testCase "and an ill-typed term fails" $
        case run hole [Do (Typing (Lit (VTerm (Trailing (App type0 type0))))) ] of
          Left (NotTypeable _) -> pure ()
          other -> assertFailure ("expected NotTypeable, got " ++ show (fmap (const ()) other))
    ]

-- | Thesis §2.7's @=@-binding.
defineTests :: TestTree
defineTests =
  testGroup
    "define"
    [ testCase "adds a definition above the focus, at the inferred type" $
        case run hole [Do (Define (Lit (VText "d")) (Lit (VTerm (Trailing type0))))] of
          Left r  -> assertFailure ("did not run: " ++ show r)
          Right m -> case context (cursor (proof m)) of
            [Definition _ (Ident "d") v t] -> do
              v @?= type0
              t @?= Universe (Level 1)
            other -> assertFailure ("unexpected context: " ++ show other)

    , testCase "and produces the variable it bound" $ do
        v <- expectBound hole
               [Bind "x" (Define (Lit (VText "d")) (Lit (VTerm (Trailing type0))))] "x"
        case v of
          VTerm (Trailing (Free _)) -> pure ()
          other -> assertFailure ("expected a variable, got " ++ show other)

      -- The focus does not move: the definition goes above it, and the hole
      -- being refined is still what the next instruction acts on.
    , testCase "the focus stays on the hole" $
        case run hole [Do (Define (Lit (VText "d")) (Lit (VTerm (Trailing type0))))] of
          Left r  -> assertFailure ("did not run: " ++ show r)
          Right m -> case focus (cursor (proof m)) of
            OnComponent (Component.Claim _ (Ident "goal") _) -> pure ()
            other -> assertFailure ("focus moved: " ++ show other)

    , testCase "an ill-typed value fails and changes nothing" $
        case run hole [Do (Define (Lit (VText "d")) (Lit (VTerm (Trailing (App type0 type0)))))] of
          Left (NotTypeable _) -> pure ()
          other -> assertFailure ("expected NotTypeable, got " ++ show (fmap (const ()) other))
    ]

-- --------------------------------------------------------------------------
-- goto (phase 24b)
-- --------------------------------------------------------------------------

-- | Focusing a hole by the variable that binds it.
--
-- The sharp check here is 'rebuild': @goto@ rewrites the /path/ and must leave
-- the development itself alone, and 'rebuild' is computed by code that knows
-- nothing about the search. That is the standing lesson — look for the
-- invariant maintained by different code from the code that checks it.
gotoTests :: TestTree
gotoTests =
  testGroup
    "goto"
    [ testCase "finds a hole claimed above the focus" $
        case run hole [ Bind "h" (Claim (Lit (VText "h")) (Lit (VTerm (Trailing type0))))
                      , Do (Goto (Ref "h"))
                      ] of
          Left r  -> assertFailure ("did not run: " ++ show r)
          Right m -> case focus (cursor (proof m)) of
            OnComponent (Component.Claim _ (Ident "h") _) -> pure ()
            other -> assertFailure ("focused " ++ show other)

      -- The development is untouched; only the path moved.
    , testCase "and changes nothing about the development" $
        let is  = [ Bind "h" (Claim (Lit (VText "h")) (Lit (VTerm (Trailing type0))))
                  , Do (Goto (Ref "h"))
                  ]
            before = [ Bind "h" (Claim (Lit (VText "h")) (Lit (VTerm (Trailing type0)))) ]
         in case (run hole before, run hole is) of
              (Right a, Right b) ->
                rebuild (cursor (proof b)) @?= rebuild (cursor (proof a))
              _ -> assertFailure "did not run"

      -- Depth first, and into guess bodies: after prim-attack the hole that
      -- matters is inside the guess, where 'along' alone never reaches.
    , -- @prim-attack@ makes a guess whose body is a hole; @into@ focuses it;
      -- the claim then lands **inside the guess body**. @back@ leaves, and
      -- @goto@ has to descend to find it again — which 'along' alone never
      -- does.
      testCase "descends into a guess body" $
        case run hole [ Do Attack
                      , Do Into
                      , Bind "h" (Claim (Lit (VText "h")) (Lit (VTerm (Trailing type0))))
                      , Do Back
                      , Do Back
                      , Do (Goto (Ref "h"))
                      ] of
          Left r  -> assertFailure ("did not run: " ++ show r)
          Right m -> case focus (cursor (proof m)) of
            OnComponent (Component.Claim _ (Ident "h") _) -> pure ()
            other -> assertFailure ("focused " ++ show other)

    , testCase "refuses an assumption" $
        case run hole [ Bind "a" (Assume (Lit (VText "a")) (Lit (VTerm (Trailing type0))))
                      , Do (Goto (Ref "a"))
                      ] of
          Left (CannotMove NoSuchHole) -> pure ()
          other -> assertFailure ("expected NoSuchHole, got " ++ show (fmap (const ()) other))

      -- **By name, from the root** — the user's correction, 2026-08-25: the
      -- move must work wherever the hole is, not only where Γ can see it. This
      -- is the case that failed before: the hole is inside a guess body the
      -- focus has left, so it is in no context at all.
    , testCase "by name, into a guess body the focus has left" $
        case run hole [ Do Attack
                      , Do Into
                      , Bind "h" (Claim (Lit (VText "h")) (Lit (VTerm (Trailing type0))))
                      , Do Back
                      , Do Back
                      , Do (Goto (Lit (VText "h")))
                      ] of
          Left r  -> assertFailure ("did not run: " ++ show r)
          Right m -> case focus (cursor (proof m)) of
            OnComponent (Component.Claim _ (Ident "h") _) -> pure ()
            other -> assertFailure ("focused " ++ show other)

    , testCase "a name nothing carries" $
        case run hole [Do (Goto (Lit (VText "nosuch")))] of
          Left (CannotMove NoSuchHole) -> pure ()
          other -> assertFailure ("expected NoSuchHole, got " ++ show (fmap (const ()) other))

      -- **Refused, not renamed** (phase 24c): inventing a name is the rule's
      -- job. Uniqueness is still guaranteed — it is just enforced rather than
      -- silently repaired.
    , testCase "a second hole asking for a taken name is refused" $
        case run hole [ Do (Claim (Lit (VText "h")) (Lit (VTerm (Trailing type0))))
                      , Do (Claim (Lit (VText "h")) (Lit (VTerm (Trailing type0))))
                      ] of
          Left (NameTaken "h") -> pure ()
          other -> assertFailure ("expected NameTaken, got " ++ show (fmap (const ()) other))

    , testCase "and fresh-name is how a rule gets one that is not" $
        case run hole [ Do (Claim (Lit (VText "h")) (Lit (VTerm (Trailing type0))))
                      , Bind "n" (FreshName (Lit (VText "h")))
                      , Do (Claim (Ref "n") (Lit (VTerm (Trailing type0))))
                      ] of
          Left r  -> assertFailure ("did not run: " ++ show r)
          Right m -> [ i | Hypothesis _ i _ <- context (cursor (proof m)) ]
                       @?= [Ident "h", Ident "h1"]

      -- A generated name must not shadow a datatype, a constructor or a
      -- theorem: a rule author cannot anticipate what is declared.
    , testCase "fresh-name avoids the globals too" $
        case go (machineIn nat hole [Bind "n" (FreshName (Lit (VText "Nat")))]) of
          Left r  -> assertFailure ("did not run: " ++ show r)
          Right m -> bound "n" m @?= Just (VText "Nat1")

    , testCase "and attack's inner hole is not its outer one" $
        case run hole [Do Attack, Do Into] of
          Left r  -> assertFailure ("did not run: " ++ show r)
          Right m -> case focus (cursor (proof m)) of
            OnComponent (Component.Claim _ (Ident "goal1") _) -> pure ()
            other -> assertFailure ("focused " ++ show other)

    , testCase "refuses a term that is not a variable" $
        case run hole [Do (Goto (Lit (VTerm (Trailing type0))))] of
          Left (CannotMove NoSuchHole) -> pure ()
          other -> assertFailure ("expected NoSuchHole, got " ++ show (fmap (const ()) other))
    ]
