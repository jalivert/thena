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
import Thena.Development.Cursor (Cursor, Focus (..), context, enter, focus, along)
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
import Thena.Errors (FailReason (..))
import Thena.Global.Env (emptyGlobals)
import Thena.Ops (Instr (..), Op (..), Operand (..), Value (..))

tests :: TestTree
tests = testGroup "reading the development (§7.2)" [goalTests, typeofTests, defineTests]

type0 :: Core
type0 = Universe (Level 0)

goalVar :: Var
goalVar = fst (fresh 0)

-- | @? goal : Type₀ . goal@ — a hole, focused.
hole :: Cursor
hole = enter (Under (Component.Claim goalVar (Ident "goal") type0) (Trailing (Free goalVar)))

machine :: Cursor -> [Instr] -> Machine
machine cur is =
  load is (Machine (Exec [] [] []) (ProofState cur) emptyGlobals [] 1000)

-- | Run to a stop, and hand back the environment or the reason.
run :: Cursor -> [Instr] -> Either FailReason Machine
run cur is = go (machine cur is)
  where
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
