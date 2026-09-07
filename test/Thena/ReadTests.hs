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

import Thena.Core.Level (Level (..), LevelVar (..), levelOfNat)
import Thena.Core.Context (Entry (..))
import Thena.Core.Term (Core (..), GlobalName (..), Ident (..), Var, close, fresh)
import qualified Thena.Development.Component as Component
import Thena.Development.Cursor
  (Cursor, Focus (..), along, context, enter, focus, identsIn, rebuild)
import Thena.Development.Partial (Partial (..))
import Thena.Engine
  ( Exec (..)
  , Machine (..)
  , Outcome (..)
  , Development (..)
  , cursor
  , load
  , development
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
    [goalTests, typeofTests, defineTests, gotoTests, universeTests, resolveTests]

type0 :: Core
type0 = Universe (LZero)

goalVar :: Var
goalVar = fst (fresh 0)

-- | @? goal : Type₀ . goal@ — a hole, focused.
hole :: Cursor
hole = enter (Under (Component.Claim goalVar (Ident "goal") type0) (Trailing (Free goalVar)))

machine :: Cursor -> [Instr] -> Machine
machine = machineIn emptyGlobals

machineIn :: GlobalEnv -> Cursor -> [Instr] -> Machine
machineIn env' cur is =
  load is (Machine (Exec [] [] []) (Development cur) [] env' [] [] 1000)

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
  Defining _ _ _ _ m' -> go m'
  Certifying _ _ m' -> go m'
  Asking _ m'       -> Right m'
  Yielding _ m'     -> Right m'
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
        v @?= VTerm (Trailing (Universe (levelOfNat 1)))

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
          Right m -> case context (cursor (development m)) of
            [Definition _ (Ident "d") v t] -> do
              v @?= type0
              t @?= Universe (levelOfNat 1)
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
          Right m -> case focus (cursor (development m)) of
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
          Right m -> case focus (cursor (development m)) of
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
                rebuild (cursor (development b)) @?= rebuild (cursor (development a))
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
          Right m -> case focus (cursor (development m)) of
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
          Right m -> case focus (cursor (development m)) of
            OnComponent (Component.Claim _ (Ident "h") _) -> pure ()
            other -> assertFailure ("focused " ++ show other)

      -- **The development stack** (MS4 phase 42) — Brady's @NEW PROOF@ and
      -- @TERM@. A pushed development is a claim of its own, and popping it
      -- extracts the term it built.
    , testCase "pop hands back what the nested development proved" $
        case run hole [ Do (PushDevelopment (Lit (VTerm (Trailing (Universe (LSuc LZero))))))
                      , Do (Try (Lit (VTerm (Trailing (Universe LZero)))))
                      , Do Solve
                      , Bind "t" PopDevelopment
                      ] of
          Left r  -> assertFailure ("did not run: " ++ show r)
          -- **And it hands back exactly what @extract@ built** — @solve@ turns
          -- the goal into a definition, so the term is @let goal = … in goal@
          -- and not the bare @Type₀@. That is why a declaration's type goes
          -- through @whnf@ before it is stored or used: a @let@-headed type
          -- makes @intro@ open a definition instead of a binder.
          Right m -> lookup "t" (env (exec m))
                       @?= Just (VTerm (Trailing
                             (Let (Ident "goal") (Universe LZero)
                                  (Universe (LSuc LZero)) (close goalVar (Free goalVar)))))

      -- And it comes back to where it was: the outer development is the one
      -- the machine had before the push.
    , testCase "and the machine is back on the development it left" $
        case run hole [ Do (PushDevelopment (Lit (VTerm (Trailing (Universe (LSuc LZero))))))
                      , Do (Try (Lit (VTerm (Trailing (Universe LZero)))))
                      , Do Solve
                      , Do PopDevelopment
                      ] of
          Left r  -> assertFailure ("did not run: " ++ show r)
          Right m -> (development m == Development hole, enclosing m) @?= (True, [])

      -- **A hole left open is reported, not silently turned into a term** —
      -- the same 'extract' @certify@ uses.
    , testCase "an unfinished nested development cannot be popped" $
        case run hole [ Do (PushDevelopment (Lit (VTerm (Trailing (Universe (LSuc LZero))))))
                      , Do PopDevelopment
                      ] of
          Left (NotYetPure _) -> pure ()
          other -> assertFailure ("expected NotYetPure: " ++ show (fmap (const ()) other))

    , testCase "and the outermost one cannot be popped at all" $
        case run hole [Do PopDevelopment] of
          Left NoEnclosingDevelopment -> pure ()
          other -> assertFailure ("expected NoEnclosingDevelopment: " ++ show (fmap (const ()) other))

    , testCase "a name nothing carries" $
        case run hole [Do (Goto (Lit (VText "nosuch")))] of
          Left (CannotMove NoSuchHole) -> pure ()
          other -> assertFailure ("expected NoSuchHole, got " ++ show (fmap (const ()) other))

      -- **The name is used as given** (MS4 phase 41f). This asserted the
      -- opposite until then — @claim@ refused a taken name (phase 24c,
      -- /"refused, not renamed"/) so that identifiers stayed unique. They did
      -- not: @prim-intro@ never checked, and elaboration hands it the surface
      -- binder's name. Elaboration's @∀@ and @let@ are what force it, since
      -- both must bind the name the user wrote.
    , testCase "a second hole may ask for a taken name and gets it" $
        case run hole [ Do (Claim (Lit (VText "h")) (Lit (VTerm (Trailing type0))))
                      , Do (Claim (Lit (VText "h")) (Lit (VTerm (Trailing type0))))
                      ] of
          Left r  -> assertFailure ("did not run: " ++ show r)
          Right m ->
            let named = [ i | Ident i <- identsIn (cursor (development m)), i == "h" ]
             in length named @?= 2

    , testCase "and fresh-name is how a rule gets one that is not" $
        case run hole [ Do (Claim (Lit (VText "h")) (Lit (VTerm (Trailing type0))))
                      , Bind "n" (FreshName (Lit (VText "h")))
                      , Do (Claim (Ref "n") (Lit (VTerm (Trailing type0))))
                      ] of
          Left r  -> assertFailure ("did not run: " ++ show r)
          Right m -> [ i | Hypothesis _ i _ <- context (cursor (development m)) ]
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
          Right m -> case focus (cursor (development m)) of
            OnComponent (Component.Claim _ (Ident "goal1") _) -> pure ()
            other -> assertFailure ("focused " ++ show other)

    , testCase "refuses a term that is not a variable" $
        case run hole [Do (Goto (Lit (VTerm (Trailing type0))))] of
          Left (CannotMove NoSuchHole) -> pure ()
          other -> assertFailure ("expected NoSuchHole, got " ++ show (fmap (const ()) other))
    ]

-- --------------------------------------------------------------------------
-- The two ops the elaborator's own operands asked for (MS4 phase 48)
-- --------------------------------------------------------------------------

-- | @fresh-universe@ — the surface's bare @Type@, at an operand.
--
-- Seven of the nine @Lit (VTerm …)@ operands the Haskell elaborator emitted
-- were this, and
-- **it is the one a rule cannot write down**: the point of the meta is that it
-- is fresh at every node.
universeTests :: TestTree
universeTests =
  testGroup
    "fresh-universe"
    [ testCase "is a universe at a meta drawn from the counter" $ do
        v <- expectBound hole [Bind "u" FreshUniverse] "u"
        v @?= VTerm (Trailing (Universe (LVar (LMeta 1000))))

    , testCase "and each one is its own" $ do
        m <- expectRun hole [Bind "a" FreshUniverse, Bind "b" FreshUniverse]
        (bound "a" m == bound "b" m) @?= False
    ]

-- | @resolve-name@ — Γ first, then the globals, with level arguments inserted.
resolveTests :: TestTree
resolveTests =
  testGroup
    "resolve-name"
    [ testCase "a declared constructor is a global" $ do
        v <- expectBoundIn nat hole [Bind "z" (ResolveName (Lit (VText "zero")))] "z"
        v @?= VTerm (Trailing (Global (GlobalName "zero") []))

      -- §3.6's one namespace: a binder shadows a global of the same name, and
      -- this is the order "Thena.Syntax.Resolve" uses for the same reason. The
      -- assumption is written with the constructor's own name, which phase 41f
      -- made legal — a name is used as given.
    , testCase "a local shadows a global of the same name" $ do
        v <- expectBoundIn nat hole
               [ Do (Assume (Lit (VText "zero")) (Lit (VTerm (Trailing type0))))
               , Bind "z" (ResolveName (Lit (VText "zero")))
               ] "z"
        case v of
          VTerm (Trailing (Free _)) -> pure ()
          other -> assertFailure ("expected a local, got " ++ show other)

    , testCase "a name nothing bears does not resolve" $
        case runIn nat hole [Do (ResolveName (Lit (VText "nope")))] of
          Left (CannotRead _) -> pure ()
          other -> assertFailure ("expected CannotRead, got " ++ show (fmap (const ()) other))
    ]

runIn :: GlobalEnv -> Cursor -> [Instr] -> Either FailReason Machine
runIn env' cur is = go (machineIn env' cur is)

expectRun :: Cursor -> [Instr] -> IO Machine
expectRun cur is = either (assertFailure . ("did not run: " ++) . show) pure (run cur is)

expectBoundIn :: GlobalEnv -> Cursor -> [Instr] -> String -> IO Value
expectBoundIn env' cur is n = case runIn env' cur is of
  Left r  -> assertFailure ("did not run: " ++ show r)
  Right m -> maybe (assertFailure (n ++ " is unbound")) pure (bound n m)
