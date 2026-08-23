-- | The machine: one instruction at a time, and what each op does to the
-- development.
--
-- Built in Haskell rather than driven through the REPL, deliberately — the same
-- reason "Thena.Fixtures" builds developments by hand. A test that goes through
-- the command compiler can only see programs the compiler emits, and phase 4's
-- compiler emits three shapes; the machine has to be right for the rest.
module Thena.EngineTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Context (Entry (..))
import Thena.Core.Term (Core (..), Ident (..), Level (..), fresh)
import Thena.Development.Component (Component (..))
import Thena.Development.Cursor (enter)
import Thena.Development.Partial (Partial (..))
import Thena.Engine
  ( Exec (..)
  , Frame (..)
  , Machine (..)
  , Outcome (..)
  , ProofState (..)
  , Question (..)
  , isAsking
  , load
  , newProof
  , proofContext
  , proofDevelopment
  , resumeAt
  , setGoal
  , step
  )
import Thena.Global.Env (emptyGlobals)
import Thena.Rules (standardRules)
import Thena.Errors (FailReason (..), MoveError (..))
import Thena.Ops (AnswerKind (..), Instr (..), Operand (..), Value (..))
import qualified Thena.Ops as Ops

type0 :: Core
type0 = Universe (Level 0)

term :: Core -> Operand
term = Lit . VTerm . Trailing

text :: String -> Operand
text = Lit . VText

-- | A machine holding the program, with the session's opening development.
machine :: [Instr] -> Machine
machine is = load is (Machine (Exec [] [] []) ps emptyGlobals standardRules n)
  where
    (ps, n) = newProof 0

-- | Run to the first stop, collecting nothing. Not the driver's loop — this is
-- a test helper and it stops at anything that is not 'Continue'.
runTo :: Machine -> Outcome
runTo m = case step m of
  Continue m' -> runTo m'
  outcome     -> outcome

devOf :: Machine -> Partial
devOf = proofDevelopment . proof

envOf :: Machine -> [(String, Value)]
envOf = env . exec

stuckWith :: FailReason -> Outcome -> IO ()
stuckWith r outcome = case outcome of
  Stuck r' _ -> r' @?= r
  other      -> assertFailure ("expected Stuck, got " ++ show other)

tests :: TestTree
tests =
  testGroup
    "Thena.Engine"
    [ testGroup
        "stepping"
        [ testCase "an empty program with an empty stack is finished" $
            case step (machine []) of
              Finished _ -> pure ()
              other      -> assertFailure ("expected Finished, got " ++ show other)
        , testCase "an empty program returns into the frame below it" $
            -- Nothing in phase 4 pushes a frame; this is the return case of
            -- §7.3, which phase 16 exercises for real.
            let resumed = [Do (Ops.Say (text "back"))]
                m = (machine []) { exec = Exec [] [] [Call resumed [("x", VText "kept")]] }
             in case step m of
                  Continue m' -> (pc (exec m'), envOf m', stack (exec m')) @?= (resumed, [("x", VText "kept")], [])
                  other       -> assertFailure ("expected Continue, got " ++ show other)
        , testCase "Bind names the op's result" $
            case runTo (machine [Bind "s" (Ops.Concat (text "a") (text "b"))]) of
              Finished m -> envOf m @?= [("s", VText "ab")]
              other      -> assertFailure ("expected Finished, got " ++ show other)
        , testCase "Do discards it" $
            case runTo (machine [Do (Ops.Concat (text "a") (text "b"))]) of
              Finished m -> envOf m @?= []
              other      -> assertFailure ("expected Finished, got " ++ show other)
        , testCase "Ref reads a name bound earlier in the body" $
            case runTo (machine [Bind "s" (Ops.Concat (text "a") (text "b")), Bind "t" (Ops.Concat (Ref "s") (text "!"))]) of
              Finished m -> lookup "t" (envOf m) @?= Just (VText "ab!")
              other      -> assertFailure ("expected Finished, got " ++ show other)
        , testCase "a stuck machine keeps stepping to the same reason" $
            case runTo (machine [Do (Ops.Say (Ref "nope"))]) of
              Stuck r m -> stuckWith r (step m)
              other     -> assertFailure ("expected Stuck, got " ++ show other)
        ]
    , testGroup
        "asking"
        [ testCase "Ask yields the prompt the body built" $
            case runTo (machine [Bind "p" (Ops.Concat (text "who? ") (text "type A")), Bind "x" (Ops.Ask (Ref "p") AName)]) of
              Asking q _ -> q @?= Question "who? type A" AName
              other      -> assertFailure ("expected Asking, got " ++ show other)
        , testCase "the asking instruction stays at the head of pc" $
            -- What lets 'resumeAt' know the destination without a field in
            -- 'Machine' that is meaningful only sometimes (§7.5).
            case runTo (machine [Bind "x" (Ops.Ask (text "?") AName), Do (Ops.Say (Ref "x"))]) of
              Asking _ m -> (pc (exec m), isAsking m) @?= ([Bind "x" (Ops.Ask (text "?") AName), Do (Ops.Say (Ref "x"))], True)
              other      -> assertFailure ("expected Asking, got " ++ show other)
        , testCase "resumeAt binds the answer where the instruction named" $
            case runTo (machine [Bind "x" (Ops.Ask (text "?") AName), Do (Ops.Say (Ref "x"))]) of
              Asking _ m ->
                let m' = resumeAt "hello" m
                 in (lookup "x" (envOf m'), pc (exec m')) @?= (Just (VText "hello"), [Do (Ops.Say (Ref "x"))])
              other -> assertFailure ("expected Asking, got " ++ show other)
        , testCase "an unbound Ask discards the answer and steps past it" $
            case runTo (machine [Do (Ops.Ask (text "?") AText)]) of
              Asking _ m -> (envOf (resumeAt "x" m), pc (exec (resumeAt "x" m))) @?= ([], [])
              other      -> assertFailure ("expected Asking, got " ++ show other)
        , testCase "resumeAt on a machine that is not asking changes nothing" $
            let m = machine [Do (Ops.Say (text "hi"))]
             in (resumeAt "x" m, isAsking m) @?= (m, False)
        , testCase "Say yields the message and steps past it" $
            case step (machine [Do (Ops.Say (text "hi"))]) of
              Saying msg m -> (msg, pc (exec m)) @?= ("hi", [])
              other        -> assertFailure ("expected Saying, got " ++ show other)
        ]
    , testGroup
        "failure"
        [ testCase "a Ref that names nothing" $
            stuckWith (UnboundInBody "gone") (runTo (machine [Do (Ops.Say (Ref "gone"))]))
        , testCase "a term where text was wanted" $
            stuckWith ExpectedText (runTo (machine [Do (Ops.Say (term type0))]))
        , testCase "text where a term was wanted" $
            stuckWith ExpectedTerm (runTo (machine [Do (Ops.Assume (text "A") (text "not a term"))]))
        , testCase "a whole development where a term was wanted" $
            let chain = Under (Assume (fst (fresh 0)) (Ident "A") type0) (Trailing type0)
             in stuckWith ExpectedTerm (runTo (machine [Do (Ops.Assume (text "A") (Lit (VTerm chain)))]))
        , testCase "a name that is not an identifier" $
            stuckWith (NotAnIdentifier "let") (runTo (machine [Do (Ops.Assume (text "let") (term type0))]))
        , testCase "a name that is two identifiers" $
            stuckWith (NotAnIdentifier "A B") (runTo (machine [Do (Ops.Assume (text "A B") (term type0))]))
        , testCase "the machine is kept, so retry can still use it" $
            case runTo (machine [Do (Ops.Say (Ref "gone"))]) of
              Stuck _ m -> devOf m @?= devOf (machine [])
              other     -> assertFailure ("expected Stuck, got " ++ show other)
        ]
    , testGroup
        "the development"
        [ testCase "assume goes outside the goal, not inside it" $
            -- The goal must stay innermost: it is what the assumption is for.
            case runTo (machine [Do (Ops.Assume (text "A") (term type0))]) of
              Finished m -> case devOf m of
                Under (Assume _ (Ident "A") _) (Under (Claim _ (Ident "goal") _) (Trailing (Free _))) -> pure ()
                other -> assertFailure ("wrong shape: " ++ show other)
              other -> assertFailure ("expected Finished, got " ++ show other)
        , testCase "two assumptions keep their order" $
            case runTo (machine [Do (Ops.Assume (text "A") (term type0)), Do (Ops.Assume (text "B") (term type0))]) of
              Finished m -> case devOf m of
                Under (Assume _ (Ident a) _) (Under (Assume _ (Ident b) _) (Under Claim {} (Trailing _))) ->
                  (a, b) @?= ("A", "B")
                other -> assertFailure ("wrong shape: " ++ show other)
              other -> assertFailure ("expected Finished, got " ++ show other)
        , testCase "claim builds a hole" $
            case runTo (machine [Do (Ops.Claim (text "h") (term type0))]) of
              Finished m -> case devOf m of
                Under (Claim _ (Ident "h") _) (Under Claim {} (Trailing _)) -> pure ()
                other -> assertFailure ("wrong shape: " ++ show other)
              other -> assertFailure ("expected Finished, got " ++ show other)
        , testCase "assume produces the variable it bound" $
            case runTo (machine [Bind "x" (Ops.Assume (text "A") (term type0))]) of
              Finished m -> case (lookup "x" (envOf m), devOf m) of
                (Just (VTerm (Trailing (Free v))), Under (Assume w _ _) _) -> v @?= w
                other -> assertFailure ("wrong shape: " ++ show other)
              other -> assertFailure ("expected Finished, got " ++ show other)
        , testCase "the counter moves on with every mint" $
            case runTo (machine [Do (Ops.Assume (text "A") (term type0)), Do (Ops.Assume (text "B") (term type0))]) of
              Finished m -> names m @?= 3   -- the opening goal, then two binders
              other      -> assertFailure ("expected Finished, got " ++ show other)
        , testCase "setGoal replaces the focus and keeps the prefix" $
            case runTo (machine [Do (Ops.Assume (text "A") (term type0))]) of
              Finished m -> case fmap (proofDevelopment . proof) (setGoal (Universe (Level 1)) m) of
                Right (Under Assume {} (Under (Claim _ _ ty) (Trailing (Free _)))) ->
                  ty @?= Universe (Level 1)
                other -> assertFailure ("wrong shape: " ++ show other)
              other -> assertFailure ("expected Finished, got " ++ show other)
        , testCase "setGoal standing at the root throws the whole chain away" $
            -- Not a corner case that arises in a session: 'newProof' focuses the
            -- goal and 'assume' leaves the focus alone, so ':goal' lands on a
            -- hole. It pins the rule, which is one sentence — everything from
            -- the focus down is discarded (§4.0 F6).
            let (v, n) = fresh 0
                bare   = Machine (Exec [] [] []) (ProofState (enter (Under (Assume v (Ident "A") type0) (Trailing type0)))) emptyGlobals standardRules n
             in case fmap (proofDevelopment . proof) (setGoal type0 bare) of
                  Right (Under (Claim x _ _) (Trailing (Free y))) -> x @?= y
                  other -> assertFailure ("wrong shape: " ++ show other)
        , testCase "a move is an op, and it moves the focus" $
            -- The moves go through the machine because the cursor IS
            -- 'ProofState' (§7.2): moving the focus changes exactly what
            -- backtracks, which is §12 invariant 3's hazard.
            case runTo (machine [Do (Ops.Assume (text "A") (term type0)), Do Ops.Along]) of
              Finished m -> map nameOf (proofContext (proof m)) @?= ["A", "goal"]
              other      -> assertFailure ("expected Finished, got " ++ show other)
        , testCase "and back undoes it, through the machine as well" $
            case runTo (machine [Do (Ops.Assume (text "A") (term type0)), Do Ops.Along, Do Ops.Back]) of
              Finished m -> map nameOf (proofContext (proof m)) @?= ["A"]
              other      -> assertFailure ("expected Finished, got " ++ show other)
        , testCase "a refused move is Stuck, and keeps the machine (§4.0 C4)" $
            stuckWith (CannotMove NotAGuess) (runTo (machine [Do Ops.Into]))
        , testCase "a core descent mints the binder it opens, so the counter moves" $
            case runTo (machine [Do Ops.CrossType]) of
              Finished m -> names m @?= 1
              other      -> assertFailure ("expected Finished, got " ++ show other)
        , testCase "Γ is the prefix of the focus, so the goal it stands on is NOT in it" $
            -- Phase 4's own version forgot the entire chain, because there was
            -- no focus to take a prefix of. §4.5: you are ON the focused
            -- component, not past it.
            case runTo (machine [Do (Ops.Assume (text "A") (term type0)), Do (Ops.Claim (text "h") (term type0))]) of
              Finished m -> map nameOf (proofContext (proof m)) @?= ["A", "h"]
              other      -> assertFailure ("expected Finished, got " ++ show other)
        ]
    ]
  where
    nameOf e = case e of
      Hypothesis _ (Ident i) _   -> i
      Definition _ (Ident i) _ _ -> i
