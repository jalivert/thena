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

import Thena.Core.Level (Level (..), levelOfNat)
import Thena.Core.Context (Entry (..))
import Thena.Core.Term
  (Core (..), Ident (..), Var, close, fresh, rootName, rootScope)
import Thena.Development.Component (Component (..))
import Thena.Development.Cursor (enter)
import Thena.Development.Partial (Partial (..))
import Thena.Core.Trust (TrustLevel (..))
import Thena.Engine
  ( Exec (..)
  , Frame (..)
  , Machine (..)
  , Outcome (..)
  , Development (..)
  , Question (..)
  , isAsking
  , isYielding
  , load
  , resumeYield
  , newDevelopment
  , focusContext
  , flatten
  , resumeAt
  , setGoal
  , step
  )
import Thena.Global.Env (emptyGlobals)
import Thena.Standard (expectedBase)
import Thena.Errors (FailReason (..), MoveError (..))
import Thena.Instral.Ops (AnswerKind (..), Instr (..), Operand (..), Value (..))
import qualified Thena.Instral.Ops as Ops

type0 :: Core
type0 = Universe (LZero)

term :: Core -> Operand
term = Lit . VTerm

text :: String -> Operand
text = Lit . VText

-- | A binder's identity as an operand: the word, and the token when there is
-- one (MS12 phase 353).
ident :: String -> Maybe Var -> Operand
ident w mv = Lit (VIdent (Ops.Identifier (Ident w) mv))

-- | A machine holding the program, with the session's opening development.
machine :: [Instr] -> Machine
machine is = load is (Machine (Exec [] [] [] []) ps [] emptyGlobals expectedBase [] [] [] [] rootScope n [] 0
                              NoUndischargeableTrust)
  where
    (ps, n) = newDevelopment 0

-- | Run to the first stop, collecting nothing. Not the driver's loop — this is
-- a test helper and it stops at anything that is not 'Continue'.
runTo :: Machine -> Outcome
runTo m = case step m of
  Continue m' -> runTo m'
  outcome     -> outcome

devOf :: Machine -> Partial
devOf = flatten . development

envOf :: Machine -> [(String, Value)]
envOf = env . exec

-- | A guess over @∀ (a : Type\8320) -> Type\8320@, which is what @intro@ needs
-- under it (MS12 phase 353). The goal is set before the program runs, because
-- 'setGoal' is a function on the machine and not an op.
atPi :: [Instr] -> Outcome
atPi is = case setGoal piGoal (machine []) of
  Left e  -> Stuck (CannotMove e) (machine [])
  Right m -> runTo (load is m)

piGoal :: Core
piGoal = Pi (Ident "a") type0 (close (fst (fresh 0)) type0)

-- | 'atPi' with the goal's own binder word already standing in the context, so
-- that whether @intro@ makes a word free is visible (MS12 phase 355, @~2n5tn@).
taken :: [Instr] -> Outcome
taken is = atPi (Do (Ops.Assume (text "a") (term type0)) : is)

-- | Every binder word in the chain, outermost first.
--
-- 'binderOf' answers the first one it reaches, which is the context entry here
-- and not the one @intro@ opened; what these two tests are about is the pair.
binderWords :: Partial -> [Ident]
binderWords p = case p of
  Under (Guess _ _ body _) rest -> binderWords body ++ binderWords rest
  Under (Assume _ i _) rest     -> i : binderWords rest
  Under _ rest                  -> binderWords rest
  Trailing _                    -> []
  Pending _ _                   -> []

-- | A token minted far past anything this machine's counter will reach, so that
-- a test asserting it was adopted cannot pass by coincidence.
someToken :: Var
someToken = fst (fresh 97)

-- | The binder @intro@ opened: the variable it is and the word it displays.
--
-- It digs through the chain rather than matching one shape, because what is
-- above the guess is the opening development's own claim and what is below the
-- binder is the hole for the rest of the goal.
binderOf :: Partial -> Maybe (Var, Ident)
binderOf p = case p of
  Under (Guess _ _ body _) rest -> maybe (binderOf rest) Just (binderOf body)
  Under (Assume v i _) _        -> Just (v, i)
  Under _ rest                  -> binderOf rest
  Trailing _                    -> Nothing
  Pending _ _                   -> Nothing

stuckWith :: FailReason -> Outcome -> IO ()
stuckWith r outcome = case outcome of
  Stuck r' _ -> r' @?= r
  other      -> assertFailure ("expected Stuck, got " ++ show other)

tests :: TestTree
tests =
  testGroup
    "Thena.Engine"
    [ testGroup
        -- **Yielding, and what @load@ may keep** (MS4 phase 45b).
        --
        -- The second group is the one that matters. The design conversation had
        -- @load@ prepending unconditionally; @pc@ is only empty when a program
        -- /finished/, so a line that halted leaves instructions behind and
        -- prepending revives them. @test\/golden\/mistakes.golden@ caught it —
        -- a failed @assume@'s @Ask@ came back two commands later and swallowed a
        -- @:show@ — and these say the rule that replaced it.
        "yielding"
        [ testCase "a yield stops the machine and does not consume itself" $
            case step (machine [Do (Ops.Yield (text "look"))]) of
              Yielding msg m -> (msg, isYielding m) @?= ("look", True)
              other -> assertFailure ("expected Yielding, got " ++ show other)

        , testCase "and stepping it again yields again" $
            case step (machine [Do (Ops.Yield (text "look"))]) of
              Yielding _ m -> case step m of
                Yielding msg _ -> msg @?= "look"
                other -> assertFailure ("expected Yielding, got " ++ show other)
              other -> assertFailure ("expected Yielding, got " ++ show other)

        , testCase "resumeYield advances past it, and the rest runs" $
            let m = machine [Do (Ops.Yield (text "look")), Do (Ops.Say (text "after"))]
             in case step m of
                  Yielding _ y -> case step (resumeYield y) of
                    Saying msg _ -> msg @?= "after"
                    other -> assertFailure ("expected Saying, got " ++ show other)
                  other -> assertFailure ("expected Yielding, got " ++ show other)

        , testCase "nothing else is yielding" $
            isYielding (machine [Do (Ops.Say (text "x"))]) @?= False
        ]
    , testGroup
        "load keeps a suspended tape and drops a dead one"
        [ testCase "a command in front of a yield keeps the rest of the program" $
            let m = machine [Do (Ops.Yield (text "look")), Do (Ops.Say (text "after"))]
             in case step m of
                  Yielding _ y ->
                    -- The typed line runs, falls back into the yield, and the
                    -- suspended program is still behind it.
                    case runTo (load [Do (Ops.Say (text "typed"))] y) of
                      Saying msg m' -> (msg, isYielding m') @?= ("typed", True)
                      other -> assertFailure (show other)
                  other -> assertFailure (show other)

        , -- **The regression.** A machine that is not yielding may still have
          -- instructions on @pc@ — one that halted does — and those are dead.
          testCase "but a tape that is not yielding is replaced, not prepended" $
            let stale = machine [Do (Ops.Say (text "stale"))]
             in case runTo (load [Do (Ops.Say (text "fresh"))] stale) of
                  Saying msg _ -> msg @?= "fresh"
                  other -> assertFailure (show other)

        , testCase "and its environment goes with it" $
            let stale = (machine []) { exec = (exec (machine [])) { env = [("x", VText "old")] } }
             in env (exec (load [] stale)) @?= []
        ]
    , testGroup
        "stepping"
        [ testCase "an empty program with an empty stack is finished" $
            case step (machine []) of
              Finished _ -> pure ()
              other      -> assertFailure ("expected Finished, got " ++ show other)
        , testCase "an empty program returns into the frame below it" $
            -- Nothing in phase 4 pushes a frame; this is the return case of
            -- §7.3, which phase 16 exercises for real.
            --
            -- **The frame is KEPT and marked, not popped** (MS4 phase 57).
            -- Popping it dismantled the stack under any 'Choice' standing on
            -- it, and a choice point relies on the frames below it for the
            -- rest of the continuation. Both frames have one lifetime now:
            -- entered, returned, stepped over ever after.
            let resumed = [Do (Ops.Say (text "back"))]
                entered = Call resumed [("x", VText "kept")] Nothing [] False
                m = (machine []) { exec = Exec [] [] [entered] [] }
             in case step m of
                  Continue m' ->
                    (pc (exec m'), envOf m', stack (exec m'))
                      @?= (resumed, [("x", VText "kept")], [entered { returned = True }])
                  other       -> assertFailure ("expected Continue, got " ++ show other)
        , testCase "Bind names the op's result" $
            case runTo (machine [Bind (Ops.PVar "s") Nothing (Ops.Concat (text "a") (text "b"))]) of
              Finished m -> envOf m @?= [("s", VText "ab")]
              other      -> assertFailure ("expected Finished, got " ++ show other)
        , testCase "Do discards it" $
            case runTo (machine [Do (Ops.Concat (text "a") (text "b"))]) of
              Finished m -> envOf m @?= []
              other      -> assertFailure ("expected Finished, got " ++ show other)
        , testCase "Ref reads a name bound earlier in the body" $
            case runTo (machine [Bind (Ops.PVar "s") Nothing (Ops.Concat (text "a") (text "b")), Bind (Ops.PVar "t") Nothing (Ops.Concat (Ref "s") (text "!"))]) of
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
            case runTo (machine [Bind (Ops.PVar "p") Nothing (Ops.Concat (text "who? ") (text "type A")), Bind (Ops.PVar "x") Nothing (Ops.Ask (Ref "p") AName)]) of
              Asking q _ -> q @?= Question "who? type A" AName
              other      -> assertFailure ("expected Asking, got " ++ show other)
        , testCase "the asking instruction stays at the head of pc" $
            -- What lets 'resumeAt' know the destination without a field in
            -- 'Machine' that is meaningful only sometimes (§7.5).
            case runTo (machine [Bind (Ops.PVar "x") Nothing (Ops.Ask (text "?") AName), Do (Ops.Say (Ref "x"))]) of
              Asking _ m -> (pc (exec m), isAsking m) @?= ([Bind (Ops.PVar "x") Nothing (Ops.Ask (text "?") AName), Do (Ops.Say (Ref "x"))], True)
              other      -> assertFailure ("expected Asking, got " ++ show other)
        , testCase "resumeAt binds the answer where the instruction named" $
            case runTo (machine [Bind (Ops.PVar "x") Nothing (Ops.Ask (text "?") AName), Do (Ops.Say (Ref "x"))]) of
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
            case runTo (machine [Bind (Ops.PVar "x") Nothing (Ops.Assume (text "A") (term type0))]) of
              Finished m -> case (lookup "x" (envOf m), devOf m) of
                (Just (VTerm (Free v)), Under (Assume w _ _) _) -> v @?= w
                other -> assertFailure ("wrong shape: " ++ show other)
              other -> assertFailure ("expected Finished, got " ++ show other)
        , testCase "the counter moves on with every mint" $
            case runTo (machine [Do (Ops.Assume (text "A") (term type0)), Do (Ops.Assume (text "B") (term type0))]) of
              Finished m -> names m @?= 3   -- the opening goal, then two binders
              other      -> assertFailure ("expected Finished, got " ++ show other)
        , testCase "setGoal replaces the focus and keeps the prefix" $
            case runTo (machine [Do (Ops.Assume (text "A") (term type0))]) of
              Finished m -> case fmap (flatten . development) (setGoal (Universe (levelOfNat 1)) m) of
                Right (Under Assume {} (Under (Claim _ _ ty) (Trailing (Free _)))) ->
                  ty @?= Universe (levelOfNat 1)
                other -> assertFailure ("wrong shape: " ++ show other)
              other -> assertFailure ("expected Finished, got " ++ show other)
        , testCase "setGoal standing at the root throws the whole chain away" $
            -- Not a corner case that arises in a session: 'newDevelopment' focuses the
            -- goal and 'assume' leaves the focus alone, so ':goal' lands on a
            -- hole. It pins the rule, which is one sentence — everything from
            -- the focus down is discarded (§4.0 F6).
            let (v, n) = fresh 0
                bare   = Machine (Exec [] [] [] []) (Development (enter (Under (Assume v (Ident "A") type0) (Trailing type0)))) [] emptyGlobals expectedBase [] [] [] [] rootScope n [] 0 NoUndischargeableTrust
             in case fmap (flatten . development) (setGoal type0 bare) of
                  Right (Under (Claim x _ _) (Trailing (Free y))) -> x @?= y
                  other -> assertFailure ("wrong shape: " ++ show other)
        , testCase "a move is an op, and it moves the focus" $
            -- The moves go through the machine because the cursor IS
            -- 'Development' (§7.2): moving the focus changes exactly what
            -- backtracks, which is §12 invariant 3's hazard.
            case runTo (machine [Do (Ops.Assume (text "A") (term type0)), Do Ops.Along]) of
              Finished m -> map nameOf (focusContext (development m)) @?= ["A", "goal"]
              other      -> assertFailure ("expected Finished, got " ++ show other)
        , testCase "and back undoes it, through the machine as well" $
            case runTo (machine [Do (Ops.Assume (text "A") (term type0)), Do Ops.Along, Do Ops.Back]) of
              Finished m -> map nameOf (focusContext (development m)) @?= ["A"]
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
              Finished m -> map nameOf (focusContext (development m)) @?= ["A", "h"]
              other      -> assertFailure ("expected Finished, got " ++ show other)
        ]
      -- **@intro@ over a binder's identity** (MS12 phase 353), his ruling of
      -- 2026-11-25: one @intro@, and the token that came with the word is
      -- adopted rather than minted over. The pattern that will hand it one is
      -- the landing after this; what is checked here is the op, which is
      -- self-contained.
    , testGroup
        "prim-lambda takes an identifier, and adopts the token in it"
        [ testCase "a word with no token mints one, which is what it always did" $
            case atPi [Do Ops.Attack, Do (Ops.IntroPi (Just (ident "a" Nothing)))] of
              Finished m ->
                (fmap snd (binderOf (devOf m)), fmap ((/= someToken) . fst) (binderOf (devOf m)))
                  @?= (Just (Ident "a"), Just True)
              other -> assertFailure ("expected Finished, got " ++ show other)

          -- The widening his ruling gave the literal set, at run time: the
          -- value really is a text, and it reads here as a word with no token.
        , testCase "and a written literal is that same word with no token" $
            case atPi [Do Ops.Attack, Do (Ops.IntroPi (Just (text "a")))] of
              Finished m -> fmap snd (binderOf (devOf m)) @?= Just (Ident "a")
              other -> assertFailure ("expected Finished, got " ++ show other)

          -- **The defect this closes.** A match opens the binder at a token and
          -- hands the rule a term pointing at it; a second mint here would
          -- leave the context holding a different binder with the same word
          -- printed on both, and @Eq@ on 'Thena.Core.Term.Core' compares tokens.
        , testCase "a token that came with the word is the binder's own" $
            case atPi [Do Ops.Attack, Do (Ops.IntroPi (Just (ident "a" (Just someToken)))) ] of
              Finished m -> binderOf (devOf m) @?= Just (someToken, Ident "a")
              other -> assertFailure ("expected Finished, got " ++ show other)

          -- The counter is the proof that nothing was minted for the binder:
          -- the hole @intro@ opens still takes one, so adopting is exactly one
          -- mint fewer than not adopting.
        , testCase "and adopting mints nothing, so the counter moves one less" $
            let counter is = case atPi [Do Ops.Attack, Do (Ops.IntroPi (Just is))] of
                  Finished m -> Just (names m)
                  _          -> Nothing
                minted = counter (ident "a" Nothing)
             in (minted, counter (ident "a" (Just someToken)))
                  @?= (minted, fmap (subtract 1) minted)

          -- **What the adopted token buys**: the development really holds that
          -- variable, so a term the rule is already carrying over it typechecks
          -- inside the binder. Before this phase the rule's term and the
          -- context named two different binders.
        , testCase "the adopted variable is in the context the binder opened" $
            case atPi
                   [ Do Ops.Attack
                   , Bind (Ops.PVar "h") Nothing
                       (Ops.IntroPi (Just (ident "a" (Just someToken))))
                   , Do (Ops.Goto (Ref "h"))
                   , Bind (Ops.PVar "s") Nothing (Ops.Typing (term (Free someToken)))
                   ] of
              Finished m -> lookup "s" (envOf m) @?= Just (VTerm type0)
              other -> assertFailure ("expected Finished, got " ++ show other)

          -- **A WORD THAT CAME OFF A TERM IS MADE FREE WHERE THE BINDER
          -- LANDS** — his ruling of 2026-11-26, @~2n5tn@, MS12 phase 355. The
          -- token is the test for provenance: nothing can attach one to a word
          -- a rule chose, so a token present means the word was read off a
          -- term, and a word the system found is free in the scope it lands in
          -- (his ruling of 2026-11-20, /THERE IS ONE NAME/, part one). With
          -- @a@ already in the context the binder lands as @a1@.
        , testCase "a word that came with a token is made free" $
            case taken [Do Ops.Attack, Do (Ops.IntroPi (Just (ident "a" (Just someToken))))] of
              Finished m -> binderWords (devOf m) @?= [Ident "a", Ident "a1"]
              other -> assertFailure ("expected Finished, got " ++ show other)

          -- **And a word the AUTHOR wrote is used as given, taken or not** (MS4
          -- phase 41f, reaffirmed 2026-11-20 part four, which made @rename@ the
          -- repair). This is the same call with the token dropped, so the only
          -- thing that moves is the provenance.
        , testCase "…and one with no token is used as written, taken or not" $
            case taken [Do Ops.Attack, Do (Ops.IntroPi (Just (ident "a" Nothing)))] of
              Finished m -> binderWords (devOf m) @?= [Ident "a", Ident "a"]
              other -> assertFailure ("expected Finished, got " ++ show other)

          -- A @Name@ variable at this position is a type error, so this is only
          -- reachable from a hand-built program — 'ExpectedIdent' is here for
          -- 'Thena.Errors.ExpectedName'\'s reason.
        , testCase "and a name is refused rather than rooted" $
            stuckWith ExpectedIdent
              (atPi [ Do Ops.Attack
                    , Do (Ops.IntroPi (Just (Lit (VName (rootName "a")))))
                    ])
        ]
    ]
  where
    nameOf e = case e of
      Hypothesis _ (Ident i) _   -> i
      Definition _ (Ident i) _ _ -> i
