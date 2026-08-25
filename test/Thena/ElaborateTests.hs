-- | Elaboration's identifier case, and @Call@ (§8, phase 17b).
--
-- Three separable things are checked here, and the third is the one that could
-- not be checked any other way.
--
--   * **The partition.** A hint changes which rules are eligible
--     ('Thena.Ops.usesHint'), so @:matches@ and @:matches ‹hint›@ are two
--     questions with two answers.
--   * **@Call@.** Arity, what binds in the callee, and what survives the
--     return — the first supplier of a rule's parameters (§8).
--   * **'Thena.Engine.entryEnv'.** Backtracking into a /second/ hint rule must
--     enter it with @hint@ still bound. MS1's own base cannot reach that state,
--     because the partition leaves exactly one hint rule and a hinted dispatch
--     is therefore always deterministic. So it is reached here with a synthetic
--     pair, in "Thena.DispatchTests"' own style — the alternative was a field
--     that is correct only by argument.
module Thena.ElaborateTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Term (Core (..), GlobalName (..), Ident (..), Level (..), Var, fresh)
import Thena.Development.Component (Component (..))
import Thena.Development.Cursor (Cursor, enter, focus)
import qualified Thena.Development.Cursor as Cursor
import Thena.Development.Partial (Partial (..))
import Thena.Engine
  ( Exec (..)
  , Machine (..)
  , Outcome (..)
  , ProofState (..)
  , load
  , step
  )
import Thena.Errors (FailReason (..), ResolveError (..), SyntaxError (..))
import Thena.Global.Env (emptyGlobals)
import Thena.Ops
  ( Instr (..)
  , Operand (..)
  , Rule (..)
  , Test (..)
  , Value (..)
  , hintName
  , usesHint
  )
import qualified Thena.Ops as Ops
import Thena.Rules
  ( RuleBase
  , RuleError (..)
  , RuleIter
  , allRules
  , dispatch
  , matches
  , next
  , ruleBase
  , validate
  )
import Thena.Standard (expectedBase)
import Thena.Syntax.Concrete (Raw (..))

tests :: TestTree
tests =
  testGroup
    "elaboration"
    [ partitionTests
    , opTests
    , entryEnvTests
    ]

-- --------------------------------------------------------------------------
-- Fixtures
-- --------------------------------------------------------------------------

type0 :: Core
type0 = Universe (Level 0)

goalVar, hypVar :: Var
goalVar = fst (fresh 0)
hypVar  = fst (fresh 1)

-- | @λ a : Type₀ . ? goal : Type₀ . goal@, focused on the hole — so there is
-- something in scope at the focus for a hint to name (§4.5).
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

nameHint, appHint :: Maybe Raw
nameHint = Just (RawName "a")
appHint  = Just (RawApp (RawName "a") (RawName "a"))

machine :: [RuleBase] -> [Instr] -> Machine
machine base is =
  load is (Machine (Exec [] [] []) (ProofState hole) emptyGlobals base 1000)

runOut :: Machine -> ([String], Either FailReason Machine)
runOut m = case step m of
  Continue m'       -> runOut m'
  Saying msg m'     -> let (ms, r) = runOut m' in (msg : ms, r)
  Declaring _ m'    -> runOut m'
  Certifying _ _ m' -> runOut m'
  Asking _ m'       -> ([], Right m')
  Finished m'       -> ([], Right m')
  Stuck r _         -> ([], Left r)

named :: [RuleBase] -> Maybe Raw -> [String]
named base hint =
  [ n | Rule (GlobalName n) _ _ _ <- drain (matches base emptyGlobals hole hint) ]

drain :: RuleIter -> [Rule]
drain it = case next it of
  Nothing        -> []
  Just (r, rest) -> r : drain rest

-- --------------------------------------------------------------------------
-- The partition (§8, decided 2026-08-23)
-- --------------------------------------------------------------------------

partitionTests :: TestTree
partitionTests =
  testGroup
    "a hint partitions the base"
    [ testCase "exactly one shipped rule asks about the hint" $
        [ n | r@(Rule (GlobalName n) _ _ _) <- allRules expectedBase, usesHint r ]
          @?= ["elab-var"]

      -- Unchanged from phase 16, and that is the point: the partition costs the
      -- hintless question nothing.
    , testCase "with no hint, the hintless half" $
        named expectedBase Nothing @?= ["attack", "try", "abandon", "eliminate"]

    , testCase "with a name, only the elaboration rule" $
        named expectedBase nameHint @?= ["elab-var"]

      -- The head is shallow (§8): it asks what the tree /is/, not whether it
      -- resolves. An application is not a name, so nothing in the hinted half
      -- matches and there is no hintless half to fall through to.
    , testCase "with a compound hint, nothing" $
        named expectedBase appHint @?= []

      -- @elab-var@ takes no parameters, so unlike @try@ and @eliminate@ it is
      -- something the engine can actually run.
    , testCase "and dispatch can run it" $
        [ n | Rule (GlobalName n) _ _ _ <-
                drain (dispatch expectedBase emptyGlobals hole nameHint) ]
          @?= ["elab-var"]

      -- Without this line 'elabVar' fails its own load-time check: @hint@ is a
      -- Ref that no Bind introduces (§7.2's validation pass).
    , testCase "a hint rule may read `hint` without binding it" $
        concatMap validate (allRules expectedBase) @?= []

    , testCase "and a rule with no hint head may not" $
        validate (Rule (GlobalName "sneaky") [] [FocusIsHole]
                    [Bind "t" (Ops.Resolve (Ref hintName))])
          @?= [UnboundInRule (GlobalName "sneaky") 0 hintName]
    ]

-- --------------------------------------------------------------------------
-- parse, resolve, and the hint's arrival
-- --------------------------------------------------------------------------

opTests :: TestTree
opTests =
  testGroup
    "parse and resolve"
    [ testCase "parse produces a surface tree" $
        bound "h" [Bind "h" (Ops.Parse (Lit (VText "a")))]
          @?= Just (VSurface (RawName "a"))

    , testCase "a stray character is a lex failure, not a crash" $
        case failed [Bind "h" (Ops.Parse (Lit (VText "%")))] of
          CannotRead (LexFailed _) -> pure ()
          other -> assertFailure ("expected a lex failure, got " ++ show other)

    , testCase "and an unfinished term is a parse failure" $
        case failed [Bind "h" (Ops.Parse (Lit (VText "\\ (x : Type\8320) ->")))] of
          CannotRead (ParseFailed _) -> pure ()
          other -> assertFailure ("expected a parse failure, got " ++ show other)

      -- Γ at the focus (§4.5) is what an identifier must be in scope in.
    , testCase "resolve reads a name in the context at the focus" $
        bound "t" [Bind "t" (Ops.Resolve (Lit (VSurface (RawName "a"))))]
          @?= Just (VTerm (Trailing (Free hypVar)))

    , testCase "a name that is not there says so" $
        failed [Bind "t" (Ops.Resolve (Lit (VSurface (RawName "b"))))]
          @?= CannotRead (ResolveFailed (NotInScope "b"))

    , testCase "resolve wants a tree, not a term" $
        failed [Bind "t" (Ops.Resolve (Lit (VTerm (Trailing type0))))]
          @?= ExpectedSurface

      -- The deliverable, in one assertion: the hint arrives bound to @hint@
      -- (§8's one magic name), @elab-var@ resolves it, calls @try@ with it and
      -- commits — so the hole ends up defined as the variable that was named.
    , testCase "prove with a name elaborates it" $
        case snd (runOut (machine expectedBase
                    [Do (Ops.Prove (Just (Lit (VSurface (RawName "a")))))])) of
          Left r  -> assertFailure ("did not elaborate: " ++ show r)
          Right m -> case focus (cursor (proof m)) of
            Cursor.OnComponent (Define _ _ v _) -> v @?= Free hypVar
            other -> assertFailure ("expected a definition, got " ++ show other)
    ]
  where
    bound n is = case snd (runOut (machine [] is)) of
      Right m -> lookup n (Thena.Engine.env (exec m))
      Left r  -> error ("the program did not run: " ++ show r)

    failed is = case snd (runOut (machine [] is)) of
      Left r  -> r
      Right _ -> error "expected the program to fail"

isGuess :: Machine -> Bool
isGuess m = case focus (cursor (proof m)) of
  Cursor.OnComponent (Guess {}) -> True
  _                             -> False

-- --------------------------------------------------------------------------
-- entryEnv: the hint survives backtracking (§7.3, phase 17b)
-- --------------------------------------------------------------------------

entryEnvTests :: TestTree
entryEnvTests =
  testGroup
    "a hint outlives the alternative that was tried first"
    [ -- Two hint rules, so the peek really builds a Choice; the first fails
      -- after the hint has been read, and the second must still be able to
      -- read it. Without 'entryEnv' this is UnboundInBody "hint".
      testCase "the second alternative still sees it" $ do
        let (msgs, out) = runOut (machine [ruleBase "test" Nothing "" [elabFails, elabWorks]]
                                    [Do (Ops.Prove (Just (Lit (VSurface (RawName "a")))))])
        msgs @?= ["chose 1000: elab-fails", "backtracking to 1000: elab-works"]
        case out of
          Left r  -> assertFailure ("expected the second to succeed, got " ++ show r)
          Right m -> isGuess m @?= True
    ]
  where
    -- Reads the hint, attaches it, then fails: @solve@ wants a guess whose body
    -- is pure and this one is a variable — so it is the /second/ instruction
    -- that fails, after the environment has been used.
    elabFails =
      Rule (GlobalName "elab-fails") [] [FocusIsHole, HintIsName]
        [ Bind "t" (Ops.Resolve (Ref hintName))
        , Do Ops.Regret
        ]

    elabWorks =
      Rule (GlobalName "elab-works") [] [FocusIsHole, HintIsName]
        [ Bind "t" (Ops.Resolve (Ref hintName))
        , Do (Ops.Try (Ref "t"))
        ]
