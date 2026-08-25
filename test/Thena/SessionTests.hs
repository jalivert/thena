-- | Proof mode, and the life of a hole (§2.4, §7.7, thesis tables 2.7 and 2.8).
--
-- **Driven as scripts through 'loadSource'.** These are sequences of commands,
-- and phase 11 made a file exactly a sequence of commands — so a test here runs
-- through the same dispatch a user's typing does, and a change that breaks the
-- REPL breaks the suite. Building the states by hand instead would test the ops
-- and not the proof.
--
-- The one that matters is 'theTheorem': §9's phase-13 deliverable, a theorem
-- proved by hand and admitted to the global environment.
module Thena.SessionTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, assertFailure, testCase, (@?=))

import Thena.Core.Term (GlobalName (..))
import Thena.Declared (natDecl)
import Thena.Standard (withRules)
import Thena.Driver
  ( CommandError (..)
  , Loaded (..)
  , Proof (..)
  , Response (..)
  , Session (..)
  , Stop (..)
  , loadSource
  )
import Thena.Engine (Machine (..), ProofState)
import Thena.Errors (FailReason (..), MoveError (..))
import Thena.Global.Env (Definition (..), GlobalEnv, lookupDefinition)

tests :: TestTree
tests =
  testGroup
    "proof mode and the life of a hole (§2.4, tables 2.7/2.8)"
    [ testGroup "the deliverable" [theTheorem, theoremIsAGlobal]
    , testGroup "the hole ops" holeTests
    , testGroup "the session" sessionTests
    , testGroup "undo" undoTests
    ]

-- --------------------------------------------------------------------------
-- The deliverable
-- --------------------------------------------------------------------------

-- | §9: *prove a theorem by hand at the REPL.* No unification and no rule
-- engine — every step is one of thesis §2's own operations.
--
-- The shape of it: `attack` wraps the goal in a guess so that introducing
-- binders changes what the /guess/ builds rather than what the development
-- proves; two `intro`s walk the two Πs of @∀ (A : Type₀) -> A -> A@; the
-- innermost hole is filled with the assumption and solved; and solving the
-- outer guess makes the whole development pure, which is what `qed` needs.
--
-- **Two `solve`s and the moves between them are the user's, not `qed`'s** —
-- decided 2026-08-22, faithful to table 2.7 where `solve` is its own step.
identityProof :: [String]
identityProof =
  [ ":theorem id : ∀ (A : Type₀) -> A -> A"
  , "attack"
  , "intro"
  , "intro"
  -- Down into the guess and past the two binders it just made, to the hole.
  , "into"
  , "along"
  , "along"
  -- The second binder of @A -> A@ is written @_@, because a non-dependent Π
  -- carries that identifier (§2.6). It is an ordinary name and is typed as one.
  , "try _"
  , "solve"
  , "back"
  , "back"
  , "back"
  , "solve"
  , "qed"
  ]

theTheorem :: TestTree
theTheorem = testCase "a theorem proved by hand, start to ∎" $ do
  let l = run identityProof
  loadedError l @?= Nothing
  case reverse (loadedResponses l) of
    Proved g _ : _ -> g @?= GlobalName "id"
    other -> assertFailure ("did not end in qed: " ++ show (take 1 other))

theoremIsAGlobal :: TestTree
theoremIsAGlobal = testCase "and it is a global definition afterwards (§3.3.1)" $
  case lookupDefinition (GlobalName "id") (globalsAfter (run identityProof)) of
    Nothing -> assertFailure "id was not admitted"
    Just d  -> assertBool "admitted with no body" (definitionBody d /= definitionType d)

-- --------------------------------------------------------------------------
-- The hole ops
-- --------------------------------------------------------------------------

holeTests :: [TestTree]
holeTests =
  [ ok "attack turns a hole into a guess holding a hole" (goal ++ ["attack"])

    -- **These say @NoClauseMatched@ where they used to say the op's own
    -- reason, and that is phase 23b arriving.** A tactic word reaches a /rule/
    -- now, so whether it applies is decided by the rule's head before the body
    -- runs — Prolog's answer, and the same one @prove@ has always given. The
    -- cost is diagnostic: @intro@ at a guess whose type is neither a ∀ nor a
    -- @let@ said @NothingToIntroduce@ and now says only that no clause applies.
    -- On MS2's closeout list.
  , halts "and refuses a focus that is not a hole at all"
      (goal ++ ["along", "attack"]) (NoClauseMatched (GlobalName "attack") 0 [0])
  , halts "intro refuses a hole that has not been attacked"
      (goal ++ ["intro"]) (NoClauseMatched (GlobalName "intro") 0 [0, 0])
  , halts "and a guess whose type is neither a ∀ nor a let"
      (natGoal ++ ["attack", "intro"]) (NoClauseMatched (GlobalName "intro") 0 [0, 0])
  , ok "intro walks a Π"        (arrowGoal ++ ["attack", "intro"])
  , ok "and then the next one"  (arrowGoal ++ ["attack", "intro", "intro"])

  , ok "try attaches a guess"   (natGoal ++ ["attack", "into", "try zero"])
  , ok "and regret takes it off again"
      (natGoal ++ ["attack", "into", "try zero", "regret"])
  , halts "regret needs a guess" (natGoal ++ ["regret"])
      (NoClauseMatched (GlobalName "regret") 0 [0])

  , ok "solve commits a pure guess"
      (natGoal ++ ["attack", "into", "try zero", "solve"])
  , notYetPure "and refuses one that is not pure" (natGoal ++ ["attack", "solve"])

    -- @claim@ inserts above the focus and leaves it where it was, so reaching
    -- the new hole is a @back@ — the path gained a step and this pops it.
  , ok "abandon drops a hole nothing refers to"
      (natGoal ++ ["attack", "into", "claim spare : Nat", "back", "abandon"])
  , halts "and refuses one that is still referred to"
      (natGoal ++ ["abandon"]) (CannotMove StillReferenced)
  ]
  where
    goal      = [":theorem t : Type₀"]
    arrowGoal = [":theorem t : ∀ (A : Type₀) -> A -> A"]
    natGoal   = ["data " ++ natDecl, ":theorem t : Nat"]

-- --------------------------------------------------------------------------
-- The session
-- --------------------------------------------------------------------------

sessionTests :: [TestTree]
sessionTests =
  [ ok "a theorem may be started" [":theorem t : Type₀"]
  , rejects "but not two at once" [":theorem t : Type₀", ":theorem u : Type₀"]
      (AlreadyProving (GlobalName "t"))
  , rejects "and not under a name the environment already has"
      ["data " ++ natDecl, ":theorem Nat : Type₀"] (AlreadyDeclaredHere "Nat")
  , testCase "a statement that is not a type is refused" $
      case reverse (loadedResponses (run [":theorem t : zero"])) of
        Failed _   : _ -> pure ()
        IllTyped _ : _ -> pure ()
        other -> assertFailure ("accepted a non-type: " ++ show (take 1 other))

  , rejects "qed outside a proof" ["qed"] NotProving
  , rejects "suspend outside a proof" [":suspend"] NotProving
  , rejects "resume names a suspended proof" [":resume nope"] (NoSuchProof "nope")

  , ok "a proof suspends and resumes"
      [":theorem t : Type₀", ":suspend", ":resume t"]
  , testCase "suspending leaves it in the list, resuming takes it out" $ do
      countsAre [":theorem t : Type₀", ":suspend"] Nothing 1
      countsAre [":theorem t : Type₀", ":suspend", ":resume t"] (Just "t") 0

    -- §2.4's promise, and the reason a suspended proof stores its own half of
    -- the machine rather than the whole of it: the environment only grows, so
    -- what was declared while it was away is simply there on return.
  , testCase "a datatype declared during a suspension is in scope on resume" $ do
      let l = run
                [ ":theorem t : Type₀", ":suspend"
                , "data " ++ natDecl
                , ":resume t", "try Nat", "solve", "qed"
                ]
      loadedError l @?= Nothing
      assertBool "t was not admitted"
        (lookupDefinition (GlobalName "t") (globalsAfter l) /= Nothing)

  , testCase "abandoning drops it, suspending keeps it" $ do
      countsAre [":theorem t : Type₀", ":abandon"] Nothing 0
      countsAre [":theorem t : Type₀", ":suspend"] Nothing 1
  ]

-- --------------------------------------------------------------------------
-- Undo
-- --------------------------------------------------------------------------

undoTests :: [TestTree]
undoTests =
  [ rejects "outside a proof there is nothing to undo (§2.4)" [":undo"] NotProving
  , rejects "nor at the start of one" [":theorem t : Type₀", ":undo"] NothingToUndo

  , testCase "one line back is the state before that line" $
      sameDevelopment
        [":theorem t : Type₀", "attack", ":undo"]
        [":theorem t : Type₀"]

    -- The whole reason undo records only when the snapshot changed: otherwise
    -- a look would sit on the stack and :undo would have to be pressed twice.
  , testCase "a look does not go on the stack" $
      sameDevelopment
        [":theorem t : Type₀", "attack", ":show", ":where", ":undo"]
        [":theorem t : Type₀"]

  , testCase "and it goes back one line at a time" $
      sameDevelopment
        [arrow, "attack", "intro", "intro", ":undo", ":undo"]
        [arrow, "attack"]
  ]
  where
    arrow = ":theorem t : ∀ (A : Type₀) -> A -> A"

-- --------------------------------------------------------------------------
-- Helpers
-- --------------------------------------------------------------------------

run :: [String] -> Loaded
run = loadSource withRules . unlines

globalsAfter :: Loaded -> GlobalEnv
globalsAfter = globals . sessionMachine . loadedSession

developmentAfter :: Loaded -> ProofState
developmentAfter = proof . sessionMachine . loadedSession

ok :: String -> [String] -> TestTree
ok name ls = testCase name $ loadedError (run ls) @?= Nothing

halts :: String -> [String] -> FailReason -> TestTree
halts name ls why = testCase name $
  case reverse (loadedResponses (run ls)) of
    Ran _ (Halted r) : _ -> r @?= why
    other -> assertFailure ("expected a halt: " ++ show (take 1 other))

rejects :: String -> [String] -> CommandError -> TestTree
rejects name ls e = testCase name $
  case reverse (loadedResponses (run ls)) of
    Rejected e' : _ -> e' @?= e
    other -> assertFailure ("expected a rejection: " ++ show (take 1 other))

-- | Two scripts must leave the same development. What undo means.
sameDevelopment :: [String] -> [String] -> Assertion
sameDevelopment a b = developmentAfter (run a) @?= developmentAfter (run b)

countsAre :: [String] -> Maybe String -> Int -> Assertion
countsAre ls current suspended = do
  fmap (nameOf . proofName) (sessionProof s) @?= current
  length (sessionSuspended s) @?= suspended
  where
    s = loadedSession (run ls)
    nameOf (GlobalName x) = x

-- | The reason names a 'Thena.Errors.Position', and the 'Var' inside it is
-- minted by the run — so the constructor is what there is to assert on.
notYetPure :: String -> [String] -> TestTree
notYetPure name ls = testCase name $
  case reverse (loadedResponses (run ls)) of
    Ran _ (Halted (NotYetPure _)) : _ -> pure ()
    other -> assertFailure ("expected a purity failure: " ++ show (take 1 other))
