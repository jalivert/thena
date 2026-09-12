-- | Inference over @instral@ (MS5 phase 66c).
--
-- **Two halves, and the first is the phase's done-when**: the shipped rule base
-- infers, and what it infers is written out here so a later phase cannot move a
-- signature quietly. The second half is one file per way a program can be
-- ill typed, written as a rule-base file and loaded — which is how a user meets
-- it, and which also checks that a bad program is refused rather than installed.
module Thena.InstralInferTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Term (GlobalName (..))
import Thena.Driver (Response (..), Session, loadRuleBases, newSession)
import Thena.Engine (Machine (..))
import Thena.Driver (Session (..))
import Thena.Instral.Infer
  ( InstralTypeError (..)
  , Site (..)
  , inferProgram
  , renderInstralTypeError
  )
import Thena.Instral.Type (Signature (..), Ty (..), renderSignature)
import Thena.Ops (Instr (..), Op (..), Operand (..), Rule (..), Value (..))
import Thena.Rules (RuleBase (..))
import Thena.Standard (expectedStandard)

tests :: TestTree
tests =
  testGroup
    "Thena.Instral.Infer"
    [ shippedBase
    , illTyped
    , wellTyped
    , blockReturn
    ]

-- --------------------------------------------------------------------------
-- The done-when
-- --------------------------------------------------------------------------

-- | **The shipped base must infer cleanly** — MS5.md names this as the real
-- constraint on how precise the signatures of phase 66b could be. It did, first
-- time and without a signature being loosened for it.
shippedBase :: TestTree
shippedBase =
  testGroup
    "the shipped base"
    [ testCase "infers with no errors at all" $
        map renderInstralTypeError (snd (inferProgram expectedStandard)) @?= []

      -- **Written out, not counted.** A signature is what a later phase will
      -- move by accident, and every one of these was inferred from the head
      -- predicates and the ops in the body — nothing is annotated.
    , testCase "and these are the signatures it works out" $
        [ n ++ "/" ++ show a ++ " : " ++ renderSignature s
        | ((GlobalName n, a), s) <- fst (inferProgram expectedStandard)
        ]
          @?= [ "attack/0 : ()"
              , "try-core/1 : Core -> ()"
              , "abandon/0 : ()"
              , "intro/0 : ()"
              , "solve/0 : ()"
              , "regret/0 : ()"
              , "eliminate-core/1 : Core -> ()"
              , "prove/0 : ()"
              , "fill/1 : Core -> ()"
              , "unify-refine-core/1 : Core -> ()"
              , "apply-core/1 : Core -> ()"
              , "claim/1 : Core -> ()"
              , "assume/1 : Core -> ()"
              , "quantify/1 : Core -> ()"
              , "elaborate/1 : Surface -> ()"
              , "intro-binders/1 : Surface -> ()"
              , "enter-binders/1 : Surface -> ()"
              , "spine-arguments/3 : Core -> Core -> Surface -> ()"
              ]

      -- **`elaborate`'s parameter is a Surface term and nothing says so.** It
      -- comes from the head predicates: sixteen clauses each ask a
      -- `surface-is-…` question of `t`, and 'Thena.Rules.testTypes' is what
      -- makes that an answer.
    , testCase "elaborate's parameter came from its head" $
        lookup (GlobalName "elaborate", 1) (fst (inferProgram expectedStandard))
          @?= Just (Signature [TSurface] Nothing)

      -- **`spine-arguments` has no head test about `h` or `f` at all.** Their
      -- types come from the body — `goto h` wants a Core, `apply-next f n` wants
      -- one — which is the part a head-only reading would miss.
    , testCase "and spine-arguments' came from its body" $
        lookup (GlobalName "spine-arguments", 3) (fst (inferProgram expectedStandard))
          @?= Just (Signature [TCore, TCore, TSurface] Nothing)
    ]

-- --------------------------------------------------------------------------
-- One file per way to be wrong
-- --------------------------------------------------------------------------

illTyped :: TestTree
illTyped =
  testGroup
    "a program that does not type check is refused"
    [ -- The head says Surface, the body hands it to an op that wants Core.
      refused "a parameter used at two types"
        "rule bad t :- when (surface-is-name t) then prim-try t"
        [ Clash (InBody (GlobalName "bad") 0) TCore TSurface ]

      -- **A literal is checked against the position**, and this one cannot be.
      -- 'Thena.Ops.Try' wants a term; a number is not one. **This is one of the
      -- three checks phase 63 and 64 had to defer to run time** — MS5.md says
      -- phase 66 is where it comes back, and this is it.
    , refused "a numeral where a term was wanted"
        "rule bad :- then prim-try 3"
        [ Clash (InBody (GlobalName "bad") 0) TCore TInt ]

      -- …and its text sibling, which is a separate error because a string
      -- literal is the one whose type the position decides.
    , refused "a string where a term was wanted"
        "rule bad :- then prim-try \"x\""
        [ TextNotTextual (InBody (GlobalName "bad") 0) TCore ]

      -- **The other deferred check** (MS5 phase 63): binding a call to a rule
      -- no clause of which returns. It was 'Thena.Errors.NothingReturned' at run
      -- time because /which clauses a name has is not known when a body is
      -- read/ — true of reading one body, false of a pass over every base.
    , refused "binding a call that cannot return"
        "rule mute t :- then say \"nothing\"\n\
        \rule bad t :- then x = mute t ; say x"
        [ BindsNothing (InBody (GlobalName "bad") 0) (GlobalName "mute") ]

      -- **Two clauses of one name must agree**, because they are one callable:
      -- dispatch chooses between them at run time and a caller cannot know
      -- which it got.
    , refused "two clauses that disagree about a parameter"
        "rule two t :- when (surface-is-name t) then prim-prove\n\
        \rule two t :- then prim-try t"
        [ Clash (InBody (GlobalName "two") 0) TCore TSurface ]

      -- A list is homogeneous, and the literal is where that is enforced.
    , refused "a list of two different things"
        "rule bad :- then prim-try [3, 'c']"
        [ Clash (InBody (GlobalName "bad") 0) TInt TChar
        , Clash (InBody (GlobalName "bad") 0) TCore (TList TInt)
        ]
    ]
  where
    refused label src want =
      testCase label $ case load src of
        BasesIllTyped errs -> errs @?= want
        other -> assertFailure ("expected a refusal, got " ++ show other)

-- --------------------------------------------------------------------------
-- …and one per thing that must keep working
-- --------------------------------------------------------------------------

wellTyped :: TestTree
wellTyped =
  testGroup
    "a program that does type check is installed"
    [ -- **A string literal is accepted where a Name is wanted** — his ruling,
      -- 2026-09-12 — so nothing about how a rule is written changes.
      accepted "a string literal at a name position"
        "rule fine :- then n = fresh-name \"h\" ; goto-named n"

      -- …and the coercion is what carries it the other way, because @n@ here is
      -- a variable and not a literal.
    , accepted "and name-text carries a name back to a string"
        "rule fine :- then n = fresh-name \"h\" ; t = name-text n ; say t"

      -- **A call to a name nothing defines constrains nothing**, and is not an
      -- error: §8 has always allowed it and the machine reports it when the
      -- search finds no clause.
    , accepted "a call to a rule nothing defines"
        "rule fine t :- then call nowhere t"

      -- **A rule used before it is written**, which is why the pass is over the
      -- whole program rather than one rule at a time.
    , accepted "a call to a rule written below it"
        "rule fine t :- then call later t\n\
        \rule later t :- when (surface-is-name t) then prove"

      -- **Recursion**: the one that would not terminate if a rule's signature
      -- had to be known before its own body was walked.
      -- **An op word at another arity is a call to a RULE** (MS5 phase 62b,
      -- his ruling), so this constrains nothing rather than being a wrong-arity
      -- error. It is the one of the three checks deferred at 62b–64 that this
      -- pass does NOT bring back; see @ms5/CLOSEOUT.md@.
    , accepted "an op word at the wrong arity is an unknown call"
        "rule fine t :- then call say t t"

    , accepted "a rule that calls itself"
        "rule walk t :- when (surface-is-app t) then a = app-tail t ; call walk a"

    ]
  where
    accepted label src =
      testCase label $ case load src of
        BasesLoaded bs -> length (concatMap baseRules bs) > 0 @?= True
        other -> assertFailure ("expected a load, got " ++ show other)

-- | **A @return@ inside a @do@ block ends the BLOCK, not the rule** — see
-- "Thena.Engine"'s 'Thena.Ops.Return' case, which says so in as many words.
--
-- Built by hand rather than written in a file, because a block is never spelled
-- in a rule body ('Thena.Ops.Block'): it comes from a surface @do { … }@. So
-- @blocked@ returns nothing, and binding a call to it is refused. Read the
-- other way — the block's @return@ taken for the rule's — this would type check
-- and then fail at run time with 'Thena.Errors.NothingReturned'.
blockReturn :: TestTree
blockReturn =
  testCase "a return inside a block is not the rule's" $
    let blocked = Rule (GlobalName "blocked") [] []
                    [Do (Block [Do (Return (Lit (VText "x")))])]
        bad     = Rule (GlobalName "bad") [] []
                    [Bind "y" (Call (GlobalName "blocked") []), Do (Say (Ref "y"))]
     in snd (inferProgram [blocked, bad])
          @?= [BindsNothing (InBody (GlobalName "bad") 0) (GlobalName "blocked")]

load :: String -> Response
load src = snd (loadRuleBases newSession [("t.thena.rules", "rule base t where\n" ++ src)])

-- Keeps @-Wall@ quiet about the imports the helpers above do not reach.
_unusedSessionShape :: Session -> [RuleBase]
_unusedSessionShape = rules . sessionMachine
