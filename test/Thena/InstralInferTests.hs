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
import Thena.Driver (Response (..), RuleFileError (..), Session, command, loadRuleBases, newSession)
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
import Thena.Instral.Grammar (GrammarError (..))
import Thena.Rules (RuleBase (..), RuleError (..))
import Thena.Standard (expectedStandard)

tests :: TestTree
tests =
  testGroup
    "Thena.Instral.Infer"
    [ shippedBase
    , illTyped
    , wellTyped
    , blockReturn
    , annotations
    , badSignatures
    , functions
    , lambdas
    , objectLanguages
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
        map renderInstralTypeError (snd (inferProgram [] expectedStandard)) @?= []

      -- **Written out, not counted.** A signature is what a later phase will
      -- move by accident, and every one of these was inferred from the head
      -- predicates and the ops in the body — nothing is annotated.
    , testCase "and these are the signatures it works out" $
        [ n ++ "/" ++ show a ++ " : " ++ renderSignature s
        | ((GlobalName n, a), s) <- fst (inferProgram [] expectedStandard)
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
        lookup (GlobalName "elaborate", 1) (fst (inferProgram [] expectedStandard))
          @?= Just (Signature [TSurface] Nothing)

      -- **`spine-arguments` has no head test about `h` or `f` at all.** Their
      -- types come from the body — `goto h` wants a Core, `apply-next f n` wants
      -- one — which is the part a head-only reading would miss.
    , testCase "and spine-arguments' came from its body" $
        lookup (GlobalName "spine-arguments", 3) (fst (inferProgram [] expectedStandard))
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
     in snd (inferProgram [] [blocked, bad])
          @?= [BindsNothing (InBody (GlobalName "bad") 0) (GlobalName "blocked")]

-- --------------------------------------------------------------------------
-- Declared signatures (MS5 phase 67)
-- --------------------------------------------------------------------------

-- | **What an annotation buys, and it is a capability rather than a comment.**
--
-- Phase 67 was originally scoped as a signature pre-pass so that bodies could be
-- parsed; §6.0.1's tags removed that need and phase 66c demonstrated it — the
-- whole shipped base infers with no annotations at all. What is left is these
-- two: a rule usable at two types, and a wrong promise reported where it was
-- made.
annotations :: TestTree
annotations =
  testGroup
    "a declared signature"
    [ -- **The payoff.** @ignore@ is used at a Name and at a Core. Inferred, the
      -- second use is a clash (@ms5\/CLOSEOUT.md@ 8 — one recursive group, one
      -- type); declared, every use gets its own copy of the scheme.
      testCase "makes a rule usable at two types" $
        case load polymorphic of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)

    , testCase "…and without it the same base is refused" $
        case load (unlines (drop 1 (lines polymorphic))) of
          BasesIllTyped [Clash _ TName TCore] -> pure ()
          other -> assertFailure ("expected a clash, got " ++ show other)

      -- **His requirement: a wrong annotation reports against the
      -- DECLARATION.** The signature promises any type; the body hands the
      -- parameter to an op that wants a term, so the promise is broken and it is
      -- the promise that is at fault, not the instruction.
    , testCase "that promises more than the body delivers is refused at the signature" $
        load "signature f : a -> ()\nrule f x :- then prim-try x"
          @?= BasesIllTyped
                [AnnotationTooGeneral (InSignature (GlobalName "f") 1) TCore]

      -- …and a signature that is simply the wrong type is still reported in the
      -- body, which is §6.5(a) — the author's own rule, local and clear.
    , testCase "that names the wrong type is refused in the body" $
        load "signature f : Core -> ()\nrule f x :- when (surface-is-name x) then prove"
          @?= BasesIllTyped [Clash (InHead (GlobalName "f") 0) TSurface TCore]

      -- A signature is a claim about a callable, so a claim nothing answers is
      -- a mistake — most likely a typo or a changed arity.
    , testCase "for a callable nothing defines is refused" $
        load "signature nobody : Core -> ()\nrule f :- then prove"
          @?= BasesIllTyped [SignatureUnanswered (GlobalName "nobody") 1]

      -- **The arity is the arrow chain's**, so this signature is about @f@ at
      -- one argument and says nothing about the @f@ of none — a different
      -- callable, which dispatch already treats as one.
    , testCase "is about one arity only" $
        case load "signature f : Core -> ()\nrule f x :- then prim-try x\nrule f :- then prove" of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)
    ]
  where
    polymorphic =
      "signature ignore : a -> ()\n\
      \rule ignore x :- then say \"ignored\"\n\
      \rule usesName :- then n = fresh-name \"h\" ; ignore n\n\
      \rule usesTerm :- then h = here ; ignore h\n"

-- | A signature that does not resolve is refused when the FILE is read, before
-- anything is inferred — it is a question one file can answer.
badSignatures :: TestTree
badSignatures =
  testGroup
    "a signature that does not resolve"
    [ refused "an unknown type"      "signature f : Trm -> ()"   (UnknownType "f" "Trm")
    , refused "a constructor's arity" "signature f : List -> ()" (TypeArity "f" "List" 1 0)
    , refused "a variable applied"   "signature f : a Core -> ()" (TypeVariableApplied "f" "a")
    , refused "() as an argument"    "signature f : () -> ()"    (UnitInsideAType "f")
    , refused "two for one callable"
        "signature f : Core -> ()\nsignature f : Surface -> ()"
        (DuplicateSignature "f" 1)
    ]
  where
    refused label src want =
      testCase label $ case load (src ++ "\nrule f x :- then prove") of
        RuleFileRefused _ (RuleIllFormed es) | want `elem` es -> pure ()
        other -> assertFailure ("expected " ++ show want ++ ", got " ++ show other)

-- --------------------------------------------------------------------------
-- Global functions (MS5 phase 68a)
-- --------------------------------------------------------------------------

-- | **A function is a rule with one clause and no head** — his §1.1 — so what
-- is checked here is mostly that nothing had to be added to make that true.
functions :: TestTree
functions =
  testGroup
    "a global function"
    [ -- **No keyword** — his choice, 2026-09-12. @rule@ and @signature@ are
      -- keywords, so a declaration beginning with a plain word can only be this.
      testCase "is declared with no keyword and is callable" $
        said "rule go :- then m = twice \"a\" ; say m" @?= Just "aa"

      -- **The boundary is column 1** — his ruling, 2026-09-12. Without it the
      -- @g@ below is parsed as another operand of @say@, silently, because
      -- Happy shifts.
    , testCase "does not get swallowed by the declaration above it" $
        said "rule go :- then m = twice \"b\" ; say m" @?= Just "bb"

      -- …and the rule that buys it: an indented declaration is a parse error
      -- now, where it was accepted (and misparsed) before.
    , testCase "and an indented declaration is refused" $
        case loadRaw "rule base i where\n  rule f :- then prove\n" of
          RuleFileRefused _ (RuleSyntaxError _) -> pure ()
          other -> assertFailure ("expected a syntax error, got " ++ show other)

      -- **It is not offered as a tactic.** A function has no head, and a
      -- headless rule matches everywhere — so if functions were kept with the
      -- rules, @prove@ would run them. 'Thena.Rules.baseFunctions' is why they
      -- are a separate list.
    , testCase "is not listed among the rules" $
        case load "twice x = concat x x\nrule go :- then prove" of
          BasesLoaded bs -> map (map ruleNameOf . baseRules) bs @?= [["go"]]
          other -> assertFailure ("expected a load, got " ++ show other)

      -- …and its type is inferred like any rule's, because it is one.
    , testCase "is inferred like a rule" $
        case load "twice x = concat x x" of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)

      -- **A function must produce.** Refused where it is written rather than by
      -- 'Thena.Rules.validate', which would report it against a binding the
      -- author never wrote.
    , testCase "that leaves nothing is refused" $
        case load "f x = say \"hi\"" of
          RuleFileRefused _ (RuleIllFormed es)
            | FunctionLeavesNothing "f" `elem` es -> pure ()
          other -> assertFailure ("expected a refusal, got " ++ show other)

      -- **@x = ‹value›@, which `ms5/CLOSEOUT.md` 3 owed this phase** (his
      -- ruling, 2026-09-12). It resolves to 'Thena.Ops.Value', an op with a word
      -- and no written form.
    , testCase "and a literal can be bound to a name at last" $
        case load "rule go :- then p = (1, true) ; l = [1, 2, 3] ; n = 42 ; prove" of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)
    ]
  where
    ruleNameOf r = case ruleName r of GlobalName n -> n

    said line = case snd (command (fst (loadRuleBases newSession
                  [("f.thena.rules", "rule base f where\ntwice x = concat x x\n" ++ line ++ "\n")]))
                  "go") of
      Ran msgs _ -> case reverse msgs of { m : _ -> Just m; [] -> Nothing }
      other      -> error ("expected Ran, got " ++ show other)

    loadRaw src = snd (loadRuleBases newSession [("i.thena.rules", src)])

-- --------------------------------------------------------------------------
-- Lambdas (MS5 phase 68b)
-- --------------------------------------------------------------------------

-- | **A lambda is a function without a name** — §1.1 read the other way — so it
-- compiles the way a function does and is applied through the frame a call
-- already pushes.
lambdas :: TestTree
lambdas =
  testGroup
    "a lambda"
    [ -- Bound to a local and applied. **This is the shadowing his ruling
      -- bought**: @k \"z\"@ is an application of the local, not a call to a rule
      -- called @k@.
      testCase "is bound to a local and applied" $
        said "rule go :- then k = \\ s -> concat \"<\" s ; n = k \"z\" ; say n"
          @?= Just "<z"

      -- **Higher order, with the signature that says so.** @(a -> b)@ in a
      -- signature was refused by name until this phase.
    , testCase "is passed to a function that takes one" $
        said "signature onTwice : (String -> String) -> String -> String\n\
             \onTwice f x = f (f x)\n\
             \rule go :- then d = \\ s -> concat s s ; m = onTwice d \"a\" ; say m"
          @?= Just "aaaa"

      -- **Parenthesised in an argument**, like every other compound one.
    , testCase "takes parentheses in an argument position" $
        said "signature once : (String -> String) -> String\n\
             \once f = f \"q\"\n\
             \rule go :- then m = once (\\ s -> concat s s) ; say m"
          @?= Just "qq"

      -- **N-ary and not curried** — a function of one is not a function of two,
      -- whatever the types, because dispatch is on arity.
    , testCase "applied at the wrong arity is refused" $
        case load "rule go :- then d = \\ s -> concat s s ; m = d \"a\" \"b\" ; say m" of
          BasesIllTyped (Clash _ _ _ : _) -> pure ()
          other -> assertFailure ("expected a clash, got " ++ show other)

      -- Its body must produce, for a function's reason and with the same
      -- message.
    , testCase "whose body leaves nothing is refused" $
        case load "rule go :- then d = \\ s -> prim-try s ; prove" of
          RuleFileRefused _ (RuleIllFormed es)
            | FunctionLeavesNothing "λ" `elem` es -> pure ()
          other -> assertFailure ("expected a refusal, got " ++ show other)

      -- **A function type is writable in a signature now**, which it was not
      -- before this phase — @TypeIsAFunction@ refused it and is deleted.
    , testCase "and a function type is writable in a signature" $
        case load "signature f : (a -> b) -> a -> b\nf g x = g x" of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)
    ]
  where
    said src = case snd (command (fst (loadRuleBases newSession
                 [("l.thena.rules", "rule base l where\n" ++ src ++ "\n")])) "go") of
      Ran msgs _ -> case reverse msgs of { m : _ -> Just m; [] -> Nothing }
      other      -> error ("expected Ran, got " ++ show other)

-- --------------------------------------------------------------------------
-- Object languages (MS5 phase 69)
-- --------------------------------------------------------------------------

-- | **The seam §6.6 asks for**: a declared language gets an opaque @instral@
-- type, a tag that is its only introduction form, and a one-way coercion to
-- Surface.
objectLanguages :: TestTree
objectLanguages =
  testGroup
    "a declared object language"
    [ -- The whole path: declared, tagged, parsed by the generated parser, and
      -- used at the type the declaration generated.
      testCase "is a type, a tag and a coercion" $
        case load (tm ++ "signature asSurface : Tm -> Surface\n\
                         \asSurface t = surface-of t\n\
                         \rule go :- then t = Tm`(x y)` ; s = asSurface t ; prove") of
          BasesLoaded _ -> pure ()
          other -> assertFailure ("expected a load, got " ++ show other)

      -- **The brand is the point.** Without the coercion an object term is not a
      -- Surface term as far as the type system is concerned, which is what makes
      -- the tag worth having.
    , testCase "is not a Surface term until it is coerced" $
        load (tm ++ "signature want : Surface -> ()\n\
                    \rule want s :- then prove\n\
                    \rule go :- then t = Tm`(x y)` ; want t")
          @?= BasesIllTyped [Clash (InBody (GlobalName "go") 1) TSurface (TObject "Tm")]

      -- **The generated parser is a real parser**, and a term it cannot read is
      -- a syntax error naming the tag — arriving at load, with every other one
      -- (§6.0.1).
    , testCase "reports a term its grammar cannot read" $
        case load (tm ++ "rule go :- then t = Tm`(x y` ; prove") of
          RuleFileRefused _ (RuleIllFormed (BadRegion _ _ "Tm" _ : _)) -> pure ()
          other -> assertFailure ("expected a region error, got " ++ show other)

      -- The three shapes the generated parser could not run, refused when the
      -- grammar is declared rather than when it is used.
    , refusedGrammar "left recursion"
        "language Tm where { loop : Tm \"x\" }"
        (BadGrammar "Tm" (LeftRecursive "Tm" "loop"))
    , refusedGrammar "an empty production"
        "language Tm where { nothing : }"
        (BadGrammar "Tm" (EmptyProduction "Tm" "nothing"))
    , refusedGrammar "a terminal that is not one token"
        "language Tm where { var : \"a b\" }"
        (BadGrammar "Tm" (TerminalDoesNotLex "Tm" "a b"))
    , refusedGrammar "a word that is neither the language nor name"
        "language Tm where { var : nonsense }"
        (BadGrammarItem "Tm" "nonsense")
    ]
  where
    tm = "language Tm where { var : name ; app : \"(\" Tm Tm \")\" }\n"

    refusedGrammar label src want =
      testCase label $ case load (src ++ "\nrule go :- then prove") of
        RuleFileRefused _ (RuleIllFormed es) | want `elem` es -> pure ()
        other -> assertFailure ("expected " ++ show want ++ ", got " ++ show other)

load :: String -> Response
load src = snd (loadRuleBases newSession [("t.thena.rules", "rule base t where\n" ++ src)])

-- Keeps @-Wall@ quiet about the imports the helpers above do not reach.
_unusedSessionShape :: Session -> [RuleBase]
_unusedSessionShape = rules . sessionMachine
