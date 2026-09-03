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

import Thena.Core.Term (GlobalName (..), Ident (..))
import Thena.Development.Component (Component (..))
import Thena.Development.Partial (Partial (..))
import Thena.Declared (natDecl)
import Thena.Standard (withRules)
import Thena.Driver
  ( CommandError (..)
  , Loaded (..)
  , Attempt (..)
  , currentAttempt
  , Response (..)
  , Session (..)
  , Stop (..)
  , loadSource
  )
import Thena.Engine (Machine (..), Development, flatten)
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
  , "try-core ⌜ _ ⌝"
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
    Proved g _ _ _ : _ -> g @?= GlobalName "id"
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

  , ok "try attaches a guess"             (natGoal ++ ["attack", "into", "try-core ⌜ zero ⌝"])

    -- **The two vocabularies, at the call site** (phase 38, come true at 41).
    -- Corners make an argument a core term and a bare word makes it a surface
    -- one — so a core tactic given a bare argument is handed the wrong kind of
    -- value and says so. Phase 38 refused it earlier, with a message; now the
    -- refusal is the op's, which is where every other operand kind is settled.
  , halts "a core tactic will not take a surface argument"
      (natGoal ++ ["attack", "into", "try-core zero"]) ExpectedTerm
    -- The corners subsume phase 23b's parenthesisation rule: an argument that
    -- is not a single atom needed parentheses, and inside corners it does not.
  , ok "and inside them an argument needs no parentheses"
      (natGoal ++ ["attack", "into", "try-core ⌜ succ zero ⌝"])
  , ok "and regret takes it off again"
      (natGoal ++ ["attack", "into", "try-core ⌜ zero ⌝", "regret"])
  , halts "regret needs a guess" (natGoal ++ ["regret"])
      (NoClauseMatched (GlobalName "regret") 0 [0])

  , ok "solve commits a pure guess"
      (natGoal ++ ["attack", "into", "try-core ⌜ zero ⌝", "solve"])
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
                , ":resume t", "try-core ⌜ Nat ⌝", "solve", "qed"
                ]
      loadedError l @?= Nothing
      assertBool "t was not admitted"
        (lookupDefinition (GlobalName "t") (globalsAfter l) /= Nothing)

  , testCase "abandoning drops it, suspending keeps it" $ do
      countsAre [":theorem t : Type₀", ":abandon"] Nothing 0
      countsAre [":theorem t : Type₀", ":suspend"] Nothing 1

    -- **A theorem starts a FRESH development** (phase 37, his ruling). Until
    -- then @:theorem@ went through the same @replaceFocus@ as @:goal@, which
    -- keeps everything above the focus, so a hole left open in the scratch
    -- development became part of the theorem's and @qed@ failed with a message
    -- about a hole the theorem never mentioned. Two tests, because the first
    -- one alone would pass for the wrong reason if @qed@ ever stopped checking
    -- purity.
  , testCase "a theorem starts a fresh development, not the one it found" $
      namesIn (developmentAfter (run ["claim spare : Type₀", ":theorem t : Type₀"]))
        @?= ["t"]
    -- **Elaboration, end to end** (MS4 phase 41e). The unit tests in
    -- "Thena.ElaborateTests" run against a synthetic cursor with no globals;
    -- these are the same clauses driven through the REPL with a datatype
    -- declared, which is the only way to reach the application case at all.
  , ok "an application elaborates and proves"
      [ "data " ++ natDecl
      , ":theorem t : Nat"
      , "elaborate (succ zero)"
      , "qed"
      ]
  , ok "a two-argument spine folds"
      [ "data " ++ natDecl
      , "data Pair : Type\8320 where { mk : Nat -> Nat -> Pair }"
      , ":theorem p : Pair"
      , "elaborate (mk zero (succ zero))"
      , "qed"
      ]
    -- **Nested lambdas were broken from the moment @here@ existed** and this is
    -- the test that would have caught it: the inner λ rebound the body-local
    -- name, so the outer @goto@ landed on the inner component.
  , ok "nested lambdas elaborate"
      [ ":theorem u : \8704 (A : Type\8320) (a : A) -> A"
      , "elaborate (\\ A -> \\ y -> y)"
      , "qed"
      ]
    -- **The structural cases** (MS4 phase 41f). A @∀@ is the one that needed
    -- the fifth component; the other three needed no new op at all.
  , ok "a ∀ elaborates and proves"
      [ ":theorem a : Type\8321"
      , "elaborate (forall (A : Type\8320) -> A)"
      , "qed"
      ]
    -- **A binder group nests**, one @quantify@ per Π: the domain hole is
    -- claimed outside the @attack@, where an earlier binder of the same group
    -- is not in scope.
  , ok "a ∀ with two binders nests"
      [ ":theorem a : Type\8321"
      , "elaborate (forall (A : Type\8320) (a : A) -> A)"
      , "qed"
      ]
  , ok "an arrow elaborates and proves"
      [ ":theorem a : Type\8321"
      , "elaborate (Type\8320 -> Type\8320)"
      , "qed"
      ]
  , ok "a let elaborates and proves"
      [ "data " ++ natDecl
      , ":theorem l : Nat"
      , "elaborate (let y = zero in y)"
      , "qed"
      ]
    -- **An annotated @let@ elaborates its annotation into the type hole
    -- first**, which is also what makes an application-valued @let@ work —
    -- see @ms4/CLOSEOUT.md@ 11.
  , ok "an annotated let takes an application value"
      [ "data " ++ natDecl
      , ":theorem l : Nat"
      , "elaborate (let y : Nat = succ zero in succ y)"
      , "qed"
      ]
    -- **A @let@ binds the name the user wrote**, which is what made phase
    -- 24c's taken-name check untenable: @y@ is a component name already.
  , ok "a let may shadow"
      [ "data " ++ natDecl
      , ":theorem l : Nat"
      , "elaborate (let y : Nat = zero in let y : Nat = succ y in y)"
      , "qed"
      ]
  , ok "an ascription elaborates and proves"
      [ "data " ++ natDecl
      , ":theorem s : Nat"
      , "elaborate (zero : Nat)"
      , "qed"
      ]
  , notOk "and an ascription that disagrees with the goal is refused"
      [ "data " ++ natDecl
      , ":theorem s : Nat"
      , "elaborate (zero : Type\8320)"
      ]
    -- **Cumulativity reaching elaboration** (MS4 phase 41g). Every one of
    -- these failed with /"Type₀ and Type₁ are different universes"/ until
    -- @fill@ stopped asking @unify@ for an equality it did not need. The
    -- second is the one with no surface workaround — a user cannot make @Nat@
    -- live at @Type₁@, which is what cumulativity is for.
  , ok "a term fits a universe above its own"
      [ "data " ++ natDecl
      , ":theorem u : Type\8321"
      , "elaborate Nat"
      , "qed"
      ]
  , ok "including as an argument to a parameter pinned above it"
      [ "data " ++ natDecl
      , "data Box (A : Type\8321) : Type\8321 where { box : A -> Box A }"
      , ":theorem u : Type\8321"
      , "elaborate (Box Nat)"
      , "qed"
      ]
  , ok "and in a lambda's body"
      [ "data " ++ natDecl
      , ":theorem u : Nat -> Type\8321"
      , "elaborate (\\ n -> Nat)"
      , "qed"
      ]
    -- **The degenerate flex-flex case** (MS4 phase 41g). An un-annotated
    -- @let@ whose value is an application is the only thing in the surface
    -- language that produces one: the value's @FILL@ equates the @let@'s type
    -- hole with the application's result hole, and both are bare.
  , ok "an un-annotated let takes an application value"
      [ "data " ++ natDecl
      , ":theorem l : Nat"
      , "elaborate (let y = succ zero in y)"
      , "qed"
      ]
  , ok "and may still shadow"
      [ "data " ++ natDecl
      , ":theorem l : Nat"
      , "elaborate (let y = zero in let y = succ y in y)"
      , "qed"
      ]
    -- **Cumulativity does not reach into an argument** (MS4 phase 41h). Both
    -- of these were ACCEPTED until then, and @:revalidate@ called the
    -- development valid — @ms4/CLOSEOUT.md@ 12. @F@ is opaque, so nothing
    -- relates @F Type₀@ to @F Type₁@.
  , notOk "a neutral spine's argument is not cumulative"
      [ "assume F : Type\8322 -> Type\8320"
      , "assume x : F Type\8320"
      , ":goal F Type\8321"
      , "try-core \8988 x \8989"
      ]
    -- The one that matters more, because datatype parameters are everywhere:
    -- the value inside is a @Type₀ -> Empty2@ and the type would have claimed
    -- its contents were a @Type₁ -> Empty2@.
  , notOk "nor is a datatype's parameter"
      [ "data Empty2 : Type\8320 where { }"
      , "data Fn (A : Type\8322) : Type\8322 where { fn : (A -> Empty2) -> Fn A }"
      , "assume g : Type\8320 -> Empty2"
      , ":goal Fn Type\8321"
      , "try-core \8988 fn Type\8320 g \8989"
      ]
    -- **`elim`, the last structural case** (MS4 phase 41i). No golden for
    -- these: an elaborated elimination's term runs to several hundred
    -- characters on one line, so a transcript of it records length rather than
    -- meaning.
  , ok "an elim elaborates and proves"
      [ "data " ++ natDecl
      , ":theorem e : Nat"
      , "elaborate (elim Nat () (\\ x -> Nat) (zero (\\ k ih -> succ ih)) () (succ zero))"
      , "qed"
      ]
    -- An indexed family, so the index group is not always empty and the
    -- telescope walk has to place them.
  , ok "including one with indices"
      [ "data " ++ natDecl
      , "data Ev : Nat -> Type\8320 where { evZero : Ev zero "
          ++ "; evSS : \8704 (n : Nat) (p : Ev n) -> Ev (succ (succ n)) }"
      , ":theorem e : Nat"
      , "elaborate (elim Ev () (\\ n p -> Nat) (zero (\\ n p ih -> succ ih)) (zero) evZero)"
      , "qed"
      ]
    -- **A dependent motive eliminates** (MS4 phase 54), and it could not
    -- between 49e and 54: giving the eliminator a wrapper made @elim@ an
    -- application, so its argument holes took the same names the nested
    -- application walk mints — and @goto@ by name then found the outer one.
    -- Every elim test before this used a constant motive, which is why nothing
    -- caught it.
  , ok "an elim with a dependent motive"
      [ "data " ++ natDecl
      , "declare data Id (A : Type\8320) : A -> A -> Type\8320 where "
          ++ "{ rfl : forall (a : A) -> Id A a a }"
      , "declare eqr : forall (n : Nat) -> Id Nat n n ; eqr = "
          ++ "\\ n -> elim Nat () (\\ k -> Id Nat k k) "
          ++ "((rfl Nat zero) (\\ k ih -> rfl Nat (succ k))) () n"
      ]
    -- **A datatype with parameters AND indices declares** (MS4 phase 54).
    -- @Box@ above has parameters and @Ev@ has indices; nothing had both, and
    -- both together is what the prelude\'s @Eq@ needs.
  , ok "a datatype with parameters and indices"
      [ "declare data Id (A : Type\8320) : A -> A -> Type\8320 where "
          ++ "{ rfl : forall (a : A) -> Id A a a }"
      , ":show Id"
      ]
    -- **A level-polymorphic datatype eliminates** (MS4 phase 49e), and until
    -- the eliminator got a wrapper it could not: @make-elim@ assembled the
    -- node with @[]@ for the datatype\'s level arguments, so the target\'s type
    -- was @Empty {0}@ and the node\'s was @Empty {ℓ}@ and the two were stuck.
    -- The wrapper writes its own prenex parameters there, exactly as a former
    -- wrapper does, so the question does not arise.
  , ok "a level-polymorphic datatype eliminates"
      [ "data " ++ natDecl
      , "data Empty : Type where { }"
      , ":theorem t : \8704 (e : Empty {0}) -> Nat"
      , "elaborate (\\ e -> elim Empty () (\\ x -> Nat) () () e)"
      , "qed"
      ]
    -- **The wrapper\'s name is checked for a clash like any other name a
    -- declaration introduces** (MS4 phase 49e) — 'Thena.Global.Declare.checkNames'.
  , notOk "a datatype whose eliminator's name is taken is refused"
      [ "data " ++ natDecl
      , "declare elimBool : Nat ; elimBool = zero"
      , "data Bool : Type\8320 where { true : Bool ; false : Bool }"
      ]
    -- The arity is checked against the declaration, so the message names the
    -- field group rather than a total.
  , notOk "and a method count that does not match the datatype is refused"
      [ "data " ++ natDecl
      , ":theorem e : Nat"
      , "elaborate (elim Nat () (\\ x -> Nat) (zero) () (succ zero))"
      ]
    -- **Surface declarations** (MS4 phase 42) — Brady's
    -- @NEW PROOF Type; E⟦t⟧; t' ← TERM; TTDECL (x : t')@, run as instructions
    -- over the development stack. The separators are written out because the
    -- driver reads one line; a file supplies them by layout at phase 43.
  , ok "a surface declaration elaborates and installs"
      [ "data " ++ natDecl
      , "declare one : Nat ; one = succ zero"
      , ":show one"
      ]
    -- **The declared type must be free of elaboration's scaffolding**, and
    -- this is the case that proves it rather than a nicety: @extract@ hands
    -- back @fill@'s @=@-bindings, 'Thena.Engine.introduce' reads a @Let@ as
    -- written and before reducing (phase 15, deliberately), so without the
    -- @whnf@ the body's λ opens a **definition** instead of a binder and the
    -- declaration fails with @Type₀ and n -> Nat cannot be made equal@.
  , ok "and a function declaration, whose body has a binder to open"
      [ "data " ++ natDecl
      , "declare idn : Nat -> Nat ; idn = \\ n -> n"
      , ":show idn"
      ]
  , ok "several declarations in one run"
      [ "data " ++ natDecl
      , "declare a : Nat ; a = zero ; b : Nat ; b = succ zero"
      , ":show b"
      ]
    -- Agda's and Haskell's rule: the equation follows its signature.
  , notOk "a signature with no equation is refused"
      [ "data " ++ natDecl
      , "declare lonely : Nat"
      ]
  , notOk "and so is a body that does not have the declared type"
      [ "data " ++ natDecl
      , "declare bad : Nat -> Nat ; bad = zero"
      ]
    -- **Datatypes in the surface** (MS4 phase 42b) — Brady's data rule: the
    -- datatype's own type first, /"so that the type is in scope when
    -- elaborating the constructor types"/, and being in scope is an assumption
    -- plus a β-step.
  , ok "a surface datatype declares"
      [ "declare data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
      , ":show Nat"
      ]
    -- And it is a real datatype: a theorem elaborates against it.
  , ok "and a theorem over it elaborates"
      [ "declare data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
      , "declare one : Nat ; one = succ zero"
      ]
    -- The parameters are shared between the datatype and its constructors,
    -- which is what the rename in @buildInductive@ is for.
  , ok "a parameterised one"
      [ "declare data Box (A : Type\8320) : Type\8320 where { box : A -> Box A }"
      , ":show Box"
      ]
    -- An indexed family, so the parameter/index split is exercised in both
    -- halves rather than only the empty one.
  , ok "and an indexed family"
      [ "declare data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
      , "declare data Ev : Nat -> Type\8320 where "
          ++ "{ evZero : Ev zero "
          ++ "; evSS : forall (n : Nat) -> Ev n -> Ev (succ (succ n)) }"
      , ":show Ev"
      ]
    -- The finished record goes through the same 'Thena.Global.Declare.declare'
    -- a written datatype does, so its checks all still apply.
  , notOk "and the declaration checker still refuses a bad one"
      [ "declare data Bad : Type\8320 where { wrap : Type\8320 -> Bad }" ]
    -- **Level arguments inserted at a use site** (MS4 phase 44, his ruling).
    -- Until then elaboration could reach no level-polymorphic global at all,
    -- so the whole prelude was out of its range.
  , ok "a polymorphic global is usable now"
      [ "data " ++ natDecl
      , "data Box (A : Type) : Type where { box : A -> Box A }"
      , ":theorem e : Type\8320"
      , "elaborate (Box Nat)"
      , "qed"
      ]
    -- **The dependent application rule.** @box@'s second domain is the first
    -- argument, which the binary rule's @f : A -> B@ cannot express — it failed
    -- with a scope violation, /"A3 is not bound before A1"/.
  , ok "and its constructor, whose domain is an earlier argument"
      [ "data " ++ natDecl
      , "data Box (A : Type) : Type where { box : A -> Box A }"
      , ":theorem e : Box {0} Nat"
      , "elaborate (box Nat zero)"
      , "qed"
      ]
    -- **A declaration may use an earlier one**, which is what a proof module
    -- is for and what this phase was ordered before 43 to make possible.
  , ok "a declaration may use an earlier one"
      [ "declare data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
      , "declare one : Nat ; one = succ zero"
      , "declare two : Nat ; two = succ one"
      ]
    -- The head's own type says how many arguments it takes, so too many is
    -- caught by the walk rather than by a later type error.
  , notOk "and too many arguments for the head is refused"
      [ "data " ++ natDecl
      , ":theorem e : Nat"
      , "elaborate (zero zero)"
      ]
    -- **A dependent signature can be declared at all** (MS4 phase 44b). It
    -- could not before: phase 42 cleared elaboration's @=@-bindings from the
    -- /head/ of a declared type and left the codomain alone, so @intro@ read a
    -- @Let@ one binder down and opened a definition where the λ belonged —
    -- @Type₀ and x -> A cannot be made equal@. Nothing to do with implicits;
    -- this is the explicit spelling.
  , ok "a dependent signature declares"
      [ "declare idty : forall (A : Type\8320) -> A -> A ; idty = \\ A x -> x" ]

    -- **Implicit arguments, inserted at a use site** — Brady's @EXPAND@.
  , ok "an implicit argument is inserted"
      [ "declare data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
      , "declare idty : forall {A : Type\8320} -> A -> A ; idty = \\ A x -> x"
      , "declare z : Nat ; z = idty zero"
      ]
    -- **And may be written by hand** — his requirement: /"They are allowed to
    -- be written explicitly too."/
  , ok "and may be written in braces instead"
      [ "declare data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
      , "declare idty : forall {A : Type\8320} -> A -> A ; idty = \\ A x -> x"
      , "declare z : Nat ; z = idty {Nat} zero"
      ]
    -- A brace the head has no position for is refused rather than falling
    -- through to a type error about a term the user did not mean to write.
  , notOk "but a brace the head has no position for is refused"
      [ "declare data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
      , "declare z : Nat ; z = succ {Nat} zero"
      ]
  , ok "so a hole left in the scratch cannot block qed"
      ["claim spare : Type₀", ":theorem t : Type₁", "try-core ⌜ Type₀ ⌝", "solve", "qed"]
  ]

-- --------------------------------------------------------------------------
-- Undo
-- --------------------------------------------------------------------------

undoTests :: [TestTree]
undoTests =
  [ -- **@:undo@ does not need a proof** (phase 34, his ruling). It used to
    -- answer @NotProving@ here, which was the wrong end of the stick: a
    -- 'Snapshot' is @(Exec, Development)@ and 'Machine' always has both, so the
    -- top level has a development to take a line back in.
    rejects "with nothing typed yet there is nothing to undo" [":undo"] NothingToUndo
  , testCase "a line at the top level is taken back like any other" $
      sameDevelopment ["assume A : Type₀", ":undo"] []
  , rejects "and then there is nothing left" ["assume A : Type₀", ":undo", ":undo"]
      NothingToUndo

    -- Every proof boundary starts a fresh history, which is what keeps @:undo@
    -- away from a @qed@ it could not honestly reverse: admitting writes to
    -- @globals@, which no 'Snapshot' carries.
  , rejects "nor at the start of one" [":theorem t : Type₀", ":undo"] NothingToUndo
  , rejects "a theorem does not let you undo back past it"
      ["assume A : Type₀", ":theorem t : Type₀", ":undo"] NothingToUndo
  , rejects "and abandoning one does not either"
      [":theorem t : Type₀", "attack", ":abandon", ":undo"] NothingToUndo

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

developmentAfter :: Loaded -> Development
developmentAfter = development . sessionMachine . loadedSession

ok :: String -> [String] -> TestTree
ok name ls = testCase name $ loadedError (run ls) @?= Nothing

-- | The other side of 'ok': the script must not get through cleanly.
notOk :: String -> [String] -> TestTree
notOk name ls = testCase name $
  case loadedError (run ls) of
    Nothing -> assertFailure "expected a failure"
    Just _  -> pure ()

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

-- | Every component the development binds, in order, by the name it shows.
namesIn :: Development -> [String]
namesIn = go . flatten
  where
    go p = case p of
      Trailing _     -> []
      Pending _ rest -> go rest
      Under c rest   -> nameOfComponent c : go rest
    nameOfComponent c = case c of
      Assume _ (Ident i) _   -> i
      Define _ (Ident i) _ _ -> i
      Claim  _ (Ident i) _   -> i
      Guess  _ (Ident i) _ _ -> i
      Quantify _ (Ident i) _ -> i

countsAre :: [String] -> Maybe String -> Int -> Assertion
countsAre ls current suspended = do
  fmap (nameOf . attemptName) (currentAttempt s) @?= current
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
