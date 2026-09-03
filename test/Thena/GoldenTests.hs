-- | Whole REPL sessions, compared against a recorded transcript.
--
-- §9: golden transcripts are the natural regression test for a tool whose
-- interface /is/ the REPL, and they start at this phase because this is the
-- first phase where a session has a history. They go through 'transcript',
-- which is the interactive loop's own dispatch with the reading and the writing
-- taken out — so a transcript cannot pass while the REPL is broken.
--
-- Regenerate with @cabal test --test-options=--accept@ after reading the diff.
module Thena.GoldenTests (tests) where

import Data.ByteString.Builder (stringUtf8, toLazyByteString)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString)

import Thena.Driver (newSession)
import Thena.Repl (loadStandardRules, transcriptFrom)

tests :: TestTree
tests =
  testGroup
    "transcripts"
    [ script
        "assume"
        [ "assume A : Type₀"
        , ":goal A -> A"
        , ":show"
        , "assume : A"
        , "x"
        , ":show"
        , ":core A"
        , ":quit"
        ]
    , script
        "typing"
        [ "data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
        , ":infer \8988 succ zero \8989"
        , ":infer \8988 \\ (x : Nat) -> x \8989"
        , ":infer \8988 \8704 (A : Type\8320) -> A \8989"
        , ":convert succ \8799 \\ (n : Nat) -> succ n"
        , ":convert Type\8320 \8799 Type\8321"
        , ":convert succ zero \8799 succ (succ zero)"
        , ":infer \8988 zero zero \8989"
        , ":infer \8988 elim Nat () (\\ (_ : Nat) -> Nat) (zero succ) () (succ zero) \8989"
        , "claim h : Nat"
        , "cross type"
        , ":infer"
        , "back"
        , "back"
        , ":infer"
        , "data Big : Type\8320 where { wrap : Type\8320 -> Big }"
        , ":quit"
        ]
      -- The elimination rule, seen (phase 10). The same datatype at two levels
      -- is §3.7's universe trick: one rule per universe the motive is valued
      -- in, and no constant that could have held either.
    , script
        "eliminators"
        [ "data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
        , "data Fin : Nat -> Type\8320 \
          \where { fz : \8704 (n : Nat) -> Fin (succ n) \
          \; fs : \8704 (n : Nat) (i : Fin n) -> Fin (succ n) }"
        , "data Empty : Type where { }"
        , ":elim Nat"
        , ":elim Nat Type\8321"
        , ":elim Fin"
        , ":elim Empty"
        , ":whnf elim Fin () (\\ (n : Nat) (i : Fin n) -> Nat) \
          \((\\ (n : Nat) -> zero) (\\ (n : Nat) (i : Fin n) (ih : Nat) -> succ ih)) \
          \((succ (succ zero))) (fs (succ zero) (fz zero))"
        , ":elim Foo"
        , ":elim Nat Nat"
        , ":elim"
        , ":show FinElim"
        , ":quit"
        ]
      -- The kernel (phase 12). @:revalidate@ at any time; @certify@ once the
      -- development is pure, which phase 9's @unify@ is enough to reach.
    , script
        "kernel"
        [ "data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
        , ":revalidate"
        , ":goal Nat"
        , ":revalidate"
        , ":extract"
        , "certify Nat"
        , "along"
        , "unify goal \8799 zero"
        , ":extract"
        , "certify Nat"
        , "certify Nat -> Nat"
        , ":revalidate"
        , "back"
        , "assume A : Type\8320"
        , ":extract"
        , "certify Nat"
        , ":quit"
        ]
      -- §9's phase-14 deliverable: @noConfusion@ for MS1's own target language,
      -- printed, computed and certified. The script declares the prelude types
      -- the generator writes its table out of, because these transcripts run
      -- prelude-free (phase 11) — which is also why the @Nat@ line here gets no
      -- note and the @Vec@ line does.
    , script
        "noconfusion"
        ( preludeLines ++
        [ "data Term : Type\8320 \
          \where { true : Term ; false : Term \
          \; ifthen : Term -> Term -> Term -> Term \
          \; zero : Term ; succ : Term -> Term }"
        , ":show noConfusionTerm"
        , ":whnf NoConfusionTerm true true"
        , ":whnf NoConfusionTerm true (succ zero)"
        , ":whnf NoConfusionTerm (succ true) (succ zero)"
        , ":whnf NoConfusionTerm (ifthen true zero zero) (ifthen false zero zero)"
          -- And the deliverable's second half: a proof that goes /through/ the
          -- generated lemma, extracted and put to the kernel. This is
          -- injectivity of @succ@, which is what a matching branch of the
          -- determinacy proof needs.
        , ":goal \8704 (a : Term) (b : Term) -> Eq {0} Term (succ a) (succ b) -> Eq {0} Term a b"
        , "along"
        , "unify goal \8799 \\ (a : Term) (b : Term) (e : Eq {0} Term (succ a) (succ b)) \
          \-> noConfusionTerm (succ a) (succ b) e"
        , ":extract"
        , "certify \8704 (a : Term) (b : Term) -> Eq {0} Term (succ a) (succ b) -> Eq {0} Term a b"
        , "back"
        , "data Nat : Type\8320 where { zero' : Nat ; succ' : Nat -> Nat }"
        , "data Vec (A : Type\8320) : Nat -> Type\8320 \
          \where { nil : Vec A zero' \
          \; cons : \8704 (n : Nat) (a : A) (as : Vec A n) -> Vec A (succ' n) }"
        , ":show noConfusionVec"
        , ":quit"
        ])
      -- §9's phase-13 deliverable: a theorem proved by hand, and admitted.
      -- Every step is one of thesis §2's own operations — no unification and
      -- no rule engine.
    , script
        "proof"
        [ ":theorem id : \8704 (A : Type\8320) -> A -> A"
        , ":show"
        , "attack"
        , "intro"
        , "intro"
        , ":show"
        , "into"
        , "along"
        , "along"
        , ":where"
        , "try-core ⌜ _ ⌝"
        , "solve"
        , "back"
        , "back"
        , "back"
        , "solve"
        , ":show"
        , "qed"
        , ":show id"
        , ":proofs"
        , ":quit"
        ]
      -- Phase 15's deliverable: what could be done next, at each shape of
      -- focus. A look and nothing more — no body runs (§7.6).
    , script
        "matching"
        [ ":rules"
        , ":matches"
        , "attack"
        , ":matches"
          -- Nothing applies in the core fragment: every head this phase has
          -- asks about a component, and a core subterm is not one.
        , "cross type"
        , ":matches"
        , "back"
        , ":theorem id : \8704 (A : Type\8320) -> A -> A"
        , ":matches"
        , "attack"
        , ":matches"
        , "intro"
        , "into"
        , "along"
        , ":where"
        , ":matches"
        , ":abandon"
          -- Section 8's stated cost, live: the head asks about the guess's own
          -- type, which is still a Pi, while the hole @intro@ reaches is at
          -- Type0. The rule is offered, runs, and fails in its body.
        , ":theorem c : \8704 (A : Type\8320) -> Type\8320"
        , "attack"
        , "intro"
        , ":matches"
        , "intro"
        , ":abandon"
          -- Table 2.8's other introduction. Its head reads the type as
          -- written, because whnf delta-reduces a term-level let away (5.1) --
          -- the bug this phase found in 'Thena.Engine.introduce'.
        , ":theorem l : let x = Type\8320 : Type\8321 in x"
        , "attack"
        , ":matches"
        , "intro"
        , ":show"
        , ":quit"
        ]
      -- Phase 16's deliverable: a goal dispatched one way, then the other on
      -- request, five commands later, because the frame stack persists (7.7).
    , script
        "backtracking"
        [ ":theorem id : \8704 (A : Type\8320) -> A -> A"
        , "attack"
          -- Three rules match a guess; two are nullary, so dispatch is a real
          -- choice and the machine says which it took.
        , ":matches"
        , "prove"
        , ":show"
        , ":choices"
          -- Deterministic commands in between. They push no frame (the peek),
          -- and they do not disturb the one that is there.
        , "into"
        , "along"
        , ":where"
        , "back"
        , "back"
        , ":choices"
          -- retry takes one ALTERNATIVE, not one command: it pops back past
          -- everything since, restores the development, and runs the next one.
          -- @solve@ then fails on its own and the engine backtracks again
          -- inside the same command, which is why both lines are printed.
        , "retry"
        , ":show"
        , ":choices"
        , "retry"
        , ":quit"
        ]
      -- Elaboration (phase 17b). @prove ‹hint›@ is the same engine and the same
      -- frames as @prove@; the only difference is that a hint is present (§8),
      -- and the hint partitions the base, so @:matches@ and @:matches ‹hint›@
      -- are two questions with two answers.
      --
      -- The identifier case is the whole of MS1's elaboration, and its rule
      -- reaches @try@ through @Call@ — the first thing to supply a rule's
      -- parameters (§8).
      -- The structural cases (MS4 phase 41f), and the fifth component under
      -- them. Driven three ways on purpose: @quantify@ by hand, so the op is
      -- visible without an elaborator around it; @:dev@, so the concrete
      -- syntax a ∀-binder reads and prints is on the record; and the four
      -- surface forms end to end.
      -- Surface declarations (MS4 phase 42) — Brady's @NEW PROOF@ run as
      -- instructions over the development stack. The separators are written
      -- out because the driver reads one line at a time; a file supplies them
      -- by layout at phase 43.
    , script
        "declarations"
        [ "data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
        , "declare one : Nat ; one = succ zero"
          -- The declared TYPE is clean; the body is not, and that is
          -- @ms4/CLOSEOUT.md@ 8 rather than this phase's.
        , ":show one"
        , "declare idn : Nat -> Nat ; idn = \\ n -> n"
        , ":show idn"
          -- **A second declaration using the first**, which is what a proof
          -- module is for and what 44-before-43 was ordered for. It failed
          -- until MS4 phase 44 — @one@ had generalised over body-only level
          -- metas and a use could not write them — and now it does not: the
          -- level arguments are inserted, and @one@ has no such metas to begin
          -- with, because a name-headed application no longer claims
          -- @A : Type ?ℓ@ and @B : Type ?ℓ@ of its own.
        , "declare two : Nat ; two = succ one"
          -- Agda's and Haskell's pairing rule.
        , "declare lonely : Nat"
        , "declare stray = zero"
          -- The body must have the type the signature declares.
        , "declare bad : Nat -> Nat ; bad = zero"
          -- **A datatype in the surface** (MS4 phase 42b). It goes through the
          -- same @declare@ a written one does, so @:show@ prints it the same
          -- way — which is the check that the record was assembled right.
        , "declare data Bool : Type\8320 where { true : Bool ; false : Bool }"
        , ":show Bool"
        , "declare data Box (A : Type\8320) : Type\8320 where { box : A -> Box A }"
        , ":show Box"
          -- **Implicit arguments** (MS4 phase 44b). The signature's braces are
          -- shown back; the body is a core term and is not hidden, because the
          -- core has no implicits at all.
        , "declare idty : forall {A : Type\8320} -> A -> A ; idty = \\ A x -> x"
        , ":show idty"
          -- Inserted at a use, and writable by hand — the two must mean the
          -- same thing.
        , "declare z : Nat ; z = idty zero"
        , ":show z"
        , "declare z2 : Nat ; z2 = idty {Nat} zero"
        , ":show z2"
          -- @push-development@ and @pop-development@ are **ops, not commands**,
          -- so they are exercised from "Thena.ReadTests" rather than here — a
          -- bare word at the REPL is a command or a rule call, and they are
          -- neither.
        , ":quit"
        ]
    , script
        "structural"
        [ ":theorem byhand : Type\8321"
        , "attack"
          -- @quantify@ is @intro@'s twin: it acts at the guess and claims the
          -- codomain at its own universe, which is why the Π's level is not
          -- pinned to the codomain's.
        , "quantify A : Type\8320"
        , ":show"
        , "into"
        , "along"
        , "try-core \8988 Type\8320 \8989"
        , "solve"
        , "back"
        , "back"
        , "solve"
        , ":extract"
        , "qed"
          -- A leading ∀ run is components, exactly as a leading λ run is; the
          -- corners are the escape that keeps a trailing Π writable.
        , ":dev \8704 (A : Type\8320) -> A"
        , ":dev \8988 \8704 (A : Type\8320) -> A \8989"
        , ":theorem pi : Type\8321"
        , "elaborate (forall (A : Type\8320) -> A)"
        , ":show"
        , "qed"
        , ":theorem arr : Type\8321"
        , "elaborate (Type\8320 -> Type\8320)"
        , "qed"
        , "data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
        , ":theorem lt : Nat"
        , "elaborate (let y : Nat = zero in succ y)"
        , ":show"
        , "qed"
        , ":theorem asc : Nat"
        , "elaborate (zero : Nat)"
        , "qed"
          -- Refused, and the message names the ∀ rather than the term.
        , ":theorem bad : Nat"
        , "attack"
        , "quantify A : Type\8320"
        , ":quit"
        ]
    , script
        "elaboration"
        [ ":theorem const : \8704 (A : Type\8320) (a : A) -> A"
        , "attack"
        , "intro"
        , "intro"
        , "into"
        , "along"
        , "along"
        , ":where"
          -- Two questions, two answers: the second lists only what could
          -- elaborate that hint.
        , ":matches"
        , "elaborate a"
        , ":show"
          -- **One more @back@ than before phase 41e.** A leaf now goes through
          -- @FILL@ — park the term in a definition, unify, attach — so the
          -- development gains a component and the walk out is one step longer.
        , "back"
        , "back"
        , "back"
        , "back"
        , "solve"
        , "qed"
        , ":show const"
          -- A hint that is not in scope: @resolve@ fails in the body, which is
          -- an ordinary op failure (§7.3), and the head could not have known —
          -- it is shallow on purpose (§8).
        , ":theorem again : \8704 (A : Type\8320) (a : A) -> A"
        , "attack"
        , "intro"
        , "intro"
        , "into"
        , "along"
        , "along"
        , "elaborate b"
          -- A hint that is not an identifier does not match at all: no rule
          -- with a hint head passes, and there is nothing else in the hinted
          -- half of the base.
        , "elaborate (a a)"
        , ":abandon"
          -- The instruction language, seen: stepping shows the driver's own
          -- two-instruction program, the callee's body, and the return.
        , ":theorem shown : \8704 (A : Type\8320) (a : A) -> A"
        , "attack"
        , "intro"
        , "intro"
        , "into"
        , "along"
        , "along"
        , ":step on"
        , "elaborate a"
        , ":step"
        , ":step"
        , ":step"
        , ":step"
        , ":step"
        , ":step off"
        , ":quit"
        ]
      -- Suspension, undo, and the promise that the environment only grows.
    , script
        "session"
        [ "data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
        , ":theorem two : Nat"
        , "attack"
        , ":show"
        , ":undo"
        , ":undo"
        , ":suspend"
        , ":proofs"
        , "data Bool : Type\8320 where { true : Bool ; false : Bool }"
        , ":theorem one : Nat"
        , "try-core ⌜ zero ⌝"
        , "solve"
        , "qed"
        , ":resume two"
        , ":core true"
        , "try-core ⌜ succ (succ zero) ⌝"
        , "solve"
        , "qed"
        , ":show two"
        , ":undo"
        , ":quit"
        ]
    , script
        "unification"
        [ "data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
        , "claim h : Nat"
        , "unify succ h \8799 succ (succ zero)"
        , ":show"
        , "claim f : Nat -> Nat"
        , "unify \\ (x : Nat) -> f x \8799 \\ (x : Nat) -> succ x"
        , ":show"
          -- **Two bare holes now SOLVE, where this recorded a parking until
          -- MS4 phase 41g.** It is the degenerate flex-flex case: no spine on
          -- either side, so Miller's pattern condition holds vacuously and the
          -- equation has a most general unifier. The direction is forced by
          -- the chain — @a@ is declared first, so @b := a@ — and the @:show@
          -- below is where that is visible.
          --
          -- Flex-flex **with** a spine still defers; that is Huet's case and
          -- §6.1 keeps it.
        , "claim a : Nat"
        , "claim b : Nat"
        , "unify a \8799 b"
        , ":show"
          -- And the solution composes: @b@ δ-unfolds to @a@, so this equation
          -- is @a ≟ zero@ and solves @a@ alone. Before 41g both were solved
          -- here at once, by the parked constraint waking.
        , "unify b \8799 zero"
        , ":show"
        , "claim c : Nat"
        , "unify c \8799 succ c"
        , "unify zero \8799 succ zero"
        , ":quit"
        ]
    , script
        "stepping"
        [ ":step on"
        , "assume A : Type\8320"
        , ":step"
        , ":step"
        , ":step off"
        , "claim h : Type\8320"
        , ":show"
          -- **Phase 25c**: the whole of @unify-refine@\'s body, one instruction
          -- at a time. Seven ops, two of them binary and one infix, so this
          -- pins both halves of what @renderOp@ now derives — the word from
          -- @opKeyword@, and the operands in the order @operandsOf@ lists them.
          -- A swapped pair in that list would show up here and nowhere else.
        , ":goal Type\8320"
        , ":step on"
        , "unify-refine-core ⌜ A ⌝"
        , ":step"
        , ":step"
        , ":step"
        , ":step"
        , ":step"
        , ":step off"
        , ":show"
        ]
    , script
        "navigation"
        [ "assume A : Type₀"
        , "assume B : A -> Type₀"
        , ":goal forall (x : A) -> B x"
        , ":where"
        , "cross type"
        , ":where"
        , "cod"
        , "arg"
        , ":where"
        , "back"
        , "back"
        , "back"
        , ":show"
        , "along"
        , ":show"
        , "back"
        , "into"
        , "fun"
        , ":quit"
        ]
    , script
        "declaring"
        [ "data Nat : Type₀ where { zero : Nat ; succ : Nat -> Nat }"
        , ":show Nat"
        , ":show succ"
        , ":show zero"
        , ":core succ (succ zero)"
        , "data Vec (A : Type₀) : Nat -> Type₀ where { nil : Vec A zero ; cons : ∀ (n : Nat) (a : A) (as : Vec A n) -> Vec A (succ n) }"
        , ":show Vec"
        , ":show cons"
        , "data Empty : Type where { }"
        , ":show Empty"
        , "data Nat : Type₀ where { z : Nat }"
        , "data Ordinal : Type₀ where { sup : (Nat -> Ordinal) -> Ordinal }"
        , "data Bad : Type₀ where { bad : (Bad -> Bad) -> Bad }"
        , ":show nowhere"
        , "assume n : Nat"
        , ":show"
        , ":quit"
        ]
    , script
        "reduction"
        [ "data Nat : Type₀ where { zero : Nat ; succ : Nat -> Nat }"
        , ":whnf succ zero"
        -- committing reduction, and the orphaning case (§4.7): claim two
        -- holes, put a redex mentioning the first in the second's type, then
        -- navigate to it — 'back' pops the step 'claim' pushed, landing on
        -- the component itself rather than the trailing goal it left alone.
        , "claim h : Nat"
        , "claim g : (\\ (_ : Nat) -> Nat) h"
        , "back"
        , "cross type"
        , ":where"
        , ":whnf"
        , "reduce"
        , ":where"
        , ":show"
        , "back"
        , "back"
        , "claim n : Nat"
        -- a hand-written elim: stuck on a neutral target, so it round-trips
        -- through the printer unreduced rather than firing ι.
        , ":whnf elim Nat () (\\ (_ : Nat) -> Nat) (zero succ) () n"
        -- arity mistakes, one per field (§2.6's resolve-time shape check).
        , ":whnf elim Nat () (\\ (_ : Nat) -> Nat) (zero) () n"
        , ":whnf elim Nat (n) (\\ (_ : Nat) -> Nat) (zero succ) () n"
        , ":whnf elim Nat () (\\ (_ : Nat) -> Nat) (zero succ) (n) n"
        , ":whnf elim NotADatatype () (\\ (_ : Nat) -> Nat) () () n"
        , ":quit"
        ]
      -- §3.7's elimination tactic (phase 17). Plain induction over @Nat@: the
      -- generalisation the motive performs is abstracting the /target/, and
      -- @plus n zero@ is the case that needs it — @plus zero n@ would not,
      -- because the recursion is on the first argument and it computes.
      --
      -- @congSucc@ is the same tactic at an /indexed/ family: eliminating an
      -- equation constrains both of @Eq@'s indices, and the use site discharges
      -- them reflexively.
      --
      -- Prelude-free like every transcript here (phase 11), so @Eq@ is declared
      -- rather than loaded.
    , script
        "induction"
        [ "data Eq (A : Type) : A -> A -> Type where { refl : ∀ (a : A) -> Eq A a a }"
        , "data Nat : Type₀ where { zero : Nat ; succ : Nat -> Nat }"
        , ":theorem plus : Nat -> Nat -> Nat"
        , "try-core ⌜ \\ (n : Nat) (m : Nat) -> elim Nat () (\\ (t : Nat) -> Nat) (m (\\ (k : Nat) (ih : Nat) -> succ ih)) () n ⌝"
        , "solve"
        , "qed"
        , ":whnf plus (succ zero) (succ zero)"
        , ":theorem congSucc : ∀ (a : Nat) (b : Nat) (e : Eq {0} Nat a b) -> Eq {0} Nat (succ a) (succ b)"
        , "attack"
        , "intro"
        , "intro"
        , "intro"
        , "into"
        , "along"
        , "along"
        , "along"
        , "eliminate-core ⌜ e ⌝"
        , "back"
        , ":where"
        , "try-core ⌜ \\ (c : Nat) -> refl {0} Nat (succ c) ⌝"
        , "solve"
        , "along"
        , "solve"
        , "back"
        , "back"
        , "back"
        , "back"
        , "back"
        , "solve"
        , "qed"
        , ":theorem plusZero : ∀ (n : Nat) -> Eq {0} Nat (plus n zero) n"
        , "attack"
        , "intro"
        , "into"
        , "along"
        , "eliminate-core ⌜ n ⌝"
        , ":show"
        , "back"
        , "back"
        , "try-core ⌜ refl {0} Nat zero ⌝"
        , "solve"
        , "along"
        , "try-core ⌜ \\ (x : Nat) (ih : Eq {0} Nat (plus x zero) x) -> congSucc (plus x zero) x ih ⌝"
        , "solve"
        , "along"
        , "solve"
        , "back"
        , "back"
        , "back"
        , "back"
        , "solve"
        , "qed"
        , ":show plusZero"
        , ":quit"
        ]
      -- The other half of §3.7: eliminating an indexed family at a **specific**
      -- index. @Ev (succ zero)@ matches no constructor, and the scheme is what
      -- says so — each method carries an equation between its own index
      -- expression and @succ zero@, and @noConfusionNat@ (phase 14) turns both
      -- into @Empty@. Ruling out @E-IfTrue@ against @E-If@ in the determinacy
      -- proof is this, at a bigger relation (§9, phase 18).
    , script
        "inversion"
        ( preludeLines ++
        [ "data Nat : Type₀ where { zero : Nat ; succ : Nat -> Nat }"
        , "data Ev : Nat -> Type₀ where { evZero : Ev zero ; evSS : ∀ (n : Nat) (p : Ev n) -> Ev (succ (succ n)) }"
        , ":whnf NoConfusionNat zero (succ zero)"
        , ":whnf NoConfusionNat (succ (succ zero)) (succ zero)"
        , ":theorem oneNotEven : ∀ (p : Ev (succ zero)) -> Empty {0}"
        , "attack"
        , "intro"
        , "into"
        , "along"
        , "eliminate-core ⌜ p ⌝"
        , ":where"
        , "back"
        , "back"
        , "try-core ⌜ \\ (q : Eq {0} Nat zero (succ zero)) -> noConfusionNat zero (succ zero) q ⌝"
        , "solve"
        , "along"
        , "try-core ⌜ \\ (n : Nat) (e : Ev n) (ih : Eq {0} Nat n (succ zero) -> Empty {0}) (q : Eq {0} Nat (succ (succ n)) (succ zero)) -> noConfusionNat (succ n) zero (noConfusionNat (succ (succ n)) (succ zero) q) ⌝"
        , "solve"
        , "along"
        , "solve"
        , "back"
        , "back"
        , "back"
        , "back"
        , "solve"
        , "qed"
        , ":show oneNotEven"
        , ":quit"
        ])
      -- What the tactic refuses. None of these is a bug: §3.7's non-dependent
      -- index telescope limit (@AGENDA.md@ item 10), @Eq@ and @refl@ being
      -- named rather than designated, and a target that is not an inhabitant of
      -- a family at all.
      --
      -- One more refusal is /not/ here: thesis §3.5.2's \"what to fix, what to
      -- abstract\". It is in "Thena.EliminateTests" instead, matched on shape,
      -- because its message ends in a conversion clash that names two raw
      -- variables by number — and the number depends on how much of the script
      -- ran before it, which would make this file churn for unrelated reasons.
    , script
        "elimination"
        [ "data Nat : Type₀ where { zero : Nat ; succ : Nat -> Nat }"
        , "data Fin : Nat -> Type₀ where { fz : ∀ (n : Nat) -> Fin (succ n) ; fs : ∀ (n : Nat) (i : Fin n) -> Fin (succ n) }"
        , ":theorem noEq : ∀ (n : Nat) (i : Fin n) -> Nat"
        , "attack"
        , "intro"
        , "intro"
        , "into"
        , "along"
        , "along"
        , "eliminate-core ⌜ i ⌝"
        , "eliminate-core ⌜ n ⌝"
        , ":abandon"
        , "data Eq (A : Type) : A -> A -> Type where { refl : ∀ (a : A) -> Eq A a a }"
        , "data Unit : Type where { unit : Unit }"
        , "data Empty : Type where { }"
        , "data And (A : Type) (B : Type) : Type where { both : ∀ (a : A) (b : B) -> And A B }"
        , "data Below : ∀ (n : Nat) (i : Fin n) -> Type₀ where { bz : ∀ (m : Nat) -> Below (succ m) (fz m) ; bs : ∀ (m : Nat) (j : Fin m) (b : Below m j) -> Below (succ m) (fs m j) }"
        , ":theorem probe : ∀ (n : Nat) (i : Fin n) (b : Below n i) -> Nat"
        , "attack"
        , "intro"
        , "intro"
        , "intro"
        , "into"
        , "along"
        , "along"
        , "along"
        , ":matches"
        , "eliminate-core ⌜ Type₀ ⌝"
        , "eliminate-core ⌜ succ ⌝"
        -- Phase 19: @Below@'s index telescope is dependent, but both indices
        -- are plain variables here, so the dependent one is friendly and
        -- states no equation. This line was a refusal until phase 19.
        , "eliminate-core ⌜ b ⌝"
        , ":where"
        , "attack"
        , "eliminate-core ⌜ n ⌝"
        , ":abandon"
        -- And the refusal that remains: index 2 is @fz m@, a constructor
        -- application, so it is tied and does want an equation.
        , ":theorem tied : ∀ (m : Nat) (b : Below (succ m) (fz m)) -> Nat"
        , "attack"
        , "intro"
        , "intro"
        , "into"
        , "along"
        , "along"
        , "eliminate-core ⌜ b ⌝"
        , ":quit"
        ]
    , -- Thesis §2.7, and the phase's deliverable. The interesting half is the
      -- second theorem: the term is parked in a @=@-binding, unification solves
      -- the holes **in the goal**, and only then is the hole filled with the
      -- binding. That is what @unify-refine@ has over @naive-refine@ — you
      -- infer values for holes in the goal, not just for the arguments.
      script
        "refining"
        [ "data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
          -- **The level arguments go on the /uses/, never on the constructor's
          -- name.** Written @refl {0} :@ this line was a syntax error, so @Eq@
          -- was never declared and every step below recorded @not in scope@ as
          -- its expected output — the third golden caught doing that
          -- (@ms3/CLOSEOUT.md@ item 14). Repaired reviewing MS3.
        , "data Eq (A : Type) : A -> A -> Type \
          \where { refl : \8704 (a : A) -> Eq A a a }"
          -- Already the goal's type: unification has nothing to do, and the
          -- binding is filled straight in.
        , ":theorem id0 : \8704 (A : Type\8320) -> A -> A"
        , "unify-refine-core ⌜ \\ (A : Type\8320) (a : A) -> a ⌝"
        , ":show"
        , "qed"
          -- Holes on both sides. @refl {0} A a@ has type @Eq {0} A a a@; unifying that
          -- with @Eq {0} Nat zero zero@ solves @A@ and @a@.
        , ":theorem refl0 : Eq {0} Nat zero zero"
        , "claim A : Type\8320"
        , "claim a : A"
        , "unify-refine-core ⌜ refl {0} A a ⌝"
        , ":show"
        , "qed"
        , ":show refl0"
          -- And the failure: nothing unifies these.
          --
          -- **The @=@-binding it had already parked is gone** (phase 25d).
          -- @define@ runs before @unify@, so this body really does change the
          -- development and then fail — it is the case that predates @apply@,
          -- and the reason the rewind lives in the driver rather than in
          -- anything @apply@ owns.
        , ":theorem wrong : Eq {0} Nat zero (succ zero)"
        , "unify-refine-core ⌜ refl {0} Nat zero ⌝"
        , ":show"
        , ":abandon"
          -- **The tactic is two calls now** (MS4 phase 48) — his request:
          -- /"add two new tactics fill and solve and define unify-refine with
          -- them"/. @fill-core@ leaves a guess and @solve@ discharges it, so
          -- the seam Brady needs between them is one a caller can get at.
        , ":theorem split : ∀ (A : Type₀) -> A -> A"
        , "fill-core ⌜ \\ (A : Type₀) (a : A) -> a ⌝"
        , ":show"
        , "solve"
        , "qed"
          -- **And cumulativity reaches the tactic.** @Type₀@ has type @Type₁@
          -- and the goal is @Type₂@; this said /Type₁ and Type₂ are different
          -- universes/ until @fill-core@ started asking @unify-into@. Phase
          -- 41g had fixed the elaborator's own inline fill and left this rule
          -- symmetric, so one operation answered differently depending on
          -- which of the two you reached it through.
        , ":theorem lower : Type₂"
        , "unify-refine-core ⌜ Type₀ ⌝"
        , ":show"
        , "qed"
        ]

    , -- **The user's own motivating example for `unify-refine`**, 2026-08-25:
      -- a goal at @Maybe Bool@, refined with @Just@, where unification works
      -- out the type argument so only the boolean is left to supply.
      --
      -- The two @claim@s are what `apply` will do for you in phase 25 — look
      -- the name up, walk its Π telescope, claim a hole per argument, hand the
      -- spine to this tactic. `apply Just` abbreviates exactly these three
      -- lines and adds no capability, which is why `MS2.md` makes it one item
      -- rather than a phase.
      -- **@:infer@ takes a surface term** (MS4 phase 43), and a core one in
      -- corners. It elaborates where you are asking, reads the type off, and
      -- undoes the line — his framing: /"if this term were put here, what would
      -- its type be?"/ The two @:show@es around it are the whole point.
      script
        "surface-inference"
        [ "data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
        , ":theorem t : Nat"
        , ":show"
        , ":infer succ zero"
        , ":infer \8988 succ zero \8989"
        , ":show"
        , ":where"
        , ":infer nosuchthing"
        , ":show"
        , ":quit"
        ]

      -- **A @do@ block is a surface term whose elaboration is to play it**
      -- (MS4 phase 45). It removes the need for a surface term meaning /no
      -- proof given, search for one/: the user writes the search as an
      -- instruction, and a search strategy is then a rule name and never
      -- syntax.
    , script
        "do-blocks"
        [ ":surface do { attack ; intro }"
          -- A block is an atom, so an argument run takes it unparenthesised.
        , ":surface f (do { attack })"
        , "data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
        , ":theorem t : Nat"
        , "elaborate (do { attack ; prove })"
          -- The block did what was written rather than what was tidy, and the
          -- development shows where it got to — the second principle.
        , ":show"
          -- An op given operands it does not take is caught when the block is
          -- resolved, before any of it runs, and the message says which
          -- instruction. **The block must be the whole of the failure**: with
          -- an instruction before it that succeeds, the engine backtracks over
          -- the failing clause and the reason is lost with it — which is how
          -- every elaboration failure behaves, not something blocks add.
          -- On a fresh proof, so that no choice point from the line above is
          -- live to backtrack into.
        , ":abandon"
        , ":theorem u : Nat"
        , "elaborate (do { say })"
        , ":quit"
        ]

      -- **Yielding to the REPL** (MS4 phase 45b). The rule stops where it is
      -- and hands control over; every command works, the development is the
      -- half-built one, and @yield@ hands control back. The word is the same in
      -- both directions — his, 2026-09-03: /"yielding is something that
      -- switches from one control to the other so returning would be named the
      -- same."/
    , script
        "yielding"
        [ "data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
        , ":theorem t : Nat"
        , "elaborate (do { h = here ; yield \"look at this\" ; goto h ; prove })"
          -- The development is what the rule has built so far, not what it
          -- started with: @attack@ has not run, but @here@ has.
        , ":show"
          -- **Every ordinary command works, and really changes things.** That
          -- is the whole difference between a yield and a question, which takes
          -- an answer and refuses everything else.
        , "assume w : Nat"
        , ":show"
        , ":infer succ zero"
        , ":revalidate"
          -- **A typed block reads the rule's own locals.** A command cannot —
          -- @goto h@ looks for a hole named @h@ — which is why the REPL types
          -- the instruction language through a block.
        , "goto h"
        , "do { goto h }"
          -- And a block's bindings survive to the next line, because a yielded
          -- machine's environment is not cleared.
        , "do { k = here }"
        , "do { goto k }"
          -- The yield is not consumed, so the prompt keeps coming back until
          -- this word advances past it.
        , "yield"
        , "yield"
        , ":quit"
        ]

    , script
        "inferring"
        [ "data Bool : Type\8320 where { true : Bool ; false : Bool }"
        , "data Maybe (A : Type\8320) : Type\8320 \
          \where { Nothing : Maybe A ; Just : \8704 (a : A) -> Maybe A }"
        , ":theorem g : Maybe Bool"
          -- One hole per argument of Just, including the type parameter.
        , "claim T : Type\8320"
        , "claim b : T"
          -- Maybe T against Maybe Bool solves T, and says so.
        , "unify-refine-core ⌜ Just T b ⌝"
        , ":show"
          -- The only hole left is the boolean, and its type is now T = Bool.
          -- @goto@ (phase 24b) goes straight to it; counting @back@s would
          -- stop scaling the moment @apply@ claims several holes at once.
        , "goto b"
        , ":where"
        , "unify-refine-core ⌜ true ⌝"
        , ":show"
        , "qed"
        , ":show g"
        ]

    , -- **Phase 25's deliverable**: the transcript above, with the two @claim@s
      -- replaced by @apply@ — and then the cases the worked example does not
      -- reach.
      --
      -- The holes are named from the Π binders they came from, so @Just@'s are
      -- @A@ and @a@ where the hand-written version chose @T@ and @b@. An
      -- anonymous domain — every @->@ — has no name to take, and gets @_@.
      script
        "applying"
        [ "data Bool : Type\8320 where { true : Bool ; false : Bool }"
        , "data Maybe (A : Type\8320) : Type\8320 \
          \where { Nothing : Maybe A ; Just : \8704 (a : A) -> Maybe A }"
        , ":theorem g : Maybe Bool"
          -- One line for the whole of `inferring`'s three.
        , ":matches"
        , "apply-core ⌜ Just ⌝"
        , ":show"
          -- A head with no Π at all: zero holes claimed, so @apply@ degenerates
          -- to @unify-refine@ exactly. That is the phase's claim that it adds
          -- no capability, in its smallest form.
        , "goto a"
        , "apply-core ⌜ true ⌝"
        , ":show"
        , "qed"
        , ":show g"
          -- **A hypothesis, not a global.** A REPL argument is resolved in the
          -- context at the focus, so @apply@ works on anything in scope — which
          -- is what @examples/determinacy.thena.script@ needs when it applies an
          -- induction hypothesis by hand.
          --
          -- Two anonymous domains, so two holes called @_@ and @_1@, and
          -- @goto _@ still reaches the first: identifiers stay unique (phase
          -- 24b) whatever they are named after.
        , ":theorem ap2 : \8704 (A : Type\8320) (f : A -> A -> A) (x : A) -> A"
        , "attack"
        , "intro"
        , "intro"
        , "intro"
        , "into"
        , "along"
        , "along"
        , "along"
        , "apply-core ⌜ f ⌝"
        , ":show"
        , "goto _"
        , ":where"
        , ":abandon"
          -- **The failure, and that it leaves nothing** (phase 25d).
          -- @prim-apply@ claims two holes and @define@ parks a binding before
          -- @unify-refine@ can find out the types will not meet — so the body
          -- really does change the development and then fail. The driver
          -- rewinds it: @:show@ is the bare hole, exactly as before the line.
          --
          -- And @:undo@ says there is nothing to undo, which is the same fact
          -- from the other side: a line that did not do what it said is not a
          -- step, so there is no step to take back.
        , ":theorem bad : Bool"
        , "apply-core ⌜ Just ⌝"
        , ":show"
        , ":undo"
        , "apply-core ⌜ true ⌝"
        , "qed"
          -- **The same failure with no proof open** (phase 34). The top level
          -- has a development too, so a line that did not do what it said is
          -- rewound there as well, and @:undo@ takes back a line there as well
          -- — neither of which happened until the undo stack moved off 'Proof'.
        , ":goal Maybe Bool"
        , "apply-core ⌜ Just ⌝"
        , ":show"
        , "apply-core ⌜ Nothing ⌝"
        , ":show"
        , ":undo"
        , ":show"
        , ":undo"
          -- And the rewind proper: a body that ran, changed the development and
          -- then failed, with no proof open. @:show@ is the bare hole.
        , ":goal \8704 (b : Bool) -> Maybe Bool"
        , "apply-core ⌜ Just ⌝"
        , ":show"
          -- **A goal `apply` cannot saturate into, and the way back** (the
          -- user, 2026-08-26). @Just@'s result is a @Maybe@, so no number of
          -- arguments makes it a function type: saturating and unifying fails.
          --
          -- Phase 27's @fit@ will get this by stopping an argument early —
          -- @Just ?A : ?A -> Maybe ?A@ does unify with it. **But it is already
          -- provable without any search**, by moving the hole through the Π
          -- first: table 2.8's @intro@ puts the λ in and leaves the goal at
          -- @Maybe Bool@, where @apply@ works as it does above.
          --
          -- **@assume@ does not do this**, and it was the first thing tried:
          -- it adds the λ /above/ the hole and leaves the hole claimed at
          -- @Bool -> Maybe Bool@, so @apply@ fails identically and the term
          -- would have type @Bool -> Bool -> Maybe Bool@ anyway. §5.3's
          -- distinction between assuming and introducing, from the other side.
        , ":theorem h : \8704 (b : Bool) -> Maybe Bool"
        , "apply-core ⌜ Just ⌝"
        , "assume q : Bool"
        , "apply-core ⌜ Just ⌝"
        , ":abandon"
        , ":theorem h : \8704 (b : Bool) -> Maybe Bool"
        , "attack"
        , "intro"
        , "into"
        , "along"
        , ":where"
        , "apply-core ⌜ Just ⌝"
        , "goto a"
        , "apply-core ⌜ b ⌝"
        , "goto h"
        , "solve"
        , "qed"
        , ":show h"
          -- The head is the guard, so @apply@ at a guess never runs its body.
        , ":theorem guessed : Bool"
        , "attack"
        , "apply-core ⌜ true ⌝"
        , ":abandon"
        ]

    , -- **Phase 25b's deliverable**: thesis table 2.7 gives @try@ the side
      -- condition @Θ ⊩ t : S@ and it is now enforced, so a guess that does not
      -- fit is refused on the line that wrote it rather than at @qed@.
      script
        "guessing"
        [ "data Nat : Type\8320 where { zero : Nat ; succ : \8704 (n : Nat) -> Nat }"
        , "data Bool : Type\8320 where { true : Bool ; false : Bool }"
        , ":theorem n : Nat"
          -- Refused, and it says which type against which. Before this phase
          -- the guess went in and @qed@ found it, arbitrarily far away.
        , "try-core ⌜ true ⌝"
          -- **And it left nothing behind** — the check runs before the
          -- component is replaced, so a refused @try@ is not the debris case.
        , ":show"
        , "try-core ⌜ zero ⌝"
        , "solve"
        , "qed"
          -- **A term mentioning an open hole still checks.** Γ comes from
          -- @forget@, so a claim is a hypothesis with no value; this is what
          -- @unify-refine@ depends on, since it tries a binding whose own value
          -- may still contain holes.
        , ":theorem m : Nat"
        , "claim h : Nat"
        , "try-core ⌜ succ h ⌝"
        , ":show"
        , ":abandon"
        ]

    , script
        "levels"
        [ -- A level-polymorphic DATATYPE: declared, instantiated at two levels,
          -- and eliminated (MS3 phase 31c). The elimination is J.
          --
          -- **Nothing declares level parameters any more** (phase 33c): a
          -- theorem's were dropped at 31e and a datatype's here, so the schema
          -- below is entirely inferred from the two written @Type@s.
          "data Id (A : Type) : A -> A -> Type where { rfl : \8704 (a : A) -> Id A a a }"
        , ":show Id"
        , ":infer \8988 Id {0} \8989"
        , ":infer \8988 rfl {0} \8989"
        , ":infer \8988 \\ (A : Type\8320) (a : A) (b : A) (q : Id {0} A a b) -> elim Id {0} (A) (\\ (x : A) (y : A) (z : Id {0} A x y) -> Id {0} A x x) ((\\ (c : A) -> rfl {0} A c)) (a b) q \8989"
          -- Prenex is all-or-nothing.
        , ":infer \8988 Id \8989"
        , ":infer \8988 Id {0 1} \8989"
          -- **There is no level-variable syntax left to get wrong.** @Type {l}@
          -- was the last thing that could name one, and phase 33c deleted it;
          -- what a use may write is a numeral, and nothing else.
        , ":core Type {l}"
        , ":infer \8988 Id {suc 0} \8989"
        , ":quit"
        ]
      -- What level polymorphism was FOR, as a pair of probes neither of which
      -- had a test (added reviewing MS3).
      --
      -- @Box1@ is §2 item 1 of @discussion\/universe-polymorphism.md@ and MS3's
      -- own done-when: before the milestone @eliminate b@ answered /the goal
      -- does not survive generalising the target/, because the elimination
      -- tactic wrote @Eq@ at no level and @Eq@ was stuck at @Type₀@. It was
      -- checked by hand when the done-when was signed off and never pinned.
      --
      -- @N@ is the shape phase 33c's inference could not declare at all: the
      -- recursive occurrence in @s@'s argument is stored before @N@ has a level
      -- parameter, so it came out with none and the declaration was refused
      -- outright. Nothing in the prelude is both polymorphic and recursive,
      -- which is why nothing caught it.
      -- **A set of level constraints that is pairwise possible and jointly
      -- impossible** (phase 35), in two ordinary lines.
      --
      -- The two constant bounds sit on *different* metas with a meta-to-meta
      -- edge between them, and that is what hides them from
      -- 'Thena.Core.Level.forced': it reads a bound only off a relation one of
      -- whose sides is a constant, so it sees @2 ≤ ?a@ and @?b ≤ 1@ and never
      -- puts them together.
      --
      -- **Before this phase @:revalidate@ said /valid/ and @qed@ said /∎/**, and
      -- the theorem entered the global environment carrying
      -- @(2 ≤ ℓ₂) (ℓ₂ ≤ ℓ₁) (ℓ₁ ≤ 1)@ — a precondition no instantiation meets,
      -- so every use of it was refused and it was noise in the scope.
      -- @:infer@ printed a type for it at any levels, because a look drops the
      -- obligations, which is what made it look usable.
      --
      -- **Its own script**, because @:theorem@ takes over the development it
      -- finds rather than a fresh one, so appending this to a transcript that
      -- has claimed anything makes @qed@ fail for an unrelated reason.
    , script
        "unsatisfiable"
        [ ":theorem vacuous : Type\8321"
        , "try-core ⌜ (\\ (y : Type) -> y) ((\\ (x : Type) -> x) Type\8321) ⌝"
        , "solve"
        , ":revalidate"
        , "qed"
        , ":show vacuous"
        , ":quit"
        ]
    , script
        "universes"
        ( preludeLines ++
        [ "data Box1 : Type\8320 -> Type\8321 \
          \where { box1 : \8704 (A : Type\8320) -> A -> Box1 A }"
        , "data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
        , ":theorem probe : \8704 (b : Box1 Nat) -> Nat"
        , "attack"
        , "intro"
        , "into"
        , "along"
        , "eliminate-core ⌜ b ⌝"
        , ":abandon"
        , "data N : Type where { z : N ; s : N -> N }"
        , ":show N"
        , ":infer \8988 s {0} \8989"
        , ":infer \8988 s {1} (z {1}) \8989"
          -- **A level a constructor argument's typing determines** (phase 50).
          -- @suc ?\8467 \8804 1@ pins the inner bare @Type@ at @Type\8320@, and @E@ takes no
          -- level argument. Before phase 50 the bound was dropped, @?\8467@ became a
          -- rigid, and the generated no-confusion family was refused as a bug.
        , "data E : Type where { k : Eq {1} Type Nat Nat -> E }"
        , ":show E"
          -- And one the bounds merely /constrain/: @suc ?\8467 \8804 2@ leaves @?\8467@ free
          -- below 1. Phase 50 refused it, because a datatype has nowhere to
          -- carry a conditional constraint; **phase 51 defaults it** to its
          -- least value instead, so @F@ takes no level argument either.
        , "data F : Type where { k2 : Eq {2} Type Nat Nat -> F }"
        , ":show F"
          -- **Real polymorphism is untouched**, which is the whole point of the
          -- partition: @\8467@ occurs in @Eq@'s own type, so a use determines it
          -- and it is never a candidate for defaulting.
        , ":show Eq"
        , ":quit"
        ])
      -- Typical ambiguity (MS3 phase 33): a bare @Type@ is a universe whose
      -- level is worked out rather than written. The script walks the three
      -- endings — the level is forced, it is refuted, or nothing determines it
      -- — because which one you get is the whole of what this phase decides.
    , script
        "ambiguity"
        [ ":infer \8988 Type \8989"
        , ":infer \8988 Type -> Type \8989"
          -- Conversion does not refuse an undecided level; it says what it
          -- would need.
        , ":convert Type \8799 Type\8320"
          -- Forced, and written back: the theorem is stored with the level the
          -- obligations left it no choice about.
        , ":theorem lift : Type\8321"
        , "try-core ⌜ Type ⌝"
        , "solve"
        , "qed"
        , ":show lift"
          -- Nothing determines it, so it is **generalised** rather than
          -- refused (phase 33b) — and the relation that was left over becomes
          -- the scheme's constraint.
        , ":theorem undetermined : Type"
        , "try-core ⌜ Type\8320 ⌝"
        , "solve"
        , ":revalidate"
        , "qed"
        , ":show undetermined"
          -- Refuted: the same meta is pushed up by one use and down by another.
        , ":theorem crossed : Type\8320"
        , "try-core ⌜ (\\ (x : Type) -> x) Type\8320 ⌝"
        , "solve"
        , ":revalidate"
        , "qed"
        , ":abandon"
          -- Unification solves a level and writes it through the whole
          -- development — a level meta has no component to be promoted, so this
          -- is the only place a solution can be recorded.
        , "claim h : Type -> Type"
        , "unify \\ (x : Type) -> x \8799 \\ (x : Type\8320) -> x"
        , ":show"
          -- **A declaration infers its level too** (phase 33c). It could not
          -- when this script was written — phase 33 refused a bare @Type@ here,
          -- because a declaration's levels are stored and instantiated at every
          -- use and nothing generalised one.
        , "data Box : Type where { }"
        , ":show Box"

        , ":quit"
        ]
      -- Generalisation at @qed@ (MS3 phase 33b): a proof's leftover level metas
      -- become the definition's prenex parameters, and the obligations that are
      -- neither valid nor false become the constraints every use owes back.
    , script
        "polymorphism"
        [ -- One parameter, not two — conversion states an equality as two
          -- inequalities and generalisation reads them back as one.
          ":theorem id : \8704 (A : Type) -> A -> A"
        , "try-core ⌜ \\ (A : Type) (a : A) -> a ⌝"
        , "solve"
        , "qed"
        , ":show id"
        , ":infer \8988 id {0} \8989"
        , ":infer \8988 id {3} \8989"
          -- Prenex is still all-or-nothing.
        , ":infer \8988 id \8989"
          -- A scheme with a real constraint between two independent parameters.
        , ":theorem lift : \8704 (A : Type) -> Type"
        , "try-core ⌜ \\ (A : Type) -> A ⌝"
        , "solve"
        , "qed"
        , ":show lift"
        , ":infer \8988 lift {0 1} \8989"
          -- **@:infer@ accepts a bad instantiation**, and that is the accepted
          -- trade: obligations are re-collected, not pooled, so the error
          -- arrives at @qed@ rather than at the line.
        , ":infer \8988 lift {1 0} \8989"
        , ":theorem bad : Type\8321 -> Type\8320"
        , "try-core ⌜ lift {1 0} ⌝"
        , "solve"
          -- Here it is: the stored constraint, instantiated. Without it
          -- @Type\8321 -> Type\8320@ is a perfectly good type and this is
          -- admitted.
        , ":revalidate"
        , "qed"
          -- **And unfolding the call does not launder it.** The wart §4 warned
          -- about needs a schema less general than inference gives, and
          -- inference never over-claims — so with written schemata gone there
          -- is nothing left to build it out of.
        , "along"
        , "reduce"
        , ":revalidate"
        , ":abandon"
        , ":quit"
        ]
    , script
        "mistakes"
        [ "wibble"
        , ":core y"
        , ":show it"
        , "assume : Type₀"
        , "let"
        , ":show"
        -- Table 2.7's @Θ ⊢ S : Type@ on both binders (phase 25f). The λ is a
        -- term, not a type, so both ops refuse it and — per phase 25d — leave
        -- the proof exactly as it was.
        , "claim h : (\\ (x : Type₀) -> x)"
        , "assume k : (\\ (x : Type₀) -> x)"
        -- **Accepted, and this line is the point of the pair.** A type family
        -- is a perfectly good type; the condition is "S is a type", not "S is
        -- a type at level 0". Closeout 4l offered
        -- @claim h : Nat -> Nat -> Nat -> Type₀@ as an example of the defect
        -- and it never was one.
        , "claim fam : Type₀ -> Type₀ -> Type₀"
        , ":show"
        ]
      -- The command list, and the one error that points at it. Pinning the
      -- whole thing is the point: a command added without a line here is a
      -- diff, which is the only pressure keeping 'commandSummary' honest that
      -- does not depend on someone remembering.
    , script
        "help"
        [ ":help"
        , ":nonesuch"
        , ":quit"
        ]
    ]
  where
    -- **From a session with the shipped rule base loaded** (phase 22), because
    -- @newSession@ no longer has one. Loading problems are prepended rather
    -- than thrown, so a broken rule file shows up as a golden diff naming it
    -- instead of as an unrelated failure somewhere downstream.
    script name ls =
      goldenVsString
        name
        ("test/golden/" ++ name ++ ".golden")
        ( do
            (s, problems) <- loadStandardRules newSession
            pure (toLazyByteString (stringUtf8 (unlines problems ++ transcriptFrom s ls)))
        )

-- | The prelude declarations a transcript must make before no-confusion can be
-- generated for anything it goes on to declare.
--
-- These transcripts run prelude-free (phase 11's accepted divergence: the
-- scripts declare their own @Nat@ and @Empty@, which the real prelude would
-- clash with). Phase 14 needed only @Eq@ for that; phase 20 writes the table
-- out of @Empty@, @Unit@ and @And@ as well, so a script that wants
-- @noConfusionD@ must declare all four up front — **and in this order**, since
-- @And@\'s own no-confusion states equations and so needs @Eq@ already there.
--
-- Only the two scripts that use no-confusion take it. A script that declares
-- @Eq@ and a datatype without these gets no lemma, silently, which is what
-- 'Thena.Global.NoConfusion.NoProducts' means.
preludeLines :: [String]
preludeLines =
  [ "data Eq (A : Type) : A -> A -> Type \
    \where { refl : \8704 (a : A) -> Eq A a a }"
  , "data Unit : Type where { unit : Unit }"
  , "data Empty : Type where { }"
  , "data And (A : Type) (B : Type) : Type \
    \where { both : \8704 (a : A) (b : B) -> And A B }"
  ]
