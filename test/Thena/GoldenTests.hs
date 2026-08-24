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

import Thena.Repl (transcript)

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
        [ "data Nat : Type\8320 { zero : Nat ; succ : Nat -> Nat }"
        , ":infer succ zero"
        , ":infer \\ (x : Nat) -> x"
        , ":infer \8704 (A : Type\8320) -> A"
        , ":convert succ \8799 \\ (n : Nat) -> succ n"
        , ":convert Type\8320 \8799 Type\8321"
        , ":convert succ zero \8799 succ (succ zero)"
        , ":infer zero zero"
        , ":infer elim Nat () (\\ (_ : Nat) -> Nat) (zero succ) () (succ zero)"
        , "claim h : Nat"
        , "cross type"
        , ":infer"
        , "back"
        , "back"
        , ":infer"
        , "data Big : Type\8320 { wrap : Type\8320 -> Big }"
        , ":quit"
        ]
      -- The elimination rule, seen (phase 10). The same datatype at two levels
      -- is §3.7's universe trick: one rule per universe the motive is valued
      -- in, and no constant that could have held either.
    , script
        "eliminators"
        [ "data Nat : Type\8320 { zero : Nat ; succ : Nat -> Nat }"
        , "data Fin : Nat -> Type\8320 \
          \{ fz : \8704 (n : Nat) -> Fin (succ n) \
          \; fs : \8704 (n : Nat) (i : Fin n) -> Fin (succ n) }"
        , "data Empty : Type\8320 { }"
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
        [ "data Nat : Type\8320 { zero : Nat ; succ : Nat -> Nat }"
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
          \{ true : Term ; false : Term \
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
        , ":goal \8704 (a : Term) (b : Term) -> Eq Term (succ a) (succ b) -> Eq Term a b"
        , "along"
        , "unify goal \8799 \\ (a : Term) (b : Term) (e : Eq Term (succ a) (succ b)) \
          \-> noConfusionTerm (succ a) (succ b) e"
        , ":extract"
        , "certify \8704 (a : Term) (b : Term) -> Eq Term (succ a) (succ b) -> Eq Term a b"
        , "back"
        , "data Nat : Type\8320 { zero' : Nat ; succ' : Nat -> Nat }"
        , "data Vec (A : Type\8320) : Nat -> Type\8320 \
          \{ nil : Vec A zero' \
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
        , "try _"
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
        [ ":matches"
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
        , ":matches a"
        , "prove a"
        , ":show"
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
        , "prove b"
          -- A hint that is not an identifier does not match at all: no rule
          -- with a hint head passes, and there is nothing else in the hinted
          -- half of the base.
        , "prove a a"
        , ":matches a a"
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
        , "prove a"
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
        [ "data Nat : Type\8320 { zero : Nat ; succ : Nat -> Nat }"
        , ":theorem two : Nat"
        , "attack"
        , ":show"
        , ":undo"
        , ":undo"
        , ":suspend"
        , ":proofs"
        , "data Bool : Type\8320 { true : Bool ; false : Bool }"
        , ":theorem one : Nat"
        , "try zero"
        , "solve"
        , "qed"
        , ":resume two"
        , ":core true"
        , "try (succ (succ zero))"
        , "solve"
        , "qed"
        , ":show two"
        , ":undo"
        , ":quit"
        ]
    , script
        "unification"
        [ "data Nat : Type\8320 { zero : Nat ; succ : Nat -> Nat }"
        , "claim h : Nat"
        , "unify succ h \8799 succ (succ zero)"
        , ":show"
        , "claim f : Nat -> Nat"
        , "unify \\ (x : Nat) -> f x \8799 \\ (x : Nat) -> succ x"
        , ":show"
        , "claim a : Nat"
        , "claim b : Nat"
        , "unify a \8799 b"
        , ":show"
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
        , "assume A : Type₀"
        , ":step"
        , ":step"
        , ":step off"
        , "claim h : Type₀"
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
        [ "data Nat : Type₀ { zero : Nat ; succ : Nat -> Nat }"
        , ":show Nat"
        , ":show succ"
        , ":show zero"
        , ":core succ (succ zero)"
        , "data Vec (A : Type₀) : Nat -> Type₀ { nil : Vec A zero ; cons : ∀ (n : Nat) (a : A) (as : Vec A n) -> Vec A (succ n) }"
        , ":show Vec"
        , ":show cons"
        , "data Empty : Type₀ { }"
        , ":show Empty"
        , "data Nat : Type₀ { z : Nat }"
        , "data Ordinal : Type₀ { sup : (Nat -> Ordinal) -> Ordinal }"
        , "data Bad : Type₀ { bad : (Bad -> Bad) -> Bad }"
        , ":show nowhere"
        , "assume n : Nat"
        , ":show"
        , ":quit"
        ]
    , script
        "reduction"
        [ "data Nat : Type₀ { zero : Nat ; succ : Nat -> Nat }"
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
        [ "data Eq (A : Type₀) : A -> A -> Type₀ { refl : ∀ (a : A) -> Eq A a a }"
        , "data Nat : Type₀ { zero : Nat ; succ : Nat -> Nat }"
        , ":theorem plus : Nat -> Nat -> Nat"
        , "try \\ (n : Nat) (m : Nat) -> elim Nat () (\\ (t : Nat) -> Nat) (m (\\ (k : Nat) (ih : Nat) -> succ ih)) () n"
        , "solve"
        , "qed"
        , ":whnf plus (succ zero) (succ zero)"
        , ":theorem congSucc : ∀ (a : Nat) (b : Nat) (e : Eq Nat a b) -> Eq Nat (succ a) (succ b)"
        , "attack"
        , "intro"
        , "intro"
        , "intro"
        , "into"
        , "along"
        , "along"
        , "along"
        , "eliminate e"
        , "back"
        , ":where"
        , "try \\ (c : Nat) -> refl Nat (succ c)"
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
        , ":theorem plusZero : ∀ (n : Nat) -> Eq Nat (plus n zero) n"
        , "attack"
        , "intro"
        , "into"
        , "along"
        , "eliminate n"
        , ":show"
        , "back"
        , "back"
        , "try refl Nat zero"
        , "solve"
        , "along"
        , "try \\ (x : Nat) (ih : Eq Nat (plus x zero) x) -> congSucc (plus x zero) x ih"
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
        [ "data Nat : Type₀ { zero : Nat ; succ : Nat -> Nat }"
        , "data Ev : Nat -> Type₀ { evZero : Ev zero ; evSS : ∀ (n : Nat) (p : Ev n) -> Ev (succ (succ n)) }"
        , ":whnf NoConfusionNat zero (succ zero)"
        , ":whnf NoConfusionNat (succ (succ zero)) (succ zero)"
        , ":theorem oneNotEven : ∀ (p : Ev (succ zero)) -> Empty"
        , "attack"
        , "intro"
        , "into"
        , "along"
        , "eliminate p"
        , ":where"
        , "back"
        , "back"
        , "try \\ (q : Eq Nat zero (succ zero)) -> noConfusionNat zero (succ zero) q"
        , "solve"
        , "along"
        , "try \\ (n : Nat) (e : Ev n) (ih : Eq Nat n (succ zero) -> Empty) (q : Eq Nat (succ (succ n)) (succ zero)) -> noConfusionNat (succ n) zero (noConfusionNat (succ (succ n)) (succ zero) q)"
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
        [ "data Nat : Type₀ { zero : Nat ; succ : Nat -> Nat }"
        , "data Fin : Nat -> Type₀ { fz : ∀ (n : Nat) -> Fin (succ n) ; fs : ∀ (n : Nat) (i : Fin n) -> Fin (succ n) }"
        , ":theorem noEq : ∀ (n : Nat) (i : Fin n) -> Nat"
        , "attack"
        , "intro"
        , "intro"
        , "into"
        , "along"
        , "along"
        , "eliminate i"
        , "eliminate n"
        , ":abandon"
        , "data Eq (A : Type₀) : A -> A -> Type₀ { refl : ∀ (a : A) -> Eq A a a }"
        , "data Unit : Type₀ { unit : Unit }"
        , "data Empty : Type₀ { }"
        , "data And (A : Type₀) (B : Type₀) : Type₀ { both : ∀ (a : A) (b : B) -> And A B }"
        , "data Below : ∀ (n : Nat) (i : Fin n) -> Type₀ { bz : ∀ (m : Nat) -> Below (succ m) (fz m) ; bs : ∀ (m : Nat) (j : Fin m) (b : Below m j) -> Below (succ m) (fs m j) }"
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
        , "eliminate Type₀"
        , "eliminate succ"
        -- Phase 19: @Below@'s index telescope is dependent, but both indices
        -- are plain variables here, so the dependent one is friendly and
        -- states no equation. This line was a refusal until phase 19.
        , "eliminate b"
        , ":where"
        , "attack"
        , "eliminate n"
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
        , "eliminate b"
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
        ]
    ]
  where
    script name ls =
      goldenVsString
        name
        ("test/golden/" ++ name ++ ".golden")
        (pure (toLazyByteString (stringUtf8 (transcript ls))))

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
  [ "data Eq (A : Type\8320) : A -> A -> Type\8320 \
    \{ refl : \8704 (a : A) -> Eq A a a }"
  , "data Unit : Type\8320 { unit : Unit }"
  , "data Empty : Type\8320 { }"
  , "data And (A : Type\8320) (B : Type\8320) : Type\8320 \
    \{ both : \8704 (a : A) (b : B) -> And A B }"
  ]
