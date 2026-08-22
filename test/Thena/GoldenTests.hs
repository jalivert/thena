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
      -- printed, computed and certified. The script declares its own @Eq@
      -- because these transcripts run prelude-free (phase 11) and no equation
      -- can be stated without one — which is also why the @Nat@ line here gets
      -- no note and the @Vec@ line does.
    , script
        "noconfusion"
        [ "data Eq (A : Type\8320) : A -> A -> Type\8320 \
          \{ refl : \8704 (a : A) -> Eq A a a }"
        , "data Term : Type\8320 \
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
          \-> noConfusionTerm (succ a) (succ b) e (Eq Term a b) (\\ (q : Eq Term a b) -> q)"
        , ":extract"
        , "certify \8704 (a : Term) (b : Term) -> Eq Term (succ a) (succ b) -> Eq Term a b"
        , "back"
        , "data Nat : Type\8320 { zero' : Nat ; succ' : Nat -> Nat }"
        , "data Vec (A : Type\8320) : Nat -> Type\8320 \
          \{ nil : Vec A zero' \
          \; cons : \8704 (n : Nat) (a : A) (as : Vec A n) -> Vec A (succ' n) }"
        , ":show noConfusionVec"
        , ":quit"
        ]
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
