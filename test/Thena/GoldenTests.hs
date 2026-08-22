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
