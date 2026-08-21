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
