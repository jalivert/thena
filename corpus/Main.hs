-- | **The example corpus, and it is NOT part of `cabal test`** — his
-- instruction, 2026-10-12: *"the main test suit that runs always covers what
-- needs to be covered and then we have these large example like the TAPL
-- theorems and the POPLMark and they run only when explicitly executed."*
--
-- > cabal test thena-examples
--
-- **Why these and not the TAPL theorems.** Measured before splitting anything:
-- of the 30 s the corpus cost the main suite, **29 s was this one group**. The
-- TAPL proofs he named are 0.94 s, determinacy 1.24 s, normal forms 0.21 s, the
-- dependent telescope 0.03 s — they stayed in `thena-test`, because moving them
-- would cost coverage and buy nothing. What is expensive is loading the whole
-- numbered series in one session and proving its headline theorems, which is
-- what lives here.
--
-- **A second test-suite is opt-in by cabal's own behaviour**, the same way
-- @thena-boundary@ is: `cabal test`, `cabal test all` and even
-- `cabal test thena-test thena-examples` all run @thena-test@ alone. Verified
-- three ways, 2026-10-12.
--
-- **What the main suite therefore no longer catches**: an example that stops
-- loading, and a headline theorem whose statement has drifted. Run this before
-- a milestone merges; `.claude/commands/finish-session.md` says so.
module Main (main) where

import Test.Tasty (defaultMain, testGroup)

import qualified Thena.ExamplesTests

main :: IO ()
main = defaultMain (testGroup "the example corpus" [Thena.ExamplesTests.tests])
