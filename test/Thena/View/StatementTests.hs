-- | Completion over an @instral@ line — Tier A (MS7 phase 137,
-- @.jalivert\/LIVE-OFFERS.md@).
--
-- **The assertion that is the phase is 'narrows'**: after @quantify @ the offer
-- wants a @Name@, and after @quantify x @ it wants a @Core@. That is
-- /"argument 2 wants a @Core@"/ — the thing Tier A was asked for — and it is not
-- a feature layered on the offer, it is what the offer already says, because a
-- slot is a nonterminal named after its type.
--
-- **The other load-bearing one is 'derived'**: every word in
-- 'Thena.Rules.opWords' has a production. That is what says the grammar is read
-- off the op table rather than written beside it, so an op added tomorrow is
-- completable tomorrow with nothing edited here.
module Thena.View.StatementTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Files (startingSession)
import Thena.Instral.Ops (signatureOf)
import Thena.Instral.Type (Signature (..), Ty (..))
import Thena.Language.Instral (instralRules, operandHead, statementHead)
import qualified Thena.Language.Earley as E
import Thena.Rules (opWords)
import Thena.View (sessionRules, statementOfferView)
import Thena.View.Chart (OfferView (..), StuckView (..), SymbolView (..), Written (..))

tests :: TestTree
tests =
  testGroup
    "instral completion (Tier A)"
    [ testCase "a slot says which type it wants, and the next slot a different one" narrows
    , testCase "every op in the table has a production, derived not written" derived
    , testCase "an empty line offers the statement words" empty
    , testCase "a rule in the loaded base may be called" callable
    , testCase "and the arity comes from the signature" arity
    , testCase "a word that is no statement is stuck, not silent" stuck
    ]

offerOf :: String -> IO OfferView
offerOf before = do
  s <- fst <$> startingSession
  pure (statementOfferView s [WrittenText before] [])

wants :: OfferView -> Ty -> Bool
wants o t = ANonterminalSymbol (operandHead t) `elem` offeredOptions o

-- | **Tier A, in one test.** @quantify :: Name -> Core -> ()@, so the first slot
-- wants a 'TName' and the second a 'TCore' — and the offer moves between them as
-- the line is typed, without anything being told where the cursor is beyond the
-- text itself.
narrows :: IO ()
narrows = do
  first  <- offerOf "quantify "
  second <- offerOf "quantify x "
  (wants first TName, wants first TCore) @?= (True, True)
  -- The point: once the Name is supplied, the Name slot is gone and only the
  -- Core slot remains. A grammar that did not carry types could not say this.
  (wants second TName, wants second TCore) @?= (False, True)

-- | The grammar is a reading of 'Thena.Rules.opWords', so nothing in it is a
-- second copy that can drift.
derived :: IO ()
derived = do
  s <- fst <$> startingSession
  let rs      = instralRules (sessionRules s)
      heads   = [ w | r <- rs, E.ruleHead r == statementHead
                    , E.Literal w : _ <- [E.ruleBody r] ]
      missing = [ w | (w, _) <- opWords, w `notElem` heads ]
  missing @?= []

empty :: IO ()
empty = do
  o <- offerOf ""
  case [ w | ALiteralSymbol w <- offeredOptions o ] of
    [] -> assertFailure "an empty line offered no statement word at all"
    ws -> if "quantify" `elem` ws && "attack" `elem` ws then pure () else
            assertFailure ("expected an op and a rule among " <> show (take 12 ws))

-- | A rule of the shipped base is a statement too — @attack@ is a rule, not an
-- op, and 'Thena.Rules.allCallable' is where it comes from.
callable :: IO ()
callable = do
  o <- offerOf ""
  if ALiteralSymbol "attack" `elem` offeredOptions o then pure ()
    else assertFailure "the shipped base's own rules are not offered"

-- | An op's arity is read from its signature, so a nullary op offers nothing
-- after it and a binary one offers two slots' worth.
arity :: IO ()
arity = do
  let Signature ps _ = signatureOf (opOf "unify")
  length ps @?= 2
  o <- offerOf "unify "
  offeredRest o @?= Just [ANonterminalSymbol (operandHead TCore)
                         , ANonterminalSymbol (operandHead TCore)]
  where
    opOf w = case lookup w opWords of
      Just op -> op
      Nothing -> error "unify is not in the op table"

-- | Phase 134's answer composes with this one for free: a line that is no
-- statement has nothing at the cursor, and says where it gave out instead of
-- being silent.
stuck :: IO ()
stuck = do
  o <- offerOf "zzz "
  case offeredStuck o of
    Nothing -> assertFailure "a nonsense word offered nothing and explained nothing"
    Just (StuckView at expected) -> do
      at @?= 0
      if null expected then assertFailure "stuck with nothing expected" else pure ()
      offeredOptions o @?= []
