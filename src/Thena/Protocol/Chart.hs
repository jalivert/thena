-- | The Earley chart's own questions, exposed to the protocol (MS7 phase
-- 115e; @ms7\/MS7.md@'s ruling of 2026-09-24, and @discussion\/editor-display.md@
-- §7's mention of the dropdown story).
--
-- **This builds nothing new.** 'Thena.Language.Earley' says of itself that
-- "the chart is the interface" and that "MS7's editor will ask them
-- directly" — the chart already answers what may stand at a position, the
-- completed readings, and how far anything got; the terminal's own @:parse@
-- mode and its Tab completion already ask it these questions (MS6 phase
-- 102b). This module gives those answers a protocol shape instead of a
-- second one.
--
-- **Two questions, because the engine already has two functions for them.**
-- 'Earley.parse' is "is the whole text one term, and if not, why" — one
-- reading, an ambiguity between two, an unbounded rule, a non-linear clash,
-- or how far it got before it was stuck. 'Earley.offer' is "what may be
-- written at the cursor such that the line can still be finished" — the
-- dropdown itself. Nothing here composes them further than the engine
-- already does; 'displayParse' and 'displayOffer' are direct wrappers.
--
-- **A 'Earley.Symbol' does not cross whole.** Its 'Thena.Language.Regex.Regex'
-- is how a scan recognises text, not something the editor renders or acts
-- on; only the name it reports itself by ("a variable", "a digit") is
-- protocol shape, exactly what the terminal already shows in its own
-- expectation lists (@Thena.Repl.parseFailureReason@'s @symbolText@).
module Thena.Protocol.Chart
  ( SymbolView (..)
  , TreeView (..)
  , FailureView (..)
  , OfferView (..)
  , displayParse
  , displayOffer
  ) where

import Thena.Language.Grammar (Grammar, earleyRules)
import qualified Thena.Language.Earley as Earley

-- | A rule's right-hand-side symbol, display-safe.
data SymbolView
  = ALiteralSymbol String
  | AScanSymbol String
  | ANonterminalSymbol String
  deriving (Eq, Show)

-- | One parse tree, mirroring 'Earley.Tree': a production applied to its
-- slots in order, a scanned token's text, a hole at the column it was left,
-- or a spliced value's index (phase 104).
data TreeView
  = ANode String [TreeView]
  | ATokenView String
  | AHoleAt Int
  | ASpliceOf Int
  deriving (Eq, Show)

-- | Why a text is not one term, mirroring 'Earley.ParseFailure'.
data FailureView
  = AStuck Int [SymbolView]
    -- ^ the column of the first piece nothing could consume — the text's
    -- length if it ended too soon — and what was expected there.
  | AnAmbiguity TreeView TreeView
    -- ^ two of its readings.
  | AnUnboundedRule String
    -- ^ it has unboundedly many readings, through a rule of this
    -- nonterminal deriving itself.
  | ADisagreement String String TreeView TreeView
    -- ^ the rule, the repeated name written more than once, and two
    -- occurrences that parsed to different things.
  deriving (Eq, Show)

-- | What may stand at the cursor, mirroring 'Earley.Offer'.
data OfferView = OfferView
  { offeredOptions    :: [SymbolView]
    -- ^ what may be written at the cursor such that the line can still be
    -- finished, each tried together with enough of its own production to
    -- know it reaches — see 'Earley.offerOptions'.
  , offeredCompletion :: Maybe [SymbolView]
    -- ^ the rest of the one production the text just before the cursor
    -- belongs to, when nothing but whitespace follows — see
    -- 'Earley.offerCompletion'.
  }
  deriving (Eq, Show)

-- | Is this text one term of this language, and if not, why. The whole-text
-- question a finished line of object syntax is asked — the same one
-- @:parse@'s mode and an @ObjectRegionUnparsed@ report already answer in
-- words (@Thena.Repl.renderUnparsed@).
displayParse :: [Grammar] -> String -> String -> Either FailureView TreeView
displayParse gs lang text =
  either (Left . failureView) (Right . treeView)
    (Earley.parse (earleyRules gs) (Earley.StartAt lang) (Earley.pieces text))

-- | What may be written at the cursor sitting between @before@ and @after@ —
-- the dropdown his design calls for (@discussion\/editor-display.md@ §7),
-- and the same question phase 102b's Tab already asks
-- (@Thena.Repl.tabComplete@).
displayOffer :: [Grammar] -> String -> String -> String -> OfferView
displayOffer gs lang before after =
  offerView (Earley.offer (earleyRules gs) (Earley.StartAt lang) (Earley.pieces before) (Earley.pieces after))

offerView :: Earley.Offer -> OfferView
offerView o = OfferView (map symbolView (Earley.offerOptions o)) (fmap (map symbolView) (Earley.offerCompletion o))

failureView :: Earley.ParseFailure -> FailureView
failureView f = case f of
  Earley.Stuck p expected -> AStuck p (map symbolView expected)
  Earley.Ambiguous a b -> AnAmbiguity (treeView a) (treeView b)
  Earley.Unbounded h -> AnUnboundedRule h
  Earley.Disagrees r x a b -> ADisagreement r x (treeView a) (treeView b)

symbolView :: Earley.Symbol -> SymbolView
symbolView s = case s of
  Earley.Literal t -> ALiteralSymbol t
  Earley.Scan n _ -> AScanSymbol n
  Earley.Nonterminal n -> ANonterminalSymbol n

treeView :: Earley.Tree -> TreeView
treeView t = case t of
  Earley.Node n cs -> ANode n (map treeView cs)
  Earley.Token x -> ATokenView x
  Earley.HoleAt p -> AHoleAt p
  Earley.SpliceOf k -> ASpliceOf k
