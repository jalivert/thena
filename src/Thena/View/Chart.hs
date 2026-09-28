-- | The Earley chart's own questions, as a view (MS7 phase
-- 115e; @ms7\/MS7.md@'s ruling of 2026-09-24, and @discussion\/editor-display.md@
-- §7's mention of the dropdown story).
--
-- **This builds nothing new.** 'Thena.Language.Earley' says of itself that
-- "the chart is the interface" and that "MS7's editor will ask them
-- directly" — the chart already answers what may stand at a position, the
-- completed readings, and how far anything got; the terminal's own @:parse@
-- mode and its Tab completion already ask it these questions (MS6 phase
-- 102b). This module gives those answers a shape an editor can lay out,
-- instead of a second one.
--
-- **Two questions, because the engine already has two functions for them.**
-- 'Earley.parse' is "is the whole text one term, and if not, why" — one
-- reading, an ambiguity between two, an unbounded rule, a non-linear clash,
-- or how far it got before it was stuck. 'Earley.offer' is what may be
-- written at the cursor, what the position is waiting for, and the rest of
-- the production the cursor is inside — the dropdown itself. Nothing here
-- composes them further than the engine already does; 'displayParse' and
-- 'displayOffer' are direct wrappers.
--
-- **A 'Earley.Symbol' does not cross whole.** Its 'Thena.Language.Regex.Regex'
-- is how a scan recognises text, not something the editor renders or acts
-- on; only the name it reports itself by ("a variable", "a digit") is
-- what crosses, exactly what the terminal already shows in its own
-- expectation lists (@Thena.Repl.parseFailureReason@'s @symbolText@).
--
-- **'displayOffer' takes a region the way the editor holds one — MS7 phase
-- 125.** It used to take the text left and right of the cursor as two
-- 'String's and always start at a language, which could express neither a
-- splice nor an explicit production, so his own TUI could not use it: it went
-- to 'Earley.offer' directly and rebuilt 'OfferView' by hand, together with
-- the two checks below. That is the dropdown this module exists for, so the
-- signature is the one a frontend needs rather than the one @:parse@'s Tab
-- happened to have.
module Thena.View.Chart
  ( SymbolView (..)
  , TreeView (..)
  , FailureView (..)
  , OfferView (..)
  , Written (..)
  , ProductionView (..)
  , OfferProblem (..)
  , displayParse
  , displayOffer
  ) where

import Data.List (intersperse)

import Thena.Language.Build (languageNames, productionNames)
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
  | APlaceholderAt Int
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
  { offeredOptions :: [SymbolView]
    -- ^ what may be written at the cursor such that the line can still be
    -- finished, each tried together with enough of its own production to
    -- know it reaches — see 'Earley.offerOptions'.
  , offeredWanted :: [SymbolView]
    -- ^ what a production already open is waiting for even though no
    -- insertion would leave the line finishable, and which 'offeredOptions'
    -- therefore does not carry — see 'Earley.offerWanted'. A frontend that
    -- wants to say so may mark these differently; the terminal, which cannot,
    -- lists them beside the rest.
  , offeredReplaces :: Bool
    -- ^ **the cursor is standing on a placeholder, and taking any of these
    -- consumes it** (MS7 phase 127).
    --
    -- The editor says so by putting 'WrittenPlaceholder' first in the text to
    -- the right of the cursor, which is what \"the cursor is in the box\" is;
    -- the offer is then computed as though the placeholder were not there, so
    -- what is offered is what may stand /in/ it rather than beside it.
    --
    -- **This is what @Thena.Repl.tabComplete@ could never express and why his
    -- own TUI put the option in front of the placeholder instead of over it.**
    -- haskeline's completion can only rewrite text to the /left/ of the cursor
    -- (@CompletionFunc@ returns the surviving prefix of the left side), so the
    -- terminal has to be standing just /after/ a placeholder to replace one at
    -- all. A frontend that owns its buffer has no such constraint, and this
    -- field is what tells it there is something to delete.
    --
    -- **Nothing is filtered on account of it.** A lone slot offered into a
    -- placeholder would replace a box with a box, which is a no-op — and which
    -- of the offers are worth showing is the editor's, not ours.
  , offeredRest :: Maybe [SymbolView]
    -- ^ the rest of the one production the cursor is inside, as much of it as
    -- the text after the cursor does not already supply — see
    -- 'Earley.offerRest'.
  , offeredProductions :: [ProductionView]
    -- ^ **every production that may begin at the cursor, to list and to insert**
    -- (MS7 phase 127b) — see 'Earley.offerProductions'.
  }
  deriving (Eq, Show)

-- | A production a frontend may offer whole: what to call it, what it looks
-- like, and what to put in the buffer when it is chosen.
--
-- **His request of 2026-09-28**, and the reason it is three fields rather than
-- one: /\"I want to see something like @app: ( LC LC )@ and when I select it, I
-- get @( \9608 \9608 )@\"/. The label and the insertion are different renderings
-- of the same body — a slot reads as @\8249LC\8250@ in a list and stands as a
-- placeholder in a buffer — so the view carries both rather than making every
-- frontend derive the second from the first.
data ProductionView = ProductionView
  { productionName :: String
    -- ^ the constructor the production declares, which is what to call it in a
    -- list.
  , productionShape :: [SymbolView]
    -- ^ its body, for the label. Slots are 'ANonterminalSymbol' and
    -- 'AScanSymbol', so a frontend shows what /kind/ of thing goes where.
  , productionInsert :: [Written]
    -- ^ **the same body as a region to insert**: its terminals as text, its
    -- slots as placeholders, one space between. A frontend puts this in its
    -- buffer and already knows where the boxes are, because they are runs and
    -- not characters it has to go looking for.
  }
  deriving (Eq, Show)

-- | Is this region one term of this language, and if not, why. The whole-text
-- question a finished line of object syntax is asked — the same one
-- @:parse@'s mode and an @ObjectRegionUnparsed@ report already answer in
-- words (@Thena.Repl.renderUnparsed@).
--
-- **No check on the names, unlike 'displayOffer', and that is not an
-- inconsistency.** A region written in a language nothing declared reads as a
-- region nothing could read — 'AStuck' at its first piece, which is true and is
-- what a reader owes. An /offer/ has no such answer: \"nothing may stand here\"
-- and \"there is no such language\" would be the same empty list, so that one
-- has to say which.
displayParse
  :: [Grammar]
  -> String          -- ^ the language the region is in
  -> Maybe String    -- ^ the production it was written with, if any
  -> [Written]
  -> Either FailureView TreeView
displayParse gs lang prod region =
  either (Left . failureView) (Right . treeView)
    (Earley.parse (earleyRules gs) (startOf lang prod) (fst (piecesFrom 0 region)))

-- | One run of a region, as an editor holds it: characters the user typed, or
-- a splice standing for a host term the object grammar cannot read (§7.6).
--
-- **A splice is numbered by its position in the list**, which is how
-- 'Earley.Splice' numbers them and how "Thena.Language.Build" pairs them with
-- the host terms written beside the region. Nothing carries the index, so
-- nothing can disagree about it.
data Written
  = WrittenText String   -- ^ written characters
  | WrittenSplice        -- ^ one splice
  | WrittenPlaceholder
    -- ^ **one part of the term not written yet** (MS7 phase 127).
    --
    -- **The same thing as 'Thena.Language.Earley.placeholderChar' inside a
    -- 'WrittenText', said the other way.** A frontend that keeps its
    -- placeholders as positions — which it must, if a box is to come back when
    -- the cursor leaves it — hands them over as runs and never splices a glyph
    -- into a string; a frontend that has only text puts the character in. Both
    -- reach the reader as 'Thena.Language.Earley.Placeholder'.
  deriving (Eq, Show)

-- | Why there is no offer to make: the region names something that is not
-- loaded. Structured, not a sentence (§12).
data OfferProblem
  = NoSuchLanguage String
  | NoSuchProduction String String  -- ^ the language, and the production asked for
  deriving (Eq, Show)

-- | What may be written at the cursor sitting between @before@ and @after@ —
-- the dropdown his design calls for (@discussion\/editor-display.md@ §7),
-- and the same question phase 102b's Tab already asks
-- (@Thena.Repl.tabComplete@).
--
-- The region reads as a term of @lang@, or of one named production of it when
-- the editor has already committed to one — 'Earley.StartAt' and
-- 'Earley.StartRule', which is the difference between a tagged region and a
-- tagged region with a production written on it.
displayOffer
  :: [Grammar]
  -> String          -- ^ the language the region is in
  -> Maybe String    -- ^ the production it was written with, if any
  -> [Written]       -- ^ left of the cursor
  -> [Written]       -- ^ right of the cursor
  -> Either OfferProblem OfferView
displayOffer gs lang prod before after
  | lang `notElem` languageNames gs = Left (NoSuchLanguage lang)
  | Just p <- prod, p `notElem` productionNames gs lang = Left (NoSuchProduction lang p)
  | otherwise =
      Right (offerView replacing (Earley.offer (earleyRules gs) (startOf lang prod) left right))
  where
    -- The cursor is in the box when the box is the first thing to its right.
    (replacing, after') = case after of
      WrittenPlaceholder : rest -> (True, rest)
      _                         -> (False, after)
    -- **The two sides are numbered as one region**, so the first splice to the
    -- right of the cursor continues the count rather than restarting it: a
    -- region has one list of host terms beside it, and which splice is which
    -- does not depend on where the cursor happens to stand.
    (left, k0) = piecesFrom 0 before
    (right, _) = piecesFrom k0 after'

-- | A region reads as a term of its language, or of the one production it was
-- written with — 'Earley.StartAt' and 'Earley.StartRule', which is the
-- difference between a tagged region and a tagged region with a production
-- written on it.
startOf :: String -> Maybe String -> Earley.Start
startOf lang = maybe (Earley.StartAt lang) Earley.StartRule

-- | Written runs as the reader's columns, numbering the splices as it goes, and
-- the next free index.
piecesFrom :: Int -> [Written] -> ([Earley.Piece], Int)
piecesFrom k0 = go k0
  where
    go k []                     = ([], k)
    go k (WrittenText t : rest)      = let (ps, k') = go k rest in (Earley.pieces t ++ ps, k')
    go k (WrittenSplice : rest)      = let (ps, k') = go (k + 1) rest in (Earley.Splice k : ps, k')
    go k (WrittenPlaceholder : rest) = let (ps, k') = go k rest in (Earley.Placeholder : ps, k')

offerView :: Bool -> Earley.Offer -> OfferView
offerView replacing o =
  OfferView
    (map symbolView (Earley.offerOptions o))
    (map symbolView (Earley.offerWanted o))
    replacing
    (fmap (map symbolView) (Earley.offerRest o))
    [ ProductionView n (map symbolView body) (insertion body)
    | (n, body) <- Earley.offerProductions o
    ]

-- | A production's body as a region to insert: terminals as text, slots as
-- placeholders, one space between.
--
-- **Adjacent text is merged**, so @( LC LC )@ inserts as three runs and not
-- seven: the spaces belong to the text beside them, and a frontend stepping
-- between the boxes should not have to skip empty runs to do it.
insertion :: [Earley.Symbol] -> [Written]
insertion = merge . intersperse (WrittenText " ") . map one
  where
    one s = case s of
      Earley.Literal t -> WrittenText t
      _                -> WrittenPlaceholder
    merge (WrittenText a : WrittenText b : rest) = merge (WrittenText (a <> b) : rest)
    merge (w : rest)                             = w : merge rest
    merge []                                     = []

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
  Earley.PlaceholderAt p -> APlaceholderAt p
  Earley.SpliceOf k -> ASpliceOf k
