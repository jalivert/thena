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
-- expectation lists (@Thena.Render.parseFailureReason@'s @symbolText@).
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
  , StuckView (..)
  , RecoveryView (..)
  , BoundView (..)
  , OfferProblem (..)
  , displayParse
  , displayOffer
  , offerAt
  ) where

import Data.List (intersperse, nub)

import Thena.Language.Build (languageNames, productionNames)
import Thena.Language.Grammar (Grammar, earleyRules)
import Thena.View.Type (TypeView)
import Thena.Language.Builtin (publicHead)
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
  , offeredRecovered :: Maybe RecoveryView
    -- ^ **this answer is about the unit under the cursor, not about the line**
    -- (MS7 phase 138). 'Nothing' on the ordinary path, and on every region
    -- offer. When it is 'Just' the whole-line parse had nothing to say and the
    -- narrower question answered instead, so what comes back is context-free:
    -- completing @ to @ says nothing about whether @ may
    -- stand there. **Draw it differently** — his design: a different background,
    -- and the line underlined to say it will not run as written.
    --
    -- Defined in "Thena.View.Statement", which is where recovery lives.
  , offeredBound :: [BoundView]
    -- ^ **the names the instructions above the cursor left in scope, that may
    -- stand at it** (MS7 phase 140).
    --
    -- A prompt entry is a block: @h = here@ on one line and @goto h@ on the next
    -- is one entry, and @h@ is in scope on the second line. The chart can say
    -- /a name goes here/ and cannot say /which/ — a name three lines up is not a
    -- grammatical fact — so this is the answer to the second question, and the
    -- only field of an offer that depends on what the text above /means/ rather
    -- than on how it is written.
    --
    -- **Already filtered to the cursor.** A name is here only when its type may
    -- stand at the slot the cursor is in, which the engine decides
    -- ('Thena.Language.Instral.standsAt'); a frontend does not need the typing
    -- rule. Empty when the cursor is in the entry's first instruction, when the
    -- lines above do not run, or when nothing they bound fits.
    --
    -- Set in "Thena.View.Statement", which is where the entry is cut up.
  , offeredStuck :: Maybe StuckView
    -- ^ **the text left of the cursor does not read, and this says where it
    -- gave out** (MS7 phase 134, @ms7\/CLOSEOUT.md@ 12) — see
    -- 'Earley.offerStuck'.
    --
    -- 'Nothing' in the ordinary case. When it is 'Just', **every other field
    -- above is empty**, and a frontend should say what this one says instead
    -- of showing an empty dropdown: the four answers are all drawn from the
    -- items at the cursor's column, and a broken prefix leaves that column
    -- with none.
    --
    -- The distinction it buys is /\"nothing may be written here\"/ against
    -- /\"I could not read what you already wrote\"/, which a user reads as a
    -- broken key when both are silence.
  }
  deriving (Eq, Show)

-- | A name an entry bound above the cursor, and what it holds.
--
-- **The type is a view and not a rendered line** — his ruling, 2026-09-29:
-- /"I want it to be principled and correct and that means instral types get
-- views too"/, which @ms7\/CLOSEOUT.md@ 27 held open and phase 133 answered.
data BoundView = BoundView
  { boundName :: String
  , boundType :: TypeView
  }
  deriving (Eq, Show)

-- | Where a recovered answer came from, so a frontend can say so.
--
-- Present only when the whole-line parse had nothing at the cursor and the
-- narrower question answered instead. **A recovered offer is context-free**:
-- completing @atta@ to @attack@ says nothing about whether @attack@ may stand
-- there. That is the point, and it is why this must be drawn differently.
data RecoveryView = RecoveryView
  { recoveredColumn :: Int
    -- ^ where the unit under the cursor starts, counting from 1 — so a frontend
    -- knows which characters an accepted completion replaces.
    --
    -- **This is about replacing, not about drawing** — see 'recoveredSpan', which is
    -- about drawing and is not the same pair of positions for a tagged literal.
  , recoveredText :: String
    -- ^ the unit as written, up to the cursor.
  , recoveredLanguage :: Maybe String
    -- ^ @Just \"LC\"@ when the cursor is inside a tagged term literal, and the
    -- offer therefore came from that language's own grammar rather than from
    -- @instral@'s. 'Nothing' when it is a bare word.
  , recoveredSpan :: (Int, Int)
    -- ^ **the whole unit, to draw it as provisional** (MS7 phase 143): the first
    -- character, counting from 1, and one past the last.
    --
    -- **Why it is not 'recoveredColumn' and the cursor.** Those two say what an
    -- accepted completion overwrites, which for a bare word is the word and for a
    -- tagged literal is the content typed inside it — never the tag, or the fences,
    -- or anything right of the cursor. The thing to /underline/ is the unit, and for
    -- a literal the unit is the literal: @LC\`@ or @LC[var]\`@ through the closing
    -- backtick. **His ask, 2026-09-30, relayed through @.jalivert\/REPORT.md@**, and
    -- the tui track filed only the left half of it — the closing fence is past the
    -- cursor, which their entry explicitly set aside.
    --
    -- **It reaches past the cursor, and only this field does.** An unclosed literal
    -- — which is every literal being typed — ends at the line's end, because there
    -- is no fence to end it.
  }
  deriving (Eq, Show)

-- | Where a reading of the text left of the cursor gave out.
--
-- **Not a 'FailureView'**, though 'AStuck' carries the same two things: a
-- 'FailureView' answers /why this text is not one term/ and has four ways to
-- do it, of which only one could ever apply here. A 'Maybe' of a type whose
-- other three constructors cannot occur is the confusion the literal
-- alternative costs nothing to avoid.
data StuckView = StuckView
  { stuckAt :: Int
    -- ^ the column the reading reached — the last one any item did. Past it
    -- nothing could be scanned.
  , stuckExpected :: [SymbolView]
    -- ^ what could have stood there, which is what would have let it go on.
    -- **Not what may stand at the cursor** — the cursor is further right than
    -- this column, which is the whole reason there is nothing to say there.
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
-- words (@Thena.Render.renderUnparsed@).
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
  | otherwise = Right (offerAt (earleyRules gs) (startOf lang prod) before after)

-- | The offer at a cursor, given the rules and where a parse starts — the half
-- of 'displayOffer' that is not about an object language's name.
--
-- **Factored out at MS7 phase 137**, when @instral@ gained a grammar of its own
-- ("Thena.Language.Instral"): a statement is not a region, has no language name
-- to check and no production to be written at, but everything below this line
-- is exactly the same question. Splitting it here is what keeps the two from
-- being two implementations of one answer.
offerAt :: [Earley.Rule] -> Earley.Start -> [Written] -> [Written] -> OfferView
offerAt rs start before after =
  offerView replacing (Earley.offer rs start left right)
  where
    -- The cursor is in the box when the box is the first thing to its right.
    (replacing, after') = case runs after of
      WrittenPlaceholder : rest -> (True, rest)
      rest                      -> (False, rest)
    -- **The two sides are numbered as one region**, so the first splice to the
    -- right of the cursor continues the count rather than restarting it: a
    -- region has one list of host terms beside it, and which splice is which
    -- does not depend on where the cursor happens to stand.
    (left, k0) = piecesFrom 0 (runs before)
    (right, _) = piecesFrom k0 after'

-- | A box written as a character becomes a box written as a run.
--
-- 'Written' already says the two are one thing — @a frontend that has only text
-- puts the character in@ — but 'offerAt' asks about the /first run/ to the right
-- of the cursor, so the two forms answered differently until this normalised
-- them: a frontend handing its line over as one 'WrittenText' never got
-- 'offeredReplaces', and worse, was answered about what may stand /beside/ the
-- box rather than /in/ it, which is the empty list wherever the production has
-- no room beside it.
--
-- **Nothing else can tell the difference.** 'Earley.pieces' already reads the
-- character as 'Earley.Placeholder', so the piece stream is unchanged, and
-- splices are untouched so their numbering is too. An empty run is dropped,
-- which is the same normalisation one step further: an empty 'WrittenText' at
-- the head of @after@ would otherwise hide the box behind it.
runs :: [Written] -> [Written]
runs = concatMap one
  where
    one w = case w of
      WrittenText t -> split t
      _             -> [w]

    split t = case break (== Earley.placeholderChar) t of
      ([],  [])         -> []
      (pre, [])         -> [WrittenText pre]
      ([],  _ : post)   -> WrittenPlaceholder : split post
      (pre, _ : post)   -> WrittenText pre : WrittenPlaceholder : split post

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
    (symbolViews (Earley.offerOptions o))
    (symbolViews (Earley.offerWanted o))
    replacing
    (fmap (map symbolView) (Earley.offerRest o))
    -- **Not deduplicated**, unlike an offer: a body is a /shape/, and @app@'s
    -- @( LC LC )@ has two slots that must both be shown.
    [ ProductionView n (map symbolView body) (insertion body)
    | (n, body) <- Earley.offerProductions o
    ]
    -- Recovery is "Thena.View.Statement"'s, and it sets this afterwards: the
    -- chart cannot know it was asked a narrower question than the caller had.
    Nothing
    -- The entry's bound names are "Thena.View.Statement"'s too, for the same
    -- reason: the chart is handed one instruction and does not know there were
    -- others above it.
    []
    (fmap stuckView (Earley.offerStuck o))

stuckView :: (Int, [Earley.Symbol]) -> StuckView
stuckView (at, expected) = StuckView at (symbolViews expected)

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
  Earley.Stuck p expected -> AStuck p (symbolViews expected)
  Earley.Ambiguous a b -> AnAmbiguity (treeView a) (treeView b)
  Earley.Unbounded h -> AnUnboundedRule h
  Earley.Disagrees r x a b -> ADisagreement r x (treeView a) (treeView b)

-- | **The one funnel from a parser symbol to what a frontend sees**, and the
-- place the stratum convention is enforced (MS7 phase 147).
--
-- A nonterminal is reported by its 'Thena.Language.Builtin.publicHead' — the
-- part before a @\/@ — so @surface:Term\/arrowed@ arrives as @surface:Term@.
-- Thena's own grammars mirror Happy's precedence strata because flattening them
-- would accept terms the running parser refuses, and the strata are names this
-- system invented that no user has met. **The invariant is phase 141's, one size
-- up: nothing a frontend sees may be a nonterminal invented for plumbing.**
--
-- An object language's nonterminal, an @Operand:T@ and @instral:Argument@
-- contain no @\/@ and pass through unchanged — a language or metavariable cannot
-- contain one.
symbolView :: Earley.Symbol -> SymbolView
symbolView s = case s of
  Earley.Literal t -> ALiteralSymbol t
  Earley.Scan n _ -> AScanSymbol n
  Earley.Nonterminal n -> ANonterminalSymbol (publicHead n)

-- | **An offer's** symbols as a frontend sees it, deduplicated after the
-- mapping, because several strata of one head collapse onto it: the chart offers
-- @surface:Term\/arrowed@ and @surface:Term\/app@ at one cursor and a frontend
-- should be told /a surface term/ once.
--
-- **Only for a set of options**, never for a production's body — a body is a
-- shape, and @app: ( LC LC )@ has two slots. 'Thena.View.ChartTests' caught that
-- when this was applied to both.
symbolViews :: [Earley.Symbol] -> [SymbolView]
symbolViews = nub . map symbolView

treeView :: Earley.Tree -> TreeView
treeView t = case t of
  Earley.Node n cs -> ANode n (map treeView cs)
  Earley.Token x -> ATokenView x
  Earley.PlaceholderAt p -> APlaceholderAt p
  Earley.SpliceOf k -> ASpliceOf k
