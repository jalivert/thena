-- | An Earley parser over characters (MS6 phase 102; @ms6\/SPEC.md@ §7.2–7.7).
--
-- **Scannerless.** A chart column per /piece/ of input — a character, or a hole
-- or splice (§7.6) — not per token, because what a token is depends on which
-- items are live: at a column only the terminals the live items expect are
-- tried (§7.3). A literal matches its text; a token class tries **every
-- length its regex matches**, so @p -> x "y"@ on @aby@ finds @ab@ then @y@,
-- and a reading that swallows a @)@ simply never completes. Whitespace is
-- skipped before each scan, so it is optional between object tokens.
--
-- **The grammar here is generic** — literals, regex scans, nonterminals — and
-- knows nothing of @language@ blocks. "Thena.Language.Grammar.earleyRules"
-- turns installed grammars into one. That is §7.7's intent: the surface, Core
-- and DC grammars could be served by this same parser; MS6 serves object
-- languages only.
--
-- **The chart is the interface** (§7.7): 'chart' builds it, and it is queried
-- for the live items at a column ('itemsAt'), what they expect
-- ('expectedAt'), the completed parses ('readings'), and how far anything got
-- ('furthest'). 'parse' is those queries composed; MS7's editor will ask them
-- directly, and phase 102b's Tab completion already does.
--
-- There are no empty rules and every scan consumes at least one piece, so no
-- nonterminal is nullable and the textbook predictor/completer needs no fix.
module Thena.Language.Earley
  ( -- * Grammars
    Symbol (..)
  , Rule (..)
  , Start (..)
    -- * Input
  , Piece (..)
  , pieces
    -- * The chart
  , Chart
  , Item (..)
  , chart
  , chartRule
  , itemsAt
  , expectedAt
  , furthest
  , inputLength
    -- * Parses
  , Tree (..)
  , Reading (..)
  , readings
  , ParseFailure (..)
  , parse
  ) where

import Data.Char (isSpace)
import Data.List (nub)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Thena.Language.Regex (Regex, matches)

-- ---------------------------------------------------------------------------
-- Grammars

data Symbol
  = Literal String          -- ^ matched character by character
  | Scan String Regex       -- ^ a token class, by name, and its expression
  | Nonterminal String
  deriving (Eq, Show)

-- | @head -> body@. The name is the production's, which is what a 'Tree' node
-- records.
data Rule = Rule
  { ruleName :: String
  , ruleHead :: String
  , ruleBody :: [Symbol]
  , ruleSame :: [(String, [Int])]
    -- ^ **the non-linear groups** (§4.3): a name written more than once, and
    -- its positions among the rule's /slot/ children (its 'Scan's and
    -- 'Nonterminal's, in order) — which must all parse to the same thing (§7.4)
  }
  deriving (Eq, Show)

-- | Where a parse starts: any rule of a nonterminal, or one rule only — which
-- is what @LC[var]`…`@ will ask for (§8).
data Start = StartAt String | StartRule String
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Input

-- | One column's worth of input.
data Piece
  = Char Char
  | Hole       -- ^ a missing slot (§7.6): completes any expected slot, never a terminal
  | Splice Int -- ^ a slot's value supplied from outside, by index (§7.6, phase 104)
  deriving (Eq, Show)

-- | Text as pieces, with @?@ as a hole — the REPL's spelling (his ruling,
-- 2026-09-19), writable until the structural editor.
pieces :: String -> [Piece]
pieces = map (\c -> if c == '?' then Hole else Char c)

-- ---------------------------------------------------------------------------
-- The chart

-- | A rule, how much of its body is recognised, and the column it began at.
data Item = Item
  { itemRule   :: Int
  , itemDot    :: Int
  , itemOrigin :: Int
  }
  deriving (Eq, Ord, Show)

data Chart = Chart
  { chartRules   :: Map Int Rule
  , chartStart   :: Start
  , chartInput   :: Map Int Piece
  , inputLength  :: Int
  , chartColumns :: Map Int (Set Item)
  }

chartRule :: Chart -> Item -> Rule
chartRule c i = chartRules c Map.! itemRule i

-- | The items live at a column — those that have recognised everything up to it.
itemsAt :: Chart -> Int -> [Item]
itemsAt c k = maybe [] Set.toList (Map.lookup k (chartColumns c))

-- | What may be written at a position: the symbol after each dot of the items
-- live there. **Whitespace is looked back over**, because it is skipped when
-- scanning rather than when items are placed: after @"( "@ the items that
-- expect @λ@ sit at column 1, and position 2 — where a cursor would be — has
-- none of its own.
expectedAt :: Chart -> Int -> [Symbol]
expectedAt c k = nub [ s | i <- itemsAt c (settled k), Just s <- [next c i] ]
  where
    settled j
      | j > 0, null (itemsAt c j), Just (Char ch) <- Map.lookup (j - 1) (chartInput c), isSpace ch =
          settled (j - 1)
      | otherwise = j

-- | The last column any item reached. Past it, nothing could be scanned.
furthest :: Chart -> Int
furthest c = maybe 0 fst (Map.lookupMax (Map.filter (not . Set.null) (chartColumns c)))

next :: Chart -> Item -> Maybe Symbol
next c i = case drop (itemDot i) (ruleBody (chartRule c i)) of
  s : _ -> Just s
  []    -> Nothing

-- | Recognise, column by column: close each column under prediction and
-- completion, then scan from it into later ones.
chart :: [Rule] -> Start -> [Piece] -> Chart
chart rs start input = go 0 (Map.singleton 0 (Set.fromList starting))
  where
    rules = Map.fromList (zip [0 ..] rs)
    inp = Map.fromList (zip [0 ..] input)
    n = length input
    starting = [ Item k 0 0 | (k, r) <- Map.toList rules, isStart r ]
    isStart r = case start of
      StartAt h   -> ruleHead r == h
      StartRule p -> ruleName r == p
    base = Chart rules start inp n

    go k cols
      | k > n = base cols
      | otherwise =
          let col = closure k cols (maybe Set.empty id (Map.lookup k cols))
              cols' = Map.insert k col cols
              scanned = concatMap (scan k) (Set.toList col)
              cols'' = foldl (\m (j, it) -> Map.insertWith Set.union j (Set.singleton it) m) cols' scanned
           in go (k + 1) cols''

    symbolAfter it = case drop (itemDot it) (ruleBody (rules Map.! itemRule it)) of
      s : _ -> Just s
      []    -> Nothing

    -- Predict and complete to a fixed point. Every completed item began at an
    -- earlier column — nothing is nullable — so completion reads columns that
    -- are already closed.
    closure k cols = loop
      where
        loop set =
          let new = Set.fromList (concatMap step (Set.toList set)) `Set.difference` set
           in if Set.null new then set else loop (set `Set.union` new)
        step it = case symbolAfter it of
          Just (Nonterminal h) -> [ Item r 0 k | (r, rule) <- Map.toList rules, ruleHead rule == h ]
          Just _ -> []
          Nothing ->
            let h = ruleHead (rules Map.! itemRule it)
                o = itemOrigin it
             in [ it' { itemDot = itemDot it' + 1 }
                | o < k
                , it' <- maybe [] Set.toList (Map.lookup o cols)
                , symbolAfter it' == Just (Nonterminal h)
                ]

    -- What this item can consume starting at column k, and where it lands.
    scan k it = case symbolAfter it of
      Nothing -> []
      Just s ->
        let p = skipSpace inp k
            advanced j = (j, it { itemDot = itemDot it + 1 })
         in case (s, Map.lookup p inp) of
              (Nonterminal _, Just h) | slotPiece h -> [advanced (p + 1)]
              (Scan _ _, Just h) | slotPiece h -> [advanced (p + 1)]
              (Scan _ re, _) ->
                [ advanced (p + l) | l <- matches re (charsFrom inp p), l > 0 ]
              (Literal t, _)
                | charsFrom inp p `startsWith` t -> [advanced (p + length t)]
              _ -> []

    startsWith xs ys = take (length ys) xs == ys

slotPiece :: Piece -> Bool
slotPiece p = case p of
  Char _ -> False
  _      -> True

-- | The first column at or after @k@ that is not whitespace.
skipSpace :: Map Int Piece -> Int -> Int
skipSpace inp k = case Map.lookup k inp of
  Just (Char c) | isSpace c -> skipSpace inp (k + 1)
  _ -> k

-- | The run of characters from a column, up to the first hole, splice or end.
charsFrom :: Map Int Piece -> Int -> String
charsFrom inp k = case Map.lookup k inp of
  Just (Char c) -> c : charsFrom inp (k + 1)
  _ -> []

-- ---------------------------------------------------------------------------
-- Parses

-- | A derivation. A node's children are its **slots** in order — terminals
-- contribute nothing — so @abs@ over @( λ x : T . E[x] )@ has three.
data Tree
  = Node String [Tree]
  | Token String        -- ^ the text a token class matched
  | HoleAt Int          -- ^ a missing slot, at its column
  | SpliceOf Int
  deriving (Eq, Show)

-- | One complete derivation of the input: a reading, or the news that there
-- are unboundedly many because a nonterminal derives itself over the same
-- text, or one the non-linear filter refused — kept, rather than dropped, so
-- that a term refused /only/ by the filter can say why.
data Reading
  = Reading Tree
  | Cycle String
  | Unequal String String Tree Tree
    -- ^ the rule, the repeated name, and two of its occurrences that differ
  deriving (Eq, Show)

-- | Every reading of the whole input, **lazily**: 'parse' asks for two.
--
-- **The non-linear filter is here, on derivations** (§7.4), never in the
-- recogniser: a node whose repeated name parsed two different ways is dropped.
-- A hole or splice is compatible with anything, since nothing can refute it.
--
-- **A cycle is found, not followed.** A rule like @wrap -> M@ derives @M@ over
-- the same text it started with, forever; the walk keeps the spans it is
-- inside, and meeting one again yields 'Cycle' instead of descending.
readings :: Chart -> [Reading]
readings c =
  [ r
  | j <- [0 .. inputLength c]
  , skipSpace (chartInput c) j == inputLength c
  , it <- itemsAt c j
  , itemOrigin it == 0
  , let rule = chartRule c it
  , itemDot it == length (ruleBody rule)
  , startsHere rule
  , r <- ofRule [] (itemRule it) 0 j
  ]
  where
    startsHere rule = case chartStart c of
      StartAt h   -> ruleHead rule == h
      StartRule p -> ruleName rule == p

    inp = chartInput c
    has k it = maybe False (Set.member it) (Map.lookup k (chartColumns c))

    -- Readings of rule @r@, complete, over @i@ to @j@.
    ofRule stack r i j =
      [ case kids of
          Left why -> why
          Right ts -> maybe (Reading (Node (ruleName rule) ts)) id (unequal rule ts)
      | kids <- children stack r (length (ruleBody rule)) i j
      ]
      where rule = chartRules c Map.! r

    -- The slot children of the first @k@ symbols of rule @r@ over @i@ to @j@.
    children stack r k i j
      | k == 0 = [Right [] | i == j]
      | otherwise =
          [ combine before here
          | m <- [i .. j]
          , k - 1 == 0 && m == i || k - 1 > 0 && has m (Item r (k - 1) i)
          , here <- child stack (ruleBody (chartRules c Map.! r) !! (k - 1)) m j
          , before <- children stack r (k - 1) i m
          ]

    combine before here = case (before, here) of
      (Left x, _) -> Left x
      (_, Left x) -> Left x
      (Right ts, Right Nothing) -> Right ts
      (Right ts, Right (Just t)) -> Right (ts ++ [t])

    -- One symbol over @m@ to @j@: 'Nothing' for a terminal, a tree for a slot.
    child stack s m j =
      let p = skipSpace inp m
       in case (s, Map.lookup p inp) of
            (Nonterminal _, Just piece) | slotPiece piece, j == p + 1 -> [Right (Just (slotTree p piece))]
            (Scan _ _, Just piece) | slotPiece piece, j == p + 1 -> [Right (Just (slotTree p piece))]
            (Literal t, _)
              | j == p + length t, take (length t) (charsFrom inp p) == t -> [Right Nothing]
              | otherwise -> []
            (Scan _ re, _)
              | j > p, (j - p) `elem` matches re (take (j - p) (charsFrom inp p)) ->
                  [Right (Just (Token (take (j - p) (charsFrom inp p))))]
              | otherwise -> []
            (Nonterminal h, _)
              | (h, m, j) `elem` stack -> [Left (Cycle h)]
              | otherwise ->
                  [ fmap Just (readingTree r)
                  | it <- itemsAt c j
                  , itemOrigin it == m
                  , let rule = chartRule c it
                  , ruleHead rule == h
                  , itemDot it == length (ruleBody rule)
                  , r <- ofRule ((h, m, j) : stack) (itemRule it) m j
                  ]

    readingTree r = case r of
      Reading t -> Right t
      other     -> Left other

    slotTree p piece = case piece of
      Splice k -> SpliceOf k
      _        -> HoleAt p

-- | The first repeated name whose occurrences do not all agree, if any.
unequal :: Rule -> [Tree] -> Maybe Reading
unequal rule kids =
  case [ Unequal (ruleName rule) x t u
       | (x, ps) <- ruleSame rule
       , t : ts <- [[ kids !! p | p <- ps, p < length kids ]]
       , u : _ <- [filter (not . compatible t) ts]
       ] of
    r : _ -> Just r
    [] -> Nothing

compatible :: Tree -> Tree -> Bool
compatible a b = case (a, b) of
  (HoleAt _, _) -> True
  (_, HoleAt _) -> True
  (SpliceOf _, _) -> True
  (_, SpliceOf _) -> True
  (Token x, Token y) -> x == y
  (Node f xs, Node g ys) -> f == g && length xs == length ys && and (zipWith compatible xs ys)
  _ -> False

-- | Why the input is not one term.
data ParseFailure
  = Stuck Int [Symbol]
    -- ^ the column of the first piece nothing could consume — the input's
    -- length if it ended too soon — and what was expected there
  | Ambiguous Tree Tree
    -- ^ two of its readings (§7.5)
  | Unbounded String
    -- ^ it has unboundedly many readings, through a rule of this nonterminal
    -- deriving itself
  | Disagrees String String Tree Tree
    -- ^ it has no reading but ones the non-linear filter refused (§7.4): the
    -- rule, the repeated name, and two occurrences that differ
  deriving (Eq, Show)

-- | The one reading, or why there is not exactly one.
parse :: [Rule] -> Start -> [Piece] -> Either ParseFailure Tree
parse rs start input = case take 2 [ t | Reading t <- all' ] of
  [a, b] -> Left (Ambiguous a b)
  found
    | h : _ <- [ h | Cycle h <- all' ] -> Left (Unbounded h)
    | [t] <- found -> Right t
    | Unequal r x a b : _ <- [ u | u@Unequal {} <- all' ] -> Left (Disagrees r x a b)
    | otherwise ->
        let k = furthest c
         in Left (Stuck (skipSpace (chartInput c) k) [ s | s <- expectedAt c k, terminal s ])
  where
    c = chart rs start input
    all' = readings c
    terminal s = case s of
      Nonterminal _ -> False
      _ -> True
