-- | Regular expressions by Brzozowski derivatives (MS6 phase 99; @SPEC.md@
-- §3.2, §7.1).
--
-- A token class (§3) is a regular expression that arrives **at load time**,
-- inside the module being loaded, so Alex — which runs when Thena is compiled —
-- is no use for it. This module is the whole of what a token class needs:
--
-- * 'parseRegex' reads the concrete syntax of §3.2, and nothing more;
-- * 'matches' gives **every** prefix length a class accepts, which is what
--   Earley's context-aware scanning tries (§7.3) — not the longest one;
-- * 'dfa' and 'inclusion' decide §3.2's typing check, that a class's language
--   lies inside the one its type allows, with the shortest counterexample.
--
-- __The derivative.__ @derive c r@ is the regular expression accepting exactly
-- the strings @w@ for which @r@ accepts @c:w@. Matching is deriving by each
-- character in turn and asking 'nullable' at every step. A DFA's states are
-- the derivatives reachable from the start, and the reason there are finitely
-- many is the normal form below.
--
-- __The normal form, and why it is load-bearing.__ Brzozowski's theorem is that
-- a regular expression has finitely many derivatives /up to/ associativity,
-- commutativity and idempotence of alternation. The smart constructors
-- ('oneOf', 'andThen', 'alternatives', 'star') keep every expression they build
-- in that normal form, and 'derive' builds only through them — so two
-- derivatives with the same normal form are the same 'Regex' value, 'dfa'\'s
-- state table is keyed on it, and exploration stops. The raw constructors are
-- exported, for building a test's reference matcher and for reading an
-- expression apart: a hand-built 'Regex' outside the normal form is
-- representable, still means what it says, and costs at most one extra DFA
-- state at the root, because 'dfa' normalises it first.
--
-- __The alphabet is all of 'Char', and is never enumerated.__ Every character
-- set in an expression is a list of ranges, and a derivative only ever
-- contains character sets that were in the expression it came from. So the
-- range boundaries of the original expression cut 'Char' into intervals within
-- which every character has the same derivative, at every state — 'intervals'.
-- A DFA's edges are one per interval, and a character is looked up by the
-- interval it falls in.
module Thena.Language.Regex
  ( -- * Character sets
    CharSet
  , fromRanges
  , singleChar
  , complement
  , member
  , ranges
    -- * Regular expressions
  , Regex (..)
  , oneOf
  , andThen
  , alternatives
  , star
  , normalise
  , nullable
  , derive
  , matches
    -- * The concrete syntax (§3.2)
  , RegexError (..)
  , parseRegex
    -- * Automata and inclusion
  , Dfa
  , dfa
  , dfaStates
  , accepts
  , Inclusion (..)
  , inclusion
  ) where

import Data.Char (isAlphaNum)
import Data.List (sort)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set

-- ---------------------------------------------------------------------------
-- Character sets

-- | A set of characters, as ascending ranges that neither overlap nor touch.
--
-- The constructor is hidden because that invariant is what makes the derived
-- 'Eq' and 'Ord' mean set equality — and 'Regex'\'s normal form, and with it
-- the termination of 'dfa', is built on those two instances.
newtype CharSet = CharSet [(Char, Char)]
  deriving (Eq, Ord, Show)

-- | The set of the characters in these inclusive ranges. A range whose bounds
-- are the wrong way round contributes nothing — 'parseRegex' refuses one before
-- it gets here.
fromRanges :: [(Char, Char)] -> CharSet
fromRanges = CharSet . merge . sort . filter (uncurry (<=))
  where
    merge ((a, b) : (c, d) : rest)
      | b == maxBound || c <= succ b = merge ((a, max b d) : rest)
    merge (r : rest) = r : merge rest
    merge [] = []

singleChar :: Char -> CharSet
singleChar c = CharSet [(c, c)]

-- | Every character not in the set.
complement :: CharSet -> CharSet
complement (CharSet rs) = CharSet (go minBound rs)
  where
    go from ((a, b) : rest)
      | from < a = (from, pred a) : next
      | otherwise = next
      where
        next = if b == maxBound then [] else go (succ b) rest
    go from [] = [(from, maxBound)]

member :: Char -> CharSet -> Bool
member c (CharSet rs) = any (\(a, b) -> a <= c && c <= b) rs

ranges :: CharSet -> [(Char, Char)]
ranges (CharSet rs) = rs

union :: CharSet -> CharSet -> CharSet
union (CharSet a) (CharSet b) = fromRanges (a ++ b)

-- ---------------------------------------------------------------------------
-- Regular expressions

-- | A regular expression.
--
-- The two that are easy to confuse aloud have names that are not: 'NoMatch'
-- accepts no string at all, 'EmptyString' accepts exactly the empty one.
-- @r+@ and @r?@ from the concrete syntax are not constructors — they are
-- @r r*@ and @ε|r@, built by 'parseRegex'.
data Regex
  = NoMatch
  | EmptyString
  | OneOf CharSet
    -- ^ one character, from the set
  | Sequence Regex Regex
  | Alternatives [Regex]
    -- ^ in normal form: at least two, ascending, distinct, none of them itself
    -- an 'Alternatives' or a 'NoMatch', and at most one 'OneOf'
  | Star Regex
  deriving (Eq, Ord, Show)

-- | One character from the set; an empty set accepts nothing.
oneOf :: CharSet -> Regex
oneOf (CharSet []) = NoMatch
oneOf s = OneOf s

-- | @r@ then @s@. 'NoMatch' absorbs, 'EmptyString' is the unit, and a sequence
-- nests to the right, so that @(ab)c@ and @a(bc)@ are one value.
andThen :: Regex -> Regex -> Regex
andThen NoMatch _ = NoMatch
andThen _ NoMatch = NoMatch
andThen EmptyString s = s
andThen r EmptyString = r
andThen (Sequence a b) s = andThen a (andThen b s)
andThen r s = Sequence r s

-- | Any of these. This is the constructor Brzozowski's theorem is about: it
-- flattens nested alternatives, sorts them, drops duplicates and 'NoMatch',
-- and merges every 'OneOf' among them into one.
alternatives :: [Regex] -> Regex
alternatives rs =
  case merged of
    [] -> NoMatch
    [r] -> r
    _ -> Alternatives merged
  where
    flat = concatMap flatten rs
    flatten (Alternatives xs) = xs
    flatten NoMatch = []
    flatten r = [r]
    sets = [s | OneOf s <- flat]
    others = [r | r <- flat, not (isOneOf r)]
    isOneOf (OneOf _) = True
    isOneOf _ = False
    single = [oneOf (foldr1 union sets) | not (null sets)]
    merged = Set.toAscList (Set.fromList (single ++ others))

-- | Zero or more.
star :: Regex -> Regex
star NoMatch = EmptyString
star EmptyString = EmptyString
star r@(Star _) = r
star r = Star r

-- | Rebuild through the smart constructors. Only ever needed at a root built
-- by hand; everything 'derive' and 'parseRegex' produce is already normal.
normalise :: Regex -> Regex
normalise NoMatch = NoMatch
normalise EmptyString = EmptyString
normalise (OneOf s) = oneOf s
normalise (Sequence r s) = andThen (normalise r) (normalise s)
normalise (Alternatives rs) = alternatives (map normalise rs)
normalise (Star r) = star (normalise r)

-- | Does it accept the empty string?
nullable :: Regex -> Bool
nullable NoMatch = False
nullable EmptyString = True
nullable (OneOf _) = False
nullable (Sequence r s) = nullable r && nullable s
nullable (Alternatives rs) = any nullable rs
nullable (Star _) = True

-- | The Brzozowski derivative by one character.
derive :: Char -> Regex -> Regex
derive _ NoMatch = NoMatch
derive _ EmptyString = NoMatch
derive c (OneOf s) = if member c s then EmptyString else NoMatch
derive c (Sequence r s)
  | nullable r = alternatives [andThen (derive c r) s, derive c s]
  | otherwise = andThen (derive c r) s
derive c (Alternatives rs) = alternatives (map (derive c) rs)
derive c (Star r) = andThen (derive c r) (star r)

-- | **Every** length of a prefix of the input that the expression accepts,
-- ascending (§7.3) — not the longest. @p -> x "y"@ on @aby@ needs @x@ to take
-- @ab@ and leave the @y@; a longest match would take all three.
--
-- Lazy, and it stops reading as soon as nothing further can match.
matches :: Regex -> String -> [Int]
matches = go 0 . normalise
  where
    go n r cs =
      [n | nullable r] ++ case cs of
        c : rest | r' <- derive c r, r' /= NoMatch -> go (n + 1) r' rest
        _ -> []

-- ---------------------------------------------------------------------------
-- The concrete syntax

-- | Why 'parseRegex' refused. Every offset counts characters from the start of
-- the text between the slashes.
data RegexError
  = RegexUnexpected Int Char
    -- ^ a character where it cannot stand — including @{ } ^ $@ outside a
    -- class, which other dialects give a meaning this one does not have
  | RegexUnexpectedEnd
  | RegexUnsupportedEscape Int Char
    -- ^ a backslash before a letter or digit other than @n@ and @t@. @\\S@,
    -- @\\d@, @\\1@ and the rest mean something in other dialects, so they are
    -- refused rather than read as a literal — his ruling, 2026-09-18
  | RegexReversedRange Int Char Char
    -- ^ a range in a class whose bounds are the wrong way round, @[z-a]@
  deriving (Eq, Show)

-- | Read the text between a regex literal's slashes (§3.2). A @\\/@ is still
-- escaped in it: finding the closing slash is the lexer's job, and this reads
-- the escape the same way as any other.
--
-- @
-- alt   ::= seq ('|' seq)*
-- seq   ::= post post*
-- post  ::= atom ('*' | '+' | '?')*
-- atom  ::= '(' alt ')' | '[' '^'? item item* ']' | '.' | escape | plain
-- item  ::= char ('-' char)?          where the '-' is not followed by ']'
-- @
--
-- There is no empty expression and no empty alternative, so @\/\/@, @()@ and
-- @a|@ are refused; a class may not be empty.
parseRegex :: String -> Either RegexError Regex
parseRegex src = do
  (r, rest) <- alt (zip [0 ..] src)
  case rest of
    [] -> Right r
    (i, c) : _ -> Left (RegexUnexpected i c)

type Input = [(Int, Char)]

type Parse a = Input -> Either RegexError (a, Input)

alt :: Parse Regex
alt input = do
  (r, rest) <- sq input
  case rest of
    (_, '|') : more -> do
      (s, rest') <- alt more
      Right (alternatives [r, s], rest')
    _ -> Right (r, rest)

sq :: Parse Regex
sq input = do
  (r, rest) <- post input
  if startsAtom rest
    then do
      (s, rest') <- sq rest
      Right (andThen r s, rest')
    else Right (r, rest)
  where
    -- A sequence ends at @|@, at @)@ and at the end. Anything else is the
    -- start of another atom, or an error 'atom' will report.
    startsAtom ((_, c) : _) = c `notElem` "|)"
    startsAtom [] = False

post :: Parse Regex
post input = atom input >>= uncurry suffixes
  where
    suffixes r ((_, '*') : rest) = suffixes (star r) rest
    suffixes r ((_, '+') : rest) = suffixes (andThen r (star r)) rest
    suffixes r ((_, '?') : rest) = suffixes (alternatives [EmptyString, r]) rest
    suffixes r rest = Right (r, rest)

atom :: Parse Regex
atom [] = Left RegexUnexpectedEnd
atom ((i, c) : rest) = case c of
  '(' -> do
    (r, rest') <- alt rest
    case rest' of
      (_, ')') : more -> Right (r, more)
      (j, d) : _ -> Left (RegexUnexpected j d)
      [] -> Left RegexUnexpectedEnd
  '[' -> charClass rest
  '.' -> Right (oneOf (complement (singleChar '\n')), rest)
  '\\' -> do
    (d, rest') <- escape rest
    Right (oneOf (singleChar d), rest')
  _
    | c `elem` metacharacters -> Left (RegexUnexpected i c)
    | otherwise -> Right (oneOf (singleChar c), rest)

-- | The characters that stand for themselves only when escaped: the ones this
-- syntax uses, and @{ } ^ $@, which it does not but other dialects do.
metacharacters :: String
metacharacters = "\\.[]()|*+?{}^$"

-- | After a backslash.
escape :: Parse Char
escape [] = Left RegexUnexpectedEnd
escape ((i, c) : rest)
  | c == 'n' = Right ('\n', rest)
  | c == 't' = Right ('\t', rest)
  | isAlphaNum c = Left (RegexUnsupportedEscape i c)
  | otherwise = Right (c, rest)

-- | After a @[@. Inside a class @]@, @\\@ and @[@ must be escaped; @^@ is
-- itself anywhere but first, and @-@ is itself where it cannot make a range.
charClass :: Parse Regex
charClass input = do
  let (negated, afterCaret) = case input of
        (_, '^') : rest -> (True, rest)
        _ -> (False, input)
  (first, rest) <- item afterCaret
  (others, rest') <- items rest
  let set = fromRanges (first : others)
  Right (oneOf (if negated then complement set else set), rest')
  where
    items ((_, ']') : rest) = Right ([], rest)
    items rest = do
      (r, rest') <- item rest
      (rs, rest'') <- items rest'
      Right (r : rs, rest'')

    item :: Parse (Char, Char)
    item cs = do
      (lo, rest) <- classChar cs
      case rest of
        (_, '-') : more@((j, d) : _) | d /= ']' -> do
          (hi, rest') <- classChar more
          if lo <= hi then Right ((lo, hi), rest') else Left (RegexReversedRange j lo hi)
        _ -> Right ((lo, lo), rest)

    classChar :: Parse Char
    classChar [] = Left RegexUnexpectedEnd
    classChar ((i, c) : rest)
      | c == '\\' = escape rest
      | c `elem` "[]" = Left (RegexUnexpected i c)
      | otherwise = Right (c, rest)

-- ---------------------------------------------------------------------------
-- Automata

-- | A deterministic automaton, whose states are derivatives.
--
-- State 0 is the start. A state accepts when its derivative is 'nullable'.
-- Every state has one edge per interval of 'Char' (see the module header),
-- keyed by the interval's lowest character, so a character's edge is the one
-- at or below it.
data Dfa = Dfa
  { states :: Map Int Regex
  , edges :: Map Int (Map Char Int)
  }
  deriving (Show)

-- | The derivative each state stands for, by state number.
dfaStates :: Dfa -> Map Int Regex
dfaStates = states

-- | Build the automaton, exploring derivatives breadth first.
dfa :: Regex -> Dfa
dfa r0 = explore (Map.singleton root 0) [root] Map.empty
  where
    root = normalise r0
    los = intervals [root]
    explore known [] es =
      Dfa {states = Map.fromList [(q, r) | (r, q) <- Map.toList known], edges = es}
    explore known (r : todo) es =
      explore known' (todo ++ reverse new) (Map.insert (known Map.! r) out es)
      where
        (known', new, targets) = foldl visit (known, [], []) los
        out = Map.fromList (zip los (reverse targets))
        visit (k, fresh, ts) lo =
          let r' = derive lo r
           in case Map.lookup r' k of
                Just q -> (k, fresh, q : ts)
                Nothing -> let q = Map.size k in (Map.insert r' q k, r' : fresh, q : ts)

-- | The lowest character of each interval of 'Char' within which every
-- character has the same derivative, for these expressions and every
-- derivative of them. A range @(a, b)@ starts an interval at @a@ and another
-- just after @b@.
intervals :: [Regex] -> [Char]
intervals rs = Set.toAscList (Set.fromList (minBound : concatMap cuts rs))
  where
    cuts (OneOf s) = concat [a : [succ b | b /= maxBound] | (a, b) <- ranges s]
    cuts (Sequence r s) = cuts r ++ cuts s
    cuts (Alternatives xs) = concatMap cuts xs
    cuts (Star r) = cuts r
    cuts NoMatch = []
    cuts EmptyString = []

step :: Dfa -> Int -> Char -> Int
step d q c =
  maybe (error "every interval list starts at minBound") snd (Map.lookupLE c (edges d Map.! q))

accepting :: Dfa -> Int -> Bool
accepting d q = nullable (states d Map.! q)

-- | Run the automaton over the whole string.
accepts :: Dfa -> String -> Bool
accepts d = accepting d . foldl (step d) 0

-- | Whether every string the first expression accepts, the second does too.
data Inclusion
  = Included
  | NotIncluded String
    -- ^ a **shortest** string the first accepts and the second does not
  deriving (Eq, Show)

-- | Decide inclusion on the product of the two automata (§3.2's typing check),
-- breadth first, so that the counterexample is a shortest one.
--
-- The product's intervals are the two automata's cut together. Each step of
-- the counterexample is one character chosen from its interval, a letter or a
-- digit where the interval has one, printable ASCII failing that — the witness
-- is shown to the user, and a string of control characters would say nothing.
inclusion :: Regex -> Regex -> Inclusion
inclusion r s = search (Set.singleton (0, 0)) [((0, 0), [])]
  where
    a = dfa r
    b = dfa s
    los = intervals [normalise r, normalise s]
    spans = zip los (map pred (drop 1 los) ++ [maxBound])
    search _ [] = Included
    search seen (((p, q), path) : queue)
      | accepting a p && not (accepting b q) = NotIncluded (reverse path)
      | states a Map.! p == NoMatch = search seen queue
      | otherwise = search seen' (queue ++ reverse next)
      where
        (seen', next) = foldl visit (seen, []) spans
        visit (sn, ns) (lo, hi) =
          let pq = (step a p lo, step b q lo)
           in if Set.member pq sn
                then (sn, ns)
                else (Set.insert pq sn, (pq, representative lo hi : path) : ns)

-- | A character from the inclusive interval, as readable as the interval
-- allows.
representative :: Char -> Char -> Char
representative lo hi =
  fromMaybe lo (lookup True [(c <= min hi b, c) | (a, b) <- preferred, let c = max lo a])
  where
    preferred = [('a', 'z'), ('A', 'Z'), ('0', '9'), ('!', '~')]
