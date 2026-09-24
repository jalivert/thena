-- | The regex engine (MS6 phase 99; @SPEC.md@ §3.2, §7.1).
--
-- **Everything load-bearing here is crossed with something that is not the
-- engine.** 'reference' is a backtracking matcher over the raw constructors:
-- no derivatives, no normal form, no automaton — it shares no line with
-- "Thena.Language.Regex" beyond 'member'. Against it:
--
-- * 'matches' — every prefix length, on random expressions and strings;
-- * 'accepts' on the 'dfa' — so the automaton is checked against a matcher
--   that is neither the automaton nor the derivatives it was built from;
-- * 'inclusion' — a counterexample must really be one, a verdict of
--   'Included' must survive an exhaustive search of short strings, and no
--   shorter counterexample may exist among them;
-- * 'parseRegex' — through 'render', a printer written here, so a random
--   expression is printed, read back, and compared by 'reference'.
--
-- A property of the engine against itself would agree with itself; these do
-- not have that way out.
module Thena.RegexTests (tests) where

import Data.List (nub, sort, (\\))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import Test.Tasty.QuickCheck
  ( Gen
  , choose
  , counterexample
  , elements
  , forAll
  , listOf
  , oneof
  , sized
  , testProperty
  , vectorOf
  , withNumTests
  , (===)
  )

import Thena.Language.Regex

tests :: TestTree
tests =
  testGroup
    "Thena.Language.Regex"
    [ testGroup "the concrete syntax, row by row" syntaxRows
    , testGroup "what the concrete syntax refuses" refusals
    , testGroup "matching gives every length" matching
    , testGroup "the typing check of §3.2" typing
    , testGroup "crossed with a backtracking matcher" crossed
    ]

-- ---------------------------------------------------------------------------
-- Unit cases

syntaxRows :: [TestTree]
syntaxRows =
  [ language "a character" "a" ["a"] ["", "b", "aa"]
  , language "an escaped metacharacter" "\\*\\." ["*."] ["a.", "*"]
  , language "\\n and \\t" "\\n\\t" ["\n\t"] ["nt"]
  , language "\\/ is a slash" "a\\/b" ["a/b"] ["a\\/b"]
  , language "a class with a range" "[a-c1]" ["a", "b", "c", "1"] ["d", "0"]
  , language "a negated class" "[^a-c]" ["d", "\n", "\120143"] ["a", "b"]
  , language "^ is itself anywhere but first" "[a^]" ["^", "a"] ["b"]
  , language "- is itself where it cannot make a range" "[-a-]" ["-", "a"] ["b"]
  , language "an escape inside a class" "[\\]\\n]" ["]", "\n"] ["n"]
  , language "dot is anything but newline" "." ["a", " ", "\120143"] ["\n", ""]
  , language "star" "a*" ["", "a", "aaa"] ["b"]
  , language "plus" "a+" ["a", "aaa"] [""]
  , language "question mark" "ab?" ["a", "ab"] ["abb"]
  , language "suffixes stack" "a+?" ["", "a", "aa"] ["b"]
  , language "sequence and alternative" "ab|cd" ["ab", "cd"] ["ad", "abcd"]
  , language "grouping" "a(b|c)*" ["a", "abcb"] ["b"]
  , language "a space is a character" "a b" ["a b"] ["ab"]
  , testCase "§7.3's corrected example: not whitespace or a parenthesis" $
      reads' "[^ \\t\\n()]+" >>= \r -> matches r "f x)" @?= [1]
  ]

refusals :: [TestTree]
refusals =
  [ refused "the empty expression" "" RegexUnexpectedEnd
  , refused "an empty group" "()" (RegexUnexpected 1 ')')
  , refused "an empty alternative on the right" "a|" RegexUnexpectedEnd
  , refused "an empty alternative on the left" "|a" (RegexUnexpected 0 '|')
  , refused "a suffix with nothing before it" "*a" (RegexUnexpected 0 '*')
  , refused "an unclosed group" "(a" RegexUnexpectedEnd
  , refused "a stray close" "a)" (RegexUnexpected 1 ')')
  , refused "an empty class" "[]" (RegexUnexpected 1 ']')
  , refused "an empty negated class" "[^]" (RegexUnexpected 2 ']')
  , refused "an unclosed class" "[ab" RegexUnexpectedEnd
  , refused "[ inside a class" "[[:alpha:]]" (RegexUnexpected 1 '[')
  , refused "a reversed range" "[z-a]" (RegexReversedRange 3 'z' 'a')
  , refused "a trailing backslash" "a\\" RegexUnexpectedEnd
  , -- His ruling, 2026-09-18: what other dialects give a meaning is refused.
    refused "\\S" "\\S+" (RegexUnsupportedEscape 1 'S')
  , refused "\\d" "a\\d" (RegexUnsupportedEscape 2 'd')
  , refused "a backreference" "(a)\\1" (RegexUnsupportedEscape 4 '1')
  , refused "\\S inside a class too" "[\\S]" (RegexUnsupportedEscape 2 'S')
  , refused "a counted repetition" "a{3}" (RegexUnexpected 1 '{')
  , refused "an anchor at the start" "^a" (RegexUnexpected 0 '^')
  , refused "an anchor at the end" "a$" (RegexUnexpected 1 '$')
  , refused "a stray ]" "a]" (RegexUnexpected 1 ']')
  ]

matching :: [TestTree]
matching =
  [ testCase "every length, not the longest: x = [a-z]+ on \"aby\"" $
      reads' "[a-z]+" >>= \r -> matches r "aby" @?= [1, 2, 3]
  , testCase "a nullable expression matches at length 0" $
      reads' "a*" >>= \r -> matches r "aab" @?= [0, 1, 2]
  , testCase "nothing matches past the first failure" $
      reads' "ab" >>= \r -> matches r "acb" @?= []
  , testCase "it stops reading — an infinite input is fine" $
      reads' "a|ab" >>= \r -> matches r ("ab" ++ repeat 'c') @?= [1, 2]
  , testCase "§3.2's empty-string check is nullable" $ do
      r <- reads' "a?"
      s <- reads' "a+"
      (nullable r, nullable s) @?= (True, False)
  , testCase "the automaton of a*b* has three states" $
      reads' "a*b*" >>= \r -> length (dfaStates (dfa r)) @?= 3
  ]

-- | The three types' languages as phase 100 will state them, and the witness
-- a user would be shown.
typing :: [TestTree]
typing =
  [ includes "a class of numerals is an Int" "-?[1-9][0-9]*" intLanguage Included
  , includes "a class of words is not, and the witness is one letter"
      "[a-z]+" intLanguage (NotIncluded "a")
  , includes "the witness is a shortest one" "x|[0-9]*y" intLanguage (NotIncluded "x")
  , includes "an empty numeral is not an Int" "-?[0-9]*" intLanguage (NotIncluded "")
  , includes "one character is a Char" "[a-z]" charLanguage Included
  , includes "two are not" "[a-z][a-z]?" charLanguage (NotIncluded "aa")
  , includes "a newline is a Char, though . does not accept it" "\\n" charLanguage Included
  , includes "a negated class reaches the newline . refuses" "[^a]" "." (NotIncluded "\n")
  , includes "a witness is readable where the interval allows" "[^b]" "[b-z]" (NotIncluded "a")
  , includes "anything is a String" "(.|\\n)+" stringLanguage Included
  ]
  where
    intLanguage = "-?[0-9]+"
    charLanguage = ".|\\n"
    stringLanguage = "(.|\\n)*"

-- ---------------------------------------------------------------------------
-- The crossings

crossed :: [TestTree]
crossed =
  [ testProperty "matches agrees with the reference" $
      withNumTests 2000 $ forAll genRegex $ \r -> forAll genString $ \w ->
        matches r w === lengths r w
  , testProperty "the automaton agrees with the reference" $
      withNumTests 2000 $ forAll genRegex $ \r -> forAll genString $ \w ->
        accepts (dfa r) w === (length w `elem` lengths r w)
  , testProperty "a counterexample is one, and none shorter exists" $
      withNumTests 1000 $ forAll genRegex $ \r -> forAll genRegex $ \s ->
        case inclusion r s of
          NotIncluded w ->
            counterexample ("witness " ++ show w) $
              accepted r w && not (accepted s w)
                && null [v | v <- upTo (min 4 (length w - 1)), accepted r v, not (accepted s v)]
          Included ->
            counterexample "included, but a short string says otherwise" $
              null [v | v <- upTo 4, accepted r v, not (accepted s v)]
  , testProperty "an expression includes itself" $
      withNumTests 500 $ forAll genRegex $ \r -> inclusion r r === Included
  , testProperty "printed and read back, it accepts the same strings" $
      withNumTests 1000 $ forAll genRegex $ \r ->
        case parseRegex (render r) of
          Left e -> counterexample (render r ++ " refused: " ++ show e) False
          Right r' ->
            counterexample (render r) $
              [w | w <- upTo 4, accepted r w] === [w | w <- upTo 4, accepted r' w]
  ]
  where
    accepted r w = length w `elem` lengths r w

-- | Every length of a prefix the expression accepts, by 'reference'.
lengths :: Regex -> String -> [Int]
lengths r w = reference r w 0

-- | A matcher over **positions**: the positions a match that starts at
-- @i@ can end at. No derivatives, no normal form, no automaton — it shares no
-- line with "Thena.Language.Regex" beyond 'member'.
--
-- **Positions, not remainders** (fixed in MS6 phase 102b). The first
-- version returned every way of matching, and a nested star finds the same
-- end position exponentially many ways; on one seed in six it ran for hours.
-- A list of at most @length w + 1@ positions cannot blow up, and a star is its
-- least fixed point: the positions reachable by repeating the body, each step
-- making progress.
reference :: Regex -> String -> Int -> [Int]
reference re w i = sort (nub (go re i))
  where
    go r j = case r of
      NoMatch -> []
      EmptyString -> [j]
      OneOf set
        | j < length w, member (w !! j) set -> [j + 1]
        | otherwise -> []
      Sequence a b -> nub (concat [ go b k | k <- nub (go a j) ])
      Alternatives rs -> nub (concatMap (`go` j) rs)
      Star a -> grow [j] [j]
        where
          grow seen [] = seen
          grow seen (k : todo) =
            let new = nub (filter (> k) (go a k)) \\ seen
             in grow (seen ++ new) (todo ++ new)

-- | Every string over the test alphabet up to this length.
upTo :: Int -> [String]
upTo n = concat [sequence (replicate k alphabet) | k <- [0 .. n]]

alphabet :: String
alphabet = "abc\n"

-- | Short, so that the exhaustive searches below stay small.
genString :: Gen String
genString = do
  n <- choose (0, 8)
  vectorOf n (elements alphabet)

-- | Raw constructors, deliberately — the engine must cope with an expression
-- no smart constructor made. Sets are small, with the occasional complement
-- so that the whole of 'Char' is in play.
genRegex :: Gen Regex
genRegex = sized (go . min 6)
  where
    go :: Int -> Gen Regex
    go 0 = oneof [OneOf <$> genSet, pure EmptyString, pure NoMatch]
    go n =
      oneof
        [ OneOf <$> genSet
        , Sequence <$> go (n - 1) <*> go (n - 1)
        , (\a b -> Alternatives [a, b]) <$> go (n - 1) <*> go (n - 1)
        , Star <$> go (n - 1)
        ]
    genSet = do
      cs <- listOf (elements "abc")
      negated <- choose (0, 4 :: Int)
      let set = fromRanges [(c, c) | c <- if null cs then "a" else cs]
      pure (if negated == 0 then complement set else set)

-- | A printer for the concrete syntax, written here so that 'parseRegex' is
-- tested against something it was not written with.
render :: Regex -> String
-- The syntax has no way to say "nothing" or "the empty string" directly, so a
-- class of every character is negated for the one and starred for the other.
render NoMatch = "[^" ++ [minBound] ++ "-" ++ [maxBound] ++ "]"
render EmptyString = "(" ++ render NoMatch ++ ")*"
render (OneOf s) = "[" ++ concatMap range (ranges s) ++ "]"
  where
    range (a, b) | a == b = char a
    range (a, b) = char a ++ "-" ++ char b
    char '\n' = "\\n"
    char c | c `elem` "\\]-[^" = ['\\', c]
    char c = [c]
render (Sequence r s) = "(" ++ render r ++ ")(" ++ render s ++ ")"
render (Alternatives rs) = foldr1 (\a b -> a ++ "|" ++ b) ["(" ++ render r ++ ")" | r <- rs]
render (Star r) = "(" ++ render r ++ ")*"

-- ---------------------------------------------------------------------------
-- Helpers

reads' :: String -> IO Regex
reads' src = either (assertFailure . (("refused " ++ src ++ ": ") ++) . show) pure (parseRegex src)

language :: String -> String -> [String] -> [String] -> TestTree
language name src yes no = testCase (name ++ ": /" ++ src ++ "/") $ do
  r <- reads' src
  [w | w <- yes, not (accepts (dfa r) w)] @?= []
  [w | w <- no, accepts (dfa r) w] @?= []

refused :: String -> String -> RegexError -> TestTree
refused name src e = testCase (name ++ ": /" ++ src ++ "/") $ parseRegex src @?= Left e

includes :: String -> String -> String -> Inclusion -> TestTree
includes name r s expected = testCase name $ do
  a <- reads' r
  b <- reads' s
  inclusion a b @?= expected
