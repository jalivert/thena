-- | A line as coloured spans (MS7 phase 136, @ms7\/CLOSEOUT.md@ 18).
--
-- **Two crossings, and they test different claims.**
--
-- * The spans **tile the line**: concatenating every token's text, with the gaps
--   the columns imply filled by the line's own characters, gives the line back.
--   That is what says the extents are right, and it is the thing 'Located' alone
--   could never have supported.
-- * The kinds are **total over 'Thena.Syntax.Lexer.Token'**, which @-Wall@
--   enforces at the case rather than here; what is tested is that the classes a
--   palette cares about actually arise from real text.
module Thena.View.TokensTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.View.Tokens (TokenKind (..), TokenView (..), tokensView)

tests :: TestTree
tests =
  testGroup
    "Thena.View.Tokens"
    [ testCase "the spans tile the line they came from" tiles
    , testCase "a keyword is a keyword in either spelling, and the extents differ" spellings
    , testCase "an unclosed region still lexes, and the fence is not reported" unclosed
    , testCase "and the raw text before the cursor is kept" unclosedKeepsText
    , testCase "a tag is its own kind, which is what the fold hides" tagKind
    , testCase "a raw chunk's span is the source's, escapes included" escapes
    , testCase "a bad character is a position, not a failure to colour" badCharacter
    , testCase "the kinds a palette needs all arise" palette
    ]

viewOf :: String -> IO [TokenView]
viewOf s = case tokensView s of
  Right ts -> pure ts
  Left p   -> assertFailure ("tokensView refused " <> show s <> " at " <> show p)

-- | **The load-bearing one.** Every token's text laid back into the line at the
-- column it claims must reproduce the line — so a wrong extent, or a wrong
-- column, or a token whose text is the payload rather than the source, all fail
-- here.
--
-- Single-line inputs only, which is what a highlighter colours a row at a time.
tiles :: IO ()
tiles = mapM_ one
  [ "let x = 3 in x"
  , "λ x ⊢ x"
  , "data Nat where"
  , "rule intro when x ≟ y"
  , "LC`( λ x )`"
  , "LC[var]`x`"
  , "f ${g} h"
  , "\"a string\" 'c' 42"
  ]
  where
    one line = do
      ts <- viewOf line
      rebuild line ts @?= line

-- | Lay each token's text at its column; whatever no token claims is whitespace
-- and is taken from the line.
rebuild :: String -> [TokenView] -> String
rebuild line = go 1
  where
    go col ts = case ts of
      [] -> drop (col - 1) line
      t : rest
        | tokenViewColumn t < col -> go col rest    -- should not happen; tiling fails loudly
        | otherwise ->
            let gap = take (tokenViewColumn t - col) (drop (col - 1) line)
             in gap ++ tokenViewText t ++ go (tokenViewColumn t + length (tokenViewText t)) rest

-- | @forall@ and @∀@ are one keyword and six characters against one — which is
-- exactly why the extent could not come from the token.
spellings :: IO ()
spellings = do
  a <- viewOf "forall"
  b <- viewOf "∀"
  (map tokenViewKind a, map tokenViewKind b) @?= ([AKeyword], [AKeyword])
  (map (length . tokenViewText) a, map (length . tokenViewText) b) @?= ([6], [1])

-- | The state a line is in the moment someone types a tag. Before this view a
-- frontend had to know to append a fence itself.
unclosed :: IO ()
unclosed = do
  ts <- viewOf "LC`( λ x"
  -- Nothing is reported past the end of what was actually written.
  case [ t | t <- ts, tokenViewColumn t > length "LC`( λ x" ] of
    []    -> pure ()
    t : _ -> assertFailure ("a token from the appended fence was reported: " <> show t)

unclosedKeepsText :: IO ()
unclosedKeepsText = do
  ts <- viewOf "LC`( λ x"
  case [ tokenViewText t | t <- ts, tokenViewKind t == AnObjectText ] of
    []  -> assertFailure "the raw text inside the unclosed region was lost"
    txt -> concat txt @?= "( λ x"

tagKind :: IO ()
tagKind = do
  ts <- viewOf "LC[var]`x`"
  map tokenViewText [ t | t <- ts, tokenViewKind t == ATag ] @?= ["LC[var]`", "`"]

-- | A raw chunk's payload has its escapes undone and its span does not — the
-- one place the two strings genuinely differ.
escapes :: IO ()
escapes = do
  let line = "LC`a\\`b`"
  ts <- viewOf line
  rebuild line ts @?= line
  map tokenViewText [ t | t <- ts, tokenViewKind t == AnObjectText ] @?= ["a\\`b"]

badCharacter :: IO ()
badCharacter = case tokensView "let # = 3" of
  Left _   -> pure ()
  Right ts -> assertFailure ("expected a position, got " <> show (map tokenViewText ts))

palette :: IO ()
palette = do
  ts <- concat <$> mapM viewOf
    [ "let x = 3 in x", "λ x ⊢ x", "\"s\" 'c'", "/ab/"
    , "LC`x`", "f ${g}", "?h", "Type0"
    ]
  let kinds = map tokenViewKind ts
  case [ k | k <- [ AKeyword, APunctuation, AnIdentifier, ANumber, AText
                  , ACharacter, ARegexLiteral, AHole, ATag, AnObjectText, AnEscape ]
           , k `notElem` kinds ] of
    []      -> pure ()
    missing -> assertFailure ("never produced: " <> show missing)
