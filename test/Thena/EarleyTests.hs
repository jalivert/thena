-- | The Earley parser (MS6 phase 102; @ms6\/SPEC.md@ §7.2–7.7).
--
-- **The load-bearing test is the round trip**: random derivation trees of an
-- unambiguous grammar are printed by 'render' — a printer written here, which
-- is §4.6's "a production is also a printing rule" and shares nothing with the
-- parser — and parsed back, and must come back as the same tree. A parser
-- checked only against itself would agree with itself.
--
-- The rest are §7's claims one by one, each on the smallest grammar that shows
-- it: every length a class matches, not the longest; a literal and a class
-- both live; whitespace optional; left recursion; the non-linear filter; a
-- cycle found rather than followed; holes and splices; starting at one rule;
-- and the chart queried as a value.
module Thena.EarleyTests (tests) where

import Data.ByteString.Builder (stringUtf8, toLazyByteString)
import Data.List (sort)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import Test.Tasty.QuickCheck (Gen, Property, choose, counterexample, elements, forAll, oneof, sized, testProperty, withNumTests, (===))

import Thena.Driver (loadProofSource)
import Thena.Language.Earley
import Thena.Language.Regex (Regex, parseRegex)
import Thena.Repl (startingSession, tabComplete, transcriptFrom)

tests :: TestTree
tests =
  testGroup
    "Thena.Language.Earley"
    [ testGroup "scanning (§7.3)" scanning
    , testGroup "the forest (§7.4, §7.5)" forest
    , testGroup "holes and splices (§7.6)" holes
    , testGroup "the chart is a value (§7.7)" charting
    , testProperty "printed and parsed back, a tree is itself" roundTrip
    , testGroup "Tab at the cursor (phase 102b)" tabbing
    , goldenVsString "parsing" "test/golden/parsing.golden" $ do
        (s0, problems) <- startingSession
        let (s1, _) = loadProofSource s0 stlc
        pure (toLazyByteString (stringUtf8 (unlines problems ++ transcriptFrom s1 prompt)))
    ]

-- ---------------------------------------------------------------------------
-- Small grammars, written as the parser takes them

re :: String -> Regex
re = either (error . show) id . parseRegex

lit :: String -> Symbol
lit = Literal

nt :: String -> Symbol
nt = Nonterminal

cls :: String -> String -> Symbol
cls name src = Scan name (re src)

rule :: String -> String -> [Symbol] -> Rule
rule n h b = Rule n h b []

run :: [Rule] -> String -> String -> Either ParseFailure Tree
run rs start = parse rs (StartAt start) . pieces

-- | The spec's STLC, as installed grammars would give it.
lc :: [Rule]
lc =
  [ rule "base" "Ty" [lit "ι"]
  , rule "arrow" "Ty" [lit "(", nt "Ty", lit "->", nt "Ty", lit ")"]
  , rule "var" "LC" [ident]
  , rule "abs" "LC" [lit "(", lit "λ", ident, lit ":", nt "Ty", lit ".", nt "LC", lit ")"]
  , rule "app" "LC" [nt "LC", nt "LC"]
  , rule "paren" "LC" [lit "(", nt "LC", lit ")"]
  ]
  where ident = cls "x" "[a-z][a-z0-9']*"

node :: String -> [Tree] -> Tree
node = Node

var :: String -> Tree
var x = Node "var" [Token x]

-- ---------------------------------------------------------------------------

scanning :: [TestTree]
scanning =
  [ testCase "a class tries every length: p -> x y on aby" $
      run [rule "p" "P" [cls "x" "[a-z]+", lit "y"]] "P" "aby" @?= Right (node "p" [Token "ab"])
  , testCase "the reading that swallows a ) never completes" $
      -- §7.3: with x = /[^ \\t\\n]+/, @f )@ could be read as the one token @f)@;
      -- that reading leaves nothing for the paren's @)@ and never completes.
      run [ rule "var" "E" [cls "x" "[^ \\t\\n]+"], rule "paren" "E" [lit "(", nt "E", lit ")"] ]
          "E" "( f)"
        @?= Right (node "paren" [Node "var" [Token "f"]])
  , testCase "whitespace between tokens is optional" $
      run lc "LC" "(λx:ι.x)" @?= run lc "LC" "( λ x : ι . x )"
  , testCase "and the spaced one is abs(x, base, var(x))" $
      run lc "LC" "( λ x : ι . x )" @?= Right (node "abs" [Token "x", node "base" [], var "x"])
  , testCase "a literal and a class that both apply are both live" $
      run [rule "kw" "E" [lit "let"], rule "var" "E" [cls "x" "[a-z]+"]] "E" "let"
        @?= Left (Ambiguous (node "kw" []) (Node "var" [Token "let"]))
  , testCase "left recursion is fine, and unparenthesised application is ambiguous" $
      case run lc "LC" "f a b" of
        Left (Ambiguous _ _) -> pure ()
        other -> assertFailure (show other)
  , testCase "a nested arrow type" $
      run lc "Ty" "( ι -> ( ι -> ι ) )"
        @?= Right (node "arrow" [node "base" [], node "arrow" [node "base" [], node "base" []]])
  ]

forest :: [TestTree]
forest =
  [ testCase "a repeated name that agrees is one reading" $
      run repeatG "E" "{ a a }" @?= Right (node "rep" [var "a", var "a"])
  , testCase "one that disagrees says so, rather than that the term ended" $
      run repeatG "E" "{ a b }" @?= Left (Disagrees "rep" "E" (var "a") (var "b"))
  , testCase "a class compares by text" $
      run [Rule "w" "E" [lit "<", cls "x" "[a-z]+", cls "x" "[a-z]+", lit ">"] [("x", [0, 1])]] "E" "< a b >"
        @?= Left (Disagrees "w" "x" (Token "a") (Token "b"))
  , testCase "a cycle is found, not followed: the parse ends" $
      case run [rule "var" "E" [cls "x" "[a-z]+"], rule "wrap" "E" [nt "E"]] "E" "q" of
        Left (Ambiguous _ _) -> pure ()
        Left (Unbounded _) -> pure ()
        other -> assertFailure (show other)
  , testCase "a cycle with only one finite reading is unbounded" $
      run [rule "var" "A" [cls "x" "[a-z]+"], rule "up" "A" [nt "B"], rule "down" "B" [nt "A"]] "B" "q"
        @?= Left (Unbounded "A")
  , testCase "stuck: where, and what was expected" $
      run lc "LC" "( λ x ι )" @?= Left (Stuck 6 [lit ":"])
  , testCase "ended too soon: the position is the end" $
      case run lc "LC" "( λ x : ι ." of
        Left (Stuck 11 _) -> pure ()
        other -> assertFailure (show other)
  ]
  where
    repeatG = [ rule "var" "E" [cls "x" "[a-z]+"]
              , Rule "rep" "E" [lit "{", nt "E", nt "E", lit "}"] [("E", [0, 1])] ]

holes :: [TestTree]
holes =
  [ testCase "a hole completes a slot" $
      run lc "LC" "( λ ? : ι . ? )" @?= Right (node "abs" [HoleAt 4, node "base" [], HoleAt 12])
  , -- His ruling, 2026-09-19: slots only.
    testCase "and never stands for a terminal" $
      case run lc "LC" "( ? x : ι . x )" of
        Left (Stuck _ _) -> pure ()
        other -> assertFailure (show other)
  , testCase "a hole is compatible with anything a repeated name reads" $
      run [ rule "var" "E" [cls "x" "[a-z]+"], Rule "rep" "E" [lit "{", nt "E", nt "E", lit "}"] [("E", [0, 1])] ]
          "E" "{ ? a }"
        @?= Right (node "rep" [HoleAt 2, var "a"])
  , testCase "a splice supplies a slot" $
      parse lc (StartAt "LC") ([Char '(', Char 'λ', Char ' ', Splice 0] ++ pieces " : ι . x )")
        @?= Right (node "abs" [SpliceOf 0, node "base" [], var "x"])
  , testCase "starting at one rule: var takes x, abs does not" $
      (parse lc (StartRule "var") (pieces "x"), either (const True) (const False) (parse lc (StartRule "abs") (pieces "x")))
        @?= (Right (var "x"), True)
  ]

charting :: [TestTree]
charting =
  [ testCase "after \"( \", the live items expect λ or a term" $ do
      let c = chart lc (StartAt "LC") (pieces "( ")
      [ s | s@(Literal "λ") <- expectedAt c 2 ] @?= [lit "λ"]
      [ s | s@(Nonterminal "LC") <- expectedAt c 2 ] @?= [nt "LC"]
  , testCase "and after \"( λ\", only abs is live there" $ do
      let c = chart lc (StartAt "LC") (pieces "( λ")
      [ ruleName (chartRule c i) | i <- itemsAt c 3, itemDot i > 0 ] @?= ["abs"]
  , -- Slots only (his ruling): in the chart itself, not just the verdict, no
    -- abs item gets past its λ on a hole.
    testCase "a hole where λ goes moves no abs item past it" $ do
      let c = chart lc (StartAt "LC") (pieces "( ?")
      [ i | k <- [0 .. 3], i <- itemsAt c k, ruleName (chartRule c i) == "abs", itemDot i >= 2 ] @?= []
  , testCase "furthest is where scanning stopped" $
      furthest (chart lc (StartAt "LC") (pieces "( λ x ι )")) @?= 5
  ]

-- ---------------------------------------------------------------------------
-- The round trip

-- | An unambiguous grammar: every production but var begins with its own
-- terminal, and application is bracketed.
unambiguous :: [Rule]
unambiguous =
  [ rule "base" "Ty" [lit "ι"]
  , rule "arrow" "Ty" [lit "(", nt "Ty", lit "->", nt "Ty", lit ")"]
  , rule "var" "LC" [cls "x" "[a-z]+"]
  , rule "abs" "LC" [lit "(", lit "λ", cls "x" "[a-z]+", lit ":", nt "Ty", lit ".", nt "LC", lit ")"]
  , rule "app" "LC" [lit "[", nt "LC", nt "LC", lit "]"]
  ]

genTree :: String -> Gen Tree
genTree = sized . go
  where
    go "Ty" 0 = pure (node "base" [])
    go "Ty" k = oneof [pure (node "base" []), (\a b -> node "arrow" [a, b]) <$> go "Ty" (k `div` 2) <*> go "Ty" (k `div` 2)]
    go _ 0 = var <$> name
    go _ k = oneof
      [ var <$> name
      , (\x t e -> node "abs" [Token x, t, e]) <$> name <*> go "Ty" (k `div` 3) <*> go "LC" (k `div` 2)
      , (\a b -> node "app" [a, b]) <$> go "LC" (k `div` 2) <*> go "LC" (k `div` 2)
      ]
    name = elements ["a", "b", "xy", "q"]

-- | Each production as a printing rule, with a random run of spaces (at least
-- one) between items.
render :: Tree -> Gen String
render t = case t of
  Node "base" [] -> pure "ι"
  Node "arrow" [a, b] -> spaced [pure "(", render a, pure "->", render b, pure ")"]
  Node "var" [Token x] -> pure x
  Node "abs" [Token x, ty, e] -> spaced [pure "(", pure "λ", pure x, pure ":", render ty, pure ".", render e, pure ")"]
  Node "app" [a, b] -> spaced [pure "[", render a, render b, pure "]"]
  _ -> pure "?"
  where
    spaced gs = do
      parts <- sequence gs
      gaps <- mapM (const (flip replicate ' ' <$> choose (1, 3))) parts
      pure (concat (zipWith (++) parts gaps))

roundTrip :: Property
roundTrip = withNumTests 300 $ forAll (genTree "LC") $ \t -> forAll (render t) $ \src ->
  counterexample src (run unambiguous "LC" src === Right t)

-- ---------------------------------------------------------------------------
-- At the prompt

stlc :: String
stlc =
  unlines
    [ "module STLC where"
    , ""
    , "x : Token String"
    , "x = /[a-z][a-zA-Z0-9']*/"
    , ""
    , "language Ty, T, S where"
    , "  base  -> \953"
    , "  arrow -> ( T -> S )"
    , ""
    , "language LC, M, N, E where"
    , "  var : x as occurrence -> x"
    , "  abs : x as binder     -> ( \955 x : T . E[x] )"
    , "  app                   -> M N"
    , "  paren                 -> ( M )"
    , "  repeat                -> { M M }"
    ]

prompt :: [String]
prompt =
  [ ":parse LC ( \955 x : \953 . x )"
  , ":parse LC (\955f:(\953->\953).(\955y:\953.f y))"
  , ":parse LC ( \955 ? : \953 . ? )"
  , ":parse LC f a b"
  , ":parse LC { a a }"
  , ":parse LC { a b }"
  , ":parse LC ( \955 x \953 )"
  , ":parse LC ( \955 x : \953 ."
  , ":parse Ty ( \953 -> ( \953 -> \953 ) )"
  , ":parse Nope x"
  , ":parse LC"
  , "( \955 x : \953 . x )"
  , "f a b"
  , ":parse LC"
  , ":done"
  , ":parse LC ( \955 y : \953 . y )"
  ]

-- ---------------------------------------------------------------------------
-- Tab (phase 102b)

-- | Tab as haskeline calls it: the text left of the cursor, reversed, and the
-- text right of it.
tab :: [Rule] -> String -> String -> String -> (String, [(String, String)])
tab rs lang left right = tabComplete rs lang (reverse left, right)

tabbing :: [TestTree]
tabbing =
  [ testCase "after ( λ, the rest of abs is inserted, slots as ?" $
      tab lc "LC" "( λ" "" @?= (reverse "( λ", [(" ? : ? . ? )", "? : ? . ? )")])
  , testCase "after ( λ x : , too — the last terminal still belongs to abs alone" $
      tab lc "LC" "( λ x : " "" @?= (reverse "( λ x : ", [("? . ? )", "? . ? )")])
  , testCase "after ( alone, abs and paren both fit, so the options are listed" $ do
      let (kept, cs) = tab lc "LC" "( " ""
      kept @?= reverse "( "
      map fst cs @?= map (const "") cs   -- nothing inserted: haskeline lists
      sort [ d | (_, d) <- cs, d `elem` ["\955", "(", "\8249LC\8250"] ]
        @?= sort ["\955", "\8249LC\8250", "("]
  , -- The completion rule is about a terminal: after f, which ends a var,
    -- app has begun but nothing has been decided, so nothing is completed.
    testCase "after a finished var, no production is completed" $
      map fst (snd (tab lc "LC" "f" "")) @?= map (const "") (snd (tab lc "LC" "f" ""))
  , -- The cursor inside the production being written: what follows it is the
    -- rest, so the slot must still be offered.
    testCase "a slot of the production under the cursor is offered" $ do
      let (_, cs) = tab lc "LC" "( \955 ? : " " . ? )"
      [ d | (_, d) <- cs, d == "\8249Ty\8250" ] @?= ["\8249Ty\8250"]
  , testCase "the text after the cursor filters the options" $ do
      let (_, cs) = tab lc "LC" "( \955 x : \953 . x " ")"
      [ d | (_, d) <- cs, d == ")" ] @?= []
  , -- With text after the cursor the rest of abs is not inserted; the one
    -- thing that fits there — a hole for the bound name — is.
    testCase "the rest of a production is never inserted into a line's middle" $
      tab lc "LC" "( \955" " x" @?= (reverse "( \955", [(" ?", "?")])
  , testCase "on a ?, a single answer replaces the hole" $
      tab [rule "e" "E" [lit "<", nt "T", lit ">"], rule "base" "T" [lit "\953"]] "E" "< ?" " >"
        @?= (reverse "< ", [("\953", "\953")])
  , testCase "and several leave it standing and are listed" $ do
      let (kept, cs) = tab lc "LC" "( \955 ? : ?" " . ? )"
      kept @?= reverse "( \955 ? : ?"
      sort [ d | ("", d) <- cs, d `elem` ["\953", "("] ] @?= sort ["\953", "("]
  ]
