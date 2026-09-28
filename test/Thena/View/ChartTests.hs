-- | The Earley chart's own questions, as a view (MS7 phase 115e, region at 125).
--
-- **The crossing, once more.** 'redrawParse' and 'redrawOffer' draw only what
-- 'Thena.View.Chart.displayParse' and 'Thena.View.Chart.displayOffer'
-- hand them; if that agrees with what 'Thena.Repl.renderTree'\/
-- 'Thena.Repl.parseFailureReason' and 'Thena.Repl.tabComplete' already do with
-- the same chart, for the same text, the view carries what those two
-- existing consumers needed.
--
-- **What is not crossed.** 'Thena.View.Chart.AnAmbiguity',
-- 'Thena.View.Chart.AnUnboundedRule' and
-- 'Thena.View.Chart.ADisagreement' mirror 'Earley.Ambiguous',
-- 'Earley.Unbounded' and 'Earley.Disagrees' one constructor to one, over the
-- same 'TreeView' already crossed by the successful case — nothing in the
-- fixture grammar below is ambiguous or self-deriving, and forcing one would
-- test the mirroring function's four-line 'case', not the view. Kept total
-- rather than partial, the same call 115d made for 'Thena.View.Instral.ValOpaque'.
module Thena.View.ChartTests (tests) where

import Data.Char (isSpace)
import Data.List (intercalate)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

import Thena.Driver
  ( Response (..)
  , loadProofSource
  , machineOf
  )
import Thena.Engine (Machine (..))
import qualified Thena.Language.Earley as Earley
import Thena.Language.Grammar (Grammar, earleyRules)
import Thena.View.Chart
  ( FailureView (..)
  , OfferProblem (..)
  , OfferView (..)
  , SymbolView (..)
  , TreeView (..)
  , Written (..)
  , displayOffer
  , displayParse
  )
import Thena.Repl (parseFailureReason, renderTree, startingSession, tabComplete)
import Thena.Syntax.Print (escapeChar)

tests :: TestTree
tests =
  testGroup
    "Thena.View.Chart"
    [ testGroup "is this text one term (Earley.parse)" parseCases
    , testGroup "what may stand at the cursor (Earley.offer)" offerCases
    , testGroup "a region, text and splices (phase 125)" regionCases
    ]

-- | @Ty@ and @LC@, exactly `ms6\/SPEC.md`'s canonical shape, unbracketed
-- application left out so nothing here is ambiguous — the point of these
-- cases is the crossing, not the parser, which 'Thena.EarleyTests' already
-- covers on its own small grammars.
source :: String
source =
  unlines
    [ "module Charting where"
    , ""
    , "w : Token String"
    , "w = /[a-z][a-zA-Z0-9']*/"
    , ""
    , "language Ty, T, S where"
    , "  base  -> \953"
    , "  arrow -> ( T -> S )"
    , ""
    , "language LC, M, N, E where"
    , "  var : w as occurrence -> w"
    , "  abs : w as binder     -> ( \955 w : T . E[w] )"
    , "  app                   -> ( M N )"
    ]

loaded :: IO [Grammar]
loaded = do
  (s0, _) <- startingSession
  case loadProofSource s0 source of
    (s1, ProofLoaded {}) -> pure (grammars (machineOf s1))
    (_, other) -> assertFailure (show other) >> pure []

-- ---------------------------------------------------------------------------
-- Is this text one term

parseCases :: [TestTree]
parseCases =
  [ agree "a complete term"
      "( \955 x : \953 . x )"
  , agree "a nested type"
      "( \955 x : ( \953 -> \953 ) . x )"
  , agree "stuck before the closing paren"
      "( \955 x : \953 . x"
  , agree "stuck right after the opening paren"
      "( "
  ]
  where
    agree name text = testCase name $ do
      gs <- loaded
      mismatchParse gs "LC" text

mismatchParse :: [Grammar] -> String -> String -> IO ()
mismatchParse gs lang text
  | shown == drawn = pure ()
  | otherwise = assertFailure ("printed: " <> shown <> "\n  drawn:   " <> drawn)
  where
    shown = case Earley.parse (earleyRules gs) (Earley.StartAt lang) (Earley.pieces text) of
      Left f  -> parseFailureReason text f
      Right t -> renderTree t
    drawn = case displayParse gs lang Nothing [WrittenText text] of
      Left f  -> redrawFailure text f
      Right t -> redrawTree t

-- | What an editor is, for a parse tree: a function from a 'TreeView' to
-- text, and nothing else — mirrors 'Thena.Repl.renderTree', the seam under
-- test.
redrawTree :: TreeView -> String
redrawTree t = case t of
  ANode n []  -> n
  ANode n cs  -> n ++ "(" ++ intercalate ", " (map redrawTree cs) ++ ")"
  ATokenView x -> x
  AHoleAt _    -> "?"
  ASpliceOf k  -> "${" ++ show k ++ "}"

-- | Mirrors 'Thena.Repl.parseFailureReason'.
redrawFailure :: String -> FailureView -> String
redrawFailure text f = case f of
  AnAmbiguity a b ->
    "this term parses two ways, as " ++ redrawTree a ++ " and as " ++ redrawTree b
  ADisagreement r x a b ->
    r ++ "'s " ++ x ++ " is written more than once and must read the same each time, "
      ++ "but here it is " ++ redrawTree a ++ " and " ++ redrawTree b
  AnUnboundedRule h ->
    "this term parses without end, because " ++ h ++ " can derive itself from the same text"
  AStuck p expected
    | p >= length text -> "the term ends too soon" ++ expecting expected
    | otherwise ->
        "unexpected " ++ escapeChar (text !! p) ++ " at character " ++ show (p + 1)
          ++ expecting expected
  where
    expecting [] = ""
    expecting ss = ", expecting " ++ oneOf (map redrawSymbolText ss)
    oneOf ws = case reverse ws of
      [w] -> w
      w : rest -> intercalate ", " (reverse rest) ++ " or " ++ w
      [] -> ""

redrawSymbolText :: SymbolView -> String
redrawSymbolText s = case s of
  ALiteralSymbol x -> x
  AScanSymbol n -> n
  ANonterminalSymbol n -> n

-- ---------------------------------------------------------------------------
-- What may stand at the cursor

offerCases :: [TestTree]
offerCases =
  [ agree "after ( \955, the rest of abs is inserted, slots as ?"
      "( \955" ""
  , agree "after ( alone, abs and paren both fit: listed"
      "( " ""
  , agree "a slot of the production under the cursor is offered"
      "( \955 x : " " . x )"
  , agree "the text after the cursor filters the options"
      "( \955 x : \953 . x " ")"
  , -- Phase 120: the rest is fitted to what follows the cursor, and a
    -- position that can have nothing still says what it wants — both of
    -- which the view has to carry, the first as 'offeredRest' and the
    -- second as 'offeredWanted'.
    agree "the rest is cut short by the closer already written"
      "( \955" " )"
  , agree "a contradicted type slot still says it wants a T"
      "( \955 x : " "? . x )"
  ]
  where
    agree name before after = testCase name $ do
      gs <- loaded
      mismatchOffer gs "LC" before after

mismatchOffer :: [Grammar] -> String -> String -> String -> IO ()
mismatchOffer gs lang before after
  | shown == drawn = pure ()
  | otherwise = assertFailure ("tabComplete: " <> show shown <> "\n  drawn:      " <> show drawn)
  where
    shown = tabComplete (earleyRules gs) lang (reverse before, after)
    -- **A region, as of phase 125** — one run of written text on each side, no
    -- splices, which is exactly what a terminal line is. The 'Left' cannot
    -- happen here: every caller names a language the fixture loaded.
    drawn = case displayOffer gs lang Nothing [WrittenText before] [WrittenText after] of
      Right o -> redrawOffer before o
      Left p  -> error ("displayOffer refused the fixture: " <> show p)

-- | 'Thena.Repl.tabComplete's own decision (the @'?'@-adjacent case aside,
-- which is the REPL's own hole spelling and not this phase's concern),
-- replayed over an 'OfferView' rather than a raw 'Earley.Offer'.
redrawOffer :: String -> OfferView -> (String, [(String, String)])
redrawOffer before (OfferView options wanted rest) =
  case (rest, options ++ wanted) of
    (Just pfx, _) -> single (unwords (map redrawWritten pfx))
    (_, [s]) | isLiteralView s -> single (redrawWritten s)
    (_, ss) -> (reverse before, [ ("", redrawSymbolText' s) | s <- ss ])
  where
    single t = (reverse before, [(spaced t, t)])
    spaced t = if null before || isSpace (last before) then t else ' ' : t

isLiteralView :: SymbolView -> Bool
isLiteralView s = case s of
  ALiteralSymbol _ -> True
  _ -> False

redrawWritten :: SymbolView -> String
redrawWritten s = case s of
  ALiteralSymbol t -> t
  _ -> "?"

redrawSymbolText' :: SymbolView -> String
redrawSymbolText' s = case s of
  ALiteralSymbol t -> t
  AScanSymbol n -> "\8249" ++ n ++ "\8250"
  ANonterminalSymbol n -> "\8249" ++ n ++ "\8250"

-- ---------------------------------------------------------------------------
-- A region, as an editor holds one
--
-- **Phase 125's own change.** 'displayOffer' took the two sides of the cursor as
-- 'String's until here, so a region with a splice in it could not be asked about
-- at all and a caller that needed one — his own TUI — went to 'Earley.offer'
-- directly and rebuilt the view by hand, the two refusals included. These are
-- the cases that signature makes possible.

regionCases :: [TestTree]
regionCases =
  [ testCase "a language nothing declared is refused, by name" $
      displayOffer [] "LC" Nothing [] [] @?= Left (NoSuchLanguage "LC")
  , testCase "so is a production the language does not have" $ do
      gs <- loaded
      displayOffer gs "LC" (Just "nope") [] [] @?= Left (NoSuchProduction "LC" "nope")
  , testCase "an explicit production starts there instead of at the language" $ do
      gs <- loaded
      -- At @app@ the region must open with @(@; at the language, @\955@ is
      -- reachable too, because @abs@ is a term as well.
      opts <- optionsOf gs "LC" (Just "app") [] []
      whole <- optionsOf gs "LC" Nothing [] []
      assertBool "app offers no more than LC does" (all (`elem` whole) opts)
      assertBool "and LC offers something app does not" (opts /= whole)
  , testCase "a splice stands where a term would" $ do
      gs <- loaded
      -- A splice fills a slot exactly as the placeholder does, so what may
      -- follow it is what may follow a filled slot.
      spliced <- optionsOf gs "LC" Nothing [WrittenText "( ", WrittenSplice] []
      holed <- optionsOf gs "LC" Nothing [WrittenText "( ?"] []
      spliced @?= holed
  , testCase "the splices of a region are numbered in order, from zero" $ do
      gs <- loaded
      -- **The numbering is only visible in a tree**, which is why this case
      -- reads rather than offers: an 'Earley.Offer' carries symbols, so a
      -- region numbered wrongly offers exactly what a region numbered rightly
      -- does. 'displayOffer' splits its region at the cursor and numbers the
      -- two halves as one; nothing about that is checkable there, and here it
      -- is.
      displayParse gs "LC" Nothing [WrittenText "( ", WrittenSplice, WrittenText " ", WrittenSplice, WrittenText " )"]
        @?= Right (ANode "app" [ASpliceOf 0, ASpliceOf 1])
  , testCase "and a written term beside a splice does not take a number" $ do
      gs <- loaded
      displayParse gs "LC" Nothing [WrittenText "( x ", WrittenSplice, WrittenText " )"]
        @?= Right (ANode "app" [ANode "var" [ATokenView "x"], ASpliceOf 0])
  , testCase "an explicit production reads at that production" $ do
      gs <- loaded
      -- @T@ is @Ty@'s own nonterminal, so @\953@ reads there and not at @LC@.
      displayParse gs "Ty" (Just "base") [WrittenText "\953"] @?= Right (ANode "base" [])
  ]

optionsOf :: [Grammar] -> String -> Maybe String -> [Written] -> [Written] -> IO [String]
optionsOf gs lang prod before after = case displayOffer gs lang prod before after of
  Left p  -> assertFailure ("displayOffer refused a fixture: " <> show p) >> pure []
  Right o -> pure (map redrawSymbolText (offeredOptions o ++ offeredWanted o))
