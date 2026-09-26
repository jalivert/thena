-- | The Earley chart's own questions, at the protocol (MS7 phase 115e).
--
-- **The crossing, once more.** 'redrawParse' and 'redrawOffer' draw only what
-- 'Thena.Protocol.Chart.displayParse' and 'Thena.Protocol.Chart.displayOffer'
-- hand them; if that agrees with what 'Thena.Repl.renderTree'\/
-- 'Thena.Repl.parseFailureReason' and 'Thena.Repl.tabComplete' already do with
-- the same chart, for the same text, the protocol view carries what those two
-- existing consumers needed.
--
-- **What is not crossed.** 'Thena.Protocol.Chart.AnAmbiguity',
-- 'Thena.Protocol.Chart.AnUnboundedRule' and
-- 'Thena.Protocol.Chart.ADisagreement' mirror 'Earley.Ambiguous',
-- 'Earley.Unbounded' and 'Earley.Disagrees' one constructor to one, over the
-- same 'TreeView' already crossed by the successful case — nothing in the
-- fixture grammar below is ambiguous or self-deriving, and forcing one would
-- test the mirroring function's four-line 'case', not the view. Kept total
-- rather than partial, the same call 115d made for 'Thena.Protocol.Instral.ValOpaque'.
module Thena.Protocol.ChartTests (tests) where

import Data.Char (isSpace)
import Data.List (intercalate)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase)

import Thena.Driver (Response (..), Session (..), loadProofSource)
import Thena.Engine (Machine (..))
import qualified Thena.Language.Earley as Earley
import Thena.Language.Grammar (Grammar, earleyRules)
import Thena.Protocol.Chart
  ( FailureView (..)
  , OfferView (..)
  , SymbolView (..)
  , TreeView (..)
  , displayOffer
  , displayParse
  )
import Thena.Repl (parseFailureReason, renderTree, startingSession, tabComplete)
import Thena.Syntax.Print (escapeChar)

tests :: TestTree
tests =
  testGroup
    "Thena.Protocol.Chart"
    [ testGroup "is this text one term (Earley.parse)" parseCases
    , testGroup "what may stand at the cursor (Earley.offer)" offerCases
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
    (s1, ProofLoaded {}) -> pure (grammars (sessionMachine s1))
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
    drawn = case displayParse gs lang text of
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
    drawn = redrawOffer before (displayOffer gs lang before after)

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
