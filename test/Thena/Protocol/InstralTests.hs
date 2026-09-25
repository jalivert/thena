-- | The @instral@ statement display (MS7 phase 115d;
-- @discussion\/editor-display.md@ §7, first half).
--
-- **The crossing**, 115a/b/c's own argument again: 'redrawBlock' draws only
-- what 'Thena.Protocol.Instral.displayBlock' hands it, and if that text is
-- what 'Thena.Repl.renderInstr' prints for the same instructions, the display
-- carries what the printer needed. The corpus is every instruction the
-- shipped rule base's own rules are written with — real bodies, not
-- hand-built ones, so the crossing is over what actually got written rather
-- than a curated sample of it.
module Thena.Protocol.InstralTests (tests) where

import Data.List (intercalate)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase)

import Thena.Driver (Session (..))
import Thena.Engine (Machine (..))
import Thena.Instral.Ops (Instr, Rule (..))
import Thena.Protocol.Address (Address (..))
import Thena.Protocol.Display (Budget (..))
import Thena.Protocol.Instral
  ( OperandView (..)
  , SkeletonView (..)
  , StatementDetail (..)
  , StatementView (..)
  , ValueView (..)
  , displayBlock
  )
import Thena.Protocol.Redraw (redraw)
import Thena.Repl (renderInstr, startingSession)
import Thena.Rules (allRules)

tests :: TestTree
tests =
  testGroup
    "Thena.Protocol.Instral"
    [ testCase "the display carries everything the printer needed" corpus
    , testCase "and the corpus really holds statements" notVacuous
    ]

-- | Every instruction in the shipped rule base's own rules.
corpusOf :: IO [Instr]
corpusOf = concatMap ruleBody . allRules . rules . sessionMachine . fst <$> startingSession

corpus :: IO ()
corpus = do
  is <- corpusOf
  case [e | Just e <- map mismatch is] of
    [] -> pure ()
    e : _ -> assertFailure e

notVacuous :: IO ()
notVacuous = do
  n <- length <$> corpusOf
  if n >= 50 then pure () else assertFailure ("only " <> show n <> " instructions in the corpus")

mismatch :: Instr -> Maybe String
mismatch instr
  | shown == drawn = Nothing
  | otherwise = Just ("printed: " <> shown <> "\n  drawn:   " <> drawn)
  where
    shown = renderInstr [] 500 [] instr
    drawn = case displayBlock [] (Budget 200) [] [] 500 (Address []) Nothing [instr] of
      [v] -> redrawStatement v
      vs  -> "wrong count: " <> show (length vs)

-- | What an editor is, for one statement: a function from a 'StatementView'
-- to text, and nothing else — mirrors 'Thena.Repl.renderInstr'\/'renderOp'\/
-- 'renderOperand'\/'renderValue' because that is the seam under test.
redrawStatement :: StatementView -> String
redrawStatement sv = bind <> word <> operandsText <> detailText
  where
    bind = case (statementBind sv, statementAnnotation sv) of
      (Nothing, _)         -> ""
      (Just p, Nothing)    -> p <> " = "
      (Just p, Just ty)    -> p <> " : " <> ty <> " ; " <> p <> " = "

    word = statementWord sv

    -- 'Thena.Repl.renderOp's own shapes: a call's target sits between the
    -- word and its arguments; a declaration's name has no arguments to sit
    -- before.
    operandsText = case statementDetail sv of
      Just (Calls nm)    -> " " <> nm <> operandsAfter
      Just (Declares nm) -> " " <> nm <> operandsAfter
      _                  -> operandsAfter
    operandsAfter = concatMap ((" " <>) . redrawOperand) (statementOperands sv)

    detailText = case statementDetail sv of
      Just (AsksFor k) -> " " <> k
      Just (Crosses w) -> " " <> w
      _                -> ""

redrawOperand :: OperandView -> String
redrawOperand o = case o of
  OpndRef x -> x
  OpndLiteral v -> redrawValue v
  OpndList os -> "[" <> intercalate ", " (map redrawOperand os) <> "]"
  OpndPair a b -> "(" <> redrawOperand a <> ", " <> redrawOperand b <> ")"
  OpndObject sk -> redrawSkeleton redrawOperand sk

redrawSkeleton :: (a -> String) -> SkeletonView a -> String
redrawSkeleton at sk = case sk of
  SkelNode nm [] -> nm
  SkelNode nm kids -> nm <> "(" <> intercalate ", " (map (redrawSkeleton at) kids) <> ")"
  SkelLiteral t -> t
  SkelHole a -> "$" <> "{" <> at a <> "}"

redrawValue :: ValueView -> String
redrawValue v = case v of
  ValText s -> s
  ValInt k -> show k
  ValChar t -> t
  ValBool True -> "true"
  ValBool False -> "false"
  ValList vs -> "[" <> intercalate ", " (map redrawValue vs) <> "]"
  ValNone -> "none"
  ValSome u -> "some " <> redrawValue u
  ValPair a b -> "(" <> redrawValue a <> ", " <> redrawValue b <> ")"
  ValLevel l -> l
  -- 'Thena.Repl.renderValue's own corners for a term operand, matched
  -- exactly rather than approximated — the one place this crossing compares
  -- a term's own text byte for byte.
  ValTerm d -> "\8988" <> redraw d <> "\8989"
  -- Never reached by this corpus: a closure, a surface focus and an
  -- unresolved core region are built by ops at run time ('Lambda',
  -- elaboration, 'resolve-core'), never written as a literal operand in a
  -- rule's own source — so 'Thena.Instral.Ops.operandsOf' never hands one to
  -- a statically-written body. Kept total rather than partial.
  ValOpaque other -> "\8249" <> other <> "\8250"
