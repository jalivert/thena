-- | A rule's name, head, params and body, as a view (MS7 phases 115g
-- and 115i).
--
-- **The crossing, in three already-proven pieces.** The name and params
-- cross against 'Thena.Render.renderMatches' — the same line
-- @:matches@\/@:rules@ show. The body reuses 115d's own
-- 'redrawStatement'\/'redrawOperand'\/'redrawSkeleton'\/'redrawValue'.
-- **The head (115i) crosses each test's word against 'Thena.Rules.testWord'
-- directly** — there is no third table to disagree with it, since
-- 'Thena.View.Rules.displayRule' calls the very function the resolver
-- itself does — **and each test's operands against
-- 'Thena.Render.renderOperand'**, a real, independently-written printer
-- ('Thena.Render.renderOp's own generic case), over the shipped rule base's
-- own rules, not a hand-built sample.
module Thena.View.RulesTests (tests) where

import Data.List (intercalate)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase)

import Thena.Driver
  ( machineOf
  )
import Thena.Engine (Machine (..))
import Thena.Core.Term (GlobalName (..))
import Thena.Instral.Ops (Rule (ruleBody, ruleHead), ruleName)
import Thena.Instral.Type (renderSignature)
import Thena.View (rulesView)
import Thena.View.Address (Address (..))
import Thena.View.Core (Budget (..))
import Thena.View.Instral
  ( OperandView (..)
  , SkeletonView (..)
  , StatementDetail (..)
  , StatementView (..)
  , ValueView (..)
  )
import Thena.View.Redraw (redraw, redrawSurface)
import Thena.View.Rules (RuleView (..), TestView (..), displayRule)
import Thena.Files (startingSession)
import Thena.Render (renderInstr, renderMatches, renderOperand)
import Thena.Rules (RuleBase (..), allRules, testOperands, testWord)

tests :: TestTree
tests =
  testGroup
    "Thena.View.Rules"
    [ testCase "the display carries everything the printer needed" corpus
    , testCase "and the corpus really holds rules" notVacuous
    , testCase "and the corpus really holds head tests" headsNotVacuous
    , testCase "a rule's declared type reaches the view it is in" declaredTypes
    , testCase "and the shipped base really declares types" declaredTypesNotVacuous
    ]

corpusOf :: IO [Rule]
corpusOf = allRules . rules . machineOf . fst <$> startingSession

-- | **The signature crossing** (MS7 phase 131, @ms7\/CLOSEOUT.md@ 17).
--
-- 'Thena.View.rulesView' looks a rule's type up in the base the rule is
-- actually in; this asserts the view's field is exactly what
-- 'Thena.Instral.Type.renderSignature' writes for that entry, and 'Nothing'
-- where the file declared none. The table is read here from 'baseSignatures'
-- directly, which is the thing a frontend used to have to reach past the seam
-- for — so the two sides really are independent.
declaredTypes :: IO ()
declaredTypes = do
  s <- fst <$> startingSession
  let bs = rules (machineOf s)
      wrong =
        [ unwords [baseName b, nameOf r, "view:", show (ruleViewSignature rv), "table:", show want]
        | b  <- bs
        , (r, rv) <- zip (baseRules b) (concat [ vs | (n, vs) <- rulesView (Budget 200) s
                                                    , n == baseName b ])
        , let want = fmap renderSignature (lookup (nameOf r) (baseSignatures b))
        , ruleViewSignature rv /= want
        ]
  case wrong of
    []    -> pure ()
    e : _ -> assertFailure e
  where
    nameOf r = case ruleName r of GlobalName g -> g

-- | A green 'declaredTypes' over a base that declares nothing would prove nothing.
declaredTypesNotVacuous :: IO ()
declaredTypesNotVacuous = do
  s <- fst <$> startingSession
  let n = length [ () | (_, vs) <- rulesView (Budget 200) s
                      , v <- vs, Just _ <- [ruleViewSignature v] ]
  if n >= 10 then pure ()
    else assertFailure ("only " <> show n <> " rules in the view carry a type")

corpus :: IO ()
corpus = do
  rs <- corpusOf
  case [e | Just e <- map mismatch rs] of
    [] -> pure ()
    e : _ -> assertFailure e

notVacuous :: IO ()
notVacuous = do
  n <- length <$> corpusOf
  if n >= 30 then pure () else assertFailure ("only " <> show n <> " rules in the corpus")

headsNotVacuous :: IO ()
headsNotVacuous = do
  n <- sum . map (length . ruleHead) <$> corpusOf
  if n >= 20 then pure () else assertFailure ("only " <> show n <> " head tests in the corpus")

mismatch :: Rule -> Maybe String
mismatch r
  | shownLine == drawnLine && shownBody == drawnBody && shownHead == drawnHead = Nothing
  | otherwise =
      Just
        ( "printed: " <> shownLine <> "\n  drawn:   " <> drawnLine
            <> "\n  printed body: " <> unlines shownBody
            <> "\n  drawn body:   " <> unlines drawnBody
            <> "\n  printed head: " <> unlines shownHead
            <> "\n  drawn head:   " <> unlines drawnHead
        )
  where
    rv = displayRule [] (Budget 200) [] [] 500 (Address []) Nothing r
    shownLine = case renderMatches [r] of
      [line] -> line
      other  -> "wrong count: " <> show (length other)
    drawnLine = unwords (ruleViewName rv : ruleViewParams rv)
    shownBody = map (renderInstr [] 500 []) (ruleBody r)
    drawnBody = map redrawStatement (ruleViewBody rv)
    shownHead =
      [ testWord t <> concatMap ((" " <>) . renderOperand [] 500 []) (testOperands t)
      | t <- ruleHead r
      ]
    drawnHead = map redrawTest (ruleViewHead rv)

redrawTest :: TestView -> String
redrawTest tv = testViewWord tv <> concatMap ((" " <>) . redrawOperand) (testViewOperands tv)

-- ---------------------------------------------------------------------------
-- 115d's own redraw, copied rather than shared — see
-- 'Thena.View.InstralTests' and 'Thena.View.MachineTests' for the
-- same call made twice already.

redrawStatement :: StatementView -> String
redrawStatement sv = bind <> word <> operandsText <> detailText
  where
    bind = case (statementBind sv, statementAnnotation sv) of
      (Nothing, _)      -> ""
      (Just p, Nothing) -> p <> " = "
      (Just p, Just ty) -> p <> " : " <> ty <> " ; " <> p <> " = "

    word = statementWord sv

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
  ValTerm d -> "\8988" <> redraw d <> "\8989"
  ValSurface sh -> "\8249" <> redrawSurface sh <> "\8250"
  ValOpaque other -> "\8249" <> other <> "\8250"
