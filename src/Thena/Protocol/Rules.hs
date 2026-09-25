-- | A rule in the base, to the editor (MS7 phases 115g and 115i;
-- @discussion\/editor-display.md@ §7's own words: "a rule in the base
-- carries its head, its tests, and its body as statements").
--
-- **115g's own plan said a rule's head had no printer to expose — that was
-- wrong, the same way 115d's `renderValue` claim about a surface focus was
-- wrong (115h).** `Thena.Rules.testWord`/`testOperands` are
-- `Thena.Instral.Ops.opKeyword`/`operandsOf`'s own trick, one type over —
-- total, generic, exported — sitting beside the very functions `RuleView`'s
-- body already reuses. `:matches`/`:rules` never call them, so there was no
-- *terminal* printer to point at, but the seam this milestone has crossed
-- against everywhere else was never "the terminal already shows it"; it was
-- "the system already resolved it into a word and its operands, generically,
-- rather than a case per constructor." A head test is exactly that.
module Thena.Protocol.Rules
  ( RuleView (..)
  , TestView (..)
  , displayRule
  ) where

import Thena.Core.Term (GlobalName (..), Var)
import Thena.Instral.Ops (Rule (..), Test)
import Thena.Instral.Pattern (Pattern (..))
import Thena.Language.Grammar (Grammar)
import Thena.Protocol.Address (Address)
import Thena.Protocol.Display (Budget)
import Thena.Protocol.Instral (OperandView, StatementView, displayBlock, displayOperand, patternText)
import Thena.Rules (testOperands, testWord)
import Thena.Syntax.Print (Env)

-- | A rule's name, its head, its params as `:matches`' own placeholders, and
-- its body as 115d's statements — a rule's body is never a live @pc@, so
-- nothing here is ever "next".
data RuleView = RuleView
  { ruleViewName   :: String
  , ruleViewHead   :: [TestView]
  , ruleViewParams :: [String]
  , ruleViewBody   :: [StatementView]
  }
  deriving (Eq, Show)

-- | One head test, generically — 'Thena.Instral.Ops.Test's own shape, the
-- word from 'Thena.Rules.testWord', the operands from
-- 'Thena.Rules.testOperands', exactly as 'Thena.Protocol.Instral.StatementView'
-- already does for an op.
data TestView = TestView
  { testViewWord     :: String
  , testViewOperands :: [OperandView]
  }
  deriving (Eq, Show)

-- | 'Thena.Repl.renderMatches's own two lines, replayed: a variable param
-- keeps its corners (it says "put something here"), anything else is shown
-- as written (it says what shape the something must be).
displayRule :: [Grammar] -> Budget -> Env -> [(Var, Address)] -> Int -> Address -> Rule -> RuleView
displayRule gs budget env bs n at r =
  RuleView
    (nameOf (ruleName r))
    (map test (ruleHead r))
    (map placeholder (ruleParams r))
    (displayBlock gs budget env bs n at Nothing (ruleBody r))
  where
    nameOf (GlobalName g) = g
    placeholder pt = case pt of
      PVar x -> "\8249" ++ x ++ "\8250"
      _      -> patternText pt
    test :: Test -> TestView
    test t = TestView (testWord t) (map (displayOperand gs budget env bs n at) (testOperands t))
