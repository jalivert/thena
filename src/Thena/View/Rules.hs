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
module Thena.View.Rules
  ( RuleView (..)
  , TestView (..)
  , displayRule
  ) where

import Thena.Core.Term (GlobalName (..), Var)
import Thena.Instral.Ops (Rule (..), Test)
import Thena.Instral.Pattern (Pattern (..))
import Thena.Language.Grammar (Grammar)
import Thena.View.Address (Address)
import Thena.View.Core (Budget)
import Thena.View.Instral (OperandView, StatementView, displayBlock, displayOperand, patternText)
import Thena.Rules (testOperands, testWord)
import Thena.Instral.Type (Signature)
import Thena.View.Type (SignatureView, displaySignature)
import Thena.Syntax.Print (Env)

-- | A rule's name, its head, its params as `:matches`' own placeholders, and
-- its body as 115d's statements — a rule's body is never a live @pc@, so
-- nothing here is ever "next".
data RuleView = RuleView
  { ruleViewName      :: String
  , ruleViewHead      :: [TestView]
  , ruleViewParams    :: [String]
  , ruleViewBody      :: [StatementView]
  , ruleViewSignature :: Maybe SignatureView
    -- ^ **the type its rule file declared for the name** (MS5 phase 67), as
    -- "Thena.View.Type" structures it — the parameters and the result, with a
    -- function-typed one fenced so the arity reads right. 'Nothing' where the
    -- file declared none.
    --
    -- Added at MS7 phase 131 (@ms7\/CLOSEOUT.md@ 17) carrying
    -- 'Thena.Instral.Type.renderSignature''s rendered 'String', knowingly and
    -- as a stopgap, because "Thena.Instral.Type" is not on @thena:view@'s list.
    -- **MS7 phase 133 replaced it rather than standing a second field beside
    -- it** (@ms7\/CLOSEOUT.md@ 27, his ruling): two spellings of one thing is
    -- the confusion the literal alternative costs nothing to avoid, and
    -- "Thena.View.TypeTests" rebuilds the rendered form from this one byte for
    -- byte, so nothing is lost by dropping it.
  }
  deriving (Eq, Show)

-- | One head test, generically — 'Thena.Instral.Ops.Test's own shape, the
-- word from 'Thena.Rules.testWord', the operands from
-- 'Thena.Rules.testOperands', exactly as 'Thena.View.Instral.StatementView'
-- already does for an op.
data TestView = TestView
  { testViewWord     :: String
  , testViewOperands :: [OperandView]
  }
  deriving (Eq, Show)

-- | 'Thena.Render.renderMatches's own two lines, replayed: a variable param
-- keeps its corners (it says "put something here"), anything else is shown
-- as written (it says what shape the something must be).
displayRule
  :: [Grammar] -> Budget -> Env -> [(Var, Address)] -> Int -> Address
  -> Maybe Signature -> Rule -> RuleView
displayRule gs budget env bs n at sig r =
  RuleView
    (nameOf (ruleName r))
    (map test (ruleHead r))
    (map placeholder (ruleParams r))
    (displayBlock gs budget env bs n at Nothing (ruleBody r))
    (fmap displaySignature sig)
  where
    nameOf (GlobalName g) = g
    placeholder pt = case pt of
      PVar x -> "\8249" ++ x ++ "\8250"
      _      -> patternText pt
    test :: Test -> TestView
    test t = TestView (testWord t) (map (displayOperand gs budget env bs n at) (testOperands t))
