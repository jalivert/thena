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

import Thena.Core.Term (Spelling, Var, spelledIn)
import Thena.Instral.Ops (Origin (..), Rule (..), Test)
import Thena.Syntax.Lexer (Pos)
import Thena.Instral.Pattern (Pattern (..))
import Thena.Language.Grammar (Grammar)
import Thena.View.Address (Address)
import Thena.View.Core (Budget)
import Thena.View.Instral (OperandView, StatementView, displayBlock, displayOperand, patternText)
import Thena.Rules (testOperands, testWord)
import Thena.Instral.Type (Signature)
import Thena.View.Type (SignatureView, displaySignature)
import Thena.Syntax.Print (Env, componentPText)

-- | A rule's name, its head, its params as `:matches`' own placeholders, and
-- its body as 115d's statements — a rule's body is never a live @pc@, so
-- nothing here is ever "next".
data RuleView = RuleView
  { ruleViewName      :: String
  , ruleViewHead      :: [TestView]
  , ruleViewParams    :: [String]
  , ruleViewFocus     :: Maybe String
    -- ^ __the clause's @at@ pattern, as written__ (MS12 phase 358, @~9j34x@;
    -- his framing of 2026-09-14) — one of the five development components with
    -- a pattern at each position, in @spec\/machine.md@ §3.2's notation and
    -- with no fence (his ruling of 2026-09-13).
    --
    -- **A 'String' for the reason 'ruleViewParams' is one**: what a pane draws
    -- here is the line the author wrote, and 'Thena.Syntax.Print.componentPText'
    -- is a spelling that reads back, so a reader who copies it has a line the
    -- grammar takes. A structured shape would be a second description of the
    -- development calculus's notation for a pane that draws it as text.
    --
    -- **'Nothing' is a clause that asks nothing about the focus**, which is
    -- every clause written before this phase.
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
  , ruleViewPath      :: Maybe FilePath
    -- ^ __the file this clause was written in__ (MS12 phase 343, @~zx8cb@).
  , ruleViewAt        :: Maybe Pos
    -- ^ __the line and column it begins at__ (MS12 phase 343, @~zx8cb@), so a
    -- pane of a rule's clauses can open one.
    --
    -- **A row of this view /is/ one clause**, which is why the position belongs
    -- here and not on 'Thena.View.Matches.MatchView': a match row stands for
    -- every clause of a name and arity (his ruling, 2026-11-19), and a group has
    -- no one place it is written at. A pane that shows the clauses behind a row
    -- gets them from here, and that is the pane this was missing for.
    --
    -- **The same two fields and the same meaning as
    -- 'Thena.View.Choices.AltView'**, which phase 342 gave the choice-point
    -- pane: a clause is a destination or it is nowhere, and a frontend should
    -- not have to learn a second shape for it depending on which pane it is
    -- drawing. 'Nothing' is a clause in no file — the synthetic @entry@ and @do@
    -- rules a typed line is wrapped in — and a clause a base read always has
    -- both ('Thena.Instral.Ops.ruleOrigin').
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
  :: Spelling -> [Grammar] -> Budget -> Env -> [(Var, Address)] -> Int -> Address
  -> Maybe Signature -> Rule -> RuleView
displayRule sp gs budget env bs n at sig r =
  RuleView
    (nameOf (ruleName r))
    (map test (ruleHead r))
    (map placeholder (ruleParams r))
    (componentPText placeholder <$> ruleFocus r)
    (displayBlock sp gs budget env bs n at Nothing (ruleBody r))
    (fmap displaySignature sig)
    (originPath <$> ruleOrigin r)
    (originAt <$> ruleOrigin r)
  where
    nameOf = spelledIn sp
    placeholder pt = case pt of
      PVar x -> "\8249" ++ x ++ "\8250"
      _      -> patternText pt
    test :: Test -> TestView
    test t = TestView (testWord t) (map (displayOperand sp gs budget env bs n at) (testOperands t))
