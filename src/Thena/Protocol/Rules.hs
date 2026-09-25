-- | A rule in the base, to the editor (MS7 phase 115g;
-- @discussion\/editor-display.md@ §7's own words: "a rule in the base
-- carries its head, its tests, and its body as statements").
--
-- **Only the name, the params and the body are here.** A rule's head
-- (@['Thena.Instral.Ops.Test']@ — fourteen-plus constructors, some carrying
-- an 'Thena.Instral.Ops.Operand' of their own) has no printer anywhere in
-- the terminal today: @:matches@\/@:rules@ show a rule's name and params
-- (@Thena.Repl.renderMatches@) and never its head at all — a match either
-- fires or it does not, and the terminal has never had to say why. Every
-- phase since 115a has stayed inside "expose what a printer already needs";
-- inventing a display for something with no printer would be the first to
-- step outside that, so it is left to him rather than decided here — see
-- the phase's own plan and @ms7\/CLOSEOUT.md@.
module Thena.Protocol.Rules
  ( RuleView (..)
  , displayRule
  ) where

import Thena.Core.Term (GlobalName (..), Var)
import Thena.Instral.Ops (Rule (..))
import Thena.Instral.Pattern (Pattern (..))
import Thena.Language.Grammar (Grammar)
import Thena.Protocol.Address (Address)
import Thena.Protocol.Display (Budget)
import Thena.Protocol.Instral (StatementView, displayBlock, patternText)
import Thena.Syntax.Print (Env)

-- | A rule's name, its params as `:matches`' own placeholders, and its body
-- as 115d's statements — a rule's body is never a live @pc@, so nothing here
-- is ever "next".
data RuleView = RuleView
  { ruleViewName   :: String
  , ruleViewParams :: [String]
  , ruleViewBody   :: [StatementView]
  }
  deriving (Eq, Show)

-- | 'Thena.Repl.renderMatches's own two lines, replayed: a variable param
-- keeps its corners (it says "put something here"), anything else is shown
-- as written (it says what shape the something must be).
displayRule :: [Grammar] -> Budget -> Env -> [(Var, Address)] -> Int -> Address -> Rule -> RuleView
displayRule gs budget env bs n at r =
  RuleView (nameOf (ruleName r)) (map placeholder (ruleParams r)) (displayBlock gs budget env bs n at Nothing (ruleBody r))
  where
    nameOf (GlobalName g) = g
    placeholder pt = case pt of
      PVar x -> "\8249" ++ x ++ "\8250"
      _      -> patternText pt
