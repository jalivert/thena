-- | __The match list, one entry per rule__ (MS12).
--
-- His ruling, 2026-11-19: /"each rule-arity, in other words — each rule, gets
-- to be represented by one entry. So I could have @foo\/2@ and @foo\/4@ but
-- never two @foo@s."/ Until then @:matches@ and this view answered with one
-- entry per /clause/, which is the unit the engine dispatches into and is not a
-- unit the reader has: nothing in the surface names a clause, so a name with
-- twenty-two clauses printed twenty-two rows that could not be told apart or
-- acted on.
--
-- **This is its own module rather than a shape of 'Thena.View.Rules.RuleView'**,
-- because a row is no longer a rule's text. A clause has a head and a body; a
-- group of clauses has neither, and putting one clause's head on a row standing
-- for all of them would be the same mistake one level down. 'RuleView' keeps
-- the clause, which is what @:rules@ shows and what a pane showing the clauses
-- behind a row will want.
module Thena.View.Matches
  ( MatchView (..)
  , displayMatch
  ) where

import Thena.Core.Term (GlobalName, Spelling, spelledIn)
import Thena.Instral.Ops (Pattern)
import Thena.Rules (patternKind)
import Thena.Instral.Type (Signature)
import Thena.View.Type (SignatureView, displaySignature)

-- | One rule that applies at the focus: what to call it, what it takes, and
-- what the system worked out its arguments and answer are.
--
-- **There is no term in here**, so like 'Thena.View.Choices' this view needs no
-- 'Thena.View.Core.Budget': a depth to print to has nothing to bound.
data MatchView = MatchView
  { matchViewName   :: String
    -- ^ **spelled, not dotted** — 'Thena.Core.Term.spelledIn', the shortest
    -- ending that still resolves under what is open, which is what the prompt
    -- prints too.
  , matchViewArity  :: Int
    -- ^ how many arguments it takes. With the name this is the key the rule is
    -- grouped by, and it is what @\/2@ says in his @foo\/2@.
  , matchViewParams :: [String]
    -- ^ one placeholder per argument, in order, **without the corners** — a
    -- frontend draws its own. A position is named by the first clause that
    -- binds a name there ('Thena.Rules.groupParams'); where no clause does,
    -- it says what kind of thing the position takes instead.
  , matchViewType   :: Maybe SignatureView
    -- ^ **what it takes and gives, declared or inferred.** His, 2026-11-19:
    -- /"There will always be one, because we do inference. We will show not
    -- only user-written type when they wrote it, but when they didn't, what
    -- the system inferred."/ 'Nothing' cannot arise for a base that loaded,
    -- since a rule whose types do not work out is refused; it is 'Maybe' so a
    -- lookup miss is a blank rather than a crash.
  }
  deriving (Eq, Show)

-- | Build one. The arity is the length of the parameter list and is not passed
-- separately, so the two cannot disagree.
displayMatch
  :: Spelling -> GlobalName -> [Pattern] -> Maybe Signature -> MatchView
displayMatch sp nm ps sig =
  MatchView
    (spelledIn sp nm)
    (length ps)
    (map placeholder ps)
    (fmap displaySignature sig)
  where
    -- **A parameter that binds a name shows it; one that does not shows what
    -- kind of thing it is** — 'Thena.Rules.patternKind', the same word the
    -- prompt prints. A row stands for every clause of this name and arity, so a
    -- clause's own shape — @[]@, @(some f)@ — is not something the row may
    -- promise: a sibling clause takes a different one.
    placeholder = patternKind
