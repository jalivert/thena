-- | Patterns — what stands on the left of a clause's parameter list and, since
-- MS5 phase 84, on the left of a binding.
--
-- **Its own module for the reason 'Thena.Instral.Type' is** (MS5 phase 84):
-- "Thena.Errors" has to name a 'Pattern' — a call's destination is one, so
-- @NothingReturned@ carries one — and it cannot import "Thena.Ops", which
-- reaches "Thena.Errors" through "Thena.Development.Cursor". The type is pure
-- syntax and depends on nothing, so it moves down a layer and both import it.
--
-- **The matcher stays in "Thena.Ops"**, because matching needs a
-- 'Thena.Ops.Value' and a value is what the machine has. What lives here is the
-- shape and the two questions that are about the shape alone.
module Thena.Instral.Pattern
  ( Pattern (..)
  , patternBinds
  , patternIrrefutable
  ) where

type Name = String

-- | What stands in a parameter position (MS5 phase 82).
--
-- **A pattern is written in the language of the value it matches** — his
-- correction, and the whole of @discussion\/pattern-matching.md@ §2. Claude
-- proposed a word notation, @(cons x xs)@; he wanted the literal's own
-- spelling, so a list pattern /is/ a list literal and a pair pattern is a pair.
-- The strongest argument for him turned out to be accuracy rather than taste: a
-- word-pattern has to name every field or silently drop one.
--
-- **A bare identifier is a VARIABLE, and that is decision 1 of §4** — it is what
-- buys @[a, ...rest]@ with no sigil, and its price is that a /named constructor/
-- cannot be matched. That price is not paid here: @instral@'s own data has no
-- named constructors except 'PSome' and 'PNone', which are words in the grammar
-- rather than values a user can shadow. It is paid at stage b and c, which are
-- not built.
--
-- **This stage is @instral@'s own data only.** A Surface pattern (@⟨ a -> b ⟩@)
-- and a Core one are stages b and c of that document, and c waits on the two
-- decisions §4 records as open.
data Pattern
  = PVar Name            -- ^ @x@ — binds, and matches anything
  | PWild                -- ^ @_@ — matches anything, binds nothing
  | PInt  Int            -- ^ @3@
  | PChar Char           -- ^ @\'c\'@
  | PBool Bool           -- ^ @true@, @false@
  | PText String         -- ^ @"…"@ — matches 'VText', so a name too
  | PList [Pattern] (Maybe Pattern)
    -- ^ @[a, b]@ closed, @[a, ...rest]@ open.
    --
    -- **The tail is a whole pattern, not a name**, so @[a, ...rest]@,
    -- @[a, ..._]@ and @[a, ...[]]@ all read — his §2. @...@ prefixes /any/ list
    -- pattern, which is why the field is a 'Pattern' and not a 'Maybe' 'Name'.
    --
    -- **Final position only.** @[...xs, a]@ is a snoc and wants the list
    -- reversed; it is not written.
  | PPair Pattern Pattern -- ^ @(x, y)@ — the pair /value/ needs nothing new
  | PSome Pattern         -- ^ @some x@
  | PNone                 -- ^ @none@
  deriving (Eq, Show)

-- | The names a pattern binds, left to right.
--
-- **Every name-shaped question about a rule goes through this**, which is what
-- keeps @ruleParams@ becoming patterns from being twenty separate changes:
-- 'Thena.Rules.initiallyBound', the reserved-name check and the head's scope
-- check all asked @ruleParams@ for its names and now ask this.
patternBinds :: Pattern -> [Name]
patternBinds pt = case pt of
  PVar n      -> [n]
  PWild       -> []
  PInt _      -> []
  PChar _     -> []
  PBool _     -> []
  PText _     -> []
  PList ps mt -> concatMap patternBinds ps ++ maybe [] patternBinds mt
  PPair a b   -> patternBinds a ++ patternBinds b
  PSome a     -> patternBinds a
  PNone       -> []

-- | Does this pattern match every value of its type?
--
-- **Only 'Thena.Driver' asks**, and only to decide whether an earlier clause of
-- a /function/ makes a later one unreachable (MS5 phase 80's refusal, narrowed
-- by this phase). A list pattern is refutable even when its elements are
-- variables, because the value may be a different length; a pair is not,
-- because the type says it is a pair.
--
-- **It is deliberately an under-approximation.** Answering 'False' only means
-- /not obviously total/, so the refusal fires less often than it could — which
-- is the safe direction: refusing a clause that would in fact be unreachable is
-- a false alarm, and admitting one is merely dead code the author can see.
patternIrrefutable :: Pattern -> Bool
patternIrrefutable pt = case pt of
  PVar _    -> True
  PWild     -> True
  PPair a b -> patternIrrefutable a && patternIrrefutable b
  _         -> False

