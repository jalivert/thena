-- | The four components of the development calculus, and the forgetful view.
module Thena.Development.Component
  ( Component (..)
  , forget
  ) where

import Thena.Core.Context (Entry (..))
import Thena.Core.Term (Core, Ident, Var)
import {-# SOURCE #-} Thena.Development.Partial (Partial)

-- | Invariant: the type is always the last field, so the shape reads like the
-- notation of §3.2.
--
-- Hard side condition on 'Claim' and 'Guess', DOCUMENTED AND NOT ENFORCED
-- (§3.2, §3.4): @x ∉ FV(S)@. The variable a hole binds may be used in the term
-- under its binder but not in its own type. Enforcing it would mean hiding
-- these constructors, and §2.5 decided against that so that
-- "Thena.Development.Cursor" can decompose a component into a @Slot@.
--
-- A guess is NOT a definition. It has no computational force and is invisible
-- to the core, which is what 'forget' below makes true.
data Component
  = Assume Var Ident         Core    -- ^ @λ x     : S@
  | Define Var Ident Core    Core    -- ^ @x  = s  : S@
  | Claim  Var Ident         Core    -- ^ @? x     : S@
  | Guess  Var Ident Partial Core    -- ^ @? x ≐ g : S@
  deriving (Eq, Show)

-- | McBride's forgetful view, printed p. 28 (§3.2).
--
-- Uniform: every component keeps exactly its @:@ and its @=@ if it has one. A
-- 'Guess' forgets to a hypothesis with no value, so δ cannot unfold it —
-- "guesses are invisible to the core" is enforced here rather than by a lookup
-- rule somebody has to remember to write.
forget :: Component -> Entry
forget (Assume x i   s) = Hypothesis x i   s
forget (Define x i v s) = Definition x i v s
forget (Claim  x i   s) = Hypothesis x i   s
forget (Guess  x i _ s) = Hypothesis x i   s
