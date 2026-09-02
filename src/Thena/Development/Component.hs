-- | The five components of the development calculus, and the forgetful view.
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
  | Quantify Var Ident       Core    -- ^ @∀ x     : S@
    -- ^ **The fifth component, and the one McBride does not have** (MS4 phase
    -- 41f, the user's decision). It binds exactly as 'Assume' does and differs
    -- in one place only: 'Thena.Development.Partial.extract' folds it into a
    -- 'Thena.Core.Term.Pi' where 'Assume' folds into a
    -- 'Thena.Core.Term.Lam'.
    --
    -- **It exists because a Π cannot otherwise be built.** Elaborating
    -- @∀ (x : A) -> B@ has to put @x@ in Γ so that @B@ can mention it, and the
    -- only way to put anything in Γ is to write a component; every component
    -- there was extracted as a term, so the chain could express @λ x : A . B@
    -- and never @Π x : A . B@. That is not a gap in the surface language but
    -- in the development calculus, and it is the same one a declaration hits:
    -- Brady elaborates a signature as a development of its own
    -- (@IDRIS.md@ §4.6, @NEW PROOF Type; E⟦t⟧; t' ← TERM@) before elaborating
    -- the body against it.
    --
    -- **A guess over one is well typed throughout.** @? h ≐ (∀ x : A . ? h₁) :
    -- Type ℓ@ is a valid state at every step of the elaboration, where the
    -- rejected alternative — assume the binder and read the guess's λs as Πs
    -- when solving — left the development transiently claiming a λ at a
    -- universe.
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
-- A ∀-binder is a hypothesis exactly as a λ-binder is: inside the codomain the
-- variable stands for an unknown of that type, and Γ cannot tell which former
-- will be built above it.
forget (Quantify x i s) = Hypothesis x i   s
