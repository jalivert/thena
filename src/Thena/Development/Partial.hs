-- | The partial construction: a chain of components with a term at the end.
module Thena.Development.Partial
  ( Partial (..)
  , Constraint (..)
  ) where

import Thena.Core.Context (Context)
import Thena.Core.Term (Core)
import Thena.Development.Component (Component)

-- | @p ::= t | c . p | κ . p@ — the grammar of §3.3 as a cons list with a
-- typed end.
--
-- There is deliberately NO application case: §2.2 forbids ?-bindings inside
-- applications, which is what keeps them out of computation entirely.
-- Applications live in 'Core'.
data Partial
  = Trailing Core                 -- ^ @t@
  | Under    Component Partial    -- ^ @c . p@, a binding
  | Pending  Constraint Partial   -- ^ @κ . p@, an undischarged unification problem
  deriving (Eq, Show)

-- | @κ ::= ∀Ξ. s ≟ t : T@ (§3.3), printed @Ξ ⊢ s ≟ t : T@ (§2.7).
--
-- Ξ is the LOCAL PREFIX: binders minted while decomposing under Π and λ, which
-- exist nowhere else in the development, so they travel with the problem.
--
-- A constraint is NOT a fifth 'Component' — it binds nothing, so it never
-- enters Γ, and it does that by construction rather than by a filter (§4.5).
-- In practice Ξ holds only 'Thena.Core.Context.Hypothesis' entries; documented,
-- not enforced, the same discipline as @x ∉ FV(S)@.
data Constraint
  = Equate Context Core Core Core   -- ^ @Ξ ⊢ s ≟ t : T@ (type last, as ever)
  deriving (Eq, Show)
