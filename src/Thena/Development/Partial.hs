-- | The partial construction: a chain of components with a term at the end.
module Thena.Development.Partial
  ( Partial (..)
  , Constraint (..)
  , freeVarsPartial
  ) where

import Data.List (nub)

import Thena.Core.Context (Context, Entry (..))
import Thena.Core.Term (Core, Var, freeVars)
import Thena.Development.Component (Component (..))

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

-- | Every 'Var' the whole development mentions, structurally — every
-- component's type, a 'Define'\'s value, a 'Guess'\'s body (recursively) and
-- its own type, a 'Constraint'\'s Ξ and its three terms, and the trailing
-- term.
--
-- What "Thena.Development.Cursor"\'s committing reduction needs to answer
-- §4.7's orphaning question: after a reduction discards a variable from the
-- one subterm it touched, does that variable still occur ANYWHERE in the
-- rest of the development? A local check (just the reduced subterm) would
-- miss a hole referenced twice, only one of which was under the focus.
freeVarsPartial :: Partial -> [Var]
freeVarsPartial = nub . go
  where
    go p = case p of
      Trailing t     -> freeVars t
      Pending k rest -> goConstraint k ++ go rest
      Under c rest   -> goComponent c ++ go rest

    goComponent c = case c of
      Assume _ _ ty     -> freeVars ty
      Define _ _ v ty   -> freeVars v ++ freeVars ty
      Claim  _ _ ty     -> freeVars ty
      Guess  _ _ g ty   -> go g ++ freeVars ty

    goConstraint (Equate xi s t ty) =
      concatMap goEntry xi ++ freeVars s ++ freeVars t ++ freeVars ty

    goEntry e = case e of
      Hypothesis _ _ ty   -> freeVars ty
      Definition _ _ v ty -> freeVars v ++ freeVars ty
