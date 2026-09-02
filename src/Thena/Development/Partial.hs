-- | The partial construction: a chain of components with a term at the end.
module Thena.Development.Partial
  ( Partial (..)
  , Constraint (..)
  , freeVarsPartial
  , Impure (..)
  , extract
  ) where

import Data.List (nub)

import Thena.Core.Context (Context, Entry (..))
import Thena.Core.Term (Core (..), Ident, Var, close, freeVars)
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
      Quantify _ _ ty   -> freeVars ty

    goConstraint (Equate xi s t ty) =
      concatMap goEntry xi ++ freeVars s ++ freeVars t ++ freeVars ty

    goEntry e = case e of
      Hypothesis _ _ ty   -> freeVars ty
      Definition _ _ v ty -> freeVars v ++ freeVars ty

-- --------------------------------------------------------------------------
-- Reading the term off a finished construction (§5.3, §7.5)
-- --------------------------------------------------------------------------

-- | What stopped a development from being pure.
--
-- Local to this module rather than in "Thena.Errors", whose header says it is
-- for types with producers on opposite sides of the layering. This one has a
-- single producer.
data Impure
  = StillAHole Var Ident        -- ^ a @?x : S@ with nothing tried
  | StillAGuess Var Ident       -- ^ a @?x ≐ g : S@ not yet solved
  | StillConstrained Constraint -- ^ an undischarged unification problem
  deriving (Eq, Show)

-- | The closed core term a finished construction stands for (§7.5, @Certify@).
--
-- A pure development is a telescope of binders with a term at the end, and
-- reading it off is the obvious fold — @assume@ becomes a λ and a local
-- definition becomes a @let@, which is exactly what thesis §2.3 says they are:
-- @solve@ turns @?x ≐ g : S@ into @x = g : S@, "the transition by which a hole
-- is solved, becoming a local definition".
--
-- @
-- extract (Trailing t)                = t
-- extract (Under (Assume x i S) p)    = Lam i S (close x (extract p))
-- extract (Under (Define x i v S) p)  = Let i v S (close x (extract p))
-- extract (Under (Quantify x i S) p)  = Pi  i S (close x (extract p))
-- @
--
-- The fourth line is the whole of what the fifth component adds (MS4 phase
-- 41f): a chain link that folds into a Π rather than a λ, so that a
-- development can /be/ a type as readily as it can be a term.
--
-- A 'Claim', a 'Guess' or a 'Pending' has no core counterpart and stops it —
-- that /is/ the purity check, and it is one traversal rather than a predicate
-- and a fold that could disagree about what pure means.
--
-- **The result need not be closed.** An @assume@ made outside the proof, or a
-- development still holding a free variable from somewhere else, comes back
-- with it. Saying so is 'Thena.Kernel.certify'\'s job, not this one\'s: this
-- function knows about developments and that one knows about scope.
extract :: Partial -> Either Impure Core
extract p = case p of
  Trailing t                    -> Right t
  Pending k _                   -> Left (StillConstrained k)
  Under (Claim x i _)     _     -> Left (StillAHole x i)
  Under (Guess x i _ _)   _     -> Left (StillAGuess x i)
  Under (Assume x i s)    rest  -> Lam i s . close x <$> extract rest
  Under (Define x i v s)  rest  -> Let i v s . close x <$> extract rest
  Under (Quantify x i s)  rest  -> Pi  i s   . close x <$> extract rest
