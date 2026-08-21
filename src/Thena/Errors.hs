-- | The failure vocabulary shared by the layers that produce failures.
--
-- This module exists because 'FailReason' has two producers on opposite sides
-- of the layering: an op in "Thena.Engine" (§7.2) and @unify@ in
-- "Thena.Core.Unify" (§6.2), which sits below @Engine@. Neither can own the
-- type, so it lives here, below both. Chosen by the user 2026-08-21,
-- @AGENDA.md@ item 18a; "Thena.Core.Typing"'s @TypeError@ (phase 8) and
-- "Thena.Kernel"'s @KernelError@ (phase 12) join it here.
--
-- It deliberately imports nothing. A reason that carried a 'Thena.Ops.Value'
-- would put the instruction language below @Core.Unify@, which is backwards —
-- so the operand-shape reasons say what was expected and nothing more. Nothing
-- is lost: 'Thena.Engine.Stuck' carries the whole machine (§7.5), whose @pc@
-- still begins with the instruction that failed and whose @env@ holds the
-- operand it read.
module Thena.Errors
  ( FailReason (..)
  , MoveError (..)
  ) where

-- | Why an operation failed. Structured, never a string (§12 invariant 2).
--
-- Phase 4's four cases are the ones the machine can currently produce. Phase 9
-- adds unification's — @Mismatch Core Core@, @OccursCheck@, @ScopeViolation@,
-- @UniverseMismatch@ (§6.2) — and that is when this module first imports
-- "Thena.Core.Term".
data FailReason
  = UnboundInBody String
    -- ^ a @Ref@ named nothing in the body's environment
  | NotAnIdentifier String
    -- ^ an answer to an @AName@ question that cannot be a name
  | ExpectedText
    -- ^ an operand was not a @VText@
  | ExpectedTerm
    -- ^ an operand was not a @VTerm@ holding a core term
  | CannotMove MoveError
    -- ^ a navigation op asked for a move the focus does not have (§4.0 C4)
  deriving (Eq, Show)

-- | Why a move was impossible (§4.0 C4, §12 invariant 2).
--
-- Payload-free, and here rather than in "Thena.Development.Cursor", for this
-- module's own reason: it imports nothing, and 'FailReason' has to carry it.
-- Nothing is lost by the missing payload — 'Thena.Engine.Stuck' carries the
-- whole machine, whose @pc@ still begins with the navigation instruction that
-- failed, and that instruction names the part it asked for.
data MoveError
  = AtRoot
    -- ^ @back@ at the root: there is no step left to pop
  | NotOnTheSpine
    -- ^ a partial-fragment move, attempted in the core fragment
  | NotInCore
    -- ^ a core-term descent, attempted on the spine
  | NotAGuess
    -- ^ @into@, on something that is not a guess
  | NotADefinition
    -- ^ @cross val@, on a component that has no value
  | NoCrossingIntoAConstraint
    -- ^ crossing into a constraint. Not a gap: decided against (§4.2)
  | NoSuchPart
    -- ^ a descent naming a field the focused form does not have
  deriving (Eq, Show)
