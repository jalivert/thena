-- | The failure vocabulary shared by the layers that produce failures.
--
-- This module exists because 'FailReason' has two producers on opposite sides
-- of the layering: an op in "Thena.Engine" (§7.2) and @unify@ in
-- "Thena.Core.Unify" (§6.2), which sits below @Engine@. Neither can own the
-- type, so it lives here, below both. Chosen by the user 2026-08-21,
-- @AGENDA.md@ item 18a; "Thena.Core.Typing"'s @TypeError@ (phase 8) and
-- "Thena.Kernel"'s @KernelError@ (phase 12) join it here.
--
-- It imports "Thena.Core.Term" and "Thena.Core.Context" and nothing else —
-- **first at phase 8**, one phase earlier than the note below predicted, because
-- 'TypeError' carries terms before unification's reasons do. What it still may
-- not import is anything above @Core@: a reason that carried a
-- 'Thena.Ops.Value' would put the instruction language below @Core.Unify@,
-- which is backwards, so the operand-shape reasons say what was expected and
-- nothing more. Nothing is lost: 'Thena.Engine.Stuck' carries the whole machine
-- (§7.5), whose @pc@ still begins with the instruction that failed and whose
-- @env@ holds the operand it read.
module Thena.Errors
  ( FailReason (..)
  , MoveError (..)

    -- * Conversion (§5.2)
  , ConversionFailure (..)
  , Site (..)
  , Clash (..)

    -- * Typing (§5.2, §7.4)
  , TypeError (..)
  ) where

import Thena.Core.Context (Context)
import Thena.Core.Term (Core, GlobalName, Ident, Level, Var)

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

-- --------------------------------------------------------------------------
-- Conversion
-- --------------------------------------------------------------------------

-- | Why two terms are not convertible (§5.2: "a structured reason, not
-- @Bool@").
--
-- Two parts, because a clash three binders down is unreadable without saying
-- where it is: 'conversionSite' is the route from the two terms conversion was
-- originally asked about to the two subterms that actually clashed, outermost
-- first, and 'conversionClash' is what went wrong when it got there.
--
-- **There is deliberately no matching /positive/ reason.** §5.2 observes that
-- with η the prover will call @f@ and @λx. f x@ equal while displaying two
-- different terms, and wants the explanation able to say "by η". Nothing in
-- MS1 consumes such a justification — @:convert@ prints a yes or a why-not, and
-- @infer@ discards a success — so recording one now would be a field written
-- and never read (§12 invariant 5). The shape here does not foreclose it: a
-- @Convertible Justification@ case is an additive change to conversion's
-- result type, not to this one.
data ConversionFailure = ConversionFailure
  { conversionSite  :: [Site]   -- ^ outermost first; empty means "at the top"
  , conversionClash :: Clash
  }
  deriving (Eq, Show)

-- | One step of the route to a clash. Named per /form/, not per constructor
-- index, so a message reads @in the domain of \x@ rather than @in field 2@.
data Site
  = TheDomain Ident            -- ^ the domain of a Π or a λ
  | TheBody Ident              -- ^ under the binder, which is named
  | TheFunction                -- ^ the left of an application
  | TheArgument                -- ^ the right of an application
  | TheArgumentOf GlobalName Int  -- ^ the nth argument of a saturated former
  | TheParameter Int           -- ^ an @Eliminate@\'s nth parameter
  | TheMotive
  | TheMethod Int
  | TheIndex Int
  | TheTarget
  deriving (Eq, Show)

-- | What actually differs, once the site is reached.
--
-- 'HeadsDiffer' carries the 'Context' the two terms live in, which is not
-- decoration: by the time conversion has opened three binders the terms mention
-- variables the caller\'s context has never heard of, and a printer without them
-- can only fall back to @‹Var 7›@.
data Clash
  = HeadsDiffer Context Core Core  -- ^ two whnfs whose heads cannot be made to agree
  | LevelsDiffer Level Level
  | NamesDiffer GlobalName GlobalName
  | VariablesDiffer Var Var
  | CountsDiffer Int Int           -- ^ two argument lists of different length
  deriving (Eq, Show)

-- --------------------------------------------------------------------------
-- Typing
-- --------------------------------------------------------------------------

-- | Why a term has no type, or not the stated one (§5.2, §12 invariant 2).
--
-- Every case that carries a 'Core' carries the 'Context' it is written in, for
-- 'HeadsDiffer'\'s reason.
--
-- **@check@ contributes exactly one case**, 'NotOfType'. That is what
-- @infer@-only checking means (decided by the user 2026-08-22): @check@ is
-- @infer@ followed by @convert@, so the only way it can fail on its own is the
-- conversion, and it hands that reason straight through.
data TypeError
  = UnknownVariable Context Var
    -- ^ a 'Thena.Core.Term.Free' naming no entry of the context
  | UnknownGlobal GlobalName
    -- ^ a 'Thena.Core.Term.Global' in neither the definitions nor the constants
  | LooseIndex Int
    -- ^ a 'Thena.Core.Term.Bound' at the top of a term. Unconstructible through
    -- 'Thena.Core.Term.close', so this reports a caller that built one by hand
  | NotAType Context Core Core
    -- ^ this term, whose inferred type is this, is not a universe
  | NotAFunction Context Core Core
    -- ^ this term, whose inferred type is this, cannot be applied
  | NotOfType Context Core Core Core ConversionFailure
    -- ^ this term has this inferred type, but this was expected — and why they
    -- differ
  | UnknownDatatype GlobalName
    -- ^ an @Eliminate@ whose 'Thena.Core.Term.eliminated' names no inductive
  | NotAMotive Context Core Core
    -- ^ an @Eliminate@\'s motive, whose inferred type does not end in a universe
    -- after the family\'s indices and target are peeled off
  | Unsaturated GlobalName Core
    -- ^ a 'Thena.Core.Term.Canonical' or an @Eliminate@ given too few
    -- arguments, and the type left over. §12 invariant 6 says both are
    -- saturated by construction, so this reports a caller that built one by
    -- hand — the resolver cannot produce it
  | OverApplied GlobalName
    -- ^ the same, given too many
  deriving (Eq, Show)
