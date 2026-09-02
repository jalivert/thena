-- | The failure vocabulary shared by the layers that produce failures.
--
-- This module exists because 'FailReason' has two producers on opposite sides
-- of the layering: an op in "Thena.Engine" (§7.2) and @unify@ in
-- "Thena.Core.Unify" (§6.2), which sits below @Engine@. Neither can own the
-- type, so it lives here, below both. Chosen by the user 2026-08-21,
-- @AGENDA.md@ item 18a; "Thena.Core.Typing"'s @TypeError@ (phase 8) and
-- "Thena.Kernel"'s @KernelError@ (phase 12) join it here.
--
-- It imports "Thena.Core.Term" and "Thena.Core.Context" — **first at phase 8**,
-- one phase earlier than the note below predicted, because 'TypeError' carries
-- terms before unification's reasons do — and, from phase 17b, the two leaves of
-- the syntax branch. What it still may
-- not import is anything above @Core@: a reason that carried a
-- 'Thena.Ops.Value' would put the instruction language below @Core.Unify@,
-- which is backwards, so the operand-shape reasons say what was expected and
-- nothing more. Nothing is lost: 'Thena.Engine.Stuck' carries the whole machine
-- (§7.5), whose @pc@ still begins with the instruction that failed and whose
-- @env@ holds the operand it read.
--
-- **'SyntaxError' moved down here at phase 17b, and with it 'ResolveError'.**
-- The @parse@ and @resolve@ ops (§7.2) fail the way every other op does, so
-- their reasons have to be cases of 'FailReason', and 'FailReason' lives here.
-- The rule above is untouched: "Thena.Syntax.Lexer" and "Thena.Syntax.Parser"
-- are not /above/ @Core@ but /beside/ it — between them they import one module,
-- "Thena.Syntax.Concrete", which imports nothing — so this module still sees
-- nothing of @Ops@, @Development@ or @Global@. 'ResolveError' comes the whole
-- way down rather than being imported, because "Thena.Syntax.Resolve" /is/
-- above @Core@; it mentions nothing this module did not already have.
module Thena.Errors
  ( DataBuildError (..)
  , FailReason (..)
  , MoveError (..)

    -- * Conversion (§5.2)
  , ConversionFailure (..)
  , Site (..)
  , Clash (..)

    -- * Typing (§5.2, §7.4)
  , TypeError (..)

    -- * The kernel (§5.3)
  , KernelError (..)
  , Position (..)

    -- * The elimination tactic (§3.7)
  , ElimError (..)

    -- * Reading a term (§2.5, §2.6) — moved here at phase 17b
  , SyntaxError (..)
  , ResolveError (..)
  , DevForm (..)
  ) where

import Thena.Core.Level (Level, Unmet)
import Thena.Core.Context (Context)
import Thena.Core.Term (Core, GlobalName, Ident, Var)
import Thena.Syntax.Lexer (LexError)
import Thena.Surface.Concrete (PairingError (..))
import Thena.Surface.Layout (LayoutError (..))
import Thena.Surface.Parser (SurfaceParseError (..))
import Thena.Syntax.Parser (ParseError)

-- | Why an operation failed. Structured, never a string (§12 invariant 2).
--
-- Phase 4's four cases are the ones the machine can currently produce. Phase 9
-- adds unification's — @Mismatch Core Core@, @OccursCheck@, @ScopeViolation@,
-- @UniverseMismatch@ (§6.2) — and that is when this module first imports
-- "Thena.Core.Term".
-- | Why an elaborated declaration is not one.
--
-- Small on purpose: everything a /user/ can get wrong about a datatype is
-- 'DeclareError'\'s, checked by 'declare' on the finished record. These three
-- are about the record not being buildable at all, which the surface form's
-- own shape should already have ruled out.
data DataBuildError
  = DeclaredTypeIsNotAUniverse GlobalName
    -- ^ the type ends in something that is not a sort
  | ConstructorTargetWrong GlobalName
    -- ^ its target is not this datatype applied to its parameters
  | TooFewBinders
    -- ^ fewer Π binders than the surface form said there were parameters
  deriving (Eq, Show)

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

    -- Unification's four (§6.2), added at phase 9.
  | Mismatch Context Core Core
    -- ^ two whnfs that cannot be made equal, in the context they live in
  | OccursCheck Context Var Core
    -- ^ solving this hole with this term would define it in terms of itself
  | ScopeViolation Context Var Var
    -- ^ the solution for this hole mentions this variable, which is not bound
    -- before it. Reported rather than repaired: repairing it means moving a
    -- declaration leftwards — Gundry\'s @DEPEND_S@, OLEG\'s @raise@ — which
    -- changes the shape of the user\'s development and is a tactic\'s decision,
    -- not a unifier\'s. @raise@ is one of table 2.8\'s ops and is deliberately
    -- not in MS1\'s vocabulary yet (§7.2)
  | UniverseMismatch Level Level
    -- ^ two universes, and no cumulativity to relate them (§5.2)
    -- The life of a hole (tables 2.7, 2.8), phase 13.
  | NotAHole
    -- ^ @attack@ or @try@ where the focus is not a @?x : S@
  | NotAGuessHere
    -- ^ @solve@ or @regret@ where the focus is not a @?x ≐ g : S@
  | NotReadyToIntroduce
    -- ^ @intro@ on anything but table 2.8's shape @?x ≐ (?x' : S . x') : …@.
    -- The shape test is the specification, not a shortcut: a hole not of that
    -- form is made ready by @attack@
  | WrongNumberOfEliminationFields GlobalName Int Int
    -- ^ @make-elim@ was handed a number of names that is not the number of
    -- fields an elimination of that datatype has (MS4 phase 41i): parameters,
    -- the motive, one method per constructor, the indices, the target.
    --
    -- Its own reason rather than one of "Thena.Errors"\'s
    -- @WrongNumberOfElimination…@ resolve errors, because those are about what
    -- a /user wrote/ in one field group and this is about the total a rule
    -- body handed an op.
  | CannotBuildDatatype DataBuildError
    -- ^ the elaborated types do not make a datatype record (MS4 phase 42b).
    -- Everything a /user/ can get wrong is checked by @declare@ on the
    -- finished record; this is about it not being buildable at all.
  | NoEnclosingDevelopment
    -- ^ @pop-development@ at the outermost one (MS4 phase 42). There is
    -- nothing to pop back to, and a machine with no development at all is not
    -- a state this language has.
  | GoalIsNotAUniverse
    -- ^ @quantify@ at a hole whose type is not a universe (MS4 phase 41f).
    -- A ∀-binder builds a Π and a Π is a type, so there is nothing for one to
    -- be part of unless the hole is claimed at a sort. The @∀@ counterpart of
    -- 'NothingToIntroduce'
  | NothingToIntroduce
    -- ^ @intro@ on the right shape, but the hole's type is neither a Π nor a
    -- @let@ once whnf'd
  | NotYetPure Position
    -- ^ @Certify@ on a development that still has a hole, a guess or an
    -- undischarged constraint in it (§5.3). The 'Position' names the first one
    -- — @certify@ before anything is proved is the normal way to meet this, so
    -- it says which component rather than only that one exists
  | NoGoalHere
    -- ^ @goal@ where nothing is written down (§4.5, phase 24). The top of a
    -- development claims nothing, so it has no goal to read
  | NoRuleMatched
    -- ^ @prove@ found no rule whose head passes at the focus (§7.3). It says
    -- only that, and no more: the focus is what it is about, and 'Stuck'
    -- carries the whole machine, so @:where@ still says where (§7.5).
    --
    -- **This is the definite case, not §8.1's suspension.** The focus's shape
    -- is known, so "no rule will ever match" is the answer. Blocked-on-a-hole
    -- is a different outcome and a later milestone (§12 invariant 2).
  | GuessIllTyped TypeError
    -- ^ @try@ handed a term that does not have the hole's type (phase 25b).
    -- Thesis table 2.7 gives @try@ the side condition @Θ ⊩ t : S@, and until
    -- this phase it was documented and not enforced: the guess went in and the
    -- kernel caught it at @qed@, one command or a hundred later.
    --
    -- **Distinct from 'NotTypeable'**, which is "this term has no type at
    -- all". Here it has one; it is not the one written down.
  | BinderNotAType TypeError
    -- ^ @assume@ or @claim@ was handed something that is not a type (phase
    -- 25f). Thesis table 2.7 gives both the side condition @Θ ⊢ S : Type@, and
    -- until this phase it was documented and not enforced — @claim h : zero@
    -- went in and the kernel caught it at @qed@.
    --
    -- **The exact analogue of 'GuessIllTyped'**, which phase 25b added for
    -- @try@'s side condition in the same table. The check is
    -- 'Thena.Core.Typing.sortOf', which is what @revalidate@ has always run on
    -- these two components via @Validate@'s @isAType@ — so the op and the
    -- kernel cannot come to disagree about what a type is.
    --
    -- **The level is discarded**, because the condition is "S is a type", not
    -- "S is a type at level ℓ". That is what makes this survive the universe
    -- work unchanged: @Universe ?ℓ@ answers it as well as @Universe 0@ does.
  | NotTypeable TypeError
    -- ^ an op was handed a term with no type. @unify@ needs one: a deferred
    -- equation records the type it was asked at (§3.3), so the op infers it
    -- from the left-hand side and this is what happens when it cannot
  | CannotEliminate ElimError
    -- ^ the elimination tactic could not build a scheme for the target it was
    -- given (§3.7, phase 17)

    -- Elaboration and @Call@ (§7.2, §8), added at phase 17b.
  | NoElaborationRule String
    -- ^ @prim-elaborate@ met a surface node it has no case for (MS4 phase 41),
    -- carrying what the node was.
    --
    -- **A failure and not a silence, deliberately.** Phase 41 compiles the
    -- leaves; the nodes that raise this are phase 41b's list, and each of them
    -- needs something the op vocabulary does not yet have. An elaborator that
    -- quietly did nothing here would leave a hole that looked elaborated.
  | CannotRead SyntaxError
    -- ^ @parse@ could not lex or parse its text, or @resolve@ could not resolve
    -- the tree it was given in the context at the focus. One case for both,
    -- because they are two halves of one pipeline and 'SyntaxError' already
    -- bundles exactly these three failures for the driver's own @parseCore@ —
    -- so "Thena.Repl" renders an op\'s failure with the renderer it already has
  | ExpectedSurface
    -- ^ an operand was not a 'Thena.Ops.VSurface'. Shaped like 'ExpectedText'
    -- and 'ExpectedTerm', and here for their reason: the value itself may not
    -- be named below @Core@
  | NoClauseMatched GlobalName Int [Int]
    -- ^ @call ‹name› ‹args›@ found nothing to run: the name, the number of
    -- arguments it was given, and the arities of the rules that do bear that
    -- name. **One reason for three mistakes**, told apart by the renderer —
    -- no rule of that name at all (the list is empty), no clause of that
    -- arity (the count is not in the list), or clauses of the right arity
    -- whose heads all failed. Phase 23; @ExpectedRule@ and
    -- @WrongNumberOfArguments@ were its two predecessors and are gone, because
    -- a call no longer takes a rule /value/ and arity is a filter rather than
    -- an error.
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
  | StillReferenced
    -- ^ @abandon@ on a hole something below it still mentions — table 2.7's
    -- @x ∉ Θ'@ (phase 13)
  | NoCrossingIntoAConstraint
    -- ^ crossing into a constraint. Not a gap: decided against (§4.2)
  | NoSuchHole
    -- ^ @goto@ naming something that is no hole or guess — either nothing
    -- binds the variable, or what binds it is an assumption or a definition
    -- (phase 24b). One case for both: the operand is a term, so "not in
    -- scope" has already been answered by resolution before this is reached
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
  | WrongNumberOfLevelArguments GlobalName Int Int
    -- ^ definition, level parameters it has, level arguments the use wrote
    -- (MS3 phase 30). A definition's level parameters are prenex: a use writes
    -- every one of them or the term is not well formed. There is no partial
    -- instantiation, and — until something infers them — no way to leave them
    -- out either
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

-- --------------------------------------------------------------------------
-- The kernel (§5.3)
-- --------------------------------------------------------------------------

-- | Why the kernel refused a term, or why a development is not a valid state.
--
-- **One type for both checks**, though §5.3 keeps @certify@ and @revalidate@
-- carefully apart: they disagree about their /input/ and their /layer/, not
-- about what going wrong looks like. Both bottom out in "this term does not
-- typecheck, here", and a second type would be the same three cases under
-- other names.
--
-- 'NotClosed' is 'certify'\'s alone — @revalidate@ walks a development whose
-- components bind the variables, so a free one there is in Γ by construction.
data KernelError
  = NotClosed Var
    -- ^ @certify@: the term mentions a variable nothing binds. §5.3\'s
    -- signature has no context, so this is the check that earns that
  | Levels Unmet
    -- ^ a level relation that no instantiation could satisfy (phase 33).
    -- Produced by @revalidate@ and by @certify@, both of which run
    -- 'Thena.Core.Level.solveLevels' over what their walk owed.
    --
    -- **There is no constructor for an /undecided/ level, and phase 33b
    -- deleted the one there was.** A relation that is neither valid nor false
    -- is the residue, which generalisation stores on the definition — see
    -- 'Thena.Global.Env.definitionConstraints'. Only a refutation is an error
  | Overabstracted Var Ident Core
    -- ^ a construction assumes something the type it is claimed to build has
    -- no binder for: @? g ≐ (λ a : A . …) : Nat@. Its own case rather than an
    -- 'Ill', because no 'TypeError' says this — @infer@ never meets the
    -- question, since only a /construction/ can abstract more than its type
  | NotAUniverseAbove Var Ident Core
    -- ^ a construction quantifies where the type it is claimed to build is not
    -- a universe: @? g ≐ (∀ a : A . …) : Nat@ (MS4 phase 41f). The @∀@
    -- counterpart of 'Overabstracted', and its own case for the same reason —
    -- @infer@ never meets the question, because only a /construction/ can put
    -- a binder above a type that has no room for one
  | Ill Position TypeError
    -- ^ it does not typecheck, and where. The 'TypeError' is the ordinary one
    -- "Thena.Core.Typing" produces — the kernel shares the core\'s typechecker
    -- (§5.3, decided 2026-08-22), so it shares the core\'s reasons too
  deriving (Eq, Show)

-- | Where in a development something failed to check.
--
-- Named after what the user wrote rather than after the constructor, because
-- this is what a message says out loud: "the type of @h@", not "the @Claim@\'s
-- third field". A 'Var' as well as an 'Ident', because two components may show
-- the same identifier and only the variable says which (§3.5).
data Position
  = TheTerm
    -- ^ @certify@\'s whole closed term, or a development\'s trailing term
  | TheHole Var Ident       -- ^ this hole has nothing in it yet
  | TypeOf Var Ident        -- ^ a component\'s stated type is not a type
  | ValueOf Var Ident       -- ^ a definition\'s value does not have its type
  | GuessOf Var Ident       -- ^ a guess\'s construction does not build its type
  | ConstraintAt Int        -- ^ the nth constraint in the chain, counting from 1
  | Inside Var Ident Position
    -- ^ under a guess: a guess\'s body is a development in its own right, so
    -- its failures nest rather than flatten
  deriving (Eq, Show)

-- | Why @eliminate@ could not build its scheme (§3.7, phase 17).
--
-- Every case is a refusal the /user/ can meet by picking a different target,
-- except 'SchemeIllTyped', which is the tactic being wrong about its own
-- construction — kept as a refusal rather than a crash, exactly as
-- 'Thena.Global.Declare.NoConfusionRejected' is.
data ElimError
  = TargetNotTypeable TypeError
    -- ^ the term fingered as the target has no type at all
  | TargetNotInductive Context Core Core
    -- ^ its type does not whnf to a saturated application of a declared
    -- inductive family. Carries the context, the target, and the type it
    -- actually had — the context because the target is usually a variable and
    -- a message that calls it @\8249Var 107\8250@ is no message
  | NoEquality GlobalName
    -- ^ eliminating at indices needs @Eq@ and @refl@ /by name/ (§3.7, decided
    -- 2026-08-11), and the named one is not declared. Only ever raised for a
    -- family that has indices: without them the scheme states no equations
  | IndexTypeDepends Int Ident
    -- ^ §3.7's stated limit, and it binds a /tied/ index only. The type of
    -- index @n@ (counting from 1, named) mentions an earlier index, so the
    -- homogeneous @Eq I i a@ that constrains it cannot be written down: @i@ is
    -- at the generalised index and @a@ at the actual one, which are two
    -- different types. A /friendly/ index states no equation, so it is
    -- abstracted and this is not raised for it (phase 19).
    --
    -- Not @Vec@: a one-element index telescope has no earlier index to depend
    -- on, so @Vec@ and @Fin@ eliminate fine. The shape is
    -- @Below : ∀ (n : Nat) (i : Fin n) -> Type₀@, two indices with the second
    -- typed by the first. @AGENDA.md@ item 10
  | IndexTypeIllTyped TypeError
    -- ^ a tied index's type has no universe (MS3 phase 31d). Needed because
    -- the equation @Eq Iₖ iₖ aₖ@ is stated at @Iₖ@'s **level** now, which has
    -- to be read
  | MotiveIllTyped TypeError
    -- ^ the generalised goal does not typecheck under the abstracted indices.
    -- Abstracting a term in a dependent theory is not always type-preserving,
    -- and thesis §3.5.3 says so; MS1 reports it rather than falling back
  | SchemeIllTyped TypeError
    -- ^ the assembled elimination does not have the goal's type. Unreachable if
    -- the motive typechecked and the generated eliminator type is right
  deriving (Eq, Show)

-- --------------------------------------------------------------------------
-- Reading a term (§2.5, §2.6)
-- --------------------------------------------------------------------------

-- | The three ways reading a term or development can fail.
--
-- It lived in "Thena.Driver" until phase 17b, where the @parse@ and @resolve@
-- ops made it something 'FailReason' has to carry. The driver still uses it for
-- a command line it could not read; nothing about that changed but the import.
data SyntaxError
  = LexFailed LexError
  | ParseFailed ParseError
  | LayoutFailed LayoutError
    -- ^ the offside rule could not lay the surface program out (MS4 phase 40)
  | SurfaceParseFailed SurfaceParseError
  | DeclarationsUnpaired PairingError
    -- ^ a surface signature with no equation after it, or the other way round
    -- (MS4 phase 42). A syntax error rather than a scope one: the declarations
    -- parsed, they just do not make a module.
    -- ^ the **surface** grammar refused it (MS4 phase 39). Its own case beside
    -- 'ParseFailed', because the two grammars are separate and an error from
    -- one must not be reported as the other's.
    --
    -- There is deliberately no @SurfaceResolveFailed@: a surface term is never
    -- resolved. Turning one into a 'Thena.Core.Term.Core' is elaboration, and
    -- elaboration fails through the machine.
  | ResolveFailed ResolveError
  deriving (Eq, Show)

-- | Why a named tree could not be turned into 'Core' (§2.5, §3.5).
--
-- Moved here from "Thena.Syntax.Resolve" at phase 17b, with 'DevForm'. It could
-- not be imported from there — @Resolve@ is above @Core@ — and it needs nothing
-- that module has: every case is a 'String', an 'Int' or an 'Ident'.
data ResolveError
  = NotInScope String
  | NotACoreTerm DevForm
    -- ^ a development-only form written where a term goes
  | NotAUniverse String
    -- ^ the datatype's declared type does not end in @Type_l@
  | TargetIsNotTheDatatype String
    -- ^ this constructor's result type is not the family being declared
  | TargetArgumentCount String Int Int
    -- ^ constructor, arguments its target should have, arguments it has
  | ParameterNotPassedThrough String Ident
    -- ^ a constructor's target changed a parameter; parameters are fixed (§3.7)
  | NotADatatype String
    -- ^ an @elim@ naming something that is not a declared inductive (phase 7)
  | WrongNumberOfEliminationParameters String Int Int
    -- ^ datatype, parameters it has, parameters the @elim@ wrote
  | WrongNumberOfMethods String Int Int
    -- ^ datatype, constructors it has, methods the @elim@ wrote
  | WrongNumberOfEliminationIndices String Int Int
    -- ^ datatype, indices it has, indices the @elim@ wrote
  | LevelArgumentsOnALocal String
    -- ^ level arguments written on a name bound by a λ or by the development.
    -- Only a definition has level parameters, so only a global can be given
    -- level arguments.
    --
    -- **This one survived phase 33c** and its two neighbours did not.
    -- @LevelNotInScope@ named a level /variable/ nobody can write any more, and
    -- @LevelNotWritten@ refused a declaration that now infers its own level;
    -- @foo {0}@ on a λ-bound name is still perfectly writable and still wrong
  deriving (Eq, Show)

-- | Which development-only form was met in a core position. An enum rather
-- than a message, per §12 invariant 2 — "Thena.Repl" turns it into English.
data DevForm = AHole | AGuess | AConstraint
  deriving (Eq, Show)
