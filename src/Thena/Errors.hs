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
-- 'Thena.Instral.Ops.Value' would put the instruction language below @Core.Unify@,
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
  , BuildError (..)
  , Warning (..)
  , Skipped (..)
  , FailReason (..)
  , ObjectError (..)
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
  , SpecialiseError (..)
  , ChainBlocker (..)
  , RecursionError (..)

    -- * Reading a term (§2.5, §2.6) — moved here at phase 17b
  , SyntaxError (..)
  , ResolveError (..)
  , DevForm (..)
  ) where

import Thena.Core.Level (Level, Unmet)
import Thena.Core.Context (Context)
import Thena.Core.Term (Core, GlobalName, Ident, Var)
import Thena.Instral.Pattern (Pattern)
import Thena.Syntax.Lexer (BlockKind, LexError)
import Thena.Language.Earley (ParseFailure)
import Thena.Language.Reader (ReadError)
import Thena.Surface.Concrete (PairingError (..))
import Thena.Surface.Layout (LayoutError (..))
import Thena.Surface.Parser (SurfaceParseError (..))
import Thena.Syntax.Parser (ParseError)

-- | Something worth telling the user about a load that nonetheless succeeded
-- (MS6 phase 98).
--
-- **A warning never changes what is installed**, which is the whole of what
-- separates it from a 'DeclareError': an error abandons the declaration, a
-- warning is a remark about one that went in. Structured, like every other
-- diagnostic (@PLAN.md@ §12), so the renderer decides the words and a test can
-- ask which warning it was rather than grep a sentence.
--
-- **Here since MS6 phase 101**, when §4.5's grammar warnings arrived: phase 98
-- put it in "Thena.Global.Declare" only because 'Skipped' and 'ElimError' both
-- had a @NoEquality@, and a grammar warning should not import a declaration
-- module to raise one.
data Warning
  -- **@NoConfusionSkipped@ was removed at MS9 phase 212**, with the only
  -- 'Skipped' that was ever about the declaration the user wrote. A datatype no
  -- longer goes in without its no-confusion equipment on account of its own
  -- shape, and the two environment cases left were silent already, so nothing
  -- could produce this.
  = VacuousBinder BlockKind String String String
    -- ^ the block, the production, and a binder declared @as binders@ that no
    -- @[…]@ mentions (@ms6\/SPEC.md@ §4.5, MS6 phase 101). A vacuous binder is
    -- allowed — that is why it can be declared — and worth saying.
  | UnprimeableClass BlockKind String String
    -- ^ the block, the language's name, and its identifier class's name — a class no
    -- single character extends, so a generated @L-fresh@ cannot rename a
    -- captured binder to a name the language can write back (MS6 closeout 23,
    -- phase 146). **It is a warning and not a refusal**: the language works, its
    -- substitution is correct, and only printing a renamed binder is lost — so
    -- the author is told rather than prevented.
  deriving (Eq, Show)


-- | Why a reading of an object term is not a term (MS6 phases 103 and 104).
--
-- **Here rather than in "Thena.Language.Build", for the reason 'Warning' is
-- here** (phase 101): a 'Failure' carries one, and "Thena.Language.Build"
-- reaches this module through "Thena.Language.Grammar", so the type has to sit
-- below both.
data BuildError
  = NoSuchProduction String
    -- ^ a reading of a production no installed grammar has
  | Incomplete String
    -- ^ **a placeholder, and the slot it stands in**: a constructor cannot have
    -- a missing argument (§7.6).
    --
    -- **Never \"a hole\" — HIS RULING, 2026-09-27**, and this comment said so
    -- until MS7 phase 127. A DC hole is saved and solved; a placeholder is a
    -- part of a term nobody has written yet.
  | NotForSlot String String
    -- ^ the production, and a slot whose reading is not what it takes
  deriving (Eq, Show)

-- | Why a datatype gets no no-confusion. Structured, per §12 invariant 2.
--
-- **Moved here from "Thena.Global.NoConfusion" at MS6 phase 101**, with
-- 'Warning', which carries it. Its first constructor was @NoEquality@ and was
-- renamed 'NoEqInScope': 'ElimError' has a @NoEquality@ of its own, older (MS1)
-- and naming the missing global, so this is the one whose name said less.
--
-- The three are ordered by how much they are about the /user's/ declaration.
-- 'NoEqInScope' is about the environment and is reported to nobody (see
-- 'generateNoConfusion'); the other two are properties of what was just
-- written, and "Thena.Driver" says them.
data Skipped
  = NoEqInScope
    -- ^ no well-shaped @Eq@ is in scope, so no equation can be stated. Arises
    -- only before the prelude is loaded — @repl@ loads it at startup — which is
    -- why it is silent.
  | NoProducts
    -- ^ a prelude type this datatype's own table would be written out of —
    -- @DPair@, @Unit@ or @Empty@ — is missing or misshapen. Silent for
    -- 'NoEqInScope'\'s reason and arising in the same situation, a prelude-free
    -- script, which is why the two are tested together.
    --
    -- **Asked per datatype, not once**, and that is load-bearing rather than
    -- fastidious: the prelude declares @Eq@ before @DPair@, so a blanket
    -- precondition would refuse @NoConfusionEq@ — which phase 14 generated —
    -- for a name it was never going to write. See 'productsInScope'.
  -- **A third case, @DependentArguments@, was removed at MS9 phase 212.** A
  -- constructor whose argument telescope is dependent used to be declined — it
  -- wanted @Eq (Vec A n) as as'@ where @as' : Vec A n'@ — and that is now the
  -- transported chain of equations @Thena.Global.NoConfusion.telescopic@
  -- states, so nothing is declined for it and no datatype is without a
  -- no-confusion lemma on account of its telescope.
  deriving (Eq, Show)

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
  | NothingReturned Pattern
    -- ^ @x = ‹rule›@ where the clause that ran reached the end of its body
    -- without a @return@ (MS5 phase 63). Carries the destination.
    --
    -- **It fails where the value was wanted**, rather than leaving @x@ unbound
    -- for a later @Ref@ to trip over, because the two are different mistakes
    -- and the second one reports the wrong line. Whether a call produces cannot
    -- be checked when the body is read — a name's clauses are not known then
    -- (phase 23) — so this is the run-time half of 'Thena.Instral.Ops.produces'.
  | NothingToReturnFrom
    -- ^ @return@ with no call to return from — typed at the REPL, or in a
    -- top-level @do@ block (MS5 phase 63).
  | NotAnIdentifier String
  | BlockOperands Int String
    -- ^ the instruction at this position in a @do@ block gave this op word the
    -- wrong operands (MS4 phase 45).
    --
    -- **Structured rather than a rendered rule error**, because
    -- @Thena.Rules.RuleError@ is above this module in the layering (§2.5) and a
    -- @String@ here would be the thing §12 forbids. It costs nothing to say it
    -- this way: resolving a block can fail in exactly one way — an op word given
    -- operands it does not take — since a word that names no op is a rule call
    -- and not an error (phase 25e).
    -- ^ an answer to an @AName@ question that cannot be a name
  | ExpectedText
    -- ^ an operand was not a @VText@
  | ExpectedRaw
    -- ^ an op wanting an unresolved core term — a @core@ region — got something
    -- else (MS5 phase 61b).
  | CannotResolve ResolveError
    -- ^ a @core@ region parsed but does not resolve where it was used: a name it
    -- mentions is not in scope at this focus, or is not a global (MS5 phase
    -- 61b). It is reported here rather than at load because it cannot be known
    -- until there is a development to resolve against.
  | ExpectedTerm
    -- ^ an operand was not a @VTerm@
  | ExpectedList
    -- ^ an operand was not a @VList@ (MS5 phase 65)
  | ExpectedPair
    -- ^ an operand was not a @VPair@ (MS5 phase 65)
  | ExpectedOption
  | ExpectedLevel
    -- ^ an op wanted a 'Thena.Instral.Type.TLevel' and was given something else
    -- (MS5 phase 89)
  | ExpectedInt
    -- ^ …and one wanted an 'Thena.Instral.Type.TInt'. @level ‹n›@ is the only
    -- op that does, and a NEGATIVE numeral reaches it too — there is no
    -- negative level, and the numeral token cannot carry a sign, so this is the
    -- refusal for a value computed rather than written
    -- ^ an operand was not a @VOption@ (MS5 phase 65)
  | NothingThere
    -- ^ @option-value none@ (MS5 phase 65). **A rule asks first** — the head
    -- test @option-is-some@ is how, and it is the same shape as every other
    -- question about a value here.
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
    -- ^ two universes that cumulativity does not relate (§5.2) — either they
    -- were compared at 'Thena.Core.Convert.Same', where subsumption does not
    -- apply at all, or at 'Thena.Core.Convert.Cumulative' the wrong way round
    -- The life of a hole (tables 2.7, 2.8), phase 13.
  | NotAHole
    -- ^ @attack@ or @try@ where the focus is not a @?x : S@
  | NotAGuessHere
    -- ^ @solve@ or @regret@ where the focus is not a @?x ≐ g : S@
  | NotReadyToIntroduce
    -- ^ @intro@ on anything but table 2.8's shape @?x ≐ (?x' : S . x') : …@.
    -- The shape test is the specification, not a shortcut: a hole not of that
    -- form is made ready by @attack@
  | CannotBuildDatatype DataBuildError
    -- ^ the elaborated types do not make a datatype record (MS4 phase 42b).
    -- Everything a /user/ can get wrong is checked by @declare@ on the
    -- finished record; this is about it not being buildable at all.
  | TooManyArgumentsForHead
    -- ^ @apply-next@ was asked for an argument the head's type has no Π domain
    -- for (MS4 phase 44, and @make-apply@'s until 49f deleted it)
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
  | WouldLeaveTheLine FailReason Int
    -- ^ **the line failed, and the only alternative left was made before it**
    -- (MS5 phase 95) — the reason it failed, and the choice point that was not
    -- taken. @retry ‹n›@ takes it.
    --
    -- **His ruling, 2026-09-16**, and the argument is the reason this is a
    -- refusal rather than a silent backtrack: unwinding past the running line
    -- takes a route on which that line was never typed, so the command that
    -- caused the backtracking could not have been given. /"It creates a
    -- paradox."/ Nothing caches prompts to replay, so the command is lost
    -- whichever way it goes — which is why making the user say @retry@ costs
    -- them nothing and shows them what happened.
    --
    -- **It carries the original reason rather than replacing it**, because the
    -- user still has to be told why their command failed; the choice point is a
    -- second sentence, not a substitute for the first.
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
  | CannotSpecialise SpecialiseError
  | CannotTieRecursion RecursionError
    -- ^ a recursive call could not be tied to an induction hypothesis (MS9
    -- phase 186). 'RecursionError' says why
    -- ^ specialisation by unification could not run on the method it was given
    -- (MS9 phase 177). Not raised when a transition simply does not apply —
    -- 'SpecialiseError' says why

    -- Elaboration and @Call@ (§7.2, §8), added at phase 17b.
  | NoElaborationRule String
    -- ^ elaboration met a surface node it cannot handle, carrying what the
    -- node was (MS4 phase 41).
    --
    -- **A failure and not a silence, deliberately.** An elaborator that quietly
    -- did nothing here would leave a hole that looked elaborated.
    --
    -- Two things raise it now that every case is a rule (phase 49f):
    -- @expand-implicits@, when the written arguments cannot be lined up against
    -- the head's plicities, and the λ accessors, on a binder shape the surface
    -- language admits and elaboration does not yet.
  | CannotRead SyntaxError
    -- ^ @parse@ could not lex or parse its text, or @resolve@ could not resolve
    -- the tree it was given in the context at the focus. One case for both,
    -- because they are two halves of one pipeline and 'SyntaxError' already
    -- bundles exactly these three failures for the driver's own @parseCore@ —
    -- so "Thena.Repl" renders an op\'s failure with the renderer it already has
  | ExpectedSurface
    -- ^ an operand was not a 'Thena.Instral.Ops.VSurface'. Shaped like 'ExpectedText'
    -- and 'ExpectedTerm', and here for their reason: the value itself may not
    -- be named below @Core@
  | ObjectFailed ObjectError
    -- ^ a tagged term literal that is not one term of its language (MS6 phase
    -- 104). The four ways are 'ObjectError', which the development calculus
    -- reader answers with too (phase 110) — one region, one set of checks.
  | ExpectedSurfaceShape String
    -- ^ a surface reader was given a term of the wrong shape (MS4 phase 49):
    -- @surface-name@ on something that is not a name, @surface-universe@ on
    -- something that is not a written universe. Carries the shape it wanted.
    --
    -- **Each reader is paired with the test that makes it total in the clause
    -- using it** — @when (surface-is-name s) then w = surface-name s@ — so this
    -- is what a body reaching one any other way gets, rather than a guess.
  | NotDeclaredAs String String
    -- ^ a declaration reader was given a name that is not the kind of thing it
    -- reads (MS9 phase 176): the name, then what the op wanted it to be — @"a
    -- datatype"@ or @"a constructor"@.
    --
    -- **'ExpectedSurfaceShape'\'s shape, for its reason**: one case carrying
    -- the thing it wanted, rather than a constructor per op. Six readers share
    -- it and a seventh needs no new case.
    --
    -- **It is how a rule tells a constructor pattern from a variable one.**
    -- @constructor-datatype@ failing /is/ the answer "that name is not a
    -- constructor", so a splitting rule asks and lets the clause fail rather
    -- than needing a separate test.
  | CaseSurvived Context [Core]
    -- ^ **a case the specialiser could not close, and the equations that keep it
    -- alive** (MS9 phase 230). Raised by @case-survived@ where the coverage
    -- rules used to refuse by having no clause — @no clause of
    -- case-must-vanish applies here@ named a rule of the implementation where
    -- what the author needs is which equation survived.
    --
    -- **The list is empty when nothing about the method is an equation**, which
    -- is a case that survived for some other reason; the renderer says so
    -- rather than printing an empty list.
  | NoClauseMatched String Int [Int]
    -- ^ @call ‹name› ‹args›@ found nothing to run: the name, the number of
    -- arguments it was given, and the arities of the rules that do bear that
    -- name. **One reason for three mistakes**, told apart by the renderer —
    -- no rule of that name at all (the list is empty), no clause of that
    -- arity (the count is not in the list), or clauses of the right arity
    -- whose heads all failed. Phase 23; @ExpectedRule@ and
    -- @WrongNumberOfArguments@ were its two predecessors and are gone, because
    -- a call no longer takes a rule /value/ and arity is a filter rather than
    -- an error.
  | BindingDidNotMatch Pattern
    -- ^ **@‹pattern› = ‹op›@ ran, and the answer does not fit** (MS5 phase 84).
    -- His ruling is that this is a failure and not a refusal: in a rule it
    -- backtracks like any other, and in a function it is the caller's.
    --
    -- Carries the pattern, which is what the reader needs — the value is in the
    -- development the failure is reported against.
  | PatternDidNotMatch String Int
    -- ^ a LAMBDA\'s parameters did not match what it was applied to (MS5 phase
    -- 82) — the local\'s name and how many arguments it was given.
    --
    -- **A rule gets 'NoClauseMatched' for the same event**, and the two are
    -- different on purpose: a rule\'s clauses are searched, so a pattern that
    -- refuses is one candidate declining and the message is about the search. A
    -- closure has one clause and no head, so there is nothing to search and the
    -- refusal is the whole answer. His ruling was that a refutable pattern which
    -- does not match is a /failure/ — in a rule it backtracks, in a function it
    -- is the caller\'s failure, as in Haskell.
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
  | TheClaimed                 -- ^ the type a @Trusted@ claims
  | TheActual                  -- ^ the type its body was checked at
  | TheTrusted                 -- ^ its body
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
    -- ^ §3.7's stated limit, and __what is left of it after MS9 phase 213__.
    -- The type of index @n@ (counting from 1, named) mentions an earlier index
    -- that the motive cannot be transported past. A /friendly/ index states no
    -- equation, so it is abstracted and this is not raised for it (phase 19);
    -- a /tied/ one has its equation stated at the actual earlier indices, with
    -- its generalised side carried there along the earlier equations.
    --
    -- Neither @Vec@ nor @Below@ any more: a one-element index telescope has no
    -- earlier index to depend on, and
    -- @Below : ∀ (n : Nat) (i : Fin n) -> Type₀@ eliminates at a tied @fz m@
    -- since phase 213. __And not @Chain@ either, since MS9 phase 237__: two
    -- mentioned indices that are /chained/ — @Iₙ@ mentioning both @j@ and @m@
    -- while @Iₘ@ mentions @j@, as in
    -- @Chain : ∀ (n : Nat) (i : Fin n) (b : Below n i) -> Type₀@ — are carried
    -- by a motive that binds the position moving with the one being
    -- transported, which needs no packaged equality (@~fq5gp@).
    --
    -- __ONE SHAPE REMAINS AND IT MAY BE UNREACHABLE.__ A tied index whose type
    -- mentions a /friendly/ one: there is no equation about a friendly index to
    -- carry anything along. A friendly index is a variable no other index
    -- mentions, while a tied index's term pins every index its type mentions —
    -- which makes the two look incompatible, and no shape anybody has written
    -- reaches it. That is an argument and not a proof, so this constructor
    -- stays rather than being deleted.
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

-- | What specialisation by unification refused (MS9 phase 177).
--
-- **There is no "no transition applies" case, and that is deliberate.**
-- @eliminating.pdf@ Definition 19 makes that a failure; "Thena.Tactics.Specialise"
-- keeps the equation as a hypothesis instead, which is what the user is handed
-- today, so the specialiser can only refuse for a reason that is about its
-- /caller/ rather than about the problem.
-- | Which transition a transported chain stopped at, and so what Thena would
-- need to carry one (MS9 phase 214, @~7gmvr@ step three).
--
-- **All three are named by what is missing rather than by what failed**,
-- because each is a different piece of the paper's §3.5 and they are not one
-- another's consequences.
data ChainBlocker
  = ByDeletion
    -- ^ the equation says nothing, and dropping its binder would need
    -- @q ≃ refl@ for an arbitrary proof of @Eq I t t@ — the K axiom, which
    -- /Pattern Matching Without K/ §3.5 identifies as exactly a dependent
    -- deletion rule. Thena is a without-K system, so this one is not coming
  | ByInjectivity
    -- ^ the equation is between two applications of one constructor, and
    -- restating the later transport along the argument equations would need
    -- @noConfusion@ backwards and its round-trip law — the paper's @noConfD⁻¹@
    -- and @isLeftInvD@. "Thena.Global.NoConfusion" generates neither
  | BySolution
    -- ^ the construction that does carry a chain needs the prelude's
    -- @DPair@ — the singleton whose contractibility derives based path
    -- induction — and this session has no such declaration
  deriving (Eq, Show)

data SpecialiseError
  = NotThatConstructor GlobalName
    -- ^ the name a method was to be specialised for is not a constructor. A
    -- method type says nothing about which constructor it belongs to, so the
    -- caller names it; this is that name being wrong
  | MethodNotShaped Int Int Core
    -- ^ the type has fewer Π binders than the constructor's telescope and the
    -- stated equation count together — so it is not that constructor's method,
    -- or not an elimination's method at all. Carries both counts and the type
  | NotAnEquation [Core]
    -- ^ a binder in the equation block is not an application of @Eq@. Carries
    -- every domain in that block, because which one is wrong is the question
  | TransportedEquation ChainBlocker Int Core
    -- ^ a later equation is stated about this one's __proof__, and the
    -- transition that would fire on it removes the binder that proof is (MS9
    -- phase 214, @~7gmvr@). Carries which transition, the position counting
    -- from 1, and the equation.
    --
    -- §3.2 of /Pattern Matching Without K/ states a telescopic equality
    -- homogeneously, by transporting each side along the equations before it,
    -- so "Thena.Tactics.Eliminate" states the motive for a family like
    -- @Below : ∀ (n : Nat) (i : Fin n) -> Type₀@ at a tied index. **The
    -- solution transition carries such a chain** — §3.5's own @solution@,
    -- derived from the contractible singleton; 'ChainBlocker' is the three ways
    -- the other transitions do not. Declined rather than attempted, so that a
    -- split refuses where it stands instead of handing back a
    -- 'SpecialisedIllTyped' about generated variables
  | SpecialisedIllTyped TypeError
    -- ^ the term built does not inhabit the method type it was built for. A
    -- **generator bug**, like 'Thena.Global.NoConfusion.Rejected': the whole of
    -- §7.2's bargain for a coarse op is that this is caught here
  deriving (Eq, Show)

-- | What tying a recursive call to its induction hypothesis refused (MS9
-- phase 186).
--
-- **Every case is about one call, or about the shape the driver handed over.**
-- There is no case for "this definition is not recursive": a body that never
-- mentions the name it is defining passes through untouched, which is what
-- makes assuming the name on every declaration uniform rather than a mode.
data RecursionError
  = RecursionNotAbstracted
    -- ^ the term is not a λ, so it is not a body elaborated under an assumed
    -- name. A **driver bug**, not a user error
  | RecursiveNameNotApplied
    -- ^ the name being defined occurs somewhere that is not the head of an
    -- application — passed as a value, say. There is no induction hypothesis
    -- for that, and leaving it would make the body open
  | CallMatchesNoHypothesis Context Core
    -- ^ a recursive call none of the hypotheses in scope is about. Carries the
    -- call. **This is structural recursion refusing**, and it is the whole of
    -- the guard: @double zero@ inside the @succ@ arm names no smaller thing
  | CallMatchesSeveral Context Core Int
    -- ^ a recursive call naming more than one of the arguments that have a
    -- hypothesis, so which one it recurses on is not written down. Carries the
    -- call and how many matched
  | CallVariesAFixedPremise Context Core Core Core
    -- ^ a recursive call that passes something other than the premise the split
    -- fixed (MS9 phase 208). Carries the call, the premise as the split holds
    -- it, and what the call passes instead.
    --
    -- **A premise the induction varies is bound inside the arm.** Bound before
    -- the split it is not quantified by the motive, so the hypothesis is the
    -- statement at that one value and a call at another value is not it. The
    -- argument would otherwise be dropped in silence and the call would read as
    -- a statement it is not
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
  | BlockUnreadable ReadError
    -- ^ a @language@ or @context@ block the reader could not take apart
    -- (MS6 phase 101). A syntax error, reported before anything in the module
    -- elaborates, as a malformed top-level @do@ block is.
  | BlockIllFormed Int String
    -- ^ the instruction at this position in a **top-level** @do@ block gave this
    -- op word the wrong operands (MS4 phase 45).
    --
    -- Structured for 'BlockOperands'\' reason — @Thena.Rules.RuleError@ is above
    -- this module — and a second constructor rather than a shared one because
    -- the two failures are in two different error languages: a top-level block
    -- is refused while the file is being read, and one inside a term fails
    -- while the machine is running.
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
-- | **Why a tagged term literal is not one term of its language** (MS6 phase
-- 110). Both readers ask the same four questions of a region — the surface's,
-- when the literal elaborates, and the development calculus's, when the text
-- is resolved — so both carry this rather than spelling it twice.
data ObjectError
  = NoSuchObjectLanguage String
    -- ^ a region named a language no @language@ block has declared. **Asked
    -- when the literal is resolved or elaborated**, not when it is read: a
    -- module is parsed whole before its own block is installed, so this is the
    -- earliest the question can be asked.
  | NoSuchObjectProduction String String
    -- ^ @LC[nope]\`…\`@ — the language, and a production it does not have.
  | ObjectNotParsed String String ParseFailure
    -- ^ the language, the region's text, and why the object grammar did not
    -- read it as one term. The same three answers @:parse@ gives, because it
    -- is the same parser.
  | ObjectNotATerm String BuildError
    -- ^ it parsed, and the reading does not denote a term.
  deriving (Eq, Show)

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
  | SpliceNotFilled String
    -- ^ **@${x}@ where nothing is bound to @x@** (MS5 phase 81). Unreachable
    -- through a rule base, which refuses an unbound name in a template when the
    -- file loads; it is answered rather than left to a pattern-match failure,
    -- and it is what a term resolved with no splice environment at all would
    -- say.
  | NotAnObjectTerm ObjectError
    -- ^ **a tagged term literal in development-calculus text** (MS6 phase
    -- 110): @LC\`( λ x : ι . x )\`@ resolves to the constructor application it
    -- denotes, and this is why it did not. It is what the printer writes, so
    -- what a goal shows can be typed back.
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
