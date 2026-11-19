-- | Why a declaration did not go in, for a pane (MS12 phase 325).
--
-- **A module that comes in partly leaves an unfinished item behind, and this is
-- the view of one.** 'Thena.Driver.unfinishedWhy' kept the run's whole answer
-- until this phase, which left a frontend no way to draw it except
-- @Thena.Render.renderResponse@ — text, in a pane that lays out structure. That
-- is the rule this module exists to let a pane keep.
--
-- **The shape is the kind, plus typed parts each labelled with its role** — his
-- choice of 2026-11-19, over an arm per failure, after the tui track said it
-- draws this inside a fold a few lines wide and has nowhere to spend the layout
-- freedom an arm per failure buys. @discussion\/failure-views.md@ is the
-- conversation (his notes directory, not in this repository).
--
-- **What he rejected, and what makes this not that**: a headline plus pieces of
-- a sentence to print. A part here is a typed value with the view it already
-- has — a name as a name, a term as a 'Display' — so a pane can colour it,
-- reach it, or ask the session about it. 'Piece' is the whole vocabulary of
-- what a part can be, and nothing in it is a sentence.
--
-- **'Nature' is the field the tui track asked for and it is the one thing here
-- that is not about the failure.** Three of the stops an unfinished item can
-- carry are not faults — a question and a spent budget mean the item is sitting
-- on a @yield@ with nothing wrong, and @:abandon@ is the user's own act — and
-- before this phase every row in a pane's fold was drawn identically, so
-- @stuck: not in scope: nonesuch@ and /you typed :abandon/ read as the same
-- kind of event. **A pane takes its glyph and its ink from 'Nature'**, so a
-- stop added later draws correctly without a note arriving from this track.
--
-- **Four values and not the three that were asked for.** 'Thena.Driver.Untrusted'
-- is in none of the three: the kernel accepted the term and the session's trust
-- level did not, so nothing is broken, nothing will continue by itself, and the
-- move is to lower the level or strengthen the proof.
--
-- **'Role' and 'Nature' are closed types this track owns** — the tui track's one
-- condition, and the reason is theirs: a pane can print a role it does not
-- recognise but cannot lay it out.
module Thena.View.Failure
  ( -- * The stop
    StopView (..)
  , Nature (..)
  , Why (..)
  , displayStop
  , natureOf

    -- * A fault, and its parts
  , FaultView (..)
  , FaultKind (..)
  , PartView (..)
  , Piece (..)
  , Role (..)
  , Wanted (..)
  , Stage (..)
  , Spot (..)
  , Form (..)
  , Block (..)
  , Blocked (..)

    -- * What a run said on the way
  , WarningView (..)

    -- * The vocabulary, re-exported so that this one import serves a pane
    --
    -- | A view whose fields cannot be named is not usable — 'Thena.View.Trust'
    -- gives the reason in full.
  , Display
  , TrustView
  ) where

import qualified Thena.Core.Level as L
import qualified Thena.Driver as Dr
import qualified Thena.Engine as En
import qualified Thena.Errors as E
import qualified Thena.Global.Declare as D
import qualified Thena.Instral.Infer as I
import qualified Thena.Language.Grammar as G
import qualified Thena.Language.Reader as Rd
import qualified Thena.Rules as R
import qualified Thena.Surface.Concrete as C
import qualified Thena.Syntax.Lexer as Lx

import Thena.Core.Context (Context, Entry (..))
import Thena.Core.Level (levelVarName)
import Thena.Core.Term (Ident (..), Spelling, Var, nameDotted, spelledIn)
import Thena.Driver (NotDone)
import Thena.Instral.Type (renderTy)
import Thena.Language.Grammar (Grammar)
import Thena.Syntax.Print (Env, freshen, nameOf, renderLevel)
import Thena.View.Address (Address)
import Thena.View.Core (Budget, Display, displayCore)
import Thena.View.Instral (patternText)
import Thena.View.Trust (TrustView, displayTrust)

-- ---------------------------------------------------------------------------
-- The stop

-- | What became of an item, as a pane sees it.
--
-- **'stopViewNature' is derived from 'stopViewWhy' and is a field all the same**,
-- for the reason 'Thena.View.Trust.trustViewRefused' is: which stops are faults
-- is this track's rule, and a second copy of it in a frontend would drift.
data StopView = StopView
  { stopViewNature :: Nature
  , stopViewSaid :: [String]
    -- ^ what the run printed before it stopped, in order. Already text when the
    -- engine makes it: a rule's @say@ takes a string.
  , stopViewWarned :: [WarningView]
    -- ^ the warnings the run raised. **Not faults** — a warning never stops an
    -- item — and here because they are raised by the run this view is of, so
    -- nothing else in a pane has them for /this/ item.
  , stopViewWhy :: Why
  }
  deriving (Eq, Show)

-- | Whether anything is wrong, and if not, what kind of not-wrong this is.
--
-- **The glyph and the ink come from here.** Every other field says what
-- happened; this one says how to read it.
data Nature
  = Broken
    -- ^ something is wrong and the item did not go in.
  | Stopped
    -- ^ nothing is wrong: it is sitting on a question, or it ran out of fuel.
    -- It can go on.
  | NotTrusted
    -- ^ the kernel accepted what the item built and the session's trust level
    -- did not. **Nothing is broken and nothing continues by itself**: the move
    -- is to lower the level or to discharge the claims.
  | GivenUp
    -- ^ the user typed @:abandon@ while it was elaborating. **Their own act, so
    -- a pane states it rather than reporting it.**
  deriving (Eq, Show, Enum, Bounded)

-- | The stop itself.
data Why
  = NothingWrong
    -- ^ the run ran out of instructions with nothing left to say. **Unreachable
    -- from a load** — an item whose program completes is a finished item — and
    -- here because 'Thena.Driver.Stop' can say it.
  | Yielding String
    -- ^ a rule handed control to the prompt and is standing still, with this to
    -- say for itself.
  | Faulty [FaultView]
    -- ^ one fault, or several — a @do@ block that did not validate has one per
    -- bad line.
  | Asked String
    -- ^ it is waiting for an answer, and this is what it asked.
  | OutOfFuel Int
    -- ^ the budget ran out, having spent this many instructions.
  | Trusting TrustView
    -- ^ the level that refused it, and every claim the term rests on.
  | WasGivenUp
    -- ^ @:abandon@.
  deriving (Eq, Show)

-- | Which nature a 'Why' has. 'stopViewNature' is this applied.
natureOf :: Why -> Nature
natureOf w = case w of
  NothingWrong -> Stopped
  Yielding _ -> Stopped
  Faulty _ -> Broken
  Asked _ -> Stopped
  OutOfFuel _ -> Stopped
  Trusting _ -> NotTrusted
  WasGivenUp -> GivenUp

-- ---------------------------------------------------------------------------
-- A fault

-- | One thing that went wrong: which failure it is, its parts, and the failure
-- it wraps.
--
-- **'faultViewInside' is a field and not a part**, because the engine's error
-- types nest — a term that has no type carries the typing failure, a line the
-- machine would not leave carries what actually went wrong — and the nesting is
-- structure rather than a value the failure is about. A pane draws the outer
-- kind and indents the inner one, which is what the text door already does.
data FaultView = FaultView
  { faultViewKind :: FaultKind
  , faultViewParts :: [PartView]
  , faultViewInside :: Maybe FaultView
  }
  deriving (Eq, Show)

-- | Which failure it is.
--
-- **A kind says what went wrong and never what it went wrong /about/** — that
-- is what the parts are for. So @expected a list@ and @expected a pair@ are one
-- kind with a 'Wanted' part, and not two kinds: a pane that wants to say which
-- reads the part, and one that does not is unaffected when another is added.
data FaultKind
  = -- * Names
    NotInScope
    -- ^ nothing of that name is in scope. 'TheWord' is the name as written.
  | NameAmbiguous
    -- ^ several things answer to it; 'TheCandidates' are they.
  | NoSuchNamespace
  | NameAlreadyDeclared
  | NameRepeated
    -- ^ one declaration binds the same name twice.
  | NameReserved
  | NotAName
    -- ^ what was written cannot be a name at all — a dotted string, a literal.
  | UnknownName
    -- ^ a name the checker does not know: a global, a datatype, a variable.
    -- **Not 'NotInScope'**, which is the surface's answer; this one is the
    -- kernel meeting a name that resolution already accepted.
    -- * Kinds and counts
  | WrongKindOfThing
    -- ^ something of another kind was wanted. 'TheWanted' says which.
  | WrongCount
    -- ^ too few or too many. 'TheExpected' and 'TheFound' are the two numbers,
    -- and 'TheWanted' what was being counted.
    -- * Typing
  | TermHasNoType
  | GuessNotOfGoalType
    -- ^ what was written does not have the hole's type.
  | TypesDiffer
    -- ^ two types cannot be made equal. 'TheExpected' and 'TheFound', and
    -- 'TheSpot' where inside them they first disagree.
  | NotAType
  | NotAFunction
  | NotAMotive
  | UniversesDiffer
  | Unsaturated
    -- ^ a former or a constructor used with fewer arguments than it takes.
  | OverApplied
  | LooseIndex
  | OccursCheck
    -- ^ solving a variable with a term that mentions it.
  | ScopeViolation
    -- ^ the solution would mention something not bound where it must stand.
  | NotClosed
    -- ^ the kernel was handed a term with a free variable in it.
  | AbstractedTooFar
    -- ^ a construction binds where the type it claims has no binder for it.
  | LevelsUnmet
    -- ^ the universe constraints have no solution, or no unique one.
  | NotStrictlyPositive
    -- ^ a datatype's argument recurses in a way that would make it unsound.
    -- * The development
  | NothingToWorkOn
    -- ^ there is no goal, no development, or nothing in the option.
  | WrongShapeOfGoal
    -- ^ the goal is there and is not the shape this needed.
  | CannotMoveThere
  | NoRuleApplies
  | WouldLeaveTheLine
    -- ^ undoing would backtrack past the line being worked on. 'TheChoice' is
    -- the choice point that would be taken, and the inside fault is what
    -- actually went wrong.
  | NotYetPure
    -- ^ a development that still rests on something impure. 'TheSpot' says
    -- where.
  | PatternDidNotMatch
  | NothingReturned
  | NoCallToReturnFrom
  | CaseSurvived
    -- ^ a split left an impossible case standing.
  | RecursionNotTied
  | SpecialisationRefused
  | EliminationRefused
    -- * Reading what was written
  | CouldNotRead
    -- ^ text that would not lex, lay out, parse or pair up. 'TheStage' says
    -- which, and the pane re-asks through 'Thena.View.parseView' if it wants
    -- the chart.
  | NoSuchLanguage
  | NoSuchProduction
  | NoSuchTag
  | TagAmbiguous
  | NotDeclaredAs
    -- * A rule, and a block of instructions
  | NoElaborationRule
  | NoSuchInstruction
  | BlockShapeWrong
    -- ^ an instruction in a @do@ block is not written in a way it can be run:
    -- the wrong operands, a binding that binds nothing, a declaration in a
    -- body. 'TheInstruction' is which line.
  | RuleTypeWrong
    -- ^ a rule's declared or inferred type does not work out.
  | SignatureUnanswered
  | ClauseUnreachable
  | NoSuchPrimitive
  | PrimitiveWrongShape
  | NoClauseMatched
  | GrammarRefused
    -- ^ a @language@, @context@, @judgment@ or @notation@ block was not
    -- admitted. **'TheBlock' and 'TheName' say which, and where inside it, and
    -- no part says what is wrong with it yet** — the grammar failures are their
    -- own tree and are not walked as of this phase.
  | TokenClassRefused
  | NotATokenType
    -- ^ a token class is declared at a type it cannot read, or its regular
    -- expression does not work.
  deriving (Eq, Show, Enum, Bounded)

-- | One part of a fault: what it plays, and what it is.
data PartView = PartView
  { partViewRole :: Role
  , partViewPiece :: Piece
  }
  deriving (Eq, Show)

-- | What a part plays in the failure it belongs to.
--
-- **Closed, and this track owns it** — the tui track's condition: a pane can
-- print a role it does not recognise but cannot lay it out.
data Role
  = TheName
  | TheWord
    -- ^ a name as the user wrote it, which may resolve to nothing.
  | TheCandidates
  | TheOther
    -- ^ the second of two things the failure is about equally — two terms that
    -- cannot be made equal, two levels that differ. **Not 'TheFound'**, which
    -- is the one of a pair that was wrong.
  | TheExpected
  | TheFound
  | TheTerm
  | TheType
  | TheTarget
  | TheGoal
  | TheVariable
  | TheBinder
  | TheWanted
  | TheSpot
    -- ^ where inside the thing the failure is.
  | TheStage
  | TheForm
  | TheLevel
  | TheRule
  | TheInstruction
  | TheClause
  | TheTest
  | TheChoice
  | ThePattern
  | TheLanguage
  | TheProduction
  | TheText
  | TheField
  | TheIndex
  | TheParameter
  | TheMethod
  | TheMotive
  | TheConstructor
  | TheDatatype
  | TheNamespace
  | TheHypothesis
  | TheCount
  | TheBlocker
  | TheBlock
  | TheObligations
  | TheClaimed
  | TheActual
  deriving (Eq, Show, Enum, Bounded)

-- | What a part is.
--
-- **Nothing here is a sentence**, which is the whole of what separates this
-- shape from the one he rejected on 2026-11-19.
data Piece
  = AName String
    -- ^ a name, spelled the way the session would print it — and so the kind of
    -- thing @resolve-name@ takes, which is what the tui track asked for.
  | ADottedName String
    -- ^ a name in full, with no printer policy on it: what an index is keyed
    -- by, where the spelled form would be ambiguous.
  | ANames [String]
  | ATerm Display
  | AVariable String
    -- ^ a variable, named from the context it is bound in.
  | ACount Int
  | ALine Int
    -- ^ a line, counting from 1.
  | AWanted Wanted
  | ALevel String
    -- ^ a universe level, as the prompt writes it. Text: a level is spelled and
    -- not reached.
  | ABlock Block
  | AStage Stage
  | ASpot Spot
  | AForm Form
  | ABlocked Blocked
  | ARuleType String
    -- ^ an instruction's type, as 'Thena.Instral.Type.renderTy' writes it.
    -- **Text, deliberately**: there is nothing in a rule's type for a pane to
    -- reach, and a part is worth being typed when it is reachable.
  | APattern String
    -- ^ a binding pattern, as the prompt writes it. Text for the same reason.
  | AnObligation [String]
    -- ^ the level obligations that cannot be met, each as written.
  | AText String
    -- ^ a region of the user's own text that something was tried on.
  deriving (Eq, Show)

-- | Which kind of thing was wanted where another was found.
data Wanted
  = AList
  | APair
  | AnOption
  | ALevelNumber
  | AWholeNumber
  | SomeText
  | AnIdentifier
  | ARawTerm
  | ACoreTerm
  | ASurfaceTerm
  | AUniverse
  | ADatatype
  | AnObjectTerm
  | AHole
  | AGuess
  | AnArgument
  | AnIndex
  | AMethod
  | AParameter
  | AMetavariable
  | AnEquation
  | AConstructorOf
  | AProduction
  deriving (Eq, Show, Enum, Bounded)

-- | How far reading got before it stopped.
data Stage
  = Lexing
  | LayingOut
  | Parsing
  | ParsingSurface
  | PairingDeclarations
  | ReadingABlock
  | Resolving
  deriving (Eq, Show, Enum, Bounded)

-- | Where inside a term or a development something is.
--
-- **The engine's own two location types, flattened into one** — a conversion's
-- 'Thena.Errors.Site' and a kernel failure's 'Thena.Errors.Position' — because a
-- pane asking /where/ does not care which of them answered.
data Spot
  = TheWholeThing
  | InTheDomain String
  | UnderTheBinder String
  | InTheFunction
  | InTheArgument
  | InTheNthArgument String Int
  | InTheNthParameter Int
  | InTheMotiveOf
  | InTheNthMethod Int
  | InTheNthIndex Int
  | InTheTargetOf
  | InTheClaimedType
  | InTheCheckedType
  | InTheTrustedBody
  | InTheHole String
  | InTheTypeOf String
  | InTheValueOf String
  | InTheGuessOf String
  | InTheNthConstraint Int
  | Within String Spot
    -- ^ under a guess, whose body is a development in its own right.
  deriving (Eq, Show)

-- | What a hole, a guess or a constraint is, where one of the three was wanted.
data Form = AsAHole | AsAGuess | AsAConstraint
  deriving (Eq, Show, Enum, Bounded)

-- | Which kind of block a grammar failure is in.
data Block = ALanguage | AContext | AJudgment | ANotation
  deriving (Eq, Show, Enum, Bounded)

-- | Why a chain could not be transported.
data Blocked = ByADeletion | ByInjectivity | BySolving
  deriving (Eq, Show, Enum, Bounded)

-- | A warning a run raised.
--
-- **Typed rather than text, and it was cheap**: 'Thena.Errors.Warning' has nine
-- constructors, so a pane gets the same reach over them as over a fault.
data WarningView
  = ABinderBindsNothing Block String String String
    -- ^ the block, its name, the production, and the binder nothing mentions.
  | AMetavariableNotOpen Block String String String String
    -- ^ the block, its name, the production, the word read as a terminal, and
    -- the language whose metavariable that word is.
  | ATokenClassNotOpen Block String String String String
  | ANameShadows String String
    -- ^ the name just declared, and the one it shadows.
  | AProofShadows String String
  | APublicConsultIdles String
  | APublicImportUnlisted String [String]
  | APublicIdlesAtThePrompt String
  | AClassCannotBePrimed Block String String
    -- ^ the block, the language, and the identifier class no character extends.
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- The walk

-- | Build the view.
--
-- **Every 'Core' is displayed in the context the failure carries**, and the
-- caller's 'Env' only where a failure carries none —
-- 'Thena.View.Trust.displayTrust' gives the reason: a term reached under a
-- binder mentions variables the focus has never heard of.
--
-- **The address is the caller's, for every part.** Nothing here is a subterm of
-- the focus: these terms are what a run was holding when it stopped, and
-- inventing a route into them would invite a @goto@ into nothing.
displayStop
  :: Spelling
  -> [Grammar]
  -> Budget
  -> Env
  -> [(Var, Address)]
  -> Int
  -> Address
  -> NotDone
  -> StopView
displayStop sp grammars budget env binders counter here nd = case nd of
  Dr.ItWasAbandoned ->
    StopView
      { stopViewNature = GivenUp
      , stopViewSaid = []
      , stopViewWarned = []
      , stopViewWhy = WasGivenUp
      }
  Dr.ItStopped msgs ws stop ->
    let w = whyOf stop
     in StopView
          { stopViewNature = natureOf w
          , stopViewSaid = msgs
          , stopViewWarned = map warningView ws
          , stopViewWhy = w
          }
  where
    -- ** The stop itself

    whyOf stop = case stop of
      Dr.Completed -> NothingWrong
      Dr.Waiting (En.Question ask _) -> Asked ask
      Dr.Yielded msg -> Yielding msg
      Dr.Paused spent -> OutOfFuel spent
      Dr.Halted r -> Faulty [failReason r]
      Dr.Refused e -> Faulty [declareError e]
      Dr.Uncertified e -> Faulty [kernelError e]
      Dr.BlockRefused es -> Faulty (map ruleError es)
      Dr.BlockIllTyped es -> Faulty (map instralError es)
      Dr.Untrusted lvl claims ->
        Trusting (displayTrust sp grammars budget binders counter here lvl claims)

    -- ** Building a fault

    fault k ps = FaultView k ps Nothing
    around k ps inner = FaultView k ps (Just inner)
    bare k = FaultView k [] Nothing
    is r pc = PartView r pc

    wanting w = fault WrongKindOfThing [is TheWanted (AWanted w)]
    counting w want got =
      fault WrongCount
        [is TheWanted (AWanted w), is TheExpected (ACount want), is TheFound (ACount got)]

    -- ** Displaying what a part holds

    coreIn ctx = ATerm . displayCore sp grammars budget (envOf ctx) binders counter here
    coreHere = ATerm . displayCore sp grammars budget env binders counter here
    name = AName . spelledIn sp
    varIn ctx x = AVariable (nameOf x (envOf ctx))
    level = ALevel . renderLevel
    ident (Ident i) = i

    -- ** Why a run failed

    failReason r = case r of
      E.UnboundInBody x -> fault NotInScope [is TheWord (AName x)]
      E.NothingReturned pt -> fault NothingReturned [is ThePattern (APattern (patternText pt))]
      E.NothingToReturnFrom -> bare NoCallToReturnFrom
      E.NotAnIdentifier w -> fault NotAName [is TheText (AText w)]
      E.BlockOperands i w ->
        fault BlockShapeWrong [is TheInstruction (ALine (i + 1)), is TheWord (AName w)]
      E.ExpectedText -> wanting SomeText
      E.ExpectedName -> wanting AnIdentifier
      E.NoSuchNamespace n -> fault NoSuchNamespace [is TheNamespace (AName n)]
      E.AmbiguousName n gs ->
        fault NameAmbiguous [is TheWord (AName n), is TheCandidates (ANames gs)]
      E.DottedTextName w -> fault NotAName [is TheText (AText w)]
      E.ExpectedRaw -> wanting ARawTerm
      E.CannotResolve e -> resolveError e
      E.ExpectedTerm -> wanting ACoreTerm
      E.ExpectedList -> wanting AList
      E.ExpectedPair -> wanting APair
      E.ExpectedOption -> wanting AnOption
      E.ExpectedLevel -> wanting ALevelNumber
      E.ExpectedInt -> wanting AWholeNumber
      E.NothingThere -> fault NothingToWorkOn [is TheWanted (AWanted AnOption)]
      E.CannotMove m -> moveError m
      E.Mismatch ctx a b ->
        fault TypesDiffer [is TheTerm (coreIn ctx a), is TheOther (coreIn ctx b)]
      E.OccursCheck ctx x t ->
        fault OccursCheck [is TheVariable (varIn ctx x), is TheTerm (coreIn ctx t)]
      E.ScopeViolation ctx x y ->
        fault ScopeViolation [is TheVariable (varIn ctx x), is TheOther (varIn ctx y)]
      E.UniverseMismatch a b ->
        fault UniversesDiffer [is TheLevel (level a), is TheOther (level b)]
      E.NotAHole -> fault WrongShapeOfGoal [is TheWanted (AWanted AHole)]
      E.NotAGuessHere -> fault WrongShapeOfGoal [is TheWanted (AWanted AGuess)]
      E.NotReadyToIntroduce -> bare WrongShapeOfGoal
      E.CannotBuildDatatype e -> dataBuildError e
      E.TooManyArgumentsForHead -> fault WrongCount [is TheWanted (AWanted AnArgument)]
      E.NoEnclosingDevelopment -> bare NothingToWorkOn
      E.GoalIsNotAUniverse -> fault WrongShapeOfGoal [is TheWanted (AWanted AUniverse)]
      E.NothingToIntroduce -> fault WrongShapeOfGoal [is TheWanted (AWanted AnArgument)]
      E.NotYetPure pos -> fault NotYetPure [is TheSpot (ASpot (spotOf pos))]
      E.NoGoalHere -> bare NothingToWorkOn
      E.NoRuleMatched -> bare NoRuleApplies
      E.WouldLeaveTheLine why i ->
        around WouldLeaveTheLine [is TheChoice (ACount i)] (failReason why)
      E.GuessIllTyped e -> around GuessNotOfGoalType [] (typeError e)
      E.BinderNotAType e -> around NotAType [] (typeError e)
      E.NotTypeable e -> around TermHasNoType [] (typeError e)
      E.CannotEliminate e -> elimError e
      E.CannotSpecialise e -> specialiseError e
      E.CannotTieRecursion e -> recursionError e
      E.NoElaborationRule what -> fault NoElaborationRule [is TheForm (AText what)]
      E.CannotRead e -> syntaxError e
      E.ExpectedSurface -> wanting ASurfaceTerm
      E.ObjectFailed e -> objectError e
      E.ExpectedSurfaceShape what ->
        fault WrongKindOfThing [is TheWanted (AWanted ASurfaceTerm), is TheForm (AText what)]
      E.NotDeclaredAs what wanted ->
        fault NotDeclaredAs [is TheName (AName what), is TheForm (AText wanted)]
      E.CaseSurvived ctx eqs -> fault CaseSurvived [ is TheTerm (coreIn ctx e) | e <- eqs ]
      E.NoClauseMatched g got want
        | null want -> fault NoRuleApplies [is TheRule (AName g)]
        | got `notElem` want ->
            fault WrongCount
              ( is TheRule (AName g)
                  : is TheFound (ACount got)
                  : [ is TheExpected (ACount k) | k <- want ]
              )
        | otherwise -> fault NoClauseMatched [is TheRule (AName g)]
      E.BindingDidNotMatch pt ->
        fault PatternDidNotMatch [is ThePattern (APattern (patternText pt))]
      E.PatternDidNotMatch g got ->
        fault PatternDidNotMatch [is TheRule (AName g), is TheFound (ACount got)]

    -- ** Why the checker refused a term

    typeError e = case e of
      E.UnknownVariable ctx x -> fault NotInScope [is TheVariable (varIn ctx x)]
      E.UnknownGlobal g -> fault UnknownName [is TheName (name g)]
      E.UnknownDatatype g -> fault UnknownName [is TheDatatype (name g)]
      E.WrongNumberOfLevelArguments g want got ->
        fault WrongCount
          [ is TheName (name g)
          , is TheWanted (AWanted ALevelNumber)
          , is TheExpected (ACount want)
          , is TheFound (ACount got)
          ]
      E.LooseIndex i -> fault LooseIndex [is TheIndex (ACount i)]
      E.NotAType ctx t ty ->
        fault NotAType [is TheTerm (coreIn ctx t), is TheType (coreIn ctx ty)]
      E.NotAFunction ctx t ty ->
        fault NotAFunction [is TheTerm (coreIn ctx t), is TheType (coreIn ctx ty)]
      E.NotAMotive ctx m ty ->
        fault NotAMotive [is TheMotive (coreIn ctx m), is TheType (coreIn ctx ty)]
      E.NotOfType ctx t want got why ->
        fault TypesDiffer
          ( is TheTerm (coreIn ctx t)
              : is TheExpected (coreIn ctx want)
              : is TheFound (coreIn ctx got)
              : conversion ctx why
          )
      E.Unsaturated g ty -> fault Unsaturated [is TheName (name g), is TheType (coreHere ty)]
      E.OverApplied g -> fault OverApplied [is TheName (name g)]

    -- | Where two types first disagree, and what about them does.
    conversion ctx why =
      is TheSpot (ASpot (spotOfSites (E.conversionSite why))) : clash ctx (E.conversionClash why)

    clash ctx c = case c of
      E.HeadsDiffer ctx' a b -> [is TheExpected (coreIn ctx' a), is TheFound (coreIn ctx' b)]
      E.LevelsDiffer a b -> [is TheExpected (level a), is TheFound (level b)]
      E.NamesDiffer a b -> [is TheExpected (name a), is TheFound (name b)]
      E.VariablesDiffer a b -> [is TheExpected (varIn ctx a), is TheFound (varIn ctx b)]
      E.CountsDiffer a b -> [is TheExpected (ACount a), is TheFound (ACount b)]

    -- ** Why the kernel refused a development

    kernelError e = case e of
      E.NotClosed _ -> bare NotClosed
      E.Overabstracted _ i ty ->
        fault AbstractedTooFar [is TheBinder (AName (ident i)), is TheType (coreHere ty)]
      E.NotAUniverseAbove _ i ty ->
        fault AbstractedTooFar
          [ is TheBinder (AName (ident i))
          , is TheType (coreHere ty)
          , is TheWanted (AWanted AUniverse)
          ]
      E.Levels (L.Refuted l k) ->
        fault LevelsUnmet [is TheLevel (level l), is TheOther (level k)]
      E.Levels (L.Unsatisfiable cs) ->
        fault LevelsUnmet [is TheObligations (AnObligation (map obligation cs))]
      E.Levels (L.Ambiguous vs) ->
        fault LevelsUnmet [is TheObligations (ANames (map levelVarName vs))]
      E.Ill pos te -> around NotYetPure [is TheSpot (ASpot (spotOf pos))] (typeError te)

    obligation (L.AtMost l k) = renderLevel l ++ " ≤ " ++ renderLevel k

    -- ** Where in a development, and where in a term

    spotOf p = case p of
      E.TheTerm -> TheWholeThing
      E.TheHole _ i -> InTheHole (ident i)
      E.TypeOf _ i -> InTheTypeOf (ident i)
      E.ValueOf _ i -> InTheValueOf (ident i)
      E.GuessOf _ i -> InTheGuessOf (ident i)
      E.ConstraintAt k -> InTheNthConstraint k
      E.Inside _ i inner -> Within (ident i) (spotOf inner)

    -- | A conversion carries the sites outermost first; nothing is dropped.
    spotOfSites ss = case ss of
      [] -> TheWholeThing
      [one] -> spotOfSite one
      one : rest -> case spotOfSite one of
        InTheHole x -> Within x (spotOfSites rest)
        outer -> outer

    spotOfSite si = case si of
      E.TheDomain i -> InTheDomain (ident i)
      E.TheBody i -> UnderTheBinder (ident i)
      E.TheFunction -> InTheFunction
      E.TheArgument -> InTheArgument
      E.TheArgumentOf g k -> InTheNthArgument (spelledIn sp g) k
      E.TheParameter k -> InTheNthParameter k
      E.TheMotive -> InTheMotiveOf
      E.TheMethod k -> InTheNthMethod k
      E.TheIndex k -> InTheNthIndex k
      E.TheTarget -> InTheTargetOf
      E.TheClaimed -> InTheClaimedType
      E.TheActual -> InTheCheckedType
      E.TheTrusted -> InTheTrustedBody

    -- ** The tactics that build on a datatype

    elimError e = case e of
      E.TargetNotTypeable te -> around TermHasNoType [is TheTarget (AWanted ADatatype)] (typeError te)
      E.TargetNotInductive ctx t ty ->
        fault WrongKindOfThing
          [ is TheTarget (coreIn ctx t)
          , is TheType (coreIn ctx ty)
          , is TheWanted (AWanted ADatatype)
          ]
      E.NoEquality g -> fault UnknownName [is TheName (name g)]
      E.IndexTypeDepends k i ->
        fault EliminationRefused [is TheIndex (ACount k), is TheName (AName (ident i))]
      E.IndexTypeIllTyped te -> around EliminationRefused [is TheIndex (AWanted AnIndex)] (typeError te)
      E.MotiveIllTyped te -> around EliminationRefused [is TheMotive (AWanted AMethod)] (typeError te)
      E.SchemeIllTyped te -> around EliminationRefused [] (typeError te)

    specialiseError e = case e of
      E.NotThatConstructor g ->
        fault WrongKindOfThing [is TheName (name g), is TheWanted (AWanted AConstructorOf)]
      E.MethodNotShaped want eqs _ ->
        fault SpecialisationRefused
          [ is TheWanted (AWanted AMethod)
          , is TheExpected (ACount want)
          , is TheOther (ACount eqs)
          ]
      E.NotAnEquation tys ->
        fault SpecialisationRefused
          [is TheWanted (AWanted AnEquation), is TheFound (ACount (length tys))]
      E.TransportedEquation why k _ ->
        fault SpecialisationRefused
          [is TheIndex (ACount k), is TheBlocker (ABlocked (blocked why))]
      E.SpecialisedIllTyped te -> around SpecialisationRefused [] (typeError te)

    blocked b = case b of
      E.ByDeletion -> ByADeletion
      E.ByInjectivity -> ByInjectivity
      E.BySolution -> BySolving

    recursionError e = case e of
      E.RecursionNotAbstracted -> bare RecursionNotTied
      E.RecursiveNameNotApplied -> fault RecursionNotTied [is TheWanted (AWanted AnArgument)]
      E.CallMatchesNoHypothesis ctx t ->
        fault RecursionNotTied [is TheTerm (coreIn ctx t), is TheHypothesis (ACount 0)]
      E.CallMatchesSeveral ctx t k ->
        fault RecursionNotTied [is TheTerm (coreIn ctx t), is TheHypothesis (ACount k)]
      E.CallVariesAFixedPremise ctx t pr a ->
        fault RecursionNotTied
          [ is TheTerm (coreIn ctx t)
          , is TheExpected (coreIn ctx pr)
          , is TheFound (coreIn ctx a)
          ]

    dataBuildError e = case e of
      E.DeclaredTypeIsNotAUniverse d ->
        fault NotAType [is TheDatatype (name d), is TheWanted (AWanted AUniverse)]
      E.ConstructorTargetWrong c ->
        fault NotDeclaredAs [is TheConstructor (name c), is TheWanted (AWanted ADatatype)]
      E.TooFewBinders -> counting AParameter 0 0

    -- ** Why a name did not resolve

    resolveError e = case e of
      E.NotInScope n -> fault NotInScope [is TheWord (AName n)]
      E.NameIsAmbiguous n gs ->
        fault NameAmbiguous [is TheWord (AName n), is TheCandidates (ANames gs)]
      E.NotACoreTerm f -> fault WrongKindOfThing [is TheForm (AForm (form f)), is TheWanted (AWanted ACoreTerm)]
      E.NotAUniverse d ->
        fault NotAType [is TheName (AName d), is TheWanted (AWanted AUniverse)]
      E.NotADatatype d ->
        fault WrongKindOfThing [is TheName (AName d), is TheWanted (AWanted ADatatype)]
      E.TargetIsNotTheDatatype c g dn ->
        fault NotDeclaredAs
          ( is TheConstructor (AName c)
              : is TheDatatype (ADottedName (nameDotted dn))
              : [ is TheFound (ADottedName (nameDotted produced)) | Just produced <- [g] ]
          )
      E.TargetArgumentCount c want got ->
        fault WrongCount (is TheConstructor (AName c) : parts)
        where parts = [ is TheWanted (AWanted AnArgument)
                      , is TheExpected (ACount want)
                      , is TheFound (ACount got) ]
      E.ParameterNotPassedThrough c i ->
        fault NotDeclaredAs
          [is TheConstructor (AName c), is TheParameter (AName (ident i))]
      E.WrongNumberOfEliminationParameters d want got ->
        fault WrongCount
          [ is TheDatatype (AName d)
          , is TheWanted (AWanted AParameter)
          , is TheExpected (ACount want)
          , is TheFound (ACount got)
          ]
      E.WrongNumberOfMethods d want got ->
        fault WrongCount
          [ is TheDatatype (AName d)
          , is TheWanted (AWanted AMethod)
          , is TheExpected (ACount want)
          , is TheFound (ACount got)
          ]
      E.WrongNumberOfEliminationIndices d want got ->
        fault WrongCount
          [ is TheDatatype (AName d)
          , is TheWanted (AWanted AnIndex)
          , is TheExpected (ACount want)
          , is TheFound (ACount got)
          ]
      E.SpliceNotFilled x -> fault NotInScope [is TheWord (AName x)]
      E.LevelArgumentsOnALocal x ->
        fault WrongKindOfThing [is TheWord (AName x), is TheWanted (AWanted ALevelNumber)]
      E.NotAnObjectTerm why -> objectError why

    form f = case f of
      E.AHole -> AsAHole
      E.AGuess -> AsAGuess
      E.AConstraint -> AsAConstraint

    -- ** Why the focus could not move

    moveError m = fault CannotMoveThere [is TheWanted (AWanted w)]
      where
        w = case m of
          E.AtRoot -> AnArgument
          E.NotOnTheSpine -> ACoreTerm
          E.NotInCore -> ACoreTerm
          E.NotAGuess -> AGuess
          E.NotADefinition -> AGuess
          E.StillReferenced -> AnArgument
          E.NoCrossingIntoAConstraint -> ACoreTerm
          E.NoSuchHole -> AHole
          E.NoSuchPart -> AnArgument

    -- ** Why a region of the user's own text did not read

    syntaxError e = case e of
      E.LexFailed _ -> fault CouldNotRead [is TheStage (AStage Lexing)]
      E.ParseFailed _ -> fault CouldNotRead [is TheStage (AStage Parsing)]
      E.LayoutFailed _ -> fault CouldNotRead [is TheStage (AStage LayingOut)]
      E.SurfaceParseFailed _ -> fault CouldNotRead [is TheStage (AStage ParsingSurface)]
      E.DeclarationsUnpaired pe -> case pe of
        C.SignatureWithNoEquation x ->
          fault CouldNotRead
            [ is TheStage (AStage PairingDeclarations)
            , is TheName (AName x)
            , is TheWanted (AWanted ACoreTerm)
            ]
        C.EquationWithNoSignature x ->
          fault CouldNotRead
            [ is TheStage (AStage PairingDeclarations)
            , is TheName (AName x)
            , is TheWanted (AWanted AUniverse)
            ]
      E.BlockIllFormed i w ->
        fault BlockShapeWrong [is TheInstruction (ALine (i + 1)), is TheWord (AName w)]
      E.BlockUnreadable r ->
        fault CouldNotRead [is TheStage (AStage ReadingABlock), is TheInstruction (ALine (whichLine r))]
      E.ResolveFailed re -> resolveError re

    whichLine r = case r of
      Rd.HeaderWithoutWhere l -> l
      Rd.HeaderMalformed l -> l
      Rd.ProductionWithoutArrow l -> l
      Rd.MetadataMalformed l _ -> l
      Rd.BindingMalformed l _ -> l
      Rd.IndentedLess l -> l
      Rd.ParamMalformed l _ -> l
      Rd.JudgmentHeaderMalformed l -> l
      Rd.RuleUnnamed l -> l
      Rd.RuleWithoutLine l -> l
      Rd.RuleWithoutConclusion l -> l
      Rd.QuantifierMalformed l -> l
      Rd.PremiseIndentedLess l -> l

    -- ** Why a term of an object language did not read
    --
    -- A pane that wants the chart for an unparsed region asks
    -- 'Thena.View.parseView' for it, which is what /pull it, there is no wire/
    -- means here: the text is a part, and the reading is a question.

    objectError e = case e of
      E.NoSuchObjectLanguage lang -> fault NoSuchLanguage [is TheLanguage (AName lang)]
      E.ObjectLanguageAmbiguous lang ls ->
        fault NameAmbiguous [is TheLanguage (AName lang), is TheCandidates (ANames ls)]
      E.NoSuchObjectProduction lang w ->
        fault NoSuchProduction [is TheLanguage (AName lang), is TheProduction (AName w)]
      E.ObjectNotParsed lang text _ ->
        fault CouldNotRead
          [ is TheStage (AStage Parsing)
          , is TheLanguage (AName lang)
          , is TheText (AText text)
          ]
      E.ObjectNotATerm lang why ->
        fault (buildKind why) (is TheLanguage (AName lang) : buildParts why)
      E.BuiltInTagNotATerm tag ->
        fault WrongKindOfThing [is TheLanguage (AName tag), is TheWanted (AWanted ACoreTerm)]
      E.CoreRegionUnread tag why ->
        around CouldNotRead [is TheLanguage (AName tag)] (syntaxError why)
      E.RegionSpliceNotAName tag ->
        fault WrongKindOfThing [is TheLanguage (AName tag), is TheWanted (AWanted AnIdentifier)]

    buildKind b = case b of
      E.NoSuchProduction _ -> NoSuchProduction
      E.Incomplete _ -> WrongCount
      E.NotForSlot _ _ -> WrongKindOfThing

    buildParts b = case b of
      E.NoSuchProduction n -> [is TheProduction (AName n)]
      E.Incomplete x -> [is TheField (AName x), is TheWanted (AWanted AnArgument)]
      E.NotForSlot n x -> [is TheProduction (AName n), is TheField (AName x)]

    -- ** Why a declaration was not admitted

    declareError e = case e of
      D.NoSuchPrimitive g -> fault NoSuchPrimitive [is TheName (name g)]
      D.PrimitiveWrongShape g want ->
        fault PrimitiveWrongShape [is TheName (name g), is TheForm (AText want)]
      D.AlreadyDeclared g -> fault NameAlreadyDeclared [is TheName (name g)]
      D.RepeatedName g -> fault NameRepeated [is TheName (name g)]
      D.WrongNumberOfIndices g want got ->
        fault WrongCount
          ( is TheName (name g)
              : [ is TheWanted (AWanted AnIndex)
                , is TheExpected (ACount want)
                , is TheFound (ACount got)
                ]
          )
      D.NotStrictlyPositive g i ->
        fault NotStrictlyPositive [is TheDatatype (name g), is TheField (AName (ident i))]
      D.HigherOrderRecursion g i ->
        fault NotStrictlyPositive
          [ is TheDatatype (name g)
          , is TheField (AName (ident i))
          , is TheWanted (AWanted AnArgument)
          ]
      D.NestedRecursion g i ->
        fault NotStrictlyPositive
          [ is TheDatatype (name g)
          , is TheField (AName (ident i))
          , is TheWanted (AWanted ADatatype)
          ]
      D.ArgumentNotAType g i te ->
        around NotAType
          [is TheDatatype (name g), is TheField (AName (ident i))]
          (typeError te)
      D.ArgumentTooLarge g i l d ->
        fault LevelsUnmet
          [ is TheDatatype (name g)
          , is TheField (AName (ident i))
          , is TheLevel (level l)
          , is TheOther (level d)
          ]
      D.AmbiguousLevels g -> fault LevelsUnmet [is TheDatatype (name g)]
      D.ArgumentLevelsUnmet g ->
        fault LevelsUnmet [is TheDatatype (name g), is TheWanted (AWanted AnArgument)]
      D.NoConfusionRejected g te ->
        around NotAType [is TheDatatype (name g)] (typeError te)
      D.TokenClassRefused g why -> around TokenClassRefused [is TheName (name g)] (tokenError why)
      D.GrammarRefused (G.GrammarError k g problem) ->
        fault GrammarRefused
          ( is TheBlock (ABlock (block k))
              : is TheName (AName g)
              : whereInGrammar problem
          )

    tokenError t = case t of
      D.TokenTypeUnsupported ty -> fault NotATokenType [is TheType (coreHere ty)]
      D.TokenValueNotLiteral v -> fault NotATokenType [is TheTerm (coreHere v)]
      D.TokenRegexRefused src _ -> fault NotATokenType [is TheText (AText src)]
      D.TokenMatchesEmpty src -> fault NotATokenType [is TheText (AText src)]
      D.TokenNotIncluded src ty w ->
        fault NotATokenType
          [is TheText (AText src), is TheType (name ty), is TheFound (AText w)]

    block k = case k of
      Lx.LanguageBlock -> ALanguage
      Lx.ContextBlock -> AContext
      Lx.JudgmentBlock -> AJudgment
      Lx.NotationBlock -> ANotation

    -- | Where in the block the problem is, where the problem says.
    --
    -- **What is wrong with it is not a part yet.** The grammar failures are a
    -- tree of their own, as big again as everything above, and a pane drawing
    -- this kind has the block, its name and the production or rule — which is
    -- where the author looks — and no more.
    whereInGrammar problem = case problem of
      G.InProduction prod _ -> [is TheProduction (AName prod)]
      G.InRule rl _ -> [is TheRule (AName rl)]
      _ -> []

    -- ** Why a line of instructions did not validate

    ruleError e = case e of
      R.UnboundInRule g i n ty ->
        fault BlockShapeWrong
          [ is TheRule (name g)
          , is TheInstruction (ALine (i + 1))
          , is TheWord (AName n)
          , is TheType (ARuleType (renderTy ty))
          ]
      R.DeclarationInBody g i -> lineOf BlockShapeWrong g i []
      R.BoundNonProducing g i n -> lineOf BlockShapeWrong g i [is TheWord (AName n)]
      R.NoSuchTest g w -> fault NoSuchInstruction [is TheRule (name g), is TheWord (AName w)]
      R.UnboundInHead g n -> fault BlockShapeWrong [is TheRule (name g), is TheWord (AName n)]
      R.BadTestOperands g w -> fault BlockShapeWrong [is TheRule (name g), is TheWord (AName w)]
      R.BadPattern g w ->
        fault BlockShapeWrong [is TheRule (name g), is ThePattern (APattern w)]
      R.RepeatedInPattern g n -> fault NameRepeated [is TheRule (name g), is TheWord (AName n)]
      R.ReservedName g n -> fault NameReserved [is TheRule (name g), is TheWord (AName n)]
      R.BadOperands g i w -> lineOf BlockShapeWrong g i [is TheWord (AName w)]
      R.NoSuchTag g i t -> lineOf NoSuchTag g i [is TheLanguage (AName t)]
      R.AmbiguousTag g i t gs ->
        lineOf TagAmbiguous g i
          [is TheLanguage (AName t), is TheCandidates (ANames (map (spelledIn sp) gs))]
      R.BadRegion g i t why ->
        FaultView CouldNotRead
          [is TheRule (name g), is TheInstruction (ALine (i + 1)), is TheLanguage (AName t)]
          (Just (syntaxError why))
      R.ObjectRegionUnparsed g i t text _ ->
        lineOf CouldNotRead g i [is TheLanguage (AName t), is TheText (AText text)]
      R.ObjectRegionNotATerm g i t why ->
        lineOf (buildKind why) g i (is TheLanguage (AName t) : buildParts why)
      R.NoObjectProduction g i t w ->
        lineOf NoSuchProduction g i [is TheLanguage (AName t), is TheProduction (AName w)]
      R.UnknownType r t -> fault RuleTypeWrong [is TheRule (AName r), is TheType (ARuleType t)]
      R.TypeArity r t want got ->
        fault WrongCount
          [ is TheRule (AName r)
          , is TheType (ARuleType t)
          , is TheExpected (ACount want)
          , is TheFound (ACount got)
          ]
      R.TypeVariableApplied r t -> fault RuleTypeWrong [is TheRule (AName r), is TheType (ARuleType t)]
      R.UnitInsideAType r -> fault RuleTypeWrong [is TheRule (AName r)]
      R.DuplicateSignature r i ->
        fault RuleTypeWrong [is TheRule (AName r), is TheClause (ALine (i + 1))]
      R.InAnnotation g i n why ->
        FaultView BlockShapeWrong
          [ is TheRule (name g)
          , is TheInstruction (ALine (i + 1))
          , is TheWord (AName n)
          ]
          (Just (ruleError why))
      R.AnnotationWithoutBinding g i n -> lineOf BlockShapeWrong g i [is TheWord (AName n)]
      R.ReturnInSurfaceBlock g i -> lineOf BlockShapeWrong g i []
      R.FunctionLeavesNothing r -> fault RuleTypeWrong [is TheRule (AName r)]
      R.FunctionClauseUnreachable r i ->
        fault ClauseUnreachable [is TheRule (AName r), is TheClause (ALine (i + 1))]
      R.RuleAndFunction r i ->
        fault NameAlreadyDeclared [is TheRule (AName r), is TheClause (ALine (i + 1))]

    lineOf k g i ps =
      fault k (is TheRule (name g) : is TheInstruction (ALine (i + 1)) : ps)

    -- ** Why a rule's own types did not work out

    instralError e = case e of
      I.Clash si want got ->
        fault TypesDiffer
          ( ruleSite si
              ++ [ is TheExpected (ARuleType (renderTy want))
                 , is TheFound (ARuleType (renderTy got))
                 ]
          )
      I.Occurs si t ->
        fault OccursCheck (ruleSite si ++ [is TheType (ARuleType (renderTy t))])
      I.BindsNothing si g ->
        fault BlockShapeWrong (ruleSite si ++ [is TheWord (name g)])
      I.AnnotationTooGeneral si t ->
        fault RuleTypeWrong (ruleSite si ++ [is TheType (ARuleType (renderTy t))])
      I.SignatureUnanswered g i ->
        fault SignatureUnanswered [is TheRule (name g), is TheCount (ACount i)]
      I.NotCallable si w ->
        fault NoSuchInstruction (ruleSite si ++ [is TheWord (AName w)])
      I.Undefined si w _ _ ->
        fault NoSuchInstruction (ruleSite si ++ [is TheWord (AName w)])
      I.TextNotTextual si t ->
        fault WrongKindOfThing
          ( ruleSite si
              ++ [is TheWanted (AWanted SomeText), is TheType (ARuleType (renderTy t))]
          )

    -- | Where in a rule a typing fault is.
    --
    -- **Parts and not a 'Spot'**: a rule's own sites are a rule and a number —
    -- which test, which instruction, which parameter — and a pane that can
    -- reach the rule by name wants it as a name.
    ruleSite si = case si of
      I.InHead g i -> [is TheRule (name g), is TheTest (ALine (i + 1))]
      I.InBody g i -> [is TheRule (name g), is TheInstruction (ALine (i + 1))]
      I.InPattern g i -> [is TheRule (name g), is TheParameter (ACount (i + 1))]
      I.InSignature g a -> [is TheRule (name g), is TheCount (ACount a)]

    -- ** A warning

    warningView w = case w of
      E.VacuousBinder k g prod x -> ABinderBindsNothing (block k) g prod x
      E.MetavariableNotOpen k g prod x l -> AMetavariableNotOpen (block k) g prod x l
      E.TokenClassNotOpen k g prod x l -> ATokenClassNotOpen (block k) g prod x l
      E.NameShadows new old -> ANameShadows (spelledIn sp new) (spelledIn sp old)
      E.ProofShadows new old -> AProofShadows (spelledIn sp new) (spelledIn sp old)
      E.PublicConsultIdle m -> APublicConsultIdles m
      E.PublicImportUnlisted m ms -> APublicImportUnlisted m ms
      E.PublicIdleAtPrompt m -> APublicIdlesAtThePrompt m
      E.UnprimeableClass k g cls -> AClassCannotBePrimed (block k) g cls

-- | Display names for a context's variables, the same fold
-- 'Thena.Render.envOf' and 'Thena.View.envAt' use — so a view agrees with them
-- about what a variable is called.
envOf :: Context -> Env
envOf = foldl add []
  where
    add e entry =
      let (v, hint) = case entry of
            Hypothesis x (Ident h) _ -> (x, h)
            Definition x (Ident h) _ _ -> (x, h)
       in (v, freshen hint e) : e
