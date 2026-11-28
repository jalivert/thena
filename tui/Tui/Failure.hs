-- | **Why a declaration did not go in, as lines of a fold** — `~8btbp`, closed
-- by MS12 phase 325.
--
-- **This module is why the modules pane no longer reaches into
-- 'Thena.Render'.** An unfinished item carried its reason as a whole
-- 'Thena.Driver.Response' until that phase, and @renderResponse@ was the only
-- thing that rendered one — so a pane drawing a ⚠️ module's fold was calling the
-- prompt's text renderer, against this track's own rule that panes render
-- through the views. The engine narrowed the field to a
-- 'Thena.Driver.NotDone' and gave it a view; this turns that view into rows.
--
-- **Every function here takes plain data and returns plain lines**, the same
-- discipline as "Tui.Panes": no 'Thena.Driver.Session', no terminal, so the
-- drawing suite can hold all of it to its text.
--
-- **The glyph and the emphasis come from 'Nature' and from nothing else** —
-- `.jalivert/FRONTEND.md`, /Why a declaration did not go in/. Three of the four
-- natures are not faults: an item sitting on a question or out of fuel can go
-- on, a term the kernel accepted and the session's trust level did not is a
-- setting one word from changing, and @:abandon@ is the user's own act. **A hue
-- is not taken, because 'Tui.Theme.Theme' has no error colour and inventing one
-- is a colour decision of his**; what is taken is the theme's own
-- ordinary-versus-dim, which is how this TUI says /in play/ everywhere else.
module Tui.Failure
  ( StopLine (..)
  , stopLines
  , refusalLines
  , positionSuffix
  , placeSuffix
  , placeText
  , natureGlyph
  , natureIsFault
  , refusedClaimsShown
  ) where

import Data.List (intercalate, stripPrefix)
import Data.Maybe (listToMaybe, mapMaybe)

import Thena.View.Failure
  ( Block (..)
  , Blocked (..)
  , FaultKind (..)
  , FaultView (..)
  , Form (..)
  , Nature (..)
  , PartView (..)
  , Piece (..)
  , Pos (..)
  , Role (..)
  , Side (..)
  , Spot (..)
  , Stage (..)
  , StopView (..)
  , WarningView (..)
  , Wanted (..)
  , Why (..)
  )
import Thena.View.Trust
  ( ClaimView (..)
  , TrustClass (..)
  , TrustLevel (..)
  , TrustSite (..)
  , TrustView (..)
  )

import Tui.Render (displayText, mark)

-- | One line of the fold, and how deep it sits inside it.
--
-- **A depth and not an indent string**, because the pane adds its own module
-- indent in front: a module three deep in the import tree has its fold stepped
-- in by six columns before any of this is laid out.
data StopLine = StopLine
  { slDepth :: Int
    -- ^ 0 is the fold's own first line — what became of the item. Everything
    -- else is 1 or more.
  , slText :: String
  , slPlace :: Bool
    -- ^ __this line is a place and nothing else__ — @path:line:col@, no label
    -- and no sentence (`~29733`, and MS12 phase 349 is what made it matter:
    -- every fault about a rule file carries one now). **A pane draws it at its
    -- own margin and ignores 'slDepth'**, because a path is only useful whole
    -- and the fold's indent is what breaks it: 'Tui.Panes.paneWrapped' splits
    -- a word longer than its pane mid-word, so two columns too many turn a
    -- destination into two fragments. The fault it belongs to is the line above
    -- it.
  }
  deriving (Eq, Show)

-- | A line of the fold that is prose, at the depth it sits at.
line_ :: Int -> String -> StopLine
line_ d t = StopLine { slDepth = d, slText = t, slPlace = False }

-- | **The fold for one unfinished item**, given what it would have declared.
--
-- The first line says what became of it and carries the nature's glyph; under
-- it come the fault or the stop, then what the run said on its way, then its
-- warnings — **the prompt's own order**, so the pane and @:show o@ do not
-- disagree about which came first.
stopLines :: String -> StopView -> [StopLine]
stopLines what sv =
  line_ 0 (natureCell (stopViewNature sv) <> " " <> became what sv)
    : concatMap (whyLines 1) [stopViewWhy sv]
    <> [line_ 1 ("it said: " <> oneLine m) | m <- stopViewSaid sv]
    <> [line_ 1 (warningText w) | w <- stopViewWarned sv]

-- | **The fold for a refused rule file** — MS12 phase 348, @~cjznk@.
--
-- **'stopLines' without its first line, and that is the whole difference.** A
-- module's row names the module and the fold's first line names the
-- /declaration/ that did not go in — two different things, so both are said.
-- A rule file has nothing inside it to name: the file is the item, the row
-- above already carries its path and its ❌, and a headline here would say
-- @it did not go in@ under a row that has just said so.
--
-- **Depth 0, because this is the fold's own top level.** The pane steps every
-- line in by its own indent either way.
--
-- **Nothing is said and nothing is warned on one of these** —
-- 'Thena.View.Failure.displayRuleFile' leaves both empty, because a load that
-- is refused never reaches a rule — so this is the faults and no more. If that
-- ever stops being true the two lists belong here, in 'stopLines'\' order.
refusalLines :: StopView -> [StopLine]
refusalLines sv = whyLines 0 (stopViewWhy sv)

-- | What became of the item, as the fold's first line says it.
--
-- **Read off 'stopViewWhy' and not off 'stopViewNature'**, although the two
-- agree: the nature is four values and this is a sentence, and /ran out of
-- fuel/ and /is waiting for an answer/ are both 'Stopped'.
became :: String -> StopView -> String
became what sv = case stopViewWhy sv of
  NothingWrong -> what <> " stopped with nothing to say"
  Yielding _ -> what <> " is standing still:"
  Faulty _ -> what <> " did not go in:"
  Asked _ -> what <> " is waiting for an answer:"
  OutOfFuel spent ->
    what <> " ran out of fuel after " <> show spent <> " instructions"
  Trusting tv -> what <> " is not trusted at " <> levelText (trustViewLevel tv) <> ":"
  WasGivenUp -> "you abandoned " <> what

-- | The stop itself, under the first line.
whyLines :: Int -> Why -> [StopLine]
whyLines d why = case why of
  NothingWrong -> []
  Yielding msg -> [line_ d (oneLine msg)]
  Faulty fs -> concatMap (faultLines d) fs
  Asked ask -> [line_ d (oneLine ask)]
  OutOfFuel _ -> []
  Trusting tv -> trustLines d tv
  WasGivenUp -> []

-- | **The place a row's file line points at, once there is one — `~hcr2d`,
-- MS12 phase 334.** 'Nothing' draws nothing: a module with nothing wrong has
-- no unfinished item to read a position off, and an item the engine could not
-- place in any file (one handed over as items, or one a grammar generated)
-- carries no 'Pos' either.
--
-- **@:line:col@, not a sentence**, so a pane can append it straight onto the
-- file path already drawn beside the row — @path@ plus this is the whole of
-- the destination, the same shape this project's own documents use to point
-- at a line.
positionSuffix :: Maybe Pos -> String
positionSuffix Nothing = ""
positionSuffix (Just p) = ":" <> show (posLine p) <> ":" <> show (posColumn p)

-- | **A place a pane row could take you, spelled so that the terminal can take
-- you there** — `~8rn4d`, and **his ruling of 2026-11-23**: the TUI does not
-- open a clause, the terminal emulator does. He runs it from a Zed terminal,
-- which detects a path in a program's output and opens the file at the line it
-- detects, so the whole affordance is a row that prints a path the emulator can
-- resolve. Two leading spaces, then @path:line:col@, and @\"\"@ for a clause
-- that is in no file — the synthetic rule a typed line is wrapped in.
--
-- **The path is spelled against the launch directory and that is not cosmetic.**
-- 'Thena.View.Choices.altViewPath' is absolute by design, a pane not being a
-- transcript — but an absolute path here runs to seventy-odd characters against
-- a pane column measured at fifty, and 'paneWrapped' breaks a word longer than
-- its pane mid-word, which leaves two fragments and no path. Relative, it is
-- @rules\/standard.thena.rules:80@ and survives whole onto a continuation line.
placeSuffix :: FilePath -> Maybe FilePath -> Maybe Pos -> String
placeSuffix cwd mp at = case placeText cwd mp at of
  "" -> ""
  t -> "  " <> t

-- | **The same place with nothing in front of it**, for a row that is a place
-- and nothing else — `~29733`'s shape, which 'Tui.Panes.PaneRow''s @Place@
-- draws at the pane's own margin. 'placeSuffix' is this plus the two spaces
-- that separate it from a name it follows on one line.
--
-- **Which of the two a pane wants is decided by the row's length, not by
-- taste.** A place may follow a name on one line only where the whole row fits
-- the pane — the @choices@ pane's headings, measured at fifty columns — because
-- 'Tui.Panes.paneWrapped' breaks a word longer than its pane mid-word and half
-- a path resolves to nothing. Everything longer puts the place on its own row.
placeText :: FilePath -> Maybe FilePath -> Maybe Pos -> String
placeText _ Nothing _ = ""
placeText cwd (Just p) at = pathUnder cwd p <> positionSuffix at

-- | A path spelled against a directory it is inside, and left alone otherwise.
--
-- **By hand and not @System.FilePath@'s @makeRelative@**, which answers the
-- path unchanged for anything not under the base anyway and would be the only
-- reason this module needed @filepath@.
pathUnder :: FilePath -> FilePath -> FilePath
pathUnder cwd p = maybe p id (stripPrefix (cwd <> "/") p)

-- ---------------------------------------------------------------------------
-- A fault

-- | One fault: its headline, its remaining parts a line each, and the fault it
-- wraps indented under it.
--
-- **The wrapped one is introduced by /because/.** Indentation alone would make
-- it read as another part of the outer fault, which is the one thing the two
-- are not — @that term has no type@ / @because not in scope: nonesuch@.
faultLines :: Int -> FaultView -> [StopLine]
faultLines d fv =
  line_ d headline
    : [line_ (d + 1) (partText p) | p <- labelled]
    <> [ StopLine { slDepth = d, slText = pieceText (partViewPiece p), slPlace = True }
       | p <- places
       ]
    <> case faultViewInside fv of
      Nothing -> []
      Just inner -> because (faultLines (d + 1) inner)
  where
    (headline, rest) = said (faultViewKind fv) (faultViewParts fv)
    -- | **A PLACE GETS A ROW OF ITS OWN, BARE** — `~29733`, and since MS12
    -- phase 349 (@~8w6qw@) every fault about a rule file carries one, so this
    -- decides whether the affordance his ruling `~8rn4d` asked for works at
    -- all: the TUI prints a place and the terminal emulator opens it.
    --
    -- **A path is only useful whole**, and 'Tui.Panes.paneWrapped' breaks a
    -- word longer than its pane mid-word on purpose — right for a module path,
    -- wrong for a destination, which becomes two fragments and no path. So the
    -- row carries nothing in front of it: no @at  @ label, which is four
    -- columns of a role nobody needs told, and 'slPlace' tells the pane to
    -- draw it at its own margin rather than at this depth. Measured in the
    -- modules pane at 200 columns, whose content is thirty: at the fault\'s
    -- depth @notatype.thena.rules:3:1@ broke after @:3@, and at the margin all
    -- five of `~8w6qw`\'s cases fit whole.
    isPlace p = partViewRole p == ThePlace
    places = filter isPlace rest
    labelled = filter (not . isPlace) rest
    because ls = case ls of
      [] -> []
      sl : more -> sl { slText = "because " <> slText sl } : more

-- | A fault's headline, and the parts it did not absorb.
--
-- **A kind says what went wrong and never what it went wrong about** — the
-- engine's rule — so the parts carry the subject, and a headline with no
-- subject in it reads as a label rather than a sentence: /not in scope/ with
-- @nonesuch@ on the line below is worse in a narrow fold than what the prompt
-- has always printed. So **one part is allowed onto the headline**, the one
-- whose role the kind is about, and the rest are drawn under it.
said :: FaultKind -> [PartView] -> (String, [PartView])
said k ps = case subject of
  Just p -> (wordsBefore w <> pieceText (partViewPiece p), without (partViewRole p))
  Nothing -> (wordsAlone w, ps)
  where
    w = kindWords k
    subject =
      listToMaybe (mapMaybe (\r -> listToMaybe (at r)) (wordsSubject w))
    at r = [p | p <- ps, partViewRole p == r]
    -- | **The role and not the part**, so a kind that absorbed /the name/ does
    -- not then draw a second name under it.
    without r = [p | p <- ps, partViewRole p /= r]

-- | How a kind is said: alone, with a subject in front of it, and which roles
-- can be that subject, in order of preference.
data Words = Words
  { wordsAlone :: String
  , wordsBefore :: String
  , wordsSubject :: [Role]
  }

-- | A kind no part can be the subject of.
plain :: String -> Words
plain s = Words s "" []

-- | **What each failure is called, in his vocabulary.** Read off
-- 'Thena.Render' where that module already had words for it, so the pane and
-- the prompt call the same thing by the same name.
kindWords :: FaultKind -> Words
kindWords k = case k of
  -- Names
  NotInScope -> Words "not in scope" "not in scope: " [TheWord, TheVariable, TheName]
  NameAmbiguous -> Words "that name is ambiguous" "ambiguous: " [TheWord, TheLanguage, TheName]
  NoSuchNamespace -> Words "no such namespace" "no such namespace: " [TheNamespace]
  NameAlreadyDeclared -> Words "already declared" "already declared: " [TheName, TheRule]
  NameRepeated -> Words "declared twice in one declaration" "declared twice: " [TheName, TheWord]
  NameReserved -> Words "that name is reserved" "a reserved name: " [TheWord, TheName]
  NotAName -> Words "that cannot be a name" "cannot be a name: " [TheText, TheWord]
  UnknownName -> Words "the checker does not know that name" "the checker does not know " [TheName, TheDatatype]
  -- **Not "not in scope", and the difference is not a nicety** (MS12 phase
  -- 360). Nothing was looked up: an identifier's token is its identity, so a
  -- word carrying none names no variable anywhere, and /not in scope/ would
  -- send the author hunting for a binding that no other spelling would have
  -- found either. 'Thena.Render' says it as @is a word and nothing more@.
  WordBindsNothing -> Words "that word names no variable" "a word and nothing more: " [TheWord]
  -- Kinds and counts
  WrongKindOfThing -> Words "something else was wanted" "expected " [TheWanted]
  WrongCount -> plain "the wrong number of them"
  -- Typing
  TermHasNoType -> plain "that term has no type"
  GuessNotOfGoalType -> plain "that is not of the goal's type"
  TypesDiffer -> plain "those types differ"
  NotAType -> Words "that is not a type" "not a type: " [TheDatatype, TheName, TheConstructor]
  NotAFunction -> plain "that is not a function"
  NotAMotive -> plain "that is not a motive"
  UniversesDiffer -> plain "those universes differ"
  Unsaturated -> Words "used with too few arguments" "too few arguments for " [TheName]
  OverApplied -> Words "used with too many arguments" "too many arguments for " [TheName]
  LooseIndex -> Words "a loose index" "loose index " [TheIndex]
  OccursCheck -> plain "that solution mentions the variable it solves"
  ScopeViolation -> plain "that solution would leave the variable's scope"
  NotClosed -> plain "the kernel was handed a term with a free variable"
  AbstractedTooFar -> Words "it binds where its type has no binder" "nothing binds " [TheBinder]
  LevelsUnmet -> plain "the universe constraints have no solution"
  NotStrictlyPositive -> Words "not strictly positive" "not strictly positive: " [TheDatatype]
  -- The development
  NothingToWorkOn -> plain "there is nothing to work on"
  WrongShapeOfGoal -> Words "the goal is not that shape" "the goal is not " [TheWanted]
  CannotMoveThere -> Words "cannot move there" "cannot move there: expected " [TheWanted]
  NoRuleApplies -> Words "no rule applies" "no rule applies: " [TheRule]
  WouldLeaveTheLine -> plain "that would backtrack past the line being worked on"
  NotYetPure -> plain "it still rests on something impure"
  PatternDidNotMatch -> Words "the pattern did not match" "did not match: " [ThePattern]
  NothingReturned -> Words "nothing was returned" "nothing was returned for " [ThePattern]
  NoCallToReturnFrom -> plain "there is no call to return from"
  CaseSurvived -> plain "an impossible case is still standing"
  RecursionNotTied -> plain "the recursion is not tied"
  SpecialisationRefused -> plain "the specialisation was refused"
  EliminationRefused -> plain "the elimination was refused"
  -- Reading what was written
  CouldNotRead -> Words "it could not be read" "could not be read while " [TheStage]
  NoSuchLanguage -> Words "no such language" "no such language: " [TheLanguage]
  NoSuchProduction -> Words "no such production" "no such production: " [TheProduction]
  NoSuchTag -> Words "no such tag" "no such tag: " [TheLanguage]
  TagAmbiguous -> Words "that tag is ambiguous" "an ambiguous tag: " [TheLanguage]
  NotDeclaredAs -> Words "not declared as that" "not declared that way: " [TheConstructor, TheName]
  -- A rule, and a block of instructions
  NoElaborationRule -> Words "no elaboration rule for it" "no elaboration rule for " [TheForm]
  NoSuchInstruction -> Words "no such instruction" "no such instruction: " [TheWord]
  BlockShapeWrong -> Words "that line cannot be run as written" "cannot be run as written: " [TheWord]
  RuleTypeWrong -> Words "the rule's type does not work out" "the type does not work out for " [TheRule]
  SignatureUnanswered -> Words "a signature with no clause" "a signature with no clause: " [TheRule]
  ClauseUnreachable -> Words "that clause is unreachable" "an unreachable clause in " [TheRule]
  NoSuchPrimitive -> Words "no such primitive" "no such primitive: " [TheName]
  PrimitiveWrongShape -> Words "that primitive is declared at the wrong shape" "the wrong shape for " [TheName]
  NoClauseMatched -> Words "no clause matched" "no clause of " [TheRule]
  GrammarRefused -> Words "that block was not admitted" "not admitted: " [TheName]
  TokenClassRefused -> Words "that token class was refused" "token class refused: " [TheName]
  NotATokenType -> plain "a token class cannot be read at that type"
  -- What is wrong inside a refused block — MS12 phase 338. **Most of that tree
  -- lands on the kinds above**, because a kind says what went wrong and never
  -- what it went wrong about; these are the ones only a grammar can say.
  VariableProductionAmbiguous ->
    Words "two productions stand for that class" "two productions stand for " [TheType]
  ClassOwnedTwice -> Words "two languages read that class" "two languages read " [TheType]
  ConstructorUnspelled ->
    Words "a constructor with no production" "no production spells " [TheCandidates]
  MetavariableNotAllowed ->
    Words "a notation block cannot declare a metavariable" "it cannot declare " [TheCandidates]
  ParameterUnspelled ->
    Words "a parameter the notation never writes" "the notation never writes " [TheParameter]
  BindsNothing -> Words "it binds nothing" "binds nothing: " [TheName]
  ScopesDiffer ->
    Words "it is written under different binders" "written under different binders: " [TheName]
  OccurrenceNotAlone ->
    Words "an occurrence is not alone in its production" "not alone in its production: " [TheName]
  NothingToRename -> Words "there would be nothing to rename" "nothing to rename in " [TheName]
  SlotAtAUniverse -> Words "a slot at a universe" "at a universe: " [TheParameter]
  NoConstructorForMetadata -> plain "metadata with no constructor to be about"
  RoleAfterTheGrammar ->
    Words "a role after the grammar is installed" "the grammar is already installed by " [TheLanguage]
  NotQuantified -> Words "it is not quantified" "not quantified: " [TheName]

-- ---------------------------------------------------------------------------
-- A part

-- | A part on its own line: what it plays, then what it is.
partText :: PartView -> String
partText p = roleLabel (partViewRole p) <> "  " <> pieceText (partViewPiece p)

-- | **What a role is called.** Short, because every one of these sits in a
-- pane two columns of indent inside a fold inside a module row.
roleLabel :: Role -> String
roleLabel r = case r of
  TheName -> "the name"
  TheWord -> "the word"
  TheCandidates -> "candidates"
  TheOther -> "and"
  TheExpected -> "expected"
  TheFound -> "found"
  TheTerm -> "the term"
  TheType -> "the type"
  TheTarget -> "the target"
  TheGoal -> "the goal"
  TheVariable -> "the variable"
  TheBinder -> "the binder"
  TheWanted -> "wanted"
  TheSpot -> "where"
  TheStage -> "while"
  TheForm -> "the form"
  TheLevel -> "the level"
  TheRule -> "the rule"
  -- **An arity, so "arity  2" and not "the clause  2"** (MS12 phase 343).
  -- A name alone does not say which callable a refusal is about: @foo\/2@ and
  -- @foo\/4@ are two of them. It rode as a clause number until that phase,
  -- which drew a count as though it located something.
  TheArity -> "arity"
  TheInstruction -> "instruction"
  -- **A place is drawn without this label** — 'faultLines' lifts a 'ThePlace'
  -- part out and gives it a row of its own, bare, because a path is only
  -- useful whole and @clause  @ in front of it cost eight columns of a pane
  -- measured at thirty (`~29733`). The word is here because the role is a
  -- role like any other and a total case is cheaper than a promise that
  -- nothing else ever draws one.
  ThePlace -> "at"
  TheTest -> "test"
  TheChoice -> "choice point"
  ThePattern -> "the pattern"
  TheLanguage -> "the language"
  TheProduction -> "the production"
  TheText -> "the text"
  TheField -> "the field"
  TheIndex -> "the index"
  TheParameter -> "the parameter"
  -- **"the focus" and not "the parameter"** (MS12 phase 358): the focus is the
  -- other half of a rule head, so /the parameter  2/ would point at the side of
  -- the line without the mistake in it. The count is a position of the clause's
  -- @at@ pattern, from 1 — the binder, then the component's sub-terms.
  TheFocus -> "the focus"
  TheMethod -> "the method"
  TheMotive -> "the motive"
  TheConstructor -> "the constructor"
  TheDatatype -> "the datatype"
  TheNamespace -> "the namespace"
  TheHypothesis -> "hypotheses"
  TheCount -> "how many"
  TheBlocker -> "blocked"
  TheBlock -> "the block"
  TheObligations -> "obligations"
  TheClaimed -> "claimed"
  TheActual -> "actually"
  TheSide -> "the side"

-- | What a part is, as one line.
--
-- **Every piece becomes one line and no piece becomes a sentence.** A
-- 'Thena.View.Core.Display' goes through 'Tui.Render.displayText' — the same
-- fold every other pane's text form uses — and 'AText', which is a region of
-- his own writing and may be several lines of it, is collapsed: a pane row is
-- one line and a row carrying a newline would tear the fold.
pieceText :: Piece -> String
pieceText pc = case pc of
  AName n -> n
  ADottedName n -> n
  ANames ns -> intercalate ", " ns
  ATerm d -> displayText d
  AVariable x reach -> x <> mark reach
  ACount n -> show n
  ALine n -> show n
  -- **The whole path and then @:line:col@** (MS12 phase 343) — a part that
  -- is a destination rather than a word. A pane is not a transcript, so it
  -- gets the absolute path the engine hands over rather than the file name
  -- @:choices@ prints at the prompt.
  APlace f at -> f <> positionSuffix (Just at)
  AWanted w -> wantedText w
  ALevel l -> l
  ABlock b -> blockText b
  AStage st -> stageText st
  ASpot sp -> spotText sp
  AForm f -> formText f
  ABlocked b -> blockedText b
  ARuleType t -> t
  APattern t -> t
  AnObligation os -> intercalate ", " os
  AText t -> oneLine t
  ASide sd -> sideText sd

wantedText :: Wanted -> String
wantedText w = case w of
  AList -> "a list"
  APair -> "a pair"
  AnOption -> "an option"
  ALevelNumber -> "a level"
  AWholeNumber -> "a whole number"
  SomeText -> "text"
  AnIdentifier -> "a name"
  ARawTerm -> "a core region"
  ACoreTerm -> "a term"
  ASurfaceTerm -> "a surface term"
  AUniverse -> "a universe"
  ADatatype -> "a datatype"
  AnObjectTerm -> "a term of an object language"
  AHole -> "a hole"
  AGuess -> "a guess"
  AnArgument -> "an argument"
  AnIndex -> "an index"
  AMethod -> "a method"
  AParameter -> "a parameter"
  AMetavariable -> "a metavariable"
  AnEquation -> "an equation"
  AConstructorOf -> "a constructor of it"
  AProduction -> "a production"
  ABinder -> "a binder"
  AFunction -> "a declared function"
  ATokenClass -> "a token class"

stageText :: Stage -> String
stageText st = case st of
  ReadingTheHeader -> "reading the header"
  Lexing -> "lexing"
  LayingOut -> "laying it out"
  Parsing -> "parsing"
  ParsingSurface -> "parsing the surface"
  PairingDeclarations -> "pairing declarations"
  ReadingABlock -> "reading the block"
  Resolving -> "resolving names"

-- | Where inside a term or a development something is.
--
-- **'Within' recurses and the rest do not**, which is the whole of why this is
-- a function and not a table: a spot under a guess is a spot of its own with a
-- route in front of it.
spotText :: Spot -> String
spotText sp = case sp of
  TheWholeThing -> "the whole term"
  InTheDomain x -> "in the domain of " <> x
  UnderTheBinder x -> "under " <> x
  InTheFunction -> "in the function"
  InTheArgument -> "in the argument"
  InTheNthArgument g n -> "in argument " <> show n <> " of " <> g
  InTheNthParameter n -> "in parameter " <> show n
  InTheMotiveOf -> "in the motive"
  InTheNthMethod n -> "in method " <> show n
  InTheNthIndex n -> "in index " <> show n
  InTheTargetOf -> "in the target"
  InTheClaimedType -> "in the claimed type"
  InTheCheckedType -> "in the type it was checked at"
  InTheTrustedBody -> "in the trusted body"
  InTheHole x -> "in the hole " <> x
  InTheTypeOf x -> "in the type of " <> x
  InTheValueOf x -> "in the value of " <> x
  InTheGuessOf x -> "in the guess for " <> x
  InTheNthConstraint n -> "in constraint " <> show n
  Within x inner -> "in the guess for " <> x <> ", " <> spotText inner

formText :: Form -> String
formText f = case f of
  AsAHole -> "a hole"
  AsAGuess -> "a guess"
  AsAConstraint -> "a constraint"

-- | Which side of a judgment's rule something was read on.
--
-- **Above and below the line, which is how he wrote them**, rather than
-- /premises/ and /conclusion/: the block draws a line and the row says which
-- side of it the reading stopped on.
sideText :: Side -> String
sideText sd = case sd of
  ThePremises -> "above the line"
  TheConclusion -> "below the line"

blockText :: Block -> String
blockText b = case b of
  ALanguage -> "a language block"
  AContext -> "a context block"
  AJudgment -> "a judgment block"
  ANotation -> "a notation block"

blockedText :: Blocked -> String
blockedText b = case b of
  ByADeletion -> "by a deletion"
  ByInjectivity -> "by injectivity"
  BySolving -> "by solving"

-- ---------------------------------------------------------------------------
-- Not trusted

-- | **How many refused claims the fold draws before it counts the rest.**
--
-- A fold is small print under a module row and a term the kernel accepted can
-- rest on a long list; this is the same cut the pane already makes on the
-- unfinished items themselves — the first says why and the rest are counted.
refusedClaimsShown :: Int
refusedClaimsShown = 3

-- | The claims the level does not permit.
--
-- **'trustViewRefused' and not a filter over 'trustViewClaims'** — which rung
-- admits which class is the engine's rule, and
-- 'Thena.View.Trust.trustViewRefused' exists so that a frontend does not keep a
-- second copy of it.
trustLines :: Int -> TrustView -> [StopLine]
trustLines d tv =
  [line_ d (claimText c) | c <- take refusedClaimsShown refused]
    <> [ line_ d ("and " <> show (n - refusedClaimsShown) <> " more")
       | n > refusedClaimsShown
       ]
  where
    refused = trustViewRefused tv
    n = length refused

-- | One refused claim: where it is, the two types that /are/ the obligation,
-- and the verdict.
--
-- **Both halves of the pair, because the pair is the obligation** — his
-- observation of 2026-10-05, which is why 'Thena.View.Trust.ClaimView' carries
-- the claimed type and the type the body was really checked at side by side.
claimText :: ClaimView -> String
claimText c =
  where' <> ": " <> displayText (claimViewClaimed c)
    <> " vs " <> displayText (claimViewBody c)
    <> " (" <> classText (claimViewClass c) <> ", " <> siteText (claimViewSite c) <> ")"
  where
    where' = case claimViewRoute c of
      [] -> "written here"
      route -> intercalate " via " route

levelText :: TrustLevel -> String
levelText l = case l of
  NoTrust -> "no trust"
  NoUndischargeableTrust -> "no undischargeable trust"
  AnyTrust -> "any trust"

classText :: TrustClass -> String
classText c = case c of
  Discharged -> "discharged"
  Pending -> "pending"
  Undischargeable -> "can never be met"

siteText :: TrustSite -> String
siteText s = case s of
  AtDefinition -> "at the definition"
  AtUse -> "at the use"

-- ---------------------------------------------------------------------------
-- A warning

-- | A warning the run raised, as one line.
--
-- **Nine of them, typed, and none is a fault** — a warning never stops an item.
-- They are in the fold because the run this fold is of is the only thing that
-- has them for this item.
warningText :: WarningView -> String
warningText w = case w of
  ABinderBindsNothing b g prod x ->
    inBlock b g prod <> x <> " binds nothing"
  AMetavariableNotOpen b g prod word lang ->
    inBlock b g prod <> word <> " is read as a terminal, not as " <> lang <> "'s metavariable"
  ATokenClassNotOpen b g prod word lang ->
    inBlock b g prod <> word <> " is read as a terminal, not as " <> lang <> "'s token class"
  ANameShadows new old -> new <> " shadows " <> old
  AProofShadows new old -> "the proof " <> new <> " shadows " <> old
  APublicConsultIdles m -> "the public consult in " <> m <> " does nothing"
  APublicImportUnlisted m ms ->
    m <> " is imported publicly but not listed: " <> intercalate ", " ms
  APublicIdlesAtThePrompt m -> "public does nothing at the prompt: " <> m
  AClassCannotBePrimed b lang cls ->
    inBlock b lang "" <> "no character extends " <> cls
  ABinderShadows x -> x <> " shadows an earlier binder, and nothing below still refers to it"
  ABinderShadowsReferenced x [] -> x <> " shadows an earlier binder that is still referred to"
  ABinderShadowsReferenced x cs ->
    x <> " shadows an earlier binder that " <> intercalate ", " cs
      <> (if length cs == 1 then " still refers" else " still refer") <> " to"
  where
    inBlock b g prod =
      "in " <> blockText b <> " " <> g
        <> (if null prod then "" else ", production " <> prod)
        <> ": "

-- | The nature's glyph.
--
-- **A fault is ❌, HIS instruction of 2026-11-20**, the same mark a module's
-- own row carries when nothing of it went in — so one symbol means /broken/
-- everywhere in the pane instead of two. It replaced ✗, which was this
-- track's own pick and chosen for being one column.
--
-- **It is safe because it is already declared.** ❌ is U+274C, which
-- 'Tui.Panes.wideGlyphs' has listed since `~8ztt3`: vty's built-in table calls
-- an emoji-presentation code point one column where a terminal spends two, and
-- an undeclared one shoves everything to its right — the neighbouring pane's
-- accent bar included. Declared, it does not. **A new glyph here that is not in
-- that list has to go in it.**
--
-- The other three are plain symbols that both reckonings call one column, so
-- 'natureCell' is what lines them up beside the fault.
natureGlyph :: Nature -> String
natureGlyph n = case n of
  Broken -> "\x274C"
  Stopped -> "\x22ef"
  NotTrusted -> "\x2298"
  GivenUp -> "\x2296"

-- | The nature's glyph **in a two-column cell**, which is what the fold's first
-- line is laid out from.
--
-- **Why a cell and not the glyph**: ❌ is two columns and the other three are
-- one, so without the pad a fold holding both a broken declaration and a
-- stopped one starts their sentences one column apart. Padding a /narrow/ glyph
-- out to the width of a declared wide one is not the thing that failed in
-- `~8ztt3` — that was padding an /undeclared/ wide glyph, where the terminal
-- shoves the pad along with everything else and the shift survives.
natureCell :: Nature -> String
natureCell n = natureGlyph n <> replicate (2 - natureColumns n) ' '

-- | How many columns a nature's glyph takes **once 'Tui.Panes.wideGlyphs' has
-- been declared**, which "Tui.App" does before it makes a vty.
--
-- Stated here rather than measured with @safeWcwidth@ for the reason the
-- drawing suite gives for @markColumns@: @safeWcwidth@ answers for a vty with
-- no table installed and reports one for ❌, which is the state no running
-- TUI is ever in.
natureColumns :: Nature -> Int
natureColumns n = case n of
  Broken -> 2 -- ❌ U+274C, in 'Tui.Panes.wideGlyphs'
  Stopped -> 1
  NotTrusted -> 1
  GivenUp -> 1

-- | **Is this a fault?** The one question the pane's ink turns on: a fault's
-- first line is ordinary ink and the other three natures stay in the fold's
-- dim small print, because nothing is wrong in them.
natureIsFault :: Nature -> Bool
natureIsFault n = n == Broken

-- | Collapse a piece of text to one line.
--
-- **A row carrying a newline tears the fold**, and two of the pieces can hold
-- one: 'AText' is a region of his own writing and a @say@ is whatever a rule
-- printed.
oneLine :: String -> String
oneLine = unwords . words
