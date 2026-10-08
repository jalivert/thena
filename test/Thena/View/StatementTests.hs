-- | Completion over an @instral@ line — Tier A (MS7 phase 137,
-- @.jalivert\/LIVE-OFFERS.md@).
--
-- **The assertion that is the phase is 'narrows'**: after @quantify @ the offer
-- wants a @Name@, and after @quantify x @ it wants a @Core@. That is
-- /"argument 2 wants a @Core@"/ — the thing Tier A was asked for — and it is not
-- a feature layered on the offer, it is what the offer already says, because a
-- slot is a nonterminal named after its type.
--
-- **The other load-bearing one is 'derived'**: every word in
-- 'Thena.Rules.opWords' has a production. That is what says the grammar is read
-- off the op table rather than written beside it, so an op added tomorrow is
-- completable tomorrow with nothing edited here.
module Thena.View.StatementTests (tests) where

import Data.Char (isAlpha)
import Data.List (isInfixOf, isPrefixOf, nub, sort)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Driver (Session)
import Thena.Files (following, startingSession)
import Thena.Driver (commandSummary, oneLine)
import Thena.Instral.Commands (Command (..), commands)
import Thena.Instral.Ops (Pattern (..), Rule (..), signatureOf)
import Thena.Instral.Type (Signature (..), Ty (..))
import Thena.Language.Earley (placeholderChar)
import Thena.Language.Instral (instralRules, operandHead, statementHead)
import qualified Thena.Language.Earley as E
import Thena.Core.Term (GlobalName (..))
import Thena.Render (renderResponse)
import Thena.Rules (RuleBase, baseSignatures, opWords, ruleBase)
import Thena.View (sessionGrammars, sessionRules, statementOfferView)
import Thena.View.Chart (offerAt)
import Thena.View.Chart
  ( BoundView (..)
  , OfferView (..)
  , RecoveryView (..)
  , StuckView (..)
  , SymbolView (..)
  , Written (..)
  )
import Thena.View.Type (TypeView (..))

tests :: TestTree
tests =
  testGroup
    "instral completion (Tier A)"
    [ testCase "a slot says which type it wants, and the next slot a different one" narrows
    , testCase "every op in the table has a production, derived not written" derived
    , testCase "an empty line offers the statement words" empty
    , testCase "a rule in the loaded base may be called" callable
    , testCase "and the arity comes from the signature" arity
    , testCase "a word that is no statement is stuck, not silent" stuck
    , testCase "a half-typed word completes to the words it begins" prefix
    , testGroup "recovery (phase 138)"
        [ testCase "a tagged term literal alone on the line is helped" standalone
        , testCase "and one in a slot that wants something else is helped too" wrongSlot
        , testCase "deeper inside it, the object language answers" deeper
        , testCase "and standing on a box inside it, what may fill the box" inBoxInLiteral
        , testCase "a word after a finished literal is helped, context-free" afterLiteral
        , testCase "and a line that parses is never marked recovered" notRecovered
        ]
    , testGroup ":-commands (phase 142)"
        [ testCase "a bare colon offers every command" everyCommand
        , testCase "a half-typed command word completes" commandPrefix
        , testCase "a command that takes nothing offers nothing, and is not stuck" takesNothing
        , testCase "an argument the chart cannot model is named, not stuck" opaqueArgument
        , testCase ":step offers its words and a number, with no invented head" stepWords
        , testCase "and a half-typed one of those completes too" stepPrefix
        , testCase ":parse offers the languages that are loaded" parseLanguages
        , testCase "every word in the table is a word the driver dispatches" tableDispatches
        , testCase "and the table and :help's list name the same commands" tableMatchesHelp
        , testCase "a statement line is untouched by any of it" statementUntouched
        ]
    , testGroup "a tagged literal is an operand (phase 141)"
        [ testCase "a slot offers the tag, so a literal may be written there" tagOffered
        , testCase "and inside it the object grammar answers, not recovery" insideIsDirect
        , testCase "a finished term offers its closing fence, and a substitution" fenceOffered
        , testCase "the production-named form narrows to that production" namedProduction
        , testCase "no nonterminal this module invented reaches the frontend" noSynthetic
        , testCase "instral's own head cannot collide with a language's" headIsNamespaced
        , testCase "recovery keeps the cases the grammar cannot reach" recoveryRemains
        , testCase "a production name is unique across every loaded grammar" productionNamesAreUnique
        , testCase "a recovered literal's span covers its tag and both fences" literalSpan
        , testCase "including a production-named tag" namedTagSpan
        , testCase "and the span counts from the start of the whole entry" spanShifts
        , testCase "a bare word's span is the word" wordSpan
        ]
    , testGroup "a multi-line entry (phase 140)"
        [ testCase "a binding on the line above puts its name in the offer" boundAbove
        , testCase "and the ; form of the same entry answers identically" bothSeparators
        , testCase "every binding above is there, in written order" severalBindings
        , testCase "a name is offered only where its type may stand" typedToTheSlot
        , testCase "a String binding is a String, not an unsolved variable" settled
        , testCase "a prefix that will not run contributes no names" brokenPrefix
        , testCase "an indented continuation is one instruction, not two" continuation
        , testCase "recovery inside a literal survives a newline" recoveryAfterNewline
        , testCase "and its column counts from the start of the entry" shiftedColumn
        ]
    , testGroup "surface and core are describable (phase 147)"
        [ testCase "a Surface slot offers the surface tag" surfaceTagOffered
        , testCase "and inside it the surface language answers" insideSurface
        , testCase "a Core slot offers the core tag, and not the surface one" coreTagOffered
        , testCase "an object literal is still writable inside a surface region" nestedLiteral
        , testCase "a : command whose argument is a term offers one" commandTerms
        , testCase ":parse names a language and then that language's own term" parseNarrows
        , testCase "a path argument is still opaque, and says so" pathStaysOpaque
        ]
    , testGroup "operand shapes (phase 139)"
        [ testCase "a slot takes a nested call, and only what returns its type" nested
        , testCase "the call's own slot narrows to its parameter" nestedNarrows
        , testCase "a name stands at a ground slot, beside the literal" nameAnywhere
        , testCase "a List slot is written as a list, and the run offers , or ]" listSlot
        , testCase "a pair slot is written as a pair" pairSlot
        ]
    ]

-- | Loaded with the shipped STLC example, so @LC@ is a language that exists.
withLC :: IO Session
withLC = do
  (s0, _) <- startingSession
  let (s1, r) = oneLine s0 ":load examples/01-stlc-syntax.thena"
  case following s1 r of
    Just io -> do (s2, _, _) <- io; pure s2
    Nothing -> pure s1

offerIn :: Session -> String -> OfferView
offerIn s before = statementOfferView s [WrittenText before] []

-- | @elaborate@ wants a @Surface@, and before this phase the only things offered
-- at that slot were an identifier and @(@ for a nested call — **no way to write a
-- surface term at all**, which is where this phase started.
surfaceTagOffered :: IO ()
surfaceTagOffered = do
  s <- withLC
  let o = offeredOptions (offerIn s "elaborate ")
  if ALiteralSymbol "surface`" `elem` o then pure () else
    assertFailure ("elaborate did not offer surface`: " <> show o)
  -- And not the other tag: a @core@ region is a @VRaw@, which is not a @Surface@.
  ALiteralSymbol "core`" `elem` o @?= False

-- | Inside the region the surface language answers for itself, slot by slot —
-- the same thing phase 141 made true for an object language.
insideSurface :: IO ()
insideSurface = do
  s <- withLC
  let opts l = offeredOptions (offerIn s l)
      has l x = if x `elem` opts l then pure () else
        assertFailure (l <> " did not offer " <> show x <> ": " <> show (opts l))
  -- Every way a surface term can open.
  has "elaborate surface`" (ALiteralSymbol "λ")
  has "elaborate surface`" (ALiteralSymbol "let")
  has "elaborate surface`" (ANonterminalSymbol "surface term")
  -- A λ wants a binder, then the arrow.
  has "elaborate surface`\\ x " (ALiteralSymbol "->")
  -- **The binder forms themselves, not a nonterminal naming them** — phase 148
  -- gave the run no singular head, so what comes back is what may be typed.
  has "elaborate surface`\\ x " (AScanSymbol "name")
  has "elaborate surface`\\ x " (ALiteralSymbol "(")
  -- And ascription is offered where it is legal and nowhere it is not.
  has "elaborate surface`x " (ALiteralSymbol ":")
  ALiteralSymbol ":" `elem` opts "elaborate surface`x : y " @?= False
  -- A finished term offers the closing fence, and the ways to go on.
  has "elaborate surface`(f a) " (ALiteralSymbol "`")
  has "elaborate surface`(f a) " (ALiteralSymbol ":")
  -- Nothing is stuck anywhere along the way.
  [ l | l <- [ "elaborate surface`", "elaborate surface`\\ x ", "elaborate surface`(f a) " ]
      , Just _ <- [offeredStuck (offerIn s l)] ] @?= []

-- | A @Core@ slot gains @core\`@ and keeps every object tag it had.
coreTagOffered :: IO ()
coreTagOffered = do
  s <- withLC
  let o = offeredOptions (offerIn s "fill ")
  [ x | x <- [ALiteralSymbol "core`", ALiteralSymbol "LC`"], x `notElem` o ] @?= []
  ALiteralSymbol "surface`" `elem` o @?= False
  -- And the development calculus answers inside it, including the forms only it
  -- has: a claim's @?@, and a binder that must carry its type.
  let o' = offeredOptions (offerIn s "fill core`let ")
  ALiteralSymbol "?" `elem` o' @?= True

-- | **Three languages deep, through one chart**: a statement, a surface region
-- inside its slot, an object literal inside that.
nestedLiteral :: IO ()
nestedLiteral = do
  s <- withLC
  offeredStuck (offerIn s "elaborate surface`LC`") @?= Nothing
  let o = offeredOptions (offerIn s "elaborate surface`LC`")
  ANonterminalSymbol "LC" `elem` o @?= True

-- | The @:@-commands whose argument is a term now offer one. **Which language is
-- the dispatch arm's**: @:core@ reads a development-calculus term, @:infer@ a
-- surface one, or a cornered core one.
commandTerms :: IO ()
commandTerms = do
  s <- withLC
  let o l = offeredOptions (offerIn s l)
  ANonterminalSymbol "core term" `elem` o ":core " @?= True
  ANonterminalSymbol "surface term" `elem` o ":infer " @?= True
  ANonterminalSymbol "core term" `elem` o ":convert " @?= True
  -- **Corners are not offered anywhere** — his instruction, 2026-10-01. The
  -- cornered @:infer@ still runs; it is not advertised, so nothing new points at
  -- a notation that is going away (@AGENDA.md@ 98).
  [ l | l <- [":infer ", ":core ", "fill ", "fill core`"]
      , ALiteralSymbol "⌜" `elem` o l || ALiteralSymbol "[|" `elem` o l ] @?= []

-- | @:parse@ takes a language and then a term of **that** language, which is one
-- argument shape and not two: the second depends on the first.
parseNarrows :: IO ()
parseNarrows = do
  s <- withLC
  [ w | ALiteralSymbol w <- offeredOptions (offerIn s ":parse ") ] @?= ["LC", "Ty"]
  ANonterminalSymbol "LC" `elem` offeredOptions (offerIn s ":parse LC ") @?= True
  ANonterminalSymbol "Ty" `elem` offeredOptions (offerIn s ":parse LC ") @?= False

-- | **What this phase did not make describable stays honest.** A path is still
-- the opaque nonterminal — /something goes here and I cannot list it/ — and the
-- line is not stuck.
pathStaysOpaque :: IO ()
pathStaysOpaque = do
  s <- withLC
  offeredOptions (offerIn s ":load ") @?= [ANonterminalSymbol "instral:Argument"]
  offeredStuck (offerIn s ":load ") @?= Nothing

-- | **The gap this found.** A statement word is a literal and the chart matches
-- one all or nothing, so before phase 138 @att@ answered nothing at all while
-- @attack@ answered — prefix completion, the most ordinary thing a prompt does,
-- had never worked.
prefix :: IO ()
prefix = do
  s <- fst <$> startingSession
  let words' o = [ w | ALiteralSymbol w <- offeredOptions o ]
  words' (offerIn s "att") @?= ["attack"]
  if "goto" `elem` words' (offerIn s "go") then pure () else
    assertFailure ("go did not offer goto: " <> show (words' (offerIn s "go")))

-- | **His requirement, first half**: open the TUI, load the language, type
-- @LC\`@ into an empty prompt, get help.
standalone :: IO ()
standalone = do
  s <- withLC
  let o = offerIn s "LC`"
  case offeredRecovered o of
    Just (RecoveryView _ _ (Just "LC") _) -> pure ()
    other -> assertFailure ("expected recovery inside LC, got " <> show other)
  if null (offeredOptions o) then assertFailure "recovered, but offered nothing" else pure ()

-- | **His requirement, second half**: a literal written where one may not stand is
-- helped anyway — marked, so the frontend can say it will not run.
--
-- **The line changed at MS7 phase 141 and the premise with it.** It was
-- @goto LC\`@, on the stated grounds that @goto@ wants a @Core@ and a literal is
-- not one. A literal /is/ a @Core@ — @Thena.Rules@ resolves one to a @VTerm@ — so
-- since 141 put literals in the grammar that line parses, is answered directly and
-- reaches the machine. @say@ is the honest case: it wants a @String@, a literal
-- cannot be one, and the offer has to fall back to recovery to say anything.
wrongSlot :: IO ()
wrongSlot = do
  s <- withLC
  let o = offerIn s "say LC`"
  case offeredRecovered o of
    Just (RecoveryView _ _ (Just "LC") _) -> pure ()
    other -> assertFailure ("expected recovery inside LC, got " <> show other)
  if null (offeredOptions o) then assertFailure "recovered, but offered nothing" else pure ()

deeper :: IO ()
deeper = do
  s <- withLC
  let o = offerIn s "fill LC`( "
  -- The offers here are LC's own productions, not instral's.
  if ALiteralSymbol "\955" `elem` offeredOptions o then pure ()
    else assertFailure ("expected LC's own lambda among " <> show (offeredOptions o))

-- | **The tui track's finding, 2026-09-30** (@.jalivert\/REPORT.md@): stand on a
-- placeholder that is inside a tagged term literal and the dropdown was empty.
--
-- The cause was not in recovery. @recover@ has to flatten the line to a
-- @String@ to get the offsets @tokensView@ works in, so the box reaches
-- 'Thena.View.Chart.offerAt' as a character inside a 'WrittenText' — and
-- 'Thena.View.Chart.offerAt' read the /run/ to decide the cursor was in the
-- box. It therefore answered about what may stand beside a box, and @abs@ has
-- no room beside its type slot, so the answer was nothing at all.
--
-- 'Thena.View.Chart.runs' normalises the two forms, which is where the fix
-- belongs: the boundary already says they are one thing.
inBoxInLiteral :: IO ()
inBoxInLiteral = do
  s <- withLC
  let box = [placeholderChar]
      o = statementOfferView s
            [WrittenText (":infer LC`( \955 " <> box <> " : ")]
            [WrittenText (box <> " . " <> box <> " )`")]
  offeredReplaces o @?= True
  if ANonterminalSymbol "Ty" `elem` (offeredOptions o <> offeredWanted o) then pure ()
    else assertFailure ("expected Ty among " <> show (offeredOptions o, offeredWanted o))
  if null (offeredProductions o)
    then assertFailure "expected Ty's own productions to be offerable into the box"
    else pure ()

afterLiteral :: IO ()
afterLiteral = do
  s <- withLC
  let o = offerIn s "LC`x` atta"
  case offeredRecovered o of
    Just (RecoveryView _ "atta" Nothing _) -> pure ()
    other -> assertFailure ("expected a bare-word recovery of atta, got " <> show other)
  [ w | ALiteralSymbol w <- offeredOptions o ] @?= ["attack"]

notRecovered :: IO ()
notRecovered = do
  s <- fst <$> startingSession
  offeredRecovered (offerIn s "quantify x ") @?= Nothing

offerOf :: String -> IO OfferView
offerOf before = do
  s <- fst <$> startingSession
  pure (statementOfferView s [WrittenText before] [])

wants :: OfferView -> Ty -> Bool
wants o t = ANonterminalSymbol (operandHead t) `elem` offeredOptions o

-- | **Tier A, in one test.** @quantify :: Name -> Core -> ()@, so the first slot
-- wants a 'TName' and the second a 'TCore' — and the offer moves between them as
-- the line is typed, without anything being told where the cursor is beyond the
-- text itself.
narrows :: IO ()
narrows = do
  first  <- offerOf "quantify "
  second <- offerOf "quantify x "
  (wants first TName, wants first TCore) @?= (True, True)
  -- The point: once the Name is supplied, the Name slot is gone and only the
  -- Core slot remains. A grammar that did not carry types could not say this.
  (wants second TName, wants second TCore) @?= (False, True)

-- | The grammar is a reading of 'Thena.Rules.opWords', so nothing in it is a
-- second copy that can drift.
derived :: IO ()
derived = do
  s <- fst <$> startingSession
  let rs      = instralRules (sessionGrammars s) (sessionRules s)
      heads   = [ w | r <- rs, E.ruleHead r == statementHead
                    , E.Literal w : _ <- [E.ruleBody r] ]
      missing = [ w | (w, _) <- opWords, w `notElem` heads ]
  missing @?= []

empty :: IO ()
empty = do
  o <- offerOf ""
  case [ w | ALiteralSymbol w <- offeredOptions o ] of
    [] -> assertFailure "an empty line offered no statement word at all"
    ws -> if "quantify" `elem` ws && "attack" `elem` ws then pure () else
            assertFailure ("expected an op and a rule among " <> show (take 12 ws))

-- | A rule of the shipped base is a statement too — @attack@ is a rule, not an
-- op, and 'Thena.Rules.allCallable' is where it comes from.
callable :: IO ()
callable = do
  o <- offerOf ""
  if ALiteralSymbol "attack" `elem` offeredOptions o then pure ()
    else assertFailure "the shipped base's own rules are not offered"

-- | An op's arity is read from its signature, so a nullary op offers nothing
-- after it and a binary one offers two slots' worth.
arity :: IO ()
arity = do
  let Signature ps _ = signatureOf (opOf "unify")
  length ps @?= 2
  o <- offerOf "unify "
  offeredRest o @?= Just [ANonterminalSymbol (operandHead TCore)
                         , ANonterminalSymbol (operandHead TCore)]
  where
    opOf w = case lookup w opWords of
      Just op -> op
      Nothing -> error "unify is not in the op table"

-- | Phase 134's answer composes with this one for free: a line that is no
-- statement has nothing at the cursor, and says where it gave out instead of
-- being silent.
stuck :: IO ()
stuck = do
  o <- offerOf "zzz "
  case offeredStuck o of
    Nothing -> assertFailure "a nonsense word offered nothing and explained nothing"
    Just (StuckView at expected) -> do
      at @?= 0
      if null expected then assertFailure "stuck with nothing expected" else pure ()
      offeredOptions o @?= []

-- | **The phase's own assertion.** @( word … )@ at a slot is
-- 'Thena.Instral.Concrete.RawNested', which resolution hoists into
-- @RhsOp (RawOp word …)@ — the same dispatch a top-level statement goes
-- through. So what may be called inside a @Core@ slot is every form whose
-- /result/ is @Core@, and nothing else.
--
-- @app-head@ is the control and it is the one that matters: it is an op, it is
-- offered at the start of a line, and its result is @Surface@ — so it must not
-- appear here. Checked against 'signatureOf' rather than against a list written
-- out, so the assertion is maintained by different code from the code it checks.
nested :: IO ()
nested = do
  s <- withLC
  let opened = offerIn s "fill "
  if ALiteralSymbol "(" `elem` offeredOptions opened then pure ()
    else assertFailure ("expected a nested call to be offerable: " <> show (offeredOptions opened))
  let inside = [ w | ALiteralSymbol w <- offeredOptions (offerIn s "fill ( ") ]
      -- **Both tables, because a word may live in either.** @fresh-universe@ is
      -- no op at all — it is a rule the standard base declares as returning a
      -- @Core@ — and a first draft of this test failed on it while the grammar
      -- was right. A statement word is whatever the op table or a loaded base
      -- says it is, and so is a nested call's.
      resultOf w =
        [ r | (w', op) <- opWords, w' == w, let Signature _ r = signatureOf op ]
          ++ [ r | b <- sessionRules s, (w', Signature _ r) <- baseSignatures b, w' == w ]
  [ w | w <- inside, Just TCore `notElem` resultOf w ] @?= []
  if "goal" `elem` inside && "typeof" `elem` inside then pure ()
    else assertFailure ("expected goal and typeof among " <> show inside)
  if "app-head" `elem` inside
    then assertFailure "app-head returns Surface and must not be callable at a Core slot"
    else pure ()

-- | Inside the call, the slot is the /called/ form's parameter, not the outer
-- one's — which is the same narrowing 'narrows' asserts one level up.
nestedNarrows :: IO ()
nestedNarrows = do
  s <- withLC
  -- @typeof : Core -> Core@, so its own slot wants a Core.
  let o = offerIn s "fill ( typeof "
  if ANonterminalSymbol "Operand:Core" `elem` offeredOptions o then pure ()
    else assertFailure ("expected Operand:Core inside the call: " <> show (offeredOptions o))
  -- And with the argument written, the call wants closing and nothing else.
  [ w | ALiteralSymbol w <- offeredOptions (offerIn s "fill ( typeof x ") ] @?= [")"]

-- | A local bound earlier in the body stands at any slot whatever its type, so
-- the name class is not a fallback for the types with no literal — it belongs at
-- every slot, beside whatever literal the type does have.
nameAnywhere :: IO ()
nameAnywhere = do
  s <- withLC
  let at b = offeredOptions (offerIn s b)
  -- @say : String -> ()@: the string literal class *and* a name.
  if AScanSymbol "name" `elem` at "say " then pure ()
    else assertFailure ("expected a name at a String slot: " <> show (at "say "))
  if AScanSymbol "string" `elem` at "say " then pure ()
    else assertFailure ("expected the string class too: " <> show (at "say "))

-- | A base that declares a @List Core@ parameter, which nothing shipped does —
-- **the measurement this phase rests on**: no op in the table and no signature in
-- @rules\/standard.thena.rules@ mentions a list, a pair or an option parameter, so
-- the shapes have no shipped caller and a fixture is the only way to exercise
-- them. Built for the principled implementation, per his MS6\/MS7 exception.
fixture :: [(String, Signature)] -> [String] -> RuleBase
fixture sigs names =
  ruleBase "fixture" Nothing "" sigs []
    [ Rule (GlobalName nm) [PWild] [] [] | nm <- names ]

askIn :: Session -> RuleBase -> String -> [SymbolView]
askIn s b before =
  offeredOptions
    (offerAt (instralRules (sessionGrammars s) (sessionRules s ++ [b])) (E.StartAt statementHead)
       [WrittenText before] [])

listSlot :: IO ()
listSlot = do
  s <- withLC
  let b = fixture [("takes-list", Signature [TList TCore] Nothing)] ["takes-list"]
      words' before = [ w | ALiteralSymbol w <- askIn s b before ]
  -- The list opens, and a name still stands there because a local may hold one.
  if ALiteralSymbol "[" `elem` askIn s b "takes-list " then pure ()
    else assertFailure ("expected [ at a List slot: " <> show (askIn s b "takes-list "))
  -- **Right-recursive on purpose**: standing after one element the item is
  -- @Elements -> Operand . "," Elements@, so both the comma and the close come
  -- back — which is what a frontend needs to draw after @[x@.
  words' "takes-list [ x " @?= ["]", ","]
  -- And the elements are the element type's operands, not the list's.
  if ANonterminalSymbol "Operand:Core" `elem` askIn s b "takes-list [ " then pure ()
    else assertFailure ("expected Operand:Core inside the list: " <> show (askIn s b "takes-list [ "))

pairSlot :: IO ()
pairSlot = do
  s <- withLC
  let b = fixture [("takes-pair", Signature [TPair TName TCore] Nothing)] ["takes-pair"]
      words' before = [ w | ALiteralSymbol w <- askIn s b before ]
  words' "takes-pair " @?= ["("]
  words' "takes-pair ( x " @?= [","]
  words' "takes-pair ( x , y " @?= [")"]

-- | **The case the phase exists for.** @h = here@ then @goto @ is one entry, @h@
-- is in scope on the second line, and before this phase the offer came back stuck
-- with nothing at all.
boundAbove :: IO ()
boundAbove = do
  s <- withLC
  let o = offerIn s "h = here\ngoto "
  offeredStuck o @?= Nothing
  offeredBound o @?= [BoundView "h" ACore]

-- | The offside rule and a written @;@ separate instructions equally, so the two
-- spellings of one entry must answer the same. **They did not**: an explicit @;@
-- is a character of the text and the instruction begins after it, while the
-- layout pass's inserted separator has none and sits where the next instruction
-- starts. Caught here, not by reading the code.
bothSeparators :: IO ()
bothSeparators = do
  s <- withLC
  let a = offerIn s "h = here\ngoto "
      b = offerIn s "h = here ; goto "
  (offeredBound b, offeredStuck b) @?= (offeredBound a, Nothing)
  offeredOptions b @?= offeredOptions a

severalBindings :: IO ()
severalBindings = do
  s <- withLC
  offeredBound (offerIn s "h = here\ng = goal\ngoto ")
    @?= [BoundView "h" ACore, BoundView "g" ACore]

-- | **Filtered by the engine, not by the frontend.** @m@ holds a @String@, so it
-- is offered at @say@'s slot and not at @goto@'s, which wants a @Core@.
typedToTheSlot :: IO ()
typedToTheSlot = do
  s <- withLC
  offeredBound (offerIn s "m = \"hi\"\nsay ") @?= [BoundView "m" AString]
  offeredBound (offerIn s "m = \"hi\"\ngoto ") @?= []

-- | **The ordering constraint inside the type checker.** 'Thena.Instral.Infer'
-- defers a text literal and pins its variable in @settleText@, at the very end —
-- so a type read out before settling would say @a@ where the entry plainly wrote
-- a @String@. This is the assertion that says the read happens after.
settled :: IO ()
settled = do
  s <- withLC
  [ boundType b | b <- offeredBound (offerIn s "m = \"hi\"\nsay ") ] @?= [AString]

-- | A prefix the system would refuse contributes nothing, rather than names read
-- out of code that will not run. @say 3@ is ill-typed — @say@ wants a @String@ —
-- so the binding below it is not reported even though it reads.
brokenPrefix :: IO ()
brokenPrefix = do
  s <- withLC
  let o = offerIn s "say 3\nh = here\ngoto "
  offeredBound o @?= []

-- | **Not every newline starts an instruction.** A line indented past the entry
-- continues the one above, so this is one statement and there is nothing bound.
continuation :: IO ()
continuation = do
  s <- withLC
  let o = offerIn s "say\n  "
  offeredBound o @?= []
  offeredOptions o @?= offeredOptions (offerIn s "say ")

-- | **The column\/offset confusion, as a test.** @tokensView@ reports a column,
-- which restarts at 1 on every line; @recover@ used it as an offset into the whole
-- entry. Identical text one newline apart answered four options and nothing.
recoveryAfterNewline :: IO ()
recoveryAfterNewline = do
  s <- withLC
  -- **A line that still goes through recovery**, which is what these offsets are
  -- about. Since phase 141 a /well-formed/ statement with a literal in it is
  -- answered by the chart directly, so @fill@ would no longer exercise this;
  -- @fil@ is the broken word that sends it down the recovery path.
  let flat = offerIn s "fil LC`( "
      over = offerIn s "fil\n  LC`( "
  case (offeredRecovered flat, offeredRecovered over) of
    (Just a, Just b) -> recoveredText b @?= recoveredText a
    other -> assertFailure ("expected recovery either way, got " <> show other)
  length (offeredOptions over) @?= length (offeredOptions flat)

-- | And a recovered position is reported against the entry the frontend passed,
-- so an accepted completion replaces the right characters.
shiftedColumn :: IO ()
shiftedColumn = do
  s <- withLC
  case offeredRecovered (offerIn s "h = here\nfil LC`( ") of
    -- @h = here\n@ is nine characters, and the literal's text opens at 8 in the
    -- instruction alone (@fil @ is four), so 17 counting from 1 in the whole entry.
    Just r  -> recoveredColumn r @?= 17
    Nothing -> assertFailure "expected recovery inside the literal"

-- | **The phase.** A @Core@ slot may be written as a tagged term literal, so the
-- tag is offered where the slot is.
tagOffered :: IO ()
tagOffered = do
  s <- withLC
  let opts = offeredOptions (offerIn s "fill ")
  if ALiteralSymbol "LC`" `elem` opts then pure ()
    else assertFailure ("expected LC` at a Core slot: " <> show opts)

-- | **And this is what makes it worth doing**: one chart reads the whole line, so
-- the offer inside the literal is an ordinary answer and not a recovered one.
-- @abs@'s second slot is a @Ty@, and @\953@ is the base type the loaded grammar
-- declares — read out of the user's own grammar, through the statement around it.
insideIsDirect :: IO ()
insideIsDirect = do
  s <- withLC
  let o = offerIn s "fill LC`( \955 x : "
  offeredRecovered o @?= Nothing
  offeredStuck o @?= Nothing
  if ALiteralSymbol "\953" `elem` offeredOptions o then pure ()
    else assertFailure ("expected Ty's base type: " <> show (offeredOptions o))

-- | **@[@ joined the list at MS8 phase 159** and the test's old name ("and
-- nothing else") stopped being true: a complete @LC@ may be continued by the
-- generated @E[x -> N]@ notation, which is a production of the grammar now
-- rather than a privilege of a rule's parser (§4.8). So after a finished term
-- the two continuations are the closing fence and a substitution.
fenceOffered :: IO ()
fenceOffered = do
  s <- withLC
  [ w | ALiteralSymbol w <- offeredOptions (offerIn s "fill LC`( \955 x : \953 . x ) ") ]
    @?= ["[", "`"]

-- | @LC[abs]\`@ says which production the literal is, so only that production's
-- own opening may follow — @abs@ begins with @(@ and then @\955@.
namedProduction :: IO ()
namedProduction = do
  s <- withLC
  [ w | ALiteralSymbol w <- offeredOptions (offerIn s "fill LC[abs]`( ") ] @?= ["\955"]

-- | **The bug this phase made and caught.** Reaching a named production through a
-- nonterminal of its own was the first shape, and the chart names whatever
-- nonterminal sits at the cursor — so @fill LC[var]\`@ answered with @At:LC:var@, a
-- name this module invented, handed to a frontend to draw. The body is inlined
-- instead. Nothing a frontend sees may be a name we made up for our own plumbing.
noSynthetic :: IO ()
noSynthetic = do
  s <- withLC
  let names l = [ n | ANonterminalSymbol n <- offeredOptions (offerIn s l) ]
      -- **A @\/@ would mean phase 147's stratum convention came back.** Phase 148
      -- flattened the grammars and took it out: every head is a phrase with no
      -- punctuation in it, so there is nothing for the view to map.
      ours n = "At:" `isPrefixOf` n || "Elements:" `isPrefixOf` n || '/' `elem` n
  [ n
    | l <- [ "fill ", "fill LC`", "fill LC[var]`", "fill LC[abs]`( "
           , "elaborate ", "elaborate surface`", "elaborate surface`\\ x "
           , "fill core`", "fill core`let ? x : ", ":infer ", ":core ", ":parse LC "
           ]
    , n <- names l, ours n
    ] @?= []

-- | The object grammars are concatenated into one rule set with @instral@'s own
-- productions, so their nonterminals share a namespace. A language name and a
-- metavariable are identifiers and cannot contain a @:@; @instral@'s heads all do.
-- **That is the whole of why a language called @Statement@ cannot capture a
-- statement**, and it is an invariant rather than a coincidence.
headIsNamespaced :: IO ()
headIsNamespaced =
  if ':' `elem` statementHead then pure ()
    else assertFailure ("instral's head must be namespaced, got " <> show statementHead)

-- | **Recovery is not dead, and its job is sharper.** Where the statement around a
-- literal does not read, the chart has nothing to say about the literal either —
-- so the narrower question is still the one that answers. @fil@ is @fill@
-- mistyped.
recoveryRemains :: IO ()
recoveryRemains = do
  s <- withLC
  let o = offerIn s "fil LC`( \955 x : "
  case offeredRecovered o of
    Just (RecoveryView _ _ (Just "LC") _) -> pure ()
    other -> assertFailure ("expected recovery inside LC, got " <> show other)
  if ALiteralSymbol "\953" `elem` offeredOptions o then pure ()
    else assertFailure ("expected Ty's base type: " <> show (offeredOptions o))

-- | **The invariant @literalProductions@ rests on, pinned here because it is not
-- this module's to enforce.** A named production's body is found by searching every
-- loaded grammar for a rule of that name, with no language filter — which is right
-- only while a production name is unique across all of them. It is: each production
-- becomes a datatype constructor, and a second language declaring one of the same
-- name is refused as it loads.
--
-- If that ever relaxed, @LC[var]\`@ could be handed another language's @var@, and
-- silently — so the fixture is a pair of languages that both declare @same@, and
-- this asserts the load refuses it.
productionNamesAreUnique :: IO ()
productionNamesAreUnique = do
  (s0, _) <- startingSession
  let (s1, r) = oneLine s0 ":load test/fixtures/two-languages-one-production.thena"
  said <- case following s1 r of
    Just io -> do (s2, rs, _) <- io; pure (unwords (concatMap (renderResponse s2) rs))
    Nothing -> pure (unwords (renderResponse s1 r))
  if "already declared" `isInfixOf` said then pure ()
    else assertFailure
      ("two languages declaring one production must be refused, got " <> show said)

-- | Typing the colon alone already offers every command, because the unit is the
-- colon and whatever follows it.
everyCommand :: IO ()
everyCommand = do
  s <- withLC
  let offered = [ w | ALiteralSymbol w <- offeredOptions (offerIn s ":") ]
  map commandWord commands @?= offered

-- | **The reason a command word needs a unit of its own.** @:inf@ lexes as two
-- tokens, @:@ and @inf@ — so the bare-word unit asks about @inf@ and filters the
-- command words by it, and not one of them starts with @inf@. @:where@ is worse:
-- its second token is a keyword.
commandPrefix :: IO ()
commandPrefix = do
  s <- withLC
  [ w | ALiteralSymbol w <- offeredOptions (offerIn s ":inf") ] @?= [":infer"]
  case offeredRecovered (offerIn s ":inf") of
    Just (RecoveryView 1 ":inf" Nothing _) -> pure ()
    other -> assertFailure ("expected the colon in the unit, got " <> show other)
  -- The keyword case, which an identifier-only rule would have missed.
  if ALiteralSymbol ":where" `elem` offeredOptions (offerIn s ":whe") then pure ()
    else assertFailure "a command word whose tail is a keyword must still complete"

takesNothing :: IO ()
takesNothing = do
  s <- withLC
  let o = offerIn s ":where "
  offeredOptions o @?= []
  -- **Not stuck**: the line reads, and there is genuinely nothing more to write.
  offeredStuck o @?= Nothing

-- | **The honest answer for an argument the chart has no grammar for**, and the
-- shape the phase turns on: a nonterminal with no productions. The line is not
-- stuck — a production is open and waiting — and the offer names what is wanted
-- without pretending to enumerate it.
--
-- **The command moved at phase 147 and the assertion did not.** It was @:infer@,
-- whose argument is a term — and a term is describable now, so that line would be
-- testing the opposite of what it says. @:load@ takes a path, which genuinely has
-- no grammar, so it is what this is about.
opaqueArgument :: IO ()
opaqueArgument = do
  s <- withLC
  let o = offerIn s ":load "
  offeredStuck o @?= Nothing
  [ n | ANonterminalSymbol n <- offeredOptions o ] @?= ["instral:Argument"]

-- | And where the argument /is/ enumerable the words come back as words. **No
-- nonterminal this module invented may appear** — the first shape routed a choice
-- through one and answered @instral:Choice:on.off.@, which is phase 141's
-- @At:LC:var@ again.
stepWords :: IO ()
stepWords = do
  s <- withLC
  let o = offerIn s ":step "
  [ w | ALiteralSymbol w <- offeredOptions o ] @?= ["on", "off"]
  if AScanSymbol "int" `elem` offeredOptions o then pure ()
    else assertFailure ("expected a numeral too: " <> show (offeredOptions o))
  [ n | ANonterminalSymbol n <- offeredOptions o ] @?= []

-- | Inside a command line the recovered offer is asked /with/ the text before the
-- word, unlike a statement's — @:step @ reads, so there is context worth using, and
-- @:step o@ offers @on@ and @off@ rather than nothing.
stepPrefix :: IO ()
stepPrefix = do
  s <- withLC
  let ws = [ w | ALiteralSymbol w <- offeredOptions (offerIn s ":step o") ]
  if "on" `elem` ws && "off" `elem` ws then pure ()
    else assertFailure ("expected on and off, got " <> show ws)

parseLanguages :: IO ()
parseLanguages = do
  s <- withLC
  let ws = [ w | ALiteralSymbol w <- offeredOptions (offerIn s ":parse ") ]
  if "LC" `elem` ws && "Ty" `elem` ws then pure ()
    else assertFailure ("expected the loaded languages, got " <> show ws)

-- | **One direction of the cross-check.** Every word in the table must be a word
-- @Thena.Driver.dispatch@ answers to — driven, not inspected: a word it does not
-- know comes back as @no such command@.
tableDispatches :: IO ()
tableDispatches = do
  (s, _) <- startingSession
  let refused w =
        let said = unwords (renderResponse s (snd (oneLine s w)))
         in "no such command" `isInfixOf` said
  filter refused (map commandWord commands) @?= []

-- | **The other direction, as far as it can be had.** @:help@'s list is written
-- separately (@.claude\/plans\/LONG-TERM.md@ 24), so the two hand-kept lists are
-- crossed against each other: a command added to one and not the other shows up
-- here. It does not reach @dispatch@'s own @case@, which is what that item holds
-- open.
tableMatchesHelp :: IO ()
tableMatchesHelp =
  sort (nub inHelp) @?= sort (nub (map commandWord commands))
  where
    -- A command word is a colon followed by a letter. **The test needs that and
    -- not just a leading colon**, because @:theorem ‹x› : ‹T›@ writes an ascription
    -- with one — found by the comparison failing on a lone @":"@, which is the
    -- extractor being wrong rather than the lists disagreeing.
    inHelp =
      [ takeWhile (`notElem` " /\8249") w
      | (usage, _) <- commandSummary
      , w <- words usage
      , (':' : c : _) <- [w]
      , isAlpha c
      ]

statementUntouched :: IO ()
statementUntouched = do
  s <- withLC
  let o = offerIn s "fill "
  offeredStuck o @?= Nothing
  if ALiteralSymbol "LC`" `elem` offeredOptions o then pure ()
    else assertFailure "a statement line must be unaffected by the command grammar"

-- | **His ask, 2026-09-30**, relayed through @.jalivert\/REPORT.md@: the underline on
-- a recovered tagged literal should cover the literal — @LC\`@ through the closing
-- backtick — and not start one character past the opening fence.
--
-- **The tui track filed only the left half of it.** Their entry set aside anything
-- past the cursor, and the closing fence is past the cursor whenever you are typing
-- inside the literal. So the span reaches past the cursor, and it is the only part of
-- an offer that does.
literalSpan :: IO ()
literalSpan = do
  s <- withLC
  -- Unclosed, which is every literal being typed: the span runs to the line's end.
  spanOf s "fil LC`( \955 x : " @?= Just "LC`( \955 x : "
  spanOf s "LC`( " @?= Just "LC`( "

namedTagSpan :: IO ()
namedTagSpan = do
  s <- withLC
  spanOf s "fil LC[abs]`( \955 " @?= Just "LC[abs]`( \955 "

-- | The span is a position in the text the frontend passed, like every other
-- position an offer reports. **It did not shift at first** and named the text of the
-- instruction above instead — the kind of wrong a frontend draws rather than crashes
-- on.
spanShifts :: IO ()
spanShifts = do
  s <- withLC
  spanOf s "h = here\nfil LC`( \955 x : " @?= Just "LC`( \955 x : "

wordSpan :: IO ()
wordSpan = do
  s <- withLC
  spanOf s "atta" @?= Just "atta"
  spanOf s ":inf" @?= Just ":inf"
  spanOf s "LC`x` atta" @?= Just "atta"

-- | The characters a recovered offer's span names, so a test can say what it covers
-- rather than quoting two numbers.
spanOf :: Session -> String -> Maybe String
spanOf s line = do
  rv <- offeredRecovered (statementOfferView s [WrittenText line] [])
  let (from, to) = recoveredSpan rv
  pure (take (to - from) (drop (from - 1) line))
