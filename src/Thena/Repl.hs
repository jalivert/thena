-- | The terminal frontend, and rendering.
--
-- The only module in the project that reads a key or writes to the screen
-- (§2.1, §12 invariant 4). Rendering lives here too, per §2.5 — 'Core',
-- 'Partial' and now the machine, back to something the user can read.
--
-- 'turn' is the whole of the loop except the reading and the writing, and it is
-- deliberately pure: the interactive 'repl' and the golden 'transcript' both go
-- through it, so a transcript cannot drift away from the loop it is supposed to
-- be testing.
module Thena.Repl
  ( repl
  , Turn (..)
  , turn
  , transcript
  , transcriptFrom
  , renderCore
  , renderLevel
  , renderPartial
  , renderCursor
  , renderWhere
  , renderMachine
  , renderSyntaxError
  , renderInductive
  , renderEliminator
  , preludePath
  , loadPrelude
  , rulesPath
  , loadStandardRules
  , startingSession
  , loadRuleFiles
  , loadFile
  , renderLoadError
  ) where

import Control.Monad.IO.Class (liftIO)
import System.Console.Haskeline
  ( InputT
  , defaultSettings
  , getInputLine
  , outputStrLn
  , runInputT
  )

import Thena.Core.Context (Context, Entry (..), entryType, entryVar, piOver)
import Thena.Core.Level (Level, LevelVar (..), Normal (..), normalise)
import Thena.Core.Term
  ( Core (..)
  , GlobalName (..)
  , Ident (..)
  , Scope
  , Var
  , freeVars
  , fresh
  , open
  )
import Thena.Development.Component (Component (..))
import Thena.Development.Cursor
  ( Crossing (..)
  , Cursor
  , Focus (..)
  , Part (..)
  , Slot (..)
  , Step (..)
  , TermStep (..)
  , context
  , expectedType
  , focus
  , prefix
  , rebuild
  )
import Thena.Development.Partial (Constraint (..), Partial (..))
import Thena.Driver
  ( CommandError (..)
  , RuleFileError (..)
  , loadRuleBases
  , LoadError (..)
  , Loaded (..)
  , Response (..)
  , ChoicePoint (..)
  , Session (..)
  , Stop (..)
  , SyntaxError (..)
  , Proof (..)
  , loadSource
  , newSession
  , oneLine
  )

import Control.Exception (IOException, try)
import qualified Paths_thena
import Thena.Engine
  ( Exec (..)
  , Frame (..)
  , Machine (..)
  , Question (..)
  , cursor
  , proof
  , proofContext
  )
import Thena.Errors
  ( Clash (..)
  , ConversionFailure (..)
  , DevForm (..)
  , ElimError (..)
  , FailReason (..)
  , KernelError (..)
  , MoveError (..)
  , Position (..)
  , ResolveError (..)
  , Site (..)
  , TypeError (..)
  )
import Thena.Global.Declare (DeclareError (..))
import Thena.Syntax.Concrete (Raw (..), RawLevel (..), RawBinder (..))
import Thena.Global.Env
  ( ConstructorDefinition (..)
  , InductiveDefinition (..)
  , constructorTarget
  )
import Thena.Ops
  ( AnswerKind (..)
  , Instr (..)
  , Op
  , Operand (..)
  , Rule (..)
  , Value (..)
  , operandsOf
  )
import Thena.Rules (RuleBase (..), RuleError (..))
import qualified Thena.Ops as Ops
import Thena.Syntax.Lexer (LexError (..), Pos (..), Token (..))
import Thena.Syntax.Parser (ParseError (..))

import Data.Foldable (toList)
import Data.List (intercalate)

-- | Run the read-eval-print loop until @:quit@ or end of input.
--
-- The prelude is loaded first (§9, phase 11) and **silently on success** — it
-- is three @data@ lines and announcing them at every start is noise. A failure
-- is reported and the loop starts anyway, with whatever did load: @Eq@ missing
-- makes elimination fail later with a message naming @Eq@, which is the bargain
-- §3.7 already struck, and a REPL that refuses to start would say less.
repl :: IO ()
repl = do
  (s, problems) <- startingSession
  runInputT defaultSettings (mapM_ outputStrLn problems >> loop s Nothing)

loop :: Session -> Maybe Question -> InputT IO ()
loop s pending = do
  input <- getInputLine (prompt s pending)
  case input of
    Nothing   -> pure ()          -- end of input: Ctrl-D
    Just line -> do
      let t = turn s pending line
      mapM_ outputStrLn (turnOutput t)
      case turnResponse t of
        -- The one response the driver cannot act on itself: it named a file,
        -- and reading files is this module's (§12 invariant 4).
        LoadRequested path | not (turnQuit t) -> do
          (s', out, problems) <- liftIO (loadFile (turnSession t) path)
          mapM_ outputStrLn (out ++ problems)
          loop s' Nothing
        -- The same shape for rule bases, and several paths rather than one:
        -- a load replaces the whole ordered list (phase 22).
        RulesRequested paths | not (turnQuit t) -> do
          (s', out, problems) <- liftIO (loadRuleFiles (turnSession t) paths)
          mapM_ outputStrLn (out ++ problems)
          loop s' Nothing
        _ | turnQuit t -> pure ()
          | otherwise  -> loop (turnSession t) (turnPending t)

-- --------------------------------------------------------------------------
-- Loading (§9, phase 11)
-- --------------------------------------------------------------------------

-- | Where the shipped prelude went.
--
-- @data-files@ and 'Paths_thena' rather than a path relative to the working
-- directory, so an installed @thena@ finds it too. This is the only place the
-- project asks cabal anything at runtime.
preludePath :: IO FilePath
preludePath = Paths_thena.getDataFileName "prelude/prelude.thena"

-- | Load the shipped prelude into a session, keeping only what went wrong.
--
-- Discarding the lines\' own output is what makes startup silent: a @data@ line
-- says @declared Eq@, and three of those at every start are noise. @:load@ on
-- the same file keeps them, because there the user asked.
loadPrelude :: Session -> IO (Session, [String])
loadPrelude s = do
  path <- preludePath
  (s', _, problems) <- loadFile s path
  pure (s', map ("prelude: " ++) problems)

-- | A session with everything shipped loaded: **the rule base first, then the
-- prelude**.
--
-- **The order is load-bearing as of phase 23b.** The prelude proves @fst@,
-- @snd@, @andLeft@ and @andRight@ with @try@ and @solve@, and those stopped
-- being driver commands when the tactic words went to the rules — so a prelude
-- loaded before the base fails at its first @try@ with /no rule is called try/.
-- Everything that starts a session goes through here rather than calling the
-- two loaders in whichever order it happened to write them.
startingSession :: IO (Session, [String])
startingSession = do
  (s0, ruleProblems)   <- loadStandardRules newSession
  (s, preludeProblems) <- loadPrelude s0
  pure (s, ruleProblems ++ preludeProblems)

-- | Where the shipped rule base went. 'preludePath'\'s reason, verbatim.
rulesPath :: IO FilePath
rulesPath = Paths_thena.getDataFileName "rules/standard.thena.rules"

-- | Load the shipped rule base at startup, keeping only what went wrong.
--
-- 'loadPrelude'\'s bargain, in the same words: a broken or missing rule base is
-- reported and the REPL starts anyway, with an empty base. @prove@ then matches
-- nothing, which says more than refusing to start would.
loadStandardRules :: Session -> IO (Session, [String])
loadStandardRules s = do
  path <- rulesPath
  (s', _, problems) <- loadRuleFiles s [path]
  pure (s', map ("rules: " ++) problems)

-- | Read every named rule base and install the whole ordered list, or none.
--
-- **All the files are read before any of them is installed**, which is what
-- makes 'Thena.Driver.loadRuleBases'\' all-or-nothing promise reach as far as
-- the disk: a second path that does not exist leaves the first uninstalled too.
loadRuleFiles :: Session -> [FilePath] -> IO (Session, [String], [String])
loadRuleFiles s paths = do
  reads' <- mapM (\p -> fmap ((,) p) (try (readFile p))) paths
  pure $ case [ (p, e) | (p, Left e) <- reads' ] of
    (p, e) : _ -> (s, [], [p ++ ": " ++ show (e :: IOException)])
    [] ->
      let contents = [ (p, c) | (p, Right c) <- reads' ]
          (s', resp) = loadRuleBases s contents
       in case resp of
            -- A refusal is a problem and not output: the whole load was
            -- abandoned, so there is nothing to report as having happened.
            RuleFileRefused p e -> (s, [], renderRuleFileError p e)
            _                   -> (s', renderResponse s' resp, [])

-- | Read a file and run it: the session after, **what its lines printed**, and
-- **what went wrong**, kept apart because the two callers want different halves.
--
-- A loaded line\'s own output is real output — a file is a script of command
-- lines (§9), so @:infer@ in a file prints what @:infer@ prints.
loadFile :: Session -> FilePath -> IO (Session, [String], [String])
loadFile s path = do
  contents <- try (readFile path)
  pure $ case contents of
    Left e  -> (s, [], [show (e :: IOException)])
    Right c ->
      let l  = loadSource s c
          s' = loadedSession l
       in ( s'
          , concatMap (renderResponse s') (loadedResponses l)
          , maybe [] (renderLoadError path) (loadedError l)
          )

-- | Why a load stopped. It says only /where/ — the reason has already been
-- printed, because a stopped line renders like any other line.
renderLoadError :: FilePath -> LoadError -> [String]
renderLoadError path e = case e of
  LoadStopped n        -> [at n ++ "stopped here"]
  NestedLoad n         -> [at n ++ ":load inside a loaded file is not followed"]
  UnansweredQuestion n -> [at n ++ "the file ended while this was still asking"]
  where
    at n = path ++ ":" ++ show n ++ ": "

-- | The machine asks with the rule body's own words, so an answer prompt is
-- bare. Otherwise the prompt says which fragment the focus is in.
--
-- **Two words, and a guess body is @spine@** — asked for by the user
-- 2026-08-21 (@AGENDA.md@ item 24) and settled two-way while planning phase 5.
-- His parenthesis is the load-bearing part: being inside a guess's proposed
-- term is still the spine, so this is not a depth question and cannot be read
-- off the nesting level. It is 'Focus'\'s own distinction and nothing else. A
-- constraint focus reads as @spine@ too: it is a link in the chain.
prompt :: Session -> Maybe Question -> String
prompt _ (Just _) = "> "
prompt s Nothing  = "thena " ++ fragment ++ "> "
  where
    fragment = case focus (cursor (proof (sessionMachine s))) of
      OnTerm {} -> "core"
      _         -> "spine"

-- | One line in, and everything that follows from it.
data Turn = Turn
  { turnOutput   :: [String]
  , turnSession  :: Session
  , turnPending  :: Maybe Question  -- ^ set when the next line is an answer
  , turnQuit     :: Bool
  , turnResponse :: Response
    -- ^ kept from phase 11, because @:load@ is a response the /caller/ has to
    -- act on: the driver may not read a file (§12 invariant 4)
  }
  deriving (Eq, Show)

turn :: Session -> Maybe Question -> String -> Turn
turn s pending line = Turn (renderResponse s' resp) s' asking (resp == Quit) resp
  where
    (s', resp, asking) = oneLine s pending line

-- | Replay a script through 'turn' and render what a terminal would have shown,
-- prompts included. The golden tests' whole harness (§9, "golden REPL
-- transcripts are the natural regression test for a tool whose interface is the
-- REPL").
--
-- **It starts from a bare 'newSession', where 'repl' starts from the prelude**
-- — the one place a transcript is not what the terminal would have done
-- (phase 11). Deliberate: the existing scripts declare their own @Nat@ and
-- @Empty@, and the prelude's @Empty@ would collide with phase 10's. It also
-- does not follow a @:load@, because it is pure and reading a file is not.
-- "Thena.LoadTests" covers both, against the real 'loadPrelude'.
transcript :: [String] -> String
transcript = transcriptFrom newSession

-- | The same, from a session that has already had something loaded into it.
--
-- Phase 22: the rule base comes off disk now, so a transcript that uses
-- @:matches@, @prove@ or @retry@ has to start from a session that has one.
-- That makes the golden suite test the **shipped file** rather than a Haskell
-- literal, which is strictly stronger than what it tested before.
transcriptFrom :: Session -> [String] -> String
transcriptFrom s0 = unlines . replay s0 Nothing
  where
    replay _ _ []           = []
    replay s pending (l : ls) =
      let t = turn s pending l
          rest
            | turnQuit t = []
            | otherwise  = replay (turnSession t) (turnPending t) ls
       in (prompt s pending ++ l) : turnOutput t ++ rest

renderResponse :: Session -> Response -> [String]
renderResponse s resp = case resp of
  Blank          -> []
  Rendered t     -> [renderCore (counter s) (contextOf s) t]
  RenderedDev p  -> [renderPartial (counter s) (contextOf s) p]
  Shown c        -> [renderCursor (counter s) c]
  ShownData d    -> renderInductive (counter s) d
  ShownEliminator g ty  -> renderEliminator (counter s) g ty
  ShownGlobal g ty body -> renderGlobal (counter s) g ty body
  Where c        -> renderWhere (counter s) c
  Inferred t ty  ->
    [renderCore (counter s) (contextOf s) t ++ " : " ++ renderCore (counter s) (contextOf s) ty]
  IllTyped e     -> renderTypeError (counter s) e
  -- The two terms are restated, because with η a yes is printed about terms
  -- that still look different (§5.2).
  Converted a b why ->
    let q = renderCore (counter s) (contextOf s) a
              ++ " ≟ " ++ renderCore (counter s) (contextOf s) b
     in case why of
          Nothing -> [q ++ "   yes"]
          Just f  -> (q ++ "   no") : renderConversionFailure (counter s) f
  -- Nothing to print: the caller reads the file and prints what that produced.
  LoadRequested _ -> []
  Revalidated Nothing  -> ["valid"]
  Revalidated (Just e) -> renderKernelError (counter s) e
  Extracted t          -> [renderCore (counter s) [] t]
  Proving g ty  -> ["proving " ++ nameString g ++ " : " ++ renderCore (counter s) [] ty]
  Proved g ty   -> [nameString g ++ " : " ++ renderCore (counter s) [] ty ++ "   ∎"]
  Suspended g   -> ["suspended " ++ nameString g]
  Resumed g     -> ["resumed " ++ nameString g]
  Abandoned g   -> ["abandoned " ++ nameString g]
  -- Show where it landed: an undo with no output looks like nothing happened.
  Undone        -> [renderCursor (counter s) (cursor (proof (sessionMachine s)))]
  Proofs cur ps -> renderProofs (counter s) cur ps
  -- Nothing to print: the caller reads the files and prints what that produced.
  RulesRequested _ -> []
  BasesLoaded bs   -> map loadedLine bs
  BasesListed bs   -> renderBases bs
  RulesListed bs   -> renderRuleBases bs
  RuleFileRefused p e -> renderRuleFileError p e
  Matched rs    -> renderMatches rs
  Choices cs    -> renderChoices cs
  Ran msgs stop  -> msgs ++ renderStop s stop
  Failed e       -> [renderSyntaxError e]
  Rejected e     -> [renderCommandError e]
  Quit           -> []

-- | Render with the counter the session holds, never with a smaller one: a
-- printer given a counter below the term's highest 'Var' mints a colliding
-- display name (phase 3's §7).
counter :: Session -> Int
counter = names . sessionMachine

-- | The context a command's argument was resolved in, so that a 'Var' standing
-- for one of the development's binders prints as its name rather than as a
-- number. @:show@ renders from the root and needs no seed.
contextOf :: Session -> Context
contextOf = proofContext . proof . sessionMachine

renderStop :: Session -> Stop -> [String]
renderStop s stop = case stop of
  Completed              -> []
  Waiting (Question p _) -> [p]
  Halted r               -> ["stuck: " ++ renderFailReason r]
  Refused e              -> ["refused: " ++ renderDeclareError e]
  Uncertified e          -> "the kernel refused it" : renderKernelError (counter s) e
  Paused                 -> renderMachine (counter s) (contextOf s) (sessionMachine s)

-- --------------------------------------------------------------------------
-- Errors, made readable
-- --------------------------------------------------------------------------

renderSyntaxError :: SyntaxError -> String
renderSyntaxError e = case e of
  LexFailed (LexError p c) ->
    at p ++ "unexpected character" ++ maybe "" (\ch -> " " ++ show ch) c
  ParseFailed (UnexpectedToken p t) -> at p ++ "unexpected " ++ describe t
  ParseFailed UnexpectedEndOfInput  -> "unexpected end of input"
  ResolveFailed (NotInScope n)      -> "not in scope: " ++ n
  ResolveFailed (NotACoreTerm f)    ->
    devForm f ++ " is part of a development, not a term"
  ResolveFailed (LevelNotInScope s) ->
    s ++ " is not a level parameter in scope"
  ResolveFailed (LevelArgumentsOnALocal s) ->
    s ++ " is bound here, and only a definition has level parameters"
  ResolveFailed LevelParametersOnABinder ->
    "only a definition has level parameters; this binds a component"
  ResolveFailed (UniverseTakesOneLevel k) ->
    "a universe takes one level, not " ++ show k
  ResolveFailed (NotAUniverse d)    ->
    d ++ " must be declared at a universe, as in \": Type\8320\""
  ResolveFailed (TargetIsNotTheDatatype c) ->
    c ++ " must produce the datatype being declared"
  ResolveFailed (TargetArgumentCount c want got) ->
    c
      ++ " should produce the datatype applied to "
      ++ show want
      ++ " argument(s), not "
      ++ show got
  ResolveFailed (ParameterNotPassedThrough c i) ->
    c ++ " must pass the parameter " ++ identString i ++ " through unchanged"
  ResolveFailed (NotADatatype d) ->
    d ++ " is not a declared datatype"
  ResolveFailed (WrongNumberOfEliminationParameters d want got) ->
    d ++ " has " ++ show want ++ " parameter(s), not " ++ show got
  ResolveFailed (WrongNumberOfMethods d want got) ->
    d ++ " has " ++ show want ++ " constructor(s), so this elim needs "
      ++ show want ++ " method(s), not " ++ show got
  ResolveFailed (WrongNumberOfEliminationIndices d want got) ->
    d ++ " has " ++ show want ++ " index/indices, not " ++ show got
  where
    at (Pos line col) = show line ++ ":" ++ show col ++ ": "

devForm :: DevForm -> String
devForm f = case f of
  AHole       -> "a hole"
  AGuess      -> "a guess"
  AConstraint -> "a constraint"

describe :: Token -> String
describe t = case t of
  TLambda     -> "λ"
  TForall     -> "∀"
  TArrow      -> "->"
  TLParen     -> "("
  TRParen     -> ")"
  TColon      -> ":"
  TLBrace     -> "{"
  TRBrace     -> "}"
  TSemi       -> ";"
  TEquals     -> "="
  TQuery      -> "?"
  TGuessed    -> "≐"
  TPending    -> "▸"
  TTurnstile  -> "⊢"
  TEquate     -> "≟"
  TOpenQuote  -> "⌜"
  TCloseQuote -> "⌝"
  TLet        -> "let"
  TIn         -> "in"
  TElim       -> "elim"
  TWhere      -> "where"
  TRule       -> "rule"
  TWhen       -> "when"
  TThen       -> "then"
  TNeck       -> ":-"
  TNumber k   -> show k
  TString txt -> show txt
  TUniverse k   -> "Type" ++ subscript k
  TUniverseOpen -> "Type"
  TIdent s    -> s

-- --------------------------------------------------------------------------
-- Terms, made readable (§2.6)
-- --------------------------------------------------------------------------

-- | Where a term is being printed, which decides whether it needs parentheses.
data Prec
  = AtTop   -- ^ λ, ∀, an arrow and let are all fine here
  | AtApp   -- ^ the function side of an application
  | AtAtom  -- ^ the argument side of an application
  deriving (Eq, Ord)

-- | The freshening environment: minted variables paired with their display
-- names. Threaded through both the term and the development printers.
type Env = [(Var, String)]

-- | Render a term.
--
-- Takes the session's name counter because it must 'open' every 'Scope' to
-- descend, 'open' needs a 'Var', and only 'fresh' mints one. It cannot inspect
-- the term's existing 'Var's to pick a safe number instead — 'Var'\'s
-- constructor is hidden (§2.6, §3.4).
renderCore :: Int -> Context -> Core -> String
renderCore n ctx = go n (envOf ctx) AtTop

-- | Display names for a context's variables, freshened as the chain printer
-- freshens a component's.
envOf :: Context -> Env
envOf = foldl add []
  where
    add e entry =
      let (v, hint) = case entry of
            Hypothesis x (Ident h) _   -> (x, h)
            Definition x (Ident h) _ _ -> (x, h)
       in (v, freshen hint e) : e

go :: Int -> Env -> Prec -> Core -> String
go n env prec term = case term of
  Bound i               -> "‹bound " ++ show i ++ "›"
  Free v                -> nameOf v env
  Global (GlobalName g) _ -> g
  Universe l            -> renderLevel l

  App f a -> parensIf (prec > AtApp) (go n env AtApp f ++ " " ++ go n env AtAtom a)

  Lam {} -> parensIf (prec > AtTop) ("λ " ++ chainLam n env [] term)

  Pi _ dom sc
    | dependent n sc -> parensIf (prec > AtTop) ("∀ " ++ chainPi n env [] term)
    | otherwise ->
        let (v, n1) = fresh n
         in parensIf (prec > AtTop)
              (go n1 env AtApp dom ++ " -> " ++ go n1 env AtTop (open v sc))

  Let (Ident hint) val ty sc ->
    let (v, n1) = fresh n
        name    = freshen hint env
     in parensIf (prec > AtTop) $
          "let " ++ name
            ++ " = " ++ go n1 env AtTop val
            ++ " : " ++ go n1 env AtTop ty
            ++ " in " ++ go n1 ((v, name) : env) AtTop (open v sc)

  -- A 'Canonical' prints as its own wrapper applied — @succ zero@, not a
  -- bracketed internal form. DECIDED by the user 2026-08-22.
  --
  -- The user never writes a 'Canonical' and the resolver never builds one
  -- (§3.6), so before phase 7 nothing could put one in front of a reader and
  -- this branch printed @‹succ zero›@, deliberately unreadable-back. Phase 7's
  -- committed @reduce@ changed that: δ on a former wrapper followed by β puts
  -- a 'Canonical' into the development itself — the thing @:show@ prints,
  -- @:undo@ will snapshot (phase 13) and @certify@ will read (phase 12) — so
  -- an internal form is no longer an internal form.
  --
  -- **The cost, stated rather than hidden: this is the one place
  -- @parse . print@ is not the identity on the nose.** @Canonical "succ" [z]@
  -- prints @succ z@, which re-reads as @App (Global "succ") z@ — δβ-convertible
  -- to what was printed, not structurally equal to it. §2.6 carries the
  -- qualification. Giving 'Canonical' a spelling of its own was the
  -- alternative and §12 invariant 6 forbids it: two spellings of a saturated
  -- former application is exactly what that invariant exists to prevent.
  Canonical (GlobalName f) _ as
    | null as   -> f
    | otherwise -> parensIf (prec > AtApp) (unwords (f : map (go n env AtAtom) as))

  -- @elim d (params) motive (methods) (indices) target@ (§2.6, phase 7) —
  -- positional, in 'Eliminate'\'s own field order, each group parenthesized
  -- so a motive or a target cannot be mistaken for the start of the next
  -- group the way an unparenthesized term could.
  Eliminate (GlobalName d) _ ps m ms is t ->
    parensIf (prec > AtTop) $
      unwords
        [ "elim", d
        , atoms ps
        , go n env AtAtom m
        , atoms ms
        , atoms is
        , go n env AtAtom t
        ]
    where
      atoms = paren . unwords . map (go n env AtAtom)
      paren s = "(" ++ s ++ ")"

-- | Does the scope's variable actually occur? This is the whole of the
-- @S -> B@ versus @∀ (x : S) -> B@ decision (§2.6).
dependent :: Int -> Scope Core -> Bool
dependent n sc = let (v, _) = fresh n in v `elem` freeVars (open v sc)

-- | A run of λs prints as one λ with several binder groups.
chainLam :: Int -> Env -> [String] -> Core -> String
chainLam n env acc term = case term of
  Lam (Ident hint) dom sc ->
    let (v, n1) = fresh n
        name    = freshen hint env
        group   = "(" ++ name ++ " : " ++ go n1 env AtTop dom ++ ")"
     in chainLam n1 ((v, name) : env) (group : acc) (open v sc)
  _ -> unwords (reverse acc) ++ " -> " ++ go n env AtTop term

-- | The same for ∀, except that a non-dependent 'Pi' ends the run — it goes on
-- to render as @S -> B@ through 'go'.
chainPi :: Int -> Env -> [String] -> Core -> String
chainPi n env acc term = case term of
  Pi (Ident hint) dom sc
    | dependent n sc ->
        let (v, n1) = fresh n
            name    = freshen hint env
            group   = "(" ++ name ++ " : " ++ go n1 env AtTop dom ++ ")"
         in chainPi n1 ((v, name) : env) (group : acc) (open v sc)
  _ -> unwords (reverse acc) ++ " -> " ++ go n env AtTop term

nameOf :: Var -> Env -> String
nameOf v env = case lookup v env of
  Just s  -> s
  Nothing -> "‹" ++ show v ++ "›"

-- | A binder whose identifier is already in scope is renamed, because a term
-- whose body refers to the /outer/ one would otherwise print as one that
-- re-parses to the inner (§2.6). Keywords are avoided for the same reason.
freshen :: String -> Env -> String
freshen hint env
  | ok hint   = hint
  | otherwise = pick (1 :: Int)
  where
    taken = map snd env
    ok s = s `notElem` taken && s `notElem` ["let", "in", "forall"]
    pick k = let s = hint ++ show k in if ok s then s else pick (k + 1)

subscript :: Int -> String
subscript = map sub . show
  where
    sub c = toEnum (fromEnum '₀' + (fromEnum c - fromEnum '0'))

-- | Render a universe, **normalising first** (phase 28).
--
-- Normalising is not cosmetic. 'Thena.Core.Typing' builds a Π's level with
-- @levelMax@ and does not evaluate it, so @:infer Type₀ -> Type₀@ now arrives
-- here as @LMax (LSuc LZero) (LSuc LZero)@ where it used to arrive as
-- @Level 1@. It must still print @Type₁@ — which is most of what this phase's
-- "the test suite does not move" check is checking.
--
-- A level with variables in it prints as an expression over @⊔@, Agda's
-- spelling of the join. **Nothing constructs one before phase 29**, so that
-- branch is exercised by unit tests rather than by the REPL; it is written now
-- because rendering is total and a partial renderer would be worse than an
-- unexercised one.
renderLevel :: Level -> String
renderLevel l = case normalise l of
  Normal c []  -> "Type" ++ subscript c
  Normal c vs  -> "Type (" ++ intercalate " ⊔ " (constant ++ map var vs) ++ ")"
    where
      constant  = [subscriptFree c | c > 0 || null vs]
      var (v, k)
        | k == 0    = levelVarName v
        | otherwise = "suc" ++ concat (replicate (k - 1) " (suc") ++ " "
                        ++ levelVarName v ++ concat (replicate (k - 1) ")")
      subscriptFree = show

-- | A level variable's display name, numbered from the shared counter.
--
-- **A meta wears the @?@ and a rigid parameter does not** — the same convention
-- the development already uses, where @? x@ is a hole and a bare name is a
-- hypothesis. A reader who knows what @?@ means in @:show@ knows what it means
-- here.
levelVarName :: LevelVar -> String
levelVarName v = case v of
  LRigid i -> "ℓ" ++ show i
  LMeta  i -> "?ℓ" ++ show i

parensIf :: Bool -> String -> String
parensIf True s  = "(" ++ s ++ ")"
parensIf False s = s

-- --------------------------------------------------------------------------
-- Developments, made readable (§2.7)
-- --------------------------------------------------------------------------

-- | One rendered line: whether the focus is on it, how far it is indented, and
-- its text. The two development printers differ only in what they do with the
-- first field.
data Line = Line Bool Int String

-- | The way from here to the focus: the prefix steps still to walk, and what is
-- at the end of them. 'Nothing' means the focus is not in this subtree at all.
--
-- This is what lets ':show' mark the focus without consulting 'context' —
-- display names are accumulated structurally, from the root down, and a guess
-- body is entered without its own hole's name (§4.5, phase 3 §7.2).
type Route = Maybe ([Step], Focus)

-- | One chain link per line, at the current indent; a guess body indented one
-- level inside its parentheses. Structural breaks only — no width, no reflow.
renderPartial :: Int -> Context -> Partial -> String
renderPartial n ctx = layout . goP n (envOf ctx) 0 Nothing
  where
    layout = intercalate "\n" . map (\(Line _ ind t) -> pad ind ++ t)

-- | The development with the focus marked (§4.0 J1) — @:show@.
--
-- The marker is chain-link precision: it names the link the focus is in, and
-- @:where@ says where inside it. Rendered from the root with no seed context,
-- because rendering from the root introduces every binder on the way down.
renderCursor :: Int -> Cursor -> String
renderCursor n cur = intercalate "\n" (map gutter lines')
  where
    lines' = goP n [] 0 (Just (toList (prefix cur), focus cur)) (rebuild cur)
    -- A different glyph from the ▸ that ends a constraint line and separates
    -- the breadcrumb: those are §2.7's "then", and this is not that.
    gutter (Line marked ind t) = (if marked then "▶ " else "  ") ++ pad ind ++ t

goP :: Int -> Env -> Int -> Route -> Partial -> [Line]
goP n env ind route p = case p of
  Trailing t -> [Line (isHere route) ind (trailing n env t)]

  Pending k rest ->
    Line (isHere route) ind (renderConstraint n env k ++ " ▸")
      : goP n env ind (past route) rest

  Under c rest ->
    let (text, env') = link n env c
        after = goP n env' ind (onward route) rest
     in Line (isHere route) ind text
          : case c of
              -- The body is rendered in 'env' WITHOUT the hole's own name,
              -- matching Γ_(?x ≐ P : S . p) = Γ_P (§4.5). Getting this wrong is
              -- invisible unless the body binds the hole's identifier — see
              -- phase 3's §7.2.
              Guess _ _ g _ ->
                goP n env (ind + 2) (inward route) g ++ Line False ind ") in" : after
              _ -> after

-- | The line a chain link prints as, and the environment for what follows it.
--
-- A guess prints as its opening line only; its body is separate lines and the
-- caller places them. Shared with @:where@, which prints exactly this line for
-- a component focus.
link :: Int -> Env -> Component -> (String, Env)
link n env c = (text, (v, name) : env)
  where
    (v, hint) = bound c
    name      = freshen hint env
    text      = case c of
      Assume _ _ ty     -> "λ (" ++ name ++ " : " ++ go n env AtTop ty ++ ") ->"
      Define _ _ val ty ->
        "let " ++ name ++ " = " ++ go n env AtTop val
          ++ " : " ++ go n env AtTop ty ++ " in"
      Claim _ _ ty      -> "let ? " ++ name ++ " : " ++ go n env AtTop ty ++ " in"
      Guess _ _ _ ty    -> "let ? " ++ name ++ " : " ++ go n env AtTop ty ++ " ≐ ("

-- | The variable a component binds, and the name it would like.
bound :: Component -> (Var, String)
bound c = case c of
  Assume v (Ident h) _   -> (v, h)
  Define v (Ident h) _ _ -> (v, h)
  Claim  v (Ident h) _   -> (v, h)
  Guess  v (Ident h) _ _ -> (v, h)

isHere :: Route -> Bool
isHere (Just ([], _)) = True
isHere _              = False

-- | Each of the three follows one kind of step and refuses the others, so a
-- route can never be handed to the wrong part of a link.
onward, past, inward :: Route -> Route
onward (Just (Along _ : ss, f))      = Just (ss, f)
onward _                             = Nothing
past   (Just (Past _ : ss, f))       = Just (ss, f)
past   _                             = Nothing
inward (Just (IntoGuess {} : ss, f)) = Just (ss, f)
inward _                             = Nothing

-- --------------------------------------------------------------------------
-- Where the focus is (§4.0 J2) — @:where@
-- --------------------------------------------------------------------------

-- | The focused form, the path that reaches it, Γ, and the type — §4.5's hover
-- panel, in text.
--
-- The type section is absent when the structure does not carry one. That is not
-- a failure to look: deriving a type for an arbitrary core subterm is @infer@'s
-- job and arrives at phase 8. See 'Thena.Development.Cursor.expectedType'.
renderWhere :: Int -> Cursor -> [String]
renderWhere n cur =
  section "focus"   [focusText]
    ++ section "path"    [intercalate " ▸ " ("root" : crumbs ++ coreCrumbs)]
    ++ section "context" (if null ctx then ["(nothing in scope)"] else map entry ctx)
    ++ maybe [] (\t -> section "type" [go n env' AtTop t]) (expectedType cur)
  where
    section heading ls = heading : map ("  " ++) ls

    ctx           = context cur
    (env, crumbs) = walkSteps (toList (prefix cur))

    (env', coreCrumbs, focusText) = case focus cur of
      OnComponent c  -> (env, [], fst (link n env c))
      OnConstraint k -> (env, [], renderConstraint n env k)
      OnTerm x ts t  ->
        let (e, ws) = walkTerm env (toList ts)
         in (e, crossingWord x : ws, go n e AtTop t)

    entry e = case e of
      Hypothesis v _ ty ->
        nameOf v env' ++ " : " ++ go n env' AtTop ty
      Definition v _ val ty ->
        nameOf v env' ++ " = " ++ go n env' AtTop val ++ " : " ++ go n env' AtTop ty

-- | Walk the prefix root first, collecting display names and breadcrumb words.
--
-- It builds the same names 'goP' builds, in the same order and by the same
-- rule, so the two agree wherever they overlap. A guess adds a crumb and no
-- name, which is §4.5's Γ rule showing up in the display for the same reason it
-- shows up in 'context'.
walkSteps :: [Step] -> (Env, [String])
walkSteps = foldl add ([], [])
  where
    add (env, crumbs) s = case s of
      Along c ->
        let (v, hint) = bound c
            name      = freshen hint env
         in ((v, name) : env, crumbs ++ [name])
      Past _ -> (env, crumbs ++ ["≟"])
      IntoGuess _ (Ident hint) _ _ -> (env, crumbs ++ ["≐ " ++ freshen hint env])

-- | The same for the core path. Only the three binder steps add a name.
walkTerm :: Env -> [TermStep] -> (Env, [String])
walkTerm env0 = foldl add (env0, [])
  where
    add (env, crumbs) s = case binderOf s of
      Nothing        -> (env, crumbs ++ [partWord (partOf s)])
      Just (v, hint) ->
        let name = freshen hint env
         in ((v, name) : env, crumbs ++ [partWord (partOf s)])

binderOf :: TermStep -> Maybe (Var, String)
binderOf s = case s of
  IntoPiCod   v (Ident h) _   -> Just (v, h)
  IntoLamBody v (Ident h) _   -> Just (v, h)
  IntoLetBody v (Ident h) _ _ -> Just (v, h)
  _                           -> Nothing

-- | Which field a step descended into. The positions are one-based, matching
-- what the user types.
partOf :: TermStep -> Part
partOf s = case s of
  IntoFun {}                    -> Fun
  IntoArg {}                    -> Arg
  IntoPiDom {}                  -> Dom
  IntoPiCod {}                  -> Cod
  IntoLamDom {}                 -> Dom
  IntoLamBody {}                -> Body
  IntoLetValue {}               -> Val
  IntoLetType {}                -> Type
  IntoLetBody {}                -> Body
  IntoCanonArg _ _ before _       -> CanonArg (length before + 1)
  IntoElimParam _ _ before _ _ _ _ _ -> Param (length before + 1)
  IntoElimMotive {}             -> Motive
  IntoElimMethod _ _ _ _ before _ _ _ -> Method (length before + 1)
  IntoElimIndex _ _ _ _ _ before _ _  -> Index (length before + 1)
  IntoElimTarget {}             -> Target

-- | A 'Part' as the user types it (§4.7, and "Thena.Driver"'s @partWords@).
partWord :: Part -> String
partWord p = case p of
  Fun        -> "fun"
  Arg        -> "arg"
  Dom        -> "dom"
  Cod        -> "cod"
  Val        -> "val"
  Type       -> "type"
  Body       -> "body"
  Motive     -> "motive"
  Target     -> "target"
  Param k    -> "param " ++ show k
  Method k   -> "method " ++ show k
  Index k    -> "index " ++ show k
  CanonArg k -> "arg " ++ show k

-- | A 'Trailing' term that is itself a binder would re-read as another chain
-- link, so it is quoted. This is longest prefix's escape hatch, and it is what
-- keeps print-then-read stable (§2.7).
trailing :: Int -> Env -> Core -> String
trailing n env t = case t of
  Lam {} -> "⌜ " ++ go n env AtTop t ++ " ⌝"
  Let {} -> "⌜ " ++ go n env AtTop t ++ " ⌝"
  _      -> go n env AtTop t

-- | The one fragment change, named for what was crossed into.
crossingWord :: Crossing -> String
crossingWord x = case x of
  TrailingTerm  -> "the term"
  InSlot slot _ -> case slot of
    TypeOfAssume  _ (Ident h)   -> "type of " ++ h
    TypeOfDefine  _ (Ident h) _ -> "type of " ++ h
    ValueOfDefine _ (Ident h) _ -> "val of "  ++ h
    TypeOfClaim   _ (Ident h)   -> "type of " ++ h
    TypeOfGuess   _ (Ident h) _ -> "type of " ++ h

renderConstraint :: Int -> Env -> Constraint -> String
renderConstraint n env (Equate xi s t ty) =
  let (groups, env') = telescopeOf n env xi
   in concatMap (++ " ") groups
        ++ "⊢ " ++ go n env' AtTop s
        ++ " ≟ " ++ go n env' AtTop t
        ++ " : " ++ go n env' AtTop ty

-- | Ξ prints as §2.6 binder groups, outermost first, each scoping over the rest.
telescopeOf :: Int -> Env -> [Entry] -> ([String], Env)
telescopeOf _ env [] = ([], env)
telescopeOf n env (e : rest) =
  let (v, hint, ty) = case e of
        Hypothesis x (Ident h) s   -> (x, h, s)
        Definition x (Ident h) _ s -> (x, h, s)
      name  = freshen hint env
      group = "(" ++ name ++ " : " ++ go n env AtTop ty ++ ")"
      (groups, env') = telescopeOf n ((v, name) : env) rest
   in (group : groups, env')

pad :: Int -> String
pad ind = replicate ind ' '

-- --------------------------------------------------------------------------
-- The machine, made readable (§7.7's stepping mode)
-- --------------------------------------------------------------------------

-- | @pc@, @env@ and the frame stack, which is the whole of what stepping mode
-- shows. It is not a debugger bolted on: 'Machine' is plain data with no
-- functions inside it, so this is printing a value (§7.7).
--
-- This is a /display/ of the instruction data, not a concrete syntax for the
-- instruction language — that is MS2's and is deliberately not in the build
-- order. Nothing here parses back.
renderMachine :: Int -> Context -> Machine -> [String]
renderMachine n ctx m =
  ["pc"]    ++ indented (zipWith instruction [0 :: Int ..] (pc (exec m)))
    ++ ["env"]   ++ indented (map binding (env (exec m)))
    ++ ["stack"] ++ indented (map frame (stack (exec m)))
  where
    indented []  = ["  (empty)"]
    indented xs  = map ("  " ++) xs
    instruction i instr = show i ++ "  " ++ renderInstr n ctx instr
    binding (x, v) = x ++ " = " ++ renderValue n ctx v
    frame fr = "call, " ++ show (length (resume fr)) ++ " instruction(s) to resume"

renderInstr :: Int -> Context -> Instr -> String
renderInstr n ctx instr = case instr of
  Bind x op -> x ++ " = " ++ renderOp n ctx op
  Do op     -> renderOp n ctx op

-- | One instruction's op, as stepping mode shows it.
--
-- **The word comes from 'Thena.Ops.opKeyword' and the operands from
-- 'Thena.Ops.operandsOf'** — phase 25c. Until then this was a second spelling
-- table, and at phase 23b the two drifted: the @prim-@ renames moved
-- 'Thena.Ops.opKeyword' and left this printing @try@, @attack@, @solve@ and
-- @eliminate@, which since that phase name the /rules/ and not the ops this is
-- displaying. The user, 2026-08-25: *"Fix the other seven right away - we are
-- not leaving something like this behind."*
--
-- So only the shapes that are **not** "the word, then its operands in order"
-- are written out below. The wildcard is deliberate and is not a loss of
-- @-Wall@\'s totality: a new op still has to answer 'Thena.Ops.opKeyword' and
-- 'Thena.Ops.operandsOf', both total, and now renders correctly by default
-- instead of needing a third case that can be written wrong. Totality here
-- bought nothing — the case that drifted at 23b existed; it was just wrong.
renderOp :: Int -> Context -> Op -> String
renderOp n ctx op = case op of
  Ops.Ask    p k  -> word ++ " " ++ operand p ++ " " ++ answerKind k
  -- The one infix operand shape.
  Ops.Unify  l r  -> word ++ " " ++ operand l ++ " \8799 " ++ operand r
  -- Neither takes an operand: the declaration is a field, and the two crossings
  -- share a keyword and are told apart by the word after it.
  Ops.DefineData d -> word ++ " " ++ nameString (inductiveName d)
  Ops.CrossType   -> word ++ " type"
  Ops.CrossValue  -> word ++ " val"
  -- A hint is optional, and reads as a phrase rather than an argument.
  Ops.Prove Nothing  -> word
  Ops.Prove (Just h) -> word ++ " with " ++ operand h
  -- Written the way a rule file writes it (phase 23): the name, then the
  -- arguments as any other op\'s, spaced and unwrapped.
  Ops.Call nm as  -> unwords (word : nameString nm : map operand as)
  _               -> unwords (word : map operand (operandsOf op))
  where
    word    = Ops.opKeyword op
    operand = renderOperand n ctx

renderOperand :: Int -> Context -> Operand -> String
renderOperand n ctx o = case o of
  Ref x -> x
  Lit v -> renderValue n ctx v

renderValue :: Int -> Context -> Value -> String
renderValue n ctx v = case v of
  VText s            -> show s
  VTerm (Trailing t) -> "⌜" ++ renderCore n ctx t ++ "⌝"
  VTerm p            -> "⌜" ++ unwords (words (renderPartial n ctx p)) ++ "⌝"
  -- A hint, printed as it was written. It is not resolved and may never
  -- resolve — that is @resolve@'s answer, given in a rule body — so this is a
  -- printer for 'Raw' and not a detour through 'Core'.
  VSurface raw       -> "‹" ++ renderRaw raw ++ "›"
  -- A rule in an operand is a rule being passed to another rule, so its name
  -- is what identifies it; its body belongs to @:show@ on the rule, not here.
  VPair a b          -> "(" ++ renderValue n ctx a ++ ", " ++ renderValue n ctx b ++ ")"

answerKind :: AnswerKind -> String
answerKind k = case k of
  AText -> ":text"
  AName -> ":name"
  ATerm -> ":term"
  ARule -> ":rule"

renderCommandError :: CommandError -> String
renderCommandError e = case e of
  NoSuchCommand w      -> "no such command: " ++ w
  MissingArgument w    -> w ++ " needs an argument"
  UnexpectedArgument w -> w ++ " takes no argument"
  NotAsking            -> "nothing was asked"
  NoSuchGlobal x       -> "nothing named " ++ x ++ " has been declared"
  NotProving           -> "no proof is being worked on"
  AlreadyProving g     -> nameString g ++ " is still being proved — :suspend or :abandon it first"
  NoSuchProof x        -> "no suspended proof called " ++ x
  AlreadyDeclaredHere x -> x ++ " is already declared"
  NothingToUndo        -> "nothing to undo"
  NothingToRetry       -> "no choice point to retry"
  NoSuchChoice n       -> "no choice point " ++ show n
  LevelExpected u      -> u ++ " is not a universe, as in \"Type\8320\""
  NotThere m           -> renderMoveError m
  MixedLoad w          -> w ++ " takes either one script or any number of " ++ ruleSuffix ++ " files"
  ProofUnderway g      ->
    "a rule base may not be loaded while " ++ nameString g ++ " is being proved"
  ProofsSuspended gs   ->
    "a rule base may not be loaded while proofs are suspended: "
      ++ intercalate ", " (map nameString gs)

renderFailReason :: FailReason -> String
renderFailReason r = case r of
  Mismatch ctx a b ->
    renderCore 0 ctx a ++ " and " ++ renderCore 0 ctx b ++ " cannot be made equal"
  OccursCheck ctx x t ->
    "solving " ++ nameIn ctx x ++ " with " ++ renderCore 0 ctx t
      ++ " would define it in terms of itself"
  ScopeViolation ctx x y ->
    nameIn ctx y ++ " is not bound before " ++ nameIn ctx x
      ++ ", so there is no solution for it there"
  UniverseMismatch a b ->
    renderLevel a ++ " and " ++ renderLevel b ++ " are different universes"
  NotTypeable e -> "that term has no type" ++ concatMap ("\n  " ++) (renderTypeError 0 e)
  BinderNotAType e ->
    "that is not a type"
      ++ concatMap ("\n  " ++) (renderTypeError 0 e)
  GuessIllTyped e ->
    "that term does not have the hole's type"
      ++ concatMap ("\n  " ++) (renderTypeError 0 e)
  NameTaken n       -> n ++ " is already taken; ask fresh-name for one"
  NoGoalHere        -> "nothing is written down here, so there is no goal"
  NoRuleMatched     -> "no rule applies here"
  CannotEliminate e -> renderElimError e
  UnboundInBody x   -> "nothing named " ++ x ++ " in this body"
  NotAnIdentifier s -> show s ++ " is not a name"
  ExpectedText      -> "expected text"
  ExpectedTerm      -> "expected a term"
  CannotMove m      -> renderMoveError m
  NotAHole            -> "that is not a hole"
  NotAGuessHere       -> "that is not a guess"
  NotReadyToIntroduce -> "intro wants a hole of the form ? x ≐ (? x' : S . x') — attack it first"
  NothingToIntroduce  -> "that hole's type is neither a ∀ nor a let"
  NotYetPure pos    ->
    "not finished: " ++ renderPosition pos ++ " is still open, so there is no term yet"
  -- Phase 17b's four. 'CannotRead' reuses the renderer the driver's own
  -- @Failed@ already had — which is the whole reason 'SyntaxError' is one case
  -- rather than two.
  CannotRead e      -> renderSyntaxError e
  ExpectedSurface   -> "expected a hint"
  -- One reason, three messages (§8, phase 23): the name is unknown, the name
  -- is known at other arities, or clauses of the right arity all failed their
  -- heads. Which one it is falls out of the arities the reason carries.
  NoClauseMatched g got want
    | null want        -> "no rule is called " ++ nameString g
    | got `notElem` want ->
        nameString g ++ " takes " ++ orList (map show want)
          ++ " argument(s), given " ++ show got
    | otherwise        ->
        "no clause of " ++ nameString g ++ " applies here"

-- | @a@, @a or b@, @a, b or c@ — for a message that lists alternatives.
orList :: [String] -> String
orList xs = case reverse xs of
  []      -> ""
  [x]     -> x
  x : ys  -> intercalate ", " (reverse ys) ++ " or " ++ x

-- | A hint, printed as written (phase 17b).
--
-- 'Raw' is the parser's own tree, so this is the inverse of the parser and not
-- of the resolver: no context is consulted and no name is looked up. Parenthesised
-- wherever a subterm could otherwise re-associate, which is enough for a hint —
-- the elaborate layout decisions are 'renderCore'\'s and belong to terms.
renderRaw :: Raw -> String
renderRaw = raw False
  where
    raw _ (RawName x)       = x
    raw _ (RawUniverse l)   = "Type" ++ subscript l
    raw _ (RawUniverseAt l) = "Type {" ++ rawLevel l ++ "}"
    raw _ (RawAt x ls)      = x ++ " {" ++ unwords (map rawLevel ls) ++ "}"
    raw p (RawApp f a)      = wrap p (raw False f ++ " " ++ raw True a)
    raw p (RawArrow a b)    = wrap p (raw True a ++ " -> " ++ raw False b)
    raw p (RawLam bs b)     = wrap p ("λ" ++ concatMap binder bs ++ " -> " ++ raw False b)
    raw p (RawPi bs b)      = wrap p ("∀" ++ concatMap binder bs ++ " -> " ++ raw False b)
    raw p (RawLet x v ty b) =
      wrap p ("let " ++ x ++ " = " ++ raw False v ++ " : " ++ raw False ty
                ++ " in " ++ raw False b)
    raw p (RawClaim x ty b) =
      wrap p ("let ? " ++ x ++ " : " ++ raw False ty ++ " in " ++ raw False b)
    raw p (RawGuess x ty g b) =
      wrap p ("let ? " ++ x ++ " : " ++ raw False ty ++ " ≐ (" ++ raw False g ++ ")"
                ++ " in " ++ raw False b)
    raw p (RawPending _ b)  = wrap p ("κ ▸ " ++ raw False b)
    raw _ (RawQuote t)      = "⌜" ++ raw False t ++ "⌝"
    raw p (RawElim d ps mot ms is tgt) =
      wrap p ("elim " ++ d ++ group ps ++ " " ++ raw True mot
                ++ " " ++ group ms ++ " " ++ group is ++ " " ++ raw True tgt)

    binder (RawBinder x ty) = " (" ++ x ++ " : " ++ raw False ty ++ ")"
    group ts = "(" ++ intercalate ", " (map (raw False) ts) ++ ")"

    wrap True t  = "(" ++ t ++ ")"
    wrap False t = t

-- | Why the kernel refused, or where a development stopped being valid (§5.3).
renderKernelError :: Int -> KernelError -> [String]
renderKernelError n e = case e of
  NotClosed x  ->
    ["the term mentions " ++ show x ++ ", which nothing binds"]
  Overabstracted _ i ty ->
    [ "the assumption " ++ identString i ++ " has no matching binder in "
        ++ renderCore n [] ty
    ]
  Ill pos te   ->
    ("in " ++ renderPosition pos ++ ":") : map ("  " ++) (renderTypeError n te)

-- | Where in a development, said the way the user would say it.
renderPosition :: Position -> String
renderPosition p = case p of
  TheTerm          -> "the term"
  TheHole _ i      -> "the hole " ++ identString i
  TypeOf _ i       -> "the type of " ++ identString i
  ValueOf _ i      -> "the value of " ++ identString i
  GuessOf _ i      -> "the guess for " ++ identString i
  ConstraintAt k   -> "constraint " ++ show k
  Inside _ i inner -> renderPosition inner ++ ", inside the guess for " ++ identString i

-- | @:proofs@ — what the session is holding (§2.4).
renderProofs :: Int -> Maybe Proof -> [Proof] -> [String]
renderProofs n cur ps
  | null everything = ["no proofs"]
  | otherwise       = everything
  where
    everything = maybe [] (pure . line "▶ ") cur ++ map (line "  ") ps
    line mark pr =
      mark ++ nameString (proofName pr) ++ " : " ++ renderCore n [] (proofClaim pr)

renderMoveError :: MoveError -> String
renderMoveError m = case m of
  AtRoot         -> "already at the root"
  NotOnTheSpine  -> "that move is for the chain, and the focus is a core term"
  NotInCore      -> "that move is for a core term, and the focus is on the chain"
  NotAGuess      -> "only a guess has a body to enter"
  NotADefinition -> "only a definition has a value"
  StillReferenced -> "something below it still refers to it"
  NoCrossingIntoAConstraint -> "there is no position inside a constraint"
  NoSuchHole    -> "that names no hole or guess"
  NoSuchPart     -> "the focus has no such part"

-- --------------------------------------------------------------------------
-- Declarations, made readable (§3.7)
-- --------------------------------------------------------------------------

-- | Print a datatype back in the syntax it was declared in.
--
-- One constructor per line, opened by @{@ and separated by @;@, the way the
-- user's own preview of the syntax reads. Structural, with no width
-- calculation and no reflow — the same rule as the development printer (§2.7).
--
-- The two halves of a declaration's header are printed by different means and
-- that is not an accident: the parameters are binder groups, because that is
-- what puts them left of the @:@ and makes the parameter/index split syntactic
-- (§3.7), while the indices are printed as the type they bind, so that
-- 'renderCore' decides between @Nat -> Type\8320@ and @\8704 (n : Nat) -> \8230@ by
-- its own rule (§2.6).
renderInductive :: Int -> InductiveDefinition -> [String]
renderInductive n d = case inductiveConstructors d of
  [] -> [header ++ " where { }"]
  cs -> header : closed (zipWith (++) ("  { " : repeat "  ; ") (map line cs))
  where
    ps   = inductiveParameters d
    penv = envOf ps

    header =
      "data "
        ++ nameString (inductiveName d)
        ++ levelParams (inductiveLevels d)
        ++ concatMap group (zip [0 ..] ps)
        ++ " : "
        ++ renderCore n ps (piOver (inductiveIndices d) (Universe (inductiveLevel d)))
        ++ " where"

    -- A parameter's type sees the parameters before it and no more.
    group (i, e) =
      " ("
        ++ nameOf (entryVar e) penv
        ++ " : "
        ++ renderCore n (take i ps) (entryType e)
        ++ ")"

    -- The parameters are already in scope, so a constructor line binds only its
    -- own arguments. Its stored type abstracts the parameters as well — that is
    -- what makes it a function (§3.7) — and printing /that/ here would rebind
    -- them and freshen the second copy to @A1@.
    line c =
      nameString (constructorName c)
        ++ " : "
        ++ renderCore n ps (piOver (constructorArguments c) (constructorTarget d c))

    closed ls = init ls ++ [last ls ++ " }"]

-- | @:elim ‹datatype› [‹universe›]@ — the elimination rule (§3.7).
--
-- Headed @elim ‹datatype› :@ rather than @‹datatype›Elim :@, because there is
-- no such constant and inventing a name for the display would suggest one
-- (§3.7, reversed 2026-08-22). What is printed on the left is the concrete
-- syntax the user actually writes.
renderEliminator :: Int -> GlobalName -> Core -> [String]
renderEliminator n g ty =
  ["elim " ++ nameString g ++ " : " ++ renderCore n [] ty]

-- | @:show ‹name›@ on anything that is not a datatype.
--
-- The body is on its own line because it is what a generated wrapper /is/, and
-- the point of generating into the environment rather than conjuring inside a
-- tactic is that the student can go and look at it (§3.7).
renderGlobal :: Int -> GlobalName -> Core -> Maybe Core -> [String]
renderGlobal n g ty body =
  (nameString g ++ " : " ++ renderCore n [] ty)
    : case body of
        Nothing -> []
        Just b  -> [nameString g ++ " = " ++ renderCore n [] b]

renderDeclareError :: DeclareError -> String
renderDeclareError e = case e of
  AlreadyDeclared g -> nameString g ++ " is already declared"
  RepeatedName g    -> "this declaration uses the name " ++ nameString g ++ " twice"
  WrongNumberOfIndices g want got ->
    nameString g
      ++ " should target the family at "
      ++ show want
      ++ " index/indices, not "
      ++ show got
  NotStrictlyPositive g i ->
    "the argument "
      ++ identString i
      ++ " of "
      ++ nameString g
      ++ " puts the datatype to the left of an arrow"
  HigherOrderRecursion g i ->
    "the argument "
      ++ identString i
      ++ " of "
      ++ nameString g
      ++ " is a function into the datatype, which MS1 does not admit yet"
  NestedRecursion g i ->
    "the argument "
      ++ identString i
      ++ " of "
      ++ nameString g
      ++ " mentions the datatype under another type, which MS1 does not admit yet"
  ArgumentTooLarge g i l d ->
    "the argument "
      ++ identString i
      ++ " of "
      ++ nameString g
      ++ " lives in "
      ++ renderLevel l
      ++ ", which the datatype's own "
      ++ renderLevel d
      ++ " does not contain"
  ArgumentNotAType g i te ->
    "the argument " ++ identString i ++ " of " ++ nameString g ++ " is ill-typed"
      ++ concatMap ("\n  " ++) (renderTypeError 0 te)
  -- Worded as a bug report because it is one: nothing the user wrote is wrong,
  -- and the term the checker refused is one they never saw (phase 14).
  NoConfusionRejected g te ->
    "the generated " ++ nameString g ++ " does not typecheck, which is a bug in Thena"
      ++ concatMap ("\n  " ++) (renderTypeError 0 te)

-- --------------------------------------------------------------------------
-- Typing and conversion (§5.2)
-- --------------------------------------------------------------------------

-- | Why a term has no type. Each case renders its terms in the context the
-- error carries, not the session's: by the time inference has opened three
-- binders the terms mention variables the session has never heard of.
-- | Why @eliminate@ refused (§3.7, phase 17).
--
-- 'IndexTypeDepends' is the one worth reading twice: it is not a bug and not a
-- typo, it is §3.7's stated limit — homogeneous @Eq@ cannot state a constraint
-- on an index whose /type/ mentions an earlier index, and lifting it is what
-- \"John Major\" equality is for (@AGENDA.md@ item 10, deferred past MS1). The
-- message says so, because a user meeting it has done nothing wrong.
--
-- Since phase 19 it is raised only for an index that is /tied/ — one that
-- actually states an equation. A friendly index is abstracted outright and its
-- type may depend on an earlier index freely, which is why eliminating a
-- @Below n i@ whose indices are plain variables now works.
renderElimError :: ElimError -> String
renderElimError e = case e of
  TargetNotTypeable te ->
    "that target has no type" ++ concatMap ("\n  " ++) (renderTypeError 0 te)
  TargetNotInductive ctx t ty ->
    renderCore 0 ctx t ++ " is not a target: its type is " ++ renderCore 0 ctx ty
      ++ ", not a fully applied datatype"
  NoEquality g ->
    "eliminating at indices needs " ++ nameString g ++ ", which is not declared"
  IndexTypeDepends k (Ident i) ->
    "index " ++ show k ++ " (" ++ i ++ ") has a type that depends on an earlier index,"
      ++ "\n  so the equation constraining it cannot be stated"
  MotiveIllTyped te ->
    "the goal does not survive generalising the target"
      ++ concatMap ("\n  " ++) (renderTypeError 0 te)
  SchemeIllTyped te ->
    "the elimination does not prove this goal"
      ++ concatMap ("\n  " ++) (renderTypeError 0 te)

renderTypeError :: Int -> TypeError -> [String]
renderTypeError n e = case e of
  UnknownVariable ctx x       -> [nameIn ctx x ++ " is not in scope"]
  UnknownGlobal g        -> [nameString g ++ " is not declared"]
  WrongNumberOfLevelArguments g want got ->
    [ nameString g ++ " has " ++ count want "level parameter"
        ++ ", and was given " ++ count got "level argument"
    , "its level parameters are prenex, so a use supplies all of them or none"
    ]
  LevelArgumentsOnAConstant g got ->
    [ nameString g ++ " has no level parameters, but was given "
        ++ count got "level argument" ]
  LooseIndex i           -> ["a loose de Bruijn index " ++ show i ++ " reached the checker"]
  NotAType ctx t ty      ->
    [renderCore n ctx t ++ " is not a type — it has type " ++ renderCore n ctx ty]
  NotAFunction ctx t ty  ->
    [renderCore n ctx t ++ " cannot be applied — it has type " ++ renderCore n ctx ty]
  NotOfType ctx t want got why ->
    [ renderCore n ctx t ++ " has type " ++ renderCore n ctx got
    , "  but " ++ renderCore n ctx want ++ " was expected"
    ] ++ renderConversionFailure n why
  UnknownDatatype g         -> [nameString g ++ " is not a declared datatype"]
  NotAMotive ctx m ty    ->
    [ renderCore n ctx m ++ " is not a motive for this family"
    , "  it has type " ++ renderCore n ctx ty ++ ", which does not end in a universe"
    ]
  Unsaturated g ty       ->
    [nameString g ++ " is not given enough arguments — " ++ renderCore n [] ty ++ " is left over"]
  OverApplied g          -> [nameString g ++ " is given too many arguments"]

-- | Why two terms are not convertible: where, then what.
renderConversionFailure :: Int -> ConversionFailure -> [String]
renderConversionFailure n (ConversionFailure sites clash) =
  [ "  " ++ where_ ++ renderClash n clash ]
  where
    where_
      | null sites = ""
      | otherwise  = concatMap ((++ ", ") . siteWord) sites

siteWord :: Site -> String
siteWord site = case site of
  TheDomain i        -> "in the domain of " ++ identString i
  TheBody i          -> "under " ++ identString i
  TheFunction        -> "in the function"
  TheArgument        -> "in the argument"
  TheArgumentOf g k  -> "in argument " ++ show (k + 1) ++ " of " ++ nameString g
  TheParameter k     -> "in parameter " ++ show (k + 1)
  TheMotive          -> "in the motive"
  TheMethod k        -> "in method " ++ show (k + 1)
  TheIndex k         -> "in index " ++ show (k + 1)
  TheTarget          -> "in the target"

renderClash :: Int -> Clash -> String
renderClash n clash = case clash of
  HeadsDiffer ctx a b  -> renderCore n ctx a ++ " and " ++ renderCore n ctx b ++ " do not match"
  LevelsDiffer a b ->
    renderLevel a ++ " and " ++ renderLevel b ++ " are different universes"
  NamesDiffer a b      -> nameString a ++ " and " ++ nameString b ++ " are different names"
  VariablesDiffer a b  -> "the variables " ++ show a ++ " and " ++ show b ++ " are different"
  CountsDiffer a b     -> show a ++ " arguments against " ++ show b

-- | A variable's display name, taken from the context the error carries.
nameIn :: Context -> Var -> String
nameIn ctx x = nameOf x (envOf ctx)

nameString :: GlobalName -> String
nameString (GlobalName g) = g

identString :: Ident -> String
identString (Ident i) = i

-- | @:matches@ — the rules that apply at the focus, in dispatch order (§7.6).
--
-- One per line, spelled the way it would be invoked: the name, then a
-- placeholder per parameter. Not the head: the user asked what could be done
-- next, and the tests are why the answer is what it is rather than part of it.
--
-- **Order is meaning here.** §8 fixes dispatch order as definition order, so
-- the first line is the one the engine would try first when phase 16 makes it
-- able to. Ranking and grouping the list for display is a separate question and
-- deliberately deferred past MS5 (§8).
ruleSuffix :: String
ruleSuffix = ".thena.rules"

-- | One line per base, as @:load@ reports what it installed.
loadedLine :: RuleBase -> String
loadedLine b = "loaded " ++ baseName b ++ " (" ++ plural n "rule" ++ ")"
  where n = length (baseRules b)

plural :: Int -> String -> String
plural 1 w = "1 " ++ w
plural n w = show n ++ " " ++ w ++ "s"

-- | @:bases@ — **name, description if there is one, and path**, which is what
-- the user asked for, 2026-08-25. In search order, which is the point of
-- listing them at all.
renderBases :: [RuleBase] -> [String]
renderBases [] = ["no rule base is loaded"]
renderBases bs = concatMap one bs
  where
    one b = (baseName b ++ maybe "" ("   " ++) (baseDescription b)) : ["    " ++ basePath b]

-- | @:rules@ — the rules themselves, under the base each came from, in search
-- order. The per-rule line is @:matches@\', so a rule reads the same in both.
renderRuleBases :: [RuleBase] -> [String]
renderRuleBases [] = ["no rule base is loaded"]
renderRuleBases bs = concatMap one bs
  where
    one b = baseName b : map ("  " ++) (renderMatches (baseRules b))

renderRuleFileError :: FilePath -> RuleFileError -> [String]
renderRuleFileError path e = case e of
  NoRuleHeader ->
    [ path ++ ": needs a header line — rule base \8249name\8250 \8249description\8250 where" ]
  RuleSyntaxError se -> [path ++ ": " ++ renderSyntaxError se]
  RuleIllFormed es   -> map ((path ++ ": ") ++) (map renderRuleError es)

renderRuleError :: RuleError -> String
renderRuleError e = case e of
  DeclarationInBody g i    -> inRule g i ++ "a declaration is a command, not a rule-body operation"
  BoundNonProducing g i n  -> inRule g i ++ n ++ " is bound to an operation that leaves nothing"
  UnboundInRule g i n      -> inRule g i ++ "no parameter or earlier binding is called " ++ n
  NoSuchTest g w           -> "in " ++ nameString g ++ ": no such test: " ++ w
  BadOperands g i w        -> inRule g i ++ w ++ " was written with the wrong arguments"
  where
    inRule g i = "in " ++ nameString g ++ ", instruction " ++ show i ++ ": "

renderMatches :: [Rule] -> [String]
renderMatches [] = ["no rule applies here"]
renderMatches rs = map one rs
  where
    one r = unwords (nameString (ruleName r) : map placeholder (ruleParams r))
    placeholder n = "‹" ++ n ++ "›"

-- | @:choices@ — the live choice points, nearest first (§7.7).
--
-- One line each: the identifier @retry ‹n›@ names it by, the alternative it is
-- running now, and the ones still untried in dispatch order. Every choice point
-- listed has something left, which is the peek's invariant (§7.3) and the
-- reason there is no \"exhausted\" column.
--
-- The identifier is minted from the session's name counter, chosen by the user
-- 2026-08-23, so the numbers are unique and stable but not consecutive — every
-- binder minted in between spends the counter too.
renderChoices :: [ChoicePoint] -> [String]
renderChoices [] = ["no choice points"]
renderChoices cs = map one cs
  where
    one c =
      show (pointId c) ++ "  " ++ nameString (pointRule c)
        ++ "   untried: " ++ intercalate ", " (map nameString (pointAlts c))

-- | A definition's prenex level parameters, as a declaration writes them:
-- @{ℓ₀ ℓ₁}@, and nothing at all when there are none (phase 31b).
levelParams :: [LevelVar] -> String
levelParams [] = ""
levelParams vs = " {" ++ unwords (map levelVarName vs) ++ "}"

-- | A level as it was written — a numeral or a parameter's name.
rawLevel :: RawLevel -> String
rawLevel l = case l of
  RawLevelNum k -> show k
  RawLevelVar x -> x

-- | @1 thing@, @2 things@ — so a message never reads "1 level arguments".
count :: Int -> String -> String
count k what = show k ++ " " ++ what ++ (if k == 1 then "" else "s")
