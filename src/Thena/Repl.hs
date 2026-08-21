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
  , renderCore
  , renderPartial
  , renderCursor
  , renderWhere
  , renderMachine
  , renderSyntaxError
  , renderInductive
  ) where

import System.Console.Haskeline
  ( InputT
  , defaultSettings
  , getInputLine
  , outputStrLn
  , runInputT
  )

import Thena.Core.Context (Context, Entry (..), entryType, entryVar, piOver)
import Thena.Core.Term
  ( Core (..)
  , GlobalName (..)
  , Ident (..)
  , Level (..)
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
  , Response (..)
  , Session (..)
  , Stop (..)
  , SyntaxError (..)
  , answer
  , command
  , newSession
  )
import Thena.Engine
  ( Exec (..)
  , Frame (..)
  , Machine (..)
  , Question (..)
  , cursor
  , proof
  , proofContext
  )
import Thena.Errors (FailReason (..), MoveError (..))
import Thena.Global.Declare (DeclareError (..))
import Thena.Global.Env
  ( ConstructorDefinition (..)
  , InductiveDefinition (..)
  , constructorTarget
  )
import Thena.Ops (AnswerKind (..), Instr (..), Op, Operand (..), Value (..))
import qualified Thena.Ops as Ops
import Thena.Syntax.Lexer (LexError (..), Pos (..), Token (..))
import Thena.Syntax.Parser (ParseError (..))
import Thena.Syntax.Resolve (DevForm (..), ResolveError (..))

import Data.Foldable (toList)
import Data.List (intercalate)

-- | Run the read-eval-print loop until @:quit@ or end of input.
repl :: IO ()
repl = runInputT defaultSettings (loop newSession Nothing)

loop :: Session -> Maybe Question -> InputT IO ()
loop s pending = do
  input <- getInputLine (prompt s pending)
  case input of
    Nothing   -> pure ()          -- end of input: Ctrl-D
    Just line -> do
      let t = turn s pending line
      mapM_ outputStrLn (turnOutput t)
      if turnQuit t then pure () else loop (turnSession t) (turnPending t)

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
  { turnOutput  :: [String]
  , turnSession :: Session
  , turnPending :: Maybe Question  -- ^ set when the next line is an answer
  , turnQuit    :: Bool
  }
  deriving (Eq, Show)

turn :: Session -> Maybe Question -> String -> Turn
turn s pending line =
  Turn (renderResponse s' resp) s' (waitingOn resp) (resp == Quit)
  where
    (s', resp) = case pending of
      Just _  -> answer s line
      Nothing -> command s line

waitingOn :: Response -> Maybe Question
waitingOn resp = case resp of
  Ran _ (Waiting q) -> Just q
  _                 -> Nothing

-- | Replay a script through 'turn' and render what a terminal would have shown,
-- prompts included. The golden tests' whole harness (§9, "golden REPL
-- transcripts are the natural regression test for a tool whose interface is the
-- REPL").
transcript :: [String] -> String
transcript = unlines . replay newSession Nothing
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
  ShownGlobal g ty body -> renderGlobal (counter s) g ty body
  Where c        -> renderWhere (counter s) c
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
  TThen       -> "▸"
  TTurnstile  -> "⊢"
  TEquate     -> "≟"
  TOpenQuote  -> "⌜"
  TCloseQuote -> "⌝"
  TLet        -> "let"
  TIn         -> "in"
  TUniverse k -> "Type" ++ subscript k
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
  Global (GlobalName g) -> g
  Universe (Level k)    -> "Type" ++ subscript k

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

  -- No concrete syntax yet (§2.6): phase 7 gives 'Eliminate' one and the user
  -- never writes a 'Canonical'. Rendered so the function is total, and
  -- deliberately in a bracketed form that does not parse back.
  Canonical (GlobalName f) as ->
    "‹" ++ unwords (f : map (go n env AtAtom) as) ++ "›"

  Eliminate (GlobalName d) ps m ms is t ->
    "‹elim "
      ++ unwords
           ( d
               : map (go n env AtAtom) ps
               ++ [go n env AtAtom m]
               ++ map (go n env AtAtom) ms
               ++ map (go n env AtAtom) is
               ++ [go n env AtAtom t]
           )
      ++ "›"

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
  IntoCanonArg _ before _       -> CanonArg (length before + 1)
  IntoElimParam _ before _ _ _ _ _ -> Param (length before + 1)
  IntoElimMotive {}             -> Motive
  IntoElimMethod _ _ _ before _ _ _ -> Method (length before + 1)
  IntoElimIndex _ _ _ _ before _ _  -> Index (length before + 1)
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

renderOp :: Int -> Context -> Op -> String
renderOp n ctx op = case op of
  Ops.Assume x ty -> "assume " ++ operand x ++ " " ++ operand ty
  Ops.Claim  x ty -> "claim "  ++ operand x ++ " " ++ operand ty
  Ops.Ask    p k  -> "ask "    ++ operand p ++ " " ++ answerKind k
  Ops.Say    msg  -> "say "    ++ operand msg
  Ops.Concat l r  -> "concat " ++ operand l ++ " " ++ operand r
  Ops.Along       -> "along"
  Ops.Into        -> "into"
  Ops.Back        -> "back"
  Ops.CrossType   -> "cross type"
  Ops.CrossValue  -> "cross val"
  Ops.Down part   -> partWord part
  Ops.DefineData d -> "data " ++ nameString (inductiveName d)
  where
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
  VSurface _         -> "‹unresolved›"
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
  NotThere m           -> renderMoveError m

renderFailReason :: FailReason -> String
renderFailReason r = case r of
  UnboundInBody x   -> "nothing named " ++ x ++ " in this body"
  NotAnIdentifier s -> show s ++ " is not a name"
  ExpectedText      -> "expected text"
  ExpectedTerm      -> "expected a term"
  CannotMove m      -> renderMoveError m

renderMoveError :: MoveError -> String
renderMoveError m = case m of
  AtRoot         -> "already at the root"
  NotOnTheSpine  -> "that move is for the chain, and the focus is a core term"
  NotInCore      -> "that move is for a core term, and the focus is on the chain"
  NotAGuess      -> "only a guess has a body to enter"
  NotADefinition -> "only a definition has a value"
  NoCrossingIntoAConstraint -> "there is no position inside a constraint"
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
  [] -> [header ++ " { }"]
  cs -> header : closed (zipWith (++) ("  { " : repeat "  ; ") (map line cs))
  where
    ps   = inductiveParameters d
    penv = envOf ps

    header =
      "data "
        ++ nameString (inductiveName d)
        ++ concatMap group (zip [0 ..] ps)
        ++ " : "
        ++ renderCore n ps (piOver (inductiveIndices d) (Universe (inductiveLevel d)))

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

nameString :: GlobalName -> String
nameString (GlobalName g) = g

identString :: Ident -> String
identString (Ident i) = i
