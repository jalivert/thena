-- | The terminal frontend, and rendering.
--
-- The only module in the project that reads a key or writes to the screen
-- (§2.1, §12 invariant 4). Rendering lives here too, per §2.5 — 'Core' and
-- 'Partial' back to something the user can read. That is "for now": when phase
-- 7 adds eliminations this may be worth its own module.
module Thena.Repl
  ( repl
  , renderCore
  , renderPartial
  , renderSyntaxError
  ) where

import System.Console.Haskeline
  ( InputT
  , defaultSettings
  , getInputLine
  , outputStrLn
  , runInputT
  )

import Thena.Core.Context (Entry (..))
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
import Thena.Development.Partial (Constraint (..), Partial (..))
import Thena.Driver
  ( Response (..)
  , Session (..)
  , SyntaxError (..)
  , command
  , newSession
  )
import Thena.Syntax.Lexer (LexError (..), Pos (..), Token (..))
import Thena.Syntax.Parser (ParseError (..))
import Thena.Syntax.Resolve (DevForm (..), ResolveError (..))

-- | Run the read-eval-print loop until @:quit@ or end of input.
repl :: IO ()
repl = runInputT defaultSettings (loop newSession)

loop :: Session -> InputT IO ()
loop s = do
  input <- getInputLine "thena> "
  case input of
    Nothing   -> pure ()          -- end of input: Ctrl-D
    Just line ->
      case command s line of
        (_, Quit)  -> pure ()
        (s', resp) -> outputStrLn (renderResponse s' resp) >> loop s'

renderResponse :: Session -> Response -> String
renderResponse s resp = case resp of
  Echoed l      -> l
  Rendered t    -> renderCore (sessionNames s) t
  RenderedDev p -> renderPartial (sessionNames s) p
  Failed e      -> renderSyntaxError e
  Quit          -> ""

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
renderCore :: Int -> Core -> String
renderCore n = go n [] AtTop

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

-- | One chain link per line, at the current indent; a guess body indented one
-- level inside its parentheses. Structural breaks only — no width, no reflow.
renderPartial :: Int -> Partial -> String
renderPartial n = goP n [] 0

goP :: Int -> Env -> Int -> Partial -> String
goP n env ind p = case p of
  Trailing t -> pad ind ++ trailing n env t

  Under c rest -> case c of
    Assume v (Ident hint) ty ->
      let name = freshen hint env
       in row ind ("λ (" ++ name ++ " : " ++ go n env AtTop ty ++ ") ->")
            ++ goP n ((v, name) : env) ind rest

    Define v (Ident hint) val ty ->
      let name = freshen hint env
       in row ind
            ( "let " ++ name ++ " = " ++ go n env AtTop val
                ++ " : " ++ go n env AtTop ty ++ " in"
            )
            ++ goP n ((v, name) : env) ind rest

    Claim v (Ident hint) ty ->
      let name = freshen hint env
       in row ind ("let ? " ++ name ++ " : " ++ go n env AtTop ty ++ " in")
            ++ goP n ((v, name) : env) ind rest

    -- The body is rendered in 'env' WITHOUT the hole's own name, matching
    -- Γ_(?x ≐ P : S . p) = Γ_P (§4.5). Getting this wrong is invisible unless
    -- the body binds the hole's identifier — see the plan's §7.2.
    Guess v (Ident hint) g ty ->
      let name = freshen hint env
       in row ind ("let ? " ++ name ++ " : " ++ go n env AtTop ty ++ " ≐ (")
            ++ goP n env (ind + 2) g
            ++ "\n"
            ++ row ind ") in"
            ++ goP n ((v, name) : env) ind rest

  Pending k rest ->
    row ind (renderConstraint n env k ++ " ▸") ++ goP n env ind rest

-- | A 'Trailing' term that is itself a binder would re-read as another chain
-- link, so it is quoted. This is longest prefix's escape hatch, and it is what
-- keeps print-then-read stable (§2.7).
trailing :: Int -> Env -> Core -> String
trailing n env t = case t of
  Lam {} -> "⌜ " ++ go n env AtTop t ++ " ⌝"
  Let {} -> "⌜ " ++ go n env AtTop t ++ " ⌝"
  _      -> go n env AtTop t

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

-- | A line at an indent. Not called @line@: that name is already bound in
-- 'loop' and 'renderSyntaxError', and @-Wall@ says so.
row :: Int -> String -> String
row ind s = pad ind ++ s ++ "\n"
