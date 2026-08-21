-- | The terminal frontend, and rendering.
--
-- The only module in the project that reads a key or writes to the screen
-- (§2.1, §12 invariant 4). Rendering lives here too, per §2.5 — 'Core' back to
-- something the user can read. That is "for now": when phase 3 adds developments
-- and phase 7 adds eliminations, this may be worth its own module.
module Thena.Repl
  ( repl
  , renderCore
  , renderSyntaxError
  ) where

import System.Console.Haskeline
  ( InputT
  , defaultSettings
  , getInputLine
  , outputStrLn
  , runInputT
  )

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
import Thena.Driver
  ( Response (..)
  , Session (..)
  , SyntaxError (..)
  , command
  , newSession
  )
import Thena.Syntax.Lexer (LexError (..), Pos (..), Token (..))
import Thena.Syntax.Parser (ParseError (..))
import Thena.Syntax.Resolve (ResolveError (..))

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
  Echoed line -> line
  Rendered t  -> renderCore (sessionNames s) t
  Failed e    -> renderSyntaxError e
  Quit        -> ""

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
  where
    at (Pos line col) = show line ++ ":" ++ show col ++ ": "

describe :: Token -> String
describe t = case t of
  TLambda     -> "λ"
  TForall     -> "∀"
  TArrow      -> "->"
  TLParen     -> "("
  TRParen     -> ")"
  TColon      -> ":"
  TEquals     -> "="
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

-- | Render a term.
--
-- Takes the session's name counter because it must 'open' every 'Scope' to
-- descend, 'open' needs a 'Var', and only 'fresh' mints one. It cannot inspect
-- the term's existing 'Var's to pick a safe number instead — 'Var'\'s
-- constructor is hidden (§2.6, §3.4).
renderCore :: Int -> Core -> String
renderCore n = go n [] AtTop

go :: Int -> [(Var, String)] -> Prec -> Core -> String
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
chainLam :: Int -> [(Var, String)] -> [String] -> Core -> String
chainLam n env acc term = case term of
  Lam (Ident hint) dom sc ->
    let (v, n1) = fresh n
        name    = freshen hint env
        group   = "(" ++ name ++ " : " ++ go n1 env AtTop dom ++ ")"
     in chainLam n1 ((v, name) : env) (group : acc) (open v sc)
  _ -> unwords (reverse acc) ++ " -> " ++ go n env AtTop term

-- | The same for ∀, except that a non-dependent 'Pi' ends the run — it goes on
-- to render as @S -> B@ through 'go'.
chainPi :: Int -> [(Var, String)] -> [String] -> Core -> String
chainPi n env acc term = case term of
  Pi (Ident hint) dom sc
    | dependent n sc ->
        let (v, n1) = fresh n
            name    = freshen hint env
            group   = "(" ++ name ++ " : " ++ go n1 env AtTop dom ++ ")"
         in chainPi n1 ((v, name) : env) (group : acc) (open v sc)
  _ -> unwords (reverse acc) ++ " -> " ++ go n env AtTop term

nameOf :: Var -> [(Var, String)] -> String
nameOf v env = case lookup v env of
  Just s  -> s
  Nothing -> "‹" ++ show v ++ "›"

-- | A binder whose identifier is already in scope is renamed, because a term
-- whose body refers to the /outer/ one would otherwise print as one that
-- re-parses to the inner (§2.6). Keywords are avoided for the same reason.
freshen :: String -> [(Var, String)] -> String
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
