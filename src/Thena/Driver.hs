-- | The session, and the commands that act on it.
--
-- Nothing in this module or below it may assume a terminal, block on 'getLine',
-- or write to stdout (@PLAN.md@ §2.1, §12 invariant 4). The terminal lives in
-- "Thena.Repl" and nowhere else, which is why 'command' is a pure function and
-- why 'Rendered'/'RenderedDev' hand back data rather than a rendered line.
--
-- At phase 4 this module is rewritten around the loop of §7.8: a command
-- compiles to @[Instr]@ and the driver dispatches on the five 'Outcome' cases.
-- @:core@ and @:dev@ survive that, being view commands (§2.4).
module Thena.Driver
  ( Session (..)
  , newSession
  , Response (..)
  , SyntaxError (..)
  , command
  , parseCore
  , parseDevelopment
  ) where

import Thena.Core.Context (Context)
import Thena.Core.Term (Core)
import Thena.Development.Partial (Partial)
import Thena.Syntax.Concrete (Raw)
import Thena.Syntax.Lexer (LexError, lexTokens)
import Thena.Syntax.Parser (ParseError, parseTerm)
import Thena.Syntax.Resolve (ResolveError, resolve, resolvePartial)

-- | Everything the session holds. It grows into the proof list, the global
-- environment and the per-proof undo stacks (§2.4).
--
-- The name counter is session-global and an 'Int', per §2.4 and
-- @PREPLAN.md@ standing rule 7. Every mint threads it by hand.
newtype Session = Session { sessionNames :: Int }
  deriving (Eq, Show)

newSession :: Session
newSession = Session { sessionNames = 0 }

-- | What the driver hands back for a frontend to render.
data Response
  = Echoed String        -- ^ the line, to be shown back
  | Rendered Core        -- ^ a term, for the frontend to print (§2.6)
  | RenderedDev Partial  -- ^ a development, likewise (§2.7)
  | Failed SyntaxError
  | Quit
  deriving (Eq, Show)

-- | The three ways reading a term or development can fail. Each carries
-- structure; turning one into English is the frontend's job (§12 invariant 2).
--
-- This sum lives here because this module is what composes the pipeline. Phase 4
-- decides where shared error types live (@AGENDA.md@ item 18a) and may move it.
data SyntaxError
  = LexFailed LexError
  | ParseFailed ParseError
  | ResolveFailed ResolveError
  deriving (Eq, Show)

-- | Lex, parse, resolve as a core term. The context is empty at this phase, so
-- only closed terms resolve — §9's "a free @y@ is a scope error".
parseCore :: Int -> String -> Either SyntaxError (Core, Int)
parseCore = parseWith resolve

-- | Lex, parse, resolve as a development (§2.7's longest-prefix convention).
parseDevelopment :: Int -> String -> Either SyntaxError (Partial, Int)
parseDevelopment = parseWith resolvePartial

-- | Lex, parse, resolve. One pipeline; the resolver argument decides at which
-- type the raw tree is read.
parseWith
  :: (Context -> Int -> Raw -> Either ResolveError (a, Int))
  -> Int -> String -> Either SyntaxError (a, Int)
parseWith res n src = do
  ts  <- mapLeft LexFailed (lexTokens src)
  raw <- mapLeft ParseFailed (parseTerm ts)
  mapLeft ResolveFailed (res [] n raw)

command :: Session -> String -> (Session, Response)
command s line
  | Just src <- argumentOf ":core" line =
      respond s (parseCore (sessionNames s) src) Rendered
  | Just src <- argumentOf ":dev" line =
      respond s (parseDevelopment (sessionNames s) src) RenderedDev
  | line == ":quit" = (s, Quit)
  | otherwise       = (s, Echoed line)

-- | Shared by the two view commands. Top-level rather than a @where@ binding
-- because it is used at both 'Core' and 'Partial', and a @where@ binding under
-- a guard does not generalise.
respond
  :: Session -> Either SyntaxError (a, Int) -> (a -> Response)
  -> (Session, Response)
respond s r f = case r of
  Right (x, n') -> (s { sessionNames = n' }, f x)
  Left e        -> (s, Failed e)

-- | @argumentOf ":core" ":core t"@ is @Just "t"@; @":corex"@ is 'Nothing', so a
-- longer command starting with the same letters is not swallowed.
argumentOf :: String -> String -> Maybe String
argumentOf name line = case splitAt (length name) line of
  (before, rest)
    | before /= name -> Nothing
    | null rest      -> Just ""
    | otherwise      -> case rest of
        c : _ | c == ' ' -> Just (dropWhile (== ' ') rest)
        _                -> Nothing

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
