-- | The session, and the commands that act on it.
--
-- Nothing in this module or below it may assume a terminal, block on 'getLine',
-- or write to stdout (@PLAN.md@ §2.1, §12 invariant 4). The terminal lives in
-- "Thena.Repl" and nowhere else, which is why 'command' is a pure function and
-- why 'Rendered' hands back a 'Core' rather than a rendered line.
--
-- At phase 4 this module is rewritten around the loop of §7.8: a command
-- compiles to @[Instr]@ and the driver dispatches on the five 'Outcome' cases.
-- @:core@ survives that, being a view command (§2.4).
module Thena.Driver
  ( Session (..)
  , newSession
  , Response (..)
  , SyntaxError (..)
  , command
  , parseCore
  ) where

import Thena.Core.Term (Core)
import Thena.Syntax.Lexer (LexError, lexTokens)
import Thena.Syntax.Parser (ParseError, parseTerm)
import Thena.Syntax.Resolve (ResolveError, resolve)

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
  = Echoed String     -- ^ the line, to be shown back
  | Rendered Core     -- ^ a term, for the frontend to print (§2.6)
  | Failed SyntaxError
  | Quit
  deriving (Eq, Show)

-- | The three ways reading a term can fail. Each carries structure; turning one
-- into English is the frontend's job (§12 invariant 2).
--
-- This sum lives here because this module is what composes the pipeline. Phase 4
-- decides where shared error types live (@AGENDA.md@ item 18a) and may move it.
data SyntaxError
  = LexFailed LexError
  | ParseFailed ParseError
  | ResolveFailed ResolveError
  deriving (Eq, Show)

-- | Lex, parse, resolve. The context is empty at this phase, so only closed
-- terms resolve — §9's "a free @y@ is a scope error".
parseCore :: Int -> String -> Either SyntaxError (Core, Int)
parseCore n src = do
  ts  <- mapLeft LexFailed (lexTokens src)
  raw <- mapLeft ParseFailed (parseTerm ts)
  mapLeft ResolveFailed (resolve [] n raw)

command :: Session -> String -> (Session, Response)
command s line = case argumentOf ":core" line of
  Just src -> case parseCore (sessionNames s) src of
    Right (t, n') -> (s { sessionNames = n' }, Rendered t)
    Left e        -> (s, Failed e)
  Nothing
    | line == ":quit" -> (s, Quit)
    | otherwise       -> (s, Echoed line)

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
