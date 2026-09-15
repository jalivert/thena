-- | Reading a surface term from its source text (MS5 phase 61b).
--
-- Lex, lay out, parse. **Its own module rather than a function in
-- "Thena.Surface.Parser"**, because that one cannot mention
-- 'Thena.Errors.SyntaxError': "Thena.Errors" imports it for
-- 'Thena.Surface.Parser.SurfaceParseError', so the dependency only goes one
-- way.
--
-- **Its caller is "Thena.Rules"**, which resolves a tagged region's contents and
-- sits far below "Thena.Driver", where this used to live as @parseSurfaceTerm@.
-- Nothing is resolved here: what a name in a surface term denotes is
-- elaboration's answer.
module Thena.Surface.Read (parseSurfaceText) where

import Thena.Errors (SyntaxError (..))
import Thena.Surface.Concrete (Surface)
import Thena.Surface.Layout (layout)
import Thena.Surface.Parser (parseSurface)
import Thena.Syntax.Lexer (lexTokens)

parseSurfaceText :: String -> Either SyntaxError Surface
parseSurfaceText src = do
  ts  <- either (Left . LexFailed) Right (lexTokens src)
  ts' <- either (Left . LayoutFailed) Right (layout ts)
  either (Left . SurfaceParseFailed) Right (parseSurface ts')
