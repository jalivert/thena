-- | Object-language grammars, and the parsers generated from them
-- (MS5 phase 69).
--
-- **The seam, and it is deliberately the small version of one** — his ruling,
-- 2026-09-12, over branding object terms with the Surface parser: build a
-- minimal grammar notation now so the generated-parser path is exercised end to
-- end, and let MS6 replace the notation with the real sub-language (§7).
--
-- **What a declared language gets** (§6.6, his): an opaque @instral@ type of its
-- own, a **tag** as that type's only introduction form, and a one-way coercion
-- to 'Thena.Surface.Concrete.Surface'. The coercion is one-way because an
-- object term /is/ a Surface term — which is also why a generated parser
-- answers with one.
--
-- **One lexer serves every language** (§0b), so a grammar is written over
-- Thena's own tokens: a terminal is a quoted string that is lexed and matched by
-- token equality. That is the one simplification MS6 is expected to undo, since
-- §6.9's argument for a raw blob is that a /foreign/ language may keep its own
-- lexical rules.
module Thena.Instral.Grammar
  ( Language (..)
  , Production (..)
  , Item (..)
  , GrammarError (..)
  , language
  , parseObject
  ) where

import Data.List.NonEmpty (NonEmpty (..))

import Thena.Errors (SyntaxError (..))
import Thena.Syntax.Parser (ParseError (..))
import Thena.Surface.Concrete (Plicity (..), Surface (..), SurfaceArg (..))
import Thena.Syntax.Lexer (Located (..), Pos (..), Token (..), lexTokens)

-- | A declared object language: its name, and its productions in the order they
-- were written.
--
-- **Order is the disambiguation**, exactly as it is for a rule's clauses: the
-- generated parser tries productions in order and takes the first that matches
-- the whole input.
data Language = Language
  { languageName        :: String
  , languageProductions :: [Production]
  }
  deriving (Eq, Show)

-- | @‹constructor› : ‹item›…@ — one production.
--
-- **The constructor is a Surface name**, and what the production builds is that
-- name applied to whatever its recursive slots parsed. So an object term is an
-- ordinary Surface value the moment it exists, which is
-- @discussion\/object-language-modelling.md@'s whole point.
data Production = Production
  { productionName  :: String
  , productionItems :: [Item]
  }
  deriving (Eq, Show)

data Item
  = Terminal String
    -- ^ @\"·\"@ — matched by **lexing the literal and comparing tokens**, so a
    -- terminal may be any single token: an identifier, a bracket, an operator.
  | Recurse
    -- ^ the language itself, written by its own name
  | NameSlot
    -- ^ @ident@ — a bare name, which becomes a 'SurfaceName'
  deriving (Eq, Show)

data GrammarError
  = LeftRecursive String String
    -- ^ language, production — its first item is the language itself, so the
    -- generated parser would not terminate
  | EmptyProduction String String
    -- ^ a production with no items matches nothing and would loop
  | TerminalDoesNotLex String String
    -- ^ a quoted terminal that is not exactly one token
  deriving (Eq, Show)

-- | Build a language, refusing the two shapes the generated parser cannot run.
--
-- **Checked when the grammar is declared and not when it is used**, which is the
-- same bargain 'Thena.Rules.validate' makes: a grammar that cannot work is a
-- grammar that cannot be written.
language :: String -> [Production] -> Either [GrammarError] Language
language nm ps = case concatMap check ps of
  []   -> Right (Language nm ps)
  errs -> Left errs
  where
    check p = case productionItems p of
      []            -> [EmptyProduction nm (productionName p)]
      Recurse : _   -> [LeftRecursive nm (productionName p)]
      items         -> concatMap terminal items

    terminal it = case it of
      Terminal t | not (oneToken t) -> [TerminalDoesNotLex nm t]
      _                             -> []

    oneToken t = case lexTokens t of
      Right [_] -> True
      _         -> False

-- | Run a language's generated parser over the text of a tagged region.
--
-- **Ordered alternatives with backtracking, and the whole input must be
-- consumed.** A production matches its items left to right; a recursive slot
-- parses the longest prefix any production accepts, trying them in order.
parseObject :: Language -> String -> Either SyntaxError Surface
parseObject lang src = case lexTokens src of
  Left e   -> Left (LexFailed e)
  Right ts -> case [ t | (t, []) <- alternatives lang ts ] of
    t : _ -> Right t
    []    -> Left (ParseFailed (UnexpectedToken (posOf ts) (tokenOf ts)))
  where
    posOf ls = case ls of { Located p _ : _ -> p; [] -> Pos 1 1 }
    tokenOf ls = case ls of { Located _ t : _ -> t; [] -> TSemi }

-- | Every way this language parses a prefix of the tokens, in production order.
alternatives :: Language -> [Located Token] -> [(Surface, [Located Token])]
alternatives lang ts = concatMap try (languageProductions lang)
  where
    try p = [ (build p args, rest) | (args, rest) <- items (productionItems p) ts ]

    items []       rest = [([], rest)]
    items (i : is) rest =
      [ (as ++ bs, rest2)
      | (as, rest1) <- item i rest
      , (bs, rest2) <- items is rest1
      ]

    item i rest = case i of
      Terminal t -> case (lexTokens t, rest) of
        (Right [Located _ want], Located _ got : more) | want == got -> [([], more)]
        _                                                            -> []
      NameSlot -> case rest of
        Located _ (TIdent n) : more -> [([SurfaceName n], more)]
        _                           -> []
      -- **The recursive slot is where the ordering matters**, and it is why this
      -- answers with every parse rather than one: a production later in the list
      -- may be the one that lets the rest of the outer production match.
      Recurse -> [ ([t], more) | (t, more) <- alternatives lang rest ]

-- | A production's constructor applied to what its slots parsed.
--
-- **A production with no slots is the bare name**, not a nullary application —
-- 'SurfaceApp' is never empty (@discussion\/application-representation.md@).
build :: Production -> [Surface] -> Surface
build p args = case args of
  []     -> SurfaceName (productionName p)
  a : as -> SurfaceApp (SurfaceName (productionName p))
              (fmap (SurfaceArg Explicit) (a :| as))
