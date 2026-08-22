{
module Thena.Syntax.Lexer
  ( Token (..)
  , Located (..)
  , Pos (..)
  , LexError (..)
  , lexTokens
  , isIdentifier
  ) where
}

%wrapper "posn"

$digit  = 0-9
$sub    = [₀₁₂₃₄₅₆₇₈₉]
$lower  = [a-z]
$upper  = [A-Z]
$idchar = [$lower $upper $digit \_ \']

@ident    = [$lower $upper \_] $idchar*
@universe = "Type" ($digit+ | $sub+)

tokens :-

  $white+       ;
  "->"          { keyword TArrow }
  "λ"           { keyword TLambda }
  \\            { keyword TLambda }
  "∀"           { keyword TForall }
  "("           { keyword TLParen }
  ")"           { keyword TRParen }
  "{"           { keyword TLBrace }
  "}"           { keyword TRBrace }
  ";"           { keyword TSemi }
  ":"           { keyword TColon }
  "="           { keyword TEquals }
  "?="          { keyword TEquate }
  "≟"           { keyword TEquate }
  "?"           { keyword TQuery }
  "≐"           { keyword TGuessed }
  "≈"           { keyword TGuessed }
  "|>"          { keyword TThen }
  "▸"           { keyword TThen }
  "|-"          { keyword TTurnstile }
  "⊢"           { keyword TTurnstile }
  "[|"          { keyword TOpenQuote }
  "⌜"           { keyword TOpenQuote }
  "|]"          { keyword TCloseQuote }
  "⌝"           { keyword TCloseQuote }
  "forall"      { keyword TForall }
  "let"         { keyword TLet }
  "in"          { keyword TIn }
  "elim"        { keyword TElim }
  @universe     { \p s -> Located (posOf p) (TUniverse (levelOf s)) }
  @ident        { \p s -> Located (posOf p) (TIdent s) }

{

-- | A source position: line and column, both counting from 1.
data Pos = Pos !Int !Int
  deriving (Eq, Show)

-- | A token and where it was written.
data Located a = Located Pos a
  deriving (Eq, Show)

data Token
  = TLambda
  | TForall
  | TArrow
  | TLParen
  | TRParen
  | TLBrace
  | TRBrace
  | TSemi
  | TColon
  | TEquals
  | TQuery
  | TGuessed
  | TThen
  | TTurnstile
  | TEquate
  | TOpenQuote
  | TCloseQuote
  | TLet
  | TIn
  | TElim
  | TUniverse Int
  | TIdent String
  deriving (Eq, Show)

-- | Structured, per §12 invariant 2: the position and the offending character,
-- never a rendered message.
data LexError = LexError Pos (Maybe Char)
  deriving (Eq, Show)

keyword :: Token -> AlexPosn -> String -> Located Token
keyword t p _ = Located (posOf p) t

posOf :: AlexPosn -> Pos
posOf (AlexPn _ line col) = Pos line col

-- | @Type₀@ and @Type0@ both mean level 0 (§2.6).
levelOf :: String -> Int
levelOf = foldl (\acc c -> acc * 10 + digitOf c) 0 . drop 4
  where
    digitOf c
      | c >= '0' && c <= '9' = fromEnum c - fromEnum '0'
      | otherwise            = fromEnum c - fromEnum '₀'

-- | The @posn@ wrapper's own 'alexScanTokens' calls 'error' on a bad character.
-- This loop is the same traversal with a structured failure instead.
lexTokens :: String -> Either LexError [Located Token]
lexTokens str0 = go (alexStartPos, '\n', [], str0)
  where
    go inp@(pos, _, _, str) =
      case alexScan inp 0 of
        AlexEOF                   -> Right []
        AlexError (p, _, _, rest) -> Left (LexError (posOf p) (firstOf rest))
        AlexSkip inp' _           -> go inp'
        AlexToken inp' len act    -> (act pos (take len str) :) <$> go inp'

    firstOf cs = case cs of
      c : _ -> Just c
      []    -> Nothing

-- | Is this string one identifier and nothing else?
--
-- Asked by "Thena.Engine" of an answer to an @AName@ question, so that an
-- 'Thena.Core.Term.Ident' the printer could not print back never enters a
-- component (§2.6). Answered by the lexer rather than by a second copy of
-- @\@ident@: keywords fail because they lex as keywords, and a leading digit
-- fails because no rule matches it.
isIdentifier :: String -> Bool
isIdentifier s = case lexTokens s of
  Right [Located _ (TIdent _)] -> True
  _                            -> False
}
