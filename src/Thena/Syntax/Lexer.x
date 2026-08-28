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
-- Reserved characters: the brackets, the separators, and every character that
-- spells an operator on its own. Nothing else is off limits inside a name.
$reserved = [\( \) \{ \} \[ \] \; \, \" λ ∀ ⊢ ≟ ≐ ≈ ▸ ⌜ ⌝]

-- A name starts with a letter — ASCII, or any non-reserved character above the
-- ASCII range — and continues with anything that is neither reserved nor
-- whitespace.
$idstart = [$lower $upper \_ \x80-\x10ffff] # $reserved
$idchar  = [\x21-\x10ffff] # $reserved

-- A string literal (phase 22b). The quote is already reserved, so this is
-- purely additive — no name has ever been able to contain one. Three escapes
-- and no more, and a string does not span a line.
--
-- An unterminated string is a lex error, but it is reported where scanning gave
-- up — the end of the line, not the opening quote — because that is where
-- Alex's longest match runs out. Good enough at the REPL and imprecise in a
-- file; on MS2's closeout list rather than fixed here, since a better message
-- needs a second 'LexError' constructor and a rule that matches the bad case.
$strchar = [$printable \t] # [\" \\]
@escape  = \\ [\" \\ n]
@string  = \" ($strchar | @escape)* \"

@ident    = $idstart $idchar*
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
  "|>"          { keyword TPending }
  "▸"           { keyword TPending }
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
  "where"       { keyword TWhere }
  "rule"        { keyword TRule }
  "when"        { keyword TWhen }
  "then"        { keyword TThen }
  ":-"          { keyword TNeck }
  $digit+       { \p s -> Located (posOf p) (TNumber (read s)) }
  @string       { \p s -> Located (posOf p) (TString (unescape s)) }
  "Type"        { \p _ -> Located (posOf p) TUniverseOpen }
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
  | TPending
  | TTurnstile
  | TEquate
  | TOpenQuote
  | TCloseQuote
  | TLet
  | TIn
  | TElim
  | TWhere
  | TRule
  | TWhen
  | TThen
  | TNeck
  | TNumber Int
  | TString String
  | TUniverse Int
  | TUniverseOpen
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

-- | The three escapes, undone. Takes the token including its quotes.
--
-- Total by construction: the lexer only hands it strings @\@string@ matched, so
-- a backslash is always followed by one of the three and the quotes are always
-- there. Written to fall through rather than to fail, because a partial
-- function here would be a crash in the lexer.
unescape :: String -> String
unescape = go . drop 1 . dropLast
  where
    dropLast str = if null str then str else init str

    go cs = case cs of
      '\\' : 'n'  : rest -> '\n' : go rest
      '\\' : '\\' : rest -> '\\' : go rest
      '\\' : '\"' : rest -> '\"' : go rest
      c          : rest -> c    : go rest
      []                -> []

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
