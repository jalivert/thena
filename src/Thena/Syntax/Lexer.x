{
module Thena.Syntax.Lexer
  ( Token (..)
  , Located (..)
  , Pos (..)
  , LexError (..)
  , lexTokens
  , isIdentifier
  ) where

import Data.List (stripPrefix)
}

%wrapper "posn"

$digit  = 0-9
$sub    = [₀₁₂₃₄₅₆₇₈₉]
$lower  = [a-z]
$upper  = [A-Z]
-- Reserved characters: the brackets, the separators, and every character that
-- spells an operator on its own. Nothing else is off limits inside a name.
$reserved = [\( \) \{ \} \[ \] \; \, \" \` ⟨ ⟩ λ ∀ ⊢ ≟ ≐ ≈ ▸ ⌜ ⌝]

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

-- A character literal (MS5 phase 64), @'c'@ — the same three escapes, plus the
-- quote itself.
--
-- **Purely additive, for the string literal's reason one step over.** The single
-- quote is an @$idchar@ and not an @$idstart@, so no identifier has ever been
-- able to /begin/ with one — @t1'@ in the determinacy script keeps lexing
-- exactly as it did. Alex's longest match settles the rest: @'a'@ is three
-- characters and an identifier after it would have to start with a letter.
$chrchar = [$printable \t] # [\' \\]
@chresc  = \\ [\' \" \\ n]
@char    = \' ($chrchar | @chresc) \'

@ident    = $idstart $idchar*
@universe = "Type" ($digit+ | $sub+)

tokens :-

  $white+       ;
  -- **A comment is @--@ followed by a space** — his ruling, 2026-09-02:
  -- /"Let's have universal comments in all languages written `--` always
  -- followed by a space. If it is not followed by a space, it is not a comment
  -- and it can be some other identifier."/
  --
  -- **One syntax for all three kinds of file**, and that is the whole argument:
  -- /"They might not fit super naturally in the .thena.script files or
  -- .thena.rules files, but that's fine. Better they are uniform than three
  -- different ones."/
  --
  -- The space is what keeps @-@ available. It is an @$idchar@ but not an
  -- @$idstart@, so no identifier /begins/ @--@ today; requiring the space means
  -- none ever has to be given up either, and an operator spelled @-->@ or @--@
  -- stays writable. Alex takes the longest match, so @-- x@ is a comment and
  -- @-->@ is not.
  "--" [\ ] [^\n]*  ;
  "--" \n            ;
  "--"                { keyword TDashes }
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
  -- **@...@ is a token and reserves nothing** (MS5 phase 82). @.@ is an
  -- @$idchar@ but not an @$idstart@, so no identifier has ever begun with one
  -- and @...rest@ lexes as this token and then a name. An identifier that
  -- /contains/ dots — @a...b@ — is untouched, because this rule can only win at
  -- the start of a token.
  "..."         { keyword TSpread }
  "["           { keyword TLBracket }
  "]"           { keyword TRBracket }
  ","           { keyword TComma }
  "⌜"           { keyword TOpenQuote }
  "|]"          { keyword TCloseQuote }
  "⌝"           { keyword TCloseQuote }
  "forall"      { keyword TForall }
  "let"         { keyword TLet }
  "in"          { keyword TIn }
  "elim"        { keyword TElim }
  "where"       { keyword TWhere }
  -- **Reserved at MS4 phase 42b**, so a surface module can say @data@ inside a
  -- declaration block. Agda and Haskell both reserve it. The DC's own @data@
  -- command is unaffected: the driver splits the word off the line before this
  -- lexer sees the rest.
  "data"        { keyword TData }
  -- **Reserved at MS4 phase 43**, for a proof module's header. Narrows
  -- identifiers project-wide the way @data@ did, which is the price of the
  -- header being real syntax rather than a textual pre-pass like the rule
  -- base's — his call, 2026-09-02.
  "module"      { keyword TModule }
  -- **Reserved at MS4 phase 45**, for a block of the instruction language
  -- inside a surface term or at the top of a module. The third word to narrow
  -- identifiers project-wide, after @data@ and @module@, and the last the
  -- surface language is expected to need.
  "do"          { keyword TDo }
  -- **The escape opener is an ordinary token too** (MS5 phase 81). The region
  -- scanner emits one when it meets @${@ inside a tagged region; this is what
  -- lets the same spelling be read again when the region's text is lexed for
  -- the embedded parser, so a splice is written one way and read one way.
  "${"          { keyword TEscapeOpen }
  "rule"        { keyword TRule }
  -- **An object language's grammar declaration** (MS5 phase 69). The fourth
  -- word to narrow identifiers project-wide, after @data@, @module@ and @do@.
  --
  -- **@signature@ was the fifth and is gone** (MS5 phase 74, his ruling): an
  -- annotation is @f : Ty@ in column 1, told from a function's @f x = e@ by the
  -- token after the name, so it needs no word of its own. @ms5\/CLOSEOUT.md@ 11.
  "language"    { keyword TLanguage }
  "when"        { keyword TWhen }
  ":-"          { keyword TNeck }
  $digit+       { \p s -> Located (posOf p) (TNumber (read s)) }
  @string       { \p s -> Located (posOf p) (TString (unescape s)) }
  @char         { \p s -> Located (posOf p) (TChar (unchar s)) }
  "Type"        { \p _ -> Located (posOf p) TUniverseOpen }
  @universe     { \p s -> Located (posOf p) (TUniverse (levelOf s)) }
  @ident \`      { \p str -> Located (posOf p) (TTagOpen (init str)) }
  "⟨"           { keyword (TTagOpen "surface") }
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
  | TDashes
    -- ^ @--@ not followed by a space, which is therefore /not/ a comment
    -- (MS4 phase 43). No grammar uses it; it exists so that the lexer can say
    -- what it saw rather than failing, and so a later operator may claim it.
  | TData
  | TModule
  | TDo
  | TRule
  | TLanguage
  | TWhen
  | TNeck
  | TNumber Integer
  | TString String
  | TChar   Char
  | TLBracket
  | TRBracket
  | TComma
  | TSpread      -- ^ @...@, the list-pattern tail marker (MS5 phase 82)
  | TUniverse Int
  | TUniverseOpen
  | TIdent String
    -- The tagged-region tokens (MS5 phase 60). A region is @name\`…\`@: the
    -- lexer finds its extent and hands over **raw text**, because an object
    -- language has its own lexical rules and tokenising it here would impose
    -- Thena's (@discussion\/the-five-languages.md@ §6.9).
  | TTagOpen String   -- ^ @name\`@ — the tag, without its backtick
  | TRaw String       -- ^ a run of raw text inside a region
  | TEscapeOpen       -- ^ the escape opener: raw text stops, ordinary lexing resumes
  | TEscapeClose      -- ^ the brace that closes an escape
  | TTagClose         -- ^ the backtick that closes a region
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

-- | One character, with its quotes taken off and its escape undone.
--
-- Total by construction, like 'unescape': the lexer only hands it what @\@char@
-- matched, which is exactly one character or one escape between two quotes. The
-- fall-through is what keeps it total rather than a crash in the lexer.
unchar :: String -> Char
unchar s = case drop 1 s of
  '\\' : 'n'  : _ -> '\n'
  '\\' : c    : _ -> c
  c          : _ -> c
  []             -> ' '

-- | @Type₀@ and @Type0@ both mean level 0 (§2.6).
levelOf :: String -> Int
levelOf = foldl (\acc c -> acc * 10 + digitOf c) 0 . drop 4
  where
    digitOf c
      | c >= '0' && c <= '9' = fromEnum c - fromEnum '0'
      | otherwise            = fromEnum c - fromEnum '₀'

-- | The @posn@ wrapper's own 'alexScanTokens' calls 'error' on a bad character.
-- This loop is the same traversal with a structured failure instead.
-- | Where the scanner is standing (MS5 phase 60).
--
-- Outside every region the list is empty and Alex does the work. 'Raw' means
-- the characters belong to an embedded language and are handed over untouched;
-- 'Esc' means an escape inside a region has resumed ordinary lexing, and the
-- 'Int' is how many braces are open inside it, so that the escape's own closing
-- brace can be told from a brace the escaped code wrote.
--
-- **It is a stack because regions nest through escapes and only through them**
-- (@discussion\/the-five-languages.md@ §6.9): raw text never contains another
-- region, so a tag met inside an escape pushes and everything stays decidable.
data Mode = Raw !Char | Esc !Int

lexTokens :: String -> Either LexError [Located Token]
lexTokens str0 = loop [] (alexStartPos, '\n', [], str0)

-- | The @posn@ wrapper's own 'alexScanTokens' calls 'error' on a bad character.
-- This loop is the same traversal with a structured failure instead, and with
-- the region modes above threaded through it.
loop :: [Mode] -> AlexInput -> Either LexError [Located Token]
loop modes inp@(pos, _, _, str) = case modes of
  Raw fence : outer -> raw fence outer pos str
  _ -> case alexScan inp 0 of
    AlexEOF
      | null modes -> Right []
      -- An escape that never closed. Reported where scanning gave up, which is
      -- the end of input rather than the region's start — the same imprecision
      -- an unterminated string literal has, and owed the same better message.
      | otherwise  -> Left (LexError (posOf pos) Nothing)
    AlexError (p, _, _, rest) -> Left (LexError (posOf p) (firstOf rest))
    AlexSkip inp' _           -> loop modes inp'
    AlexToken inp' len act ->
      let t@(Located lp tk) = act pos (take len str)
       in case (modes, tk) of
            -- **An escape opened by the main lexer pushes the same mode the
            -- region scanner pushes** (MS5 phase 81), so its closing brace
            -- becomes a 'TEscapeClose' here exactly as it does there. Without
            -- it an escape outside a region ends in a bare closing brace, which
            -- the layout pass then reports as closing a block nobody opened.
            -- NB: no literal braces in this comment — Alex counts them.
            (_, TEscapeOpen) -> (t :) <$> loop (Esc 0 : modes) inp'
            -- The brace that closes the escape, rather than one its code wrote.
            (Esc 0 : outer, TRBrace) ->
              (Located lp TEscapeClose :) <$> loop outer inp'
            (Esc d : outer, TRBrace) -> (t :) <$> loop (Esc (d - 1) : outer) inp'
            (Esc d : outer, TLBrace) -> (t :) <$> loop (Esc (d + 1) : outer) inp'
            -- Which character closes the region depends on how it was opened:
            -- a tag's own backtick, or the ⟩ that closes the ⟨ alias.
            (_, TTagOpen _)
              | take 1 (take len str) == "⟨" -> (t :) <$> loop (Raw '⟩' : modes) inp'
              | otherwise                    -> (t :) <$> loop (Raw '`' : modes) inp'
            _                        -> (t :) <$> loop modes inp'
  where
    firstOf cs = case cs of
      c : _ -> Just c
      []    -> Nothing

-- | Raw text, to the fence that closes the region.
--
-- Three things end a chunk: the closing backtick, an escape opener (a dollar
-- followed by an open brace), and the end of input, which is a failure. A
-- backslash escapes a backtick, a backslash, and a dollar, so a region can
-- carry all three literally.
-- | What a backslash may escape inside raw text.
rawEscapes :: String
rawEscapes = ['`', '\\', '$', '⟩']

-- | The two characters that open an escape, written without a literal brace
-- because Alex counts braces inside a code fragment and would end this one.
escapeOpener :: String
escapeOpener = ['$', toEnum 123]

raw :: Char -> [Mode] -> AlexPosn -> String -> Either LexError [Located Token]
raw fence outer p0 s0 = chunk p0 p0 s0 ""
  where
    chunk began p cs acc = case cs of
      [] -> Left (LexError (posOf p) Nothing)
      '\\' : c : rest
        | c `elem` rawEscapes ->
            chunk began (alexMove (alexMove p '\\') c) rest (c : acc)
      c : rest
        | c == fence ->
            ((flush began acc ++) . (Located (posOf p) TTagClose :))
              <$> loop outer (alexMove p c, c, [], rest)
      _ | Just rest <- stripPrefix escapeOpener cs ->
            let p1 = foldl alexMove p escapeOpener
             in ((flush began acc ++) . (Located (posOf p) TEscapeOpen :))
                  <$> loop (Esc 0 : Raw fence : outer) (p1, last escapeOpener, [], rest)
      c : rest -> chunk began (alexMove p c) rest (c : acc)

    -- A chunk is reported at the position it began, not where it ended, so an
    -- embedded parser's own positions can be offset from something meaningful.
    flush began acc
      | null acc  = []
      | otherwise = [Located (posOf began) (TRaw (reverse acc))]

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
