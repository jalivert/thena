-- | A line of Thena as coloured spans (MS7 phase 136, @ms7\/CLOSEOUT.md@ 18).
--
-- **His TUI lexed the line itself**, importing "Thena.Syntax.Lexer" and working
-- with 'Located', 'Pos' and 'Token' — the one place a frontend reached past the
-- views into the /lexer/. The item asked whether that is a gap at all, since a
-- token stream is the lexer's own output rather than an interpretation of
-- anything, and a frontend that holds the grammars could reasonably hold the
-- lexer too.
--
-- **HIS ruling, 2026-09-29: the engine says what a token is.** Two things a raw
-- 'lexTokens' cannot give a frontend decided it:
--
-- * **Extents.** 'Located' says where a token starts and nothing about how far
--   it runs, and the token cannot say either — @TForall@ is @forall@ or @∀@,
--   six characters or one. A highlighter needs the span, so 'Thena.Syntax.Lexer'
--   grew 'Spanned' and this takes it from there.
-- * **The retry.** A line being typed is usually /not/ a whole lexeme: an
--   unclosed region fails the lex outright, so a frontend has to know the trick
--   of appending a fence and lexing again. His TUI does exactly that, by hand.
--   'tokensView' owns it — see 'tokensView'\'s own note on which fences.
--
-- **The kinds are a closed set and deliberately few.** 'Token' has fifty-odd
-- constructors and a frontend colouring by constructor would have to be edited
-- every time the language grows a keyword. 'TokenKind' is what a /palette/ has
-- entries for.
module Thena.View.Tokens
  ( TokenKind (..)
  , TokenView (..)
  , tokensView
  , mendedTokens
  , offsetIn
  ) where

import Thena.Syntax.Lexer
  ( LexError (..)
  , Pos (..)
  , Spanned (..)
  , Token (..)
  , lexSpanned
  )

-- | What a token is, for the purpose of giving it a colour.
--
-- **Not one per 'Token' constructor.** A palette has a handful of entries and a
-- frontend should not have to grow one when the surface gains a keyword.
data TokenKind
  = AKeyword
    -- ^ @let@, @in@, @data@, @module@, @where@, @do@, @rule@, @elim@,
    -- @language@, @context@, @judgment@, @when@ — and the binders @λ@ and @∀@,
    -- which are keywords however they are spelled.
  | APunctuation
    -- ^ brackets, braces, parens, @;@ @,@ @:@ @=@ @->@ @⊢@ @≟@ @≐@ and the
    -- rest of the fixed notation.
  | AnIdentifier    -- ^ a name the user chose.
  | ANumber         -- ^ a numeral, and a universe level.
  | AText           -- ^ a string literal, quotes included.
  | ACharacter      -- ^ a character literal, quotes included.
  | ARegexLiteral   -- ^ @\/…\/@, slashes included.
  | AHole
    -- ^ @?@, @▸@ and @⌜⌝@ — the things that stand for what is not written yet.
    -- **Its own kind rather than punctuation**, because it is the one a reader
    -- most wants to find, and a frontend that treats it as a bracket cannot.
  | ATag
    -- ^ a region's opening tag, backtick included — @LC\`@ or @LC[var]\`@ —
    -- and the backtick that closes it. **This is what the fold hides**
    -- (@.jalivert\/TAGGED-LITERALS.md@); a frontend hiding tags hides exactly
    -- the spans of this kind.
  | AnObjectText
    -- ^ raw text inside a region: another language's notation, which Thena's
    -- lexer deliberately does not tokenise.
  | AnEscape        -- ^ @${@ and its closing brace — the splice fences.
  deriving (Eq, Show)

-- | One token, where it is, how far it runs, and what to colour it.
--
-- Line and column both count from 1, which is 'Thena.Syntax.Lexer.Pos'\'s own
-- convention. **The extent is @length tokenViewText@** — the text is the
-- source's, not the token's payload, so this is a span of the line even where
-- the two differ (a raw chunk's escapes).
data TokenView = TokenView
  { tokenViewLine   :: Int
  , tokenViewColumn :: Int
  , tokenViewText   :: String
  , tokenViewKind   :: TokenKind
  }
  deriving (Eq, Show)

-- | The tokens of a line, for colouring it.
--
-- **A line being typed is lexed even when it is not yet a whole one.** An
-- unclosed region fails 'lexSpanned' outright — the scanner reaches the end of
-- input inside 'Thena.Syntax.Lexer.Raw' and says so — which is the ordinary
-- state of a line the moment someone types @LC\`@. So a fence is appended and
-- the lex retried, and the tokens the fence itself produced are dropped.
--
-- **The two fences are the two the lexer has**: a backtick, which closes
-- @name\`…\`@, and @⟩@, which closes the @⟨@ surface alias. They are tried in
-- that order.
--
-- 'Left' is the position and offending character of a lex that fails for a
-- reason a fence cannot mend — a genuinely bad character. A frontend may colour
-- up to there and leave the rest plain.
tokensView :: String -> Either Pos [TokenView]
tokensView line = map viewOf <$> mendedTokens line

-- | Where a line and column falls in the text, **counting from zero**.
--
-- **A column restarts at 1 on every line, and an offset does not.** The two are
-- the same number only for a single-line entry, which is why three places in this
-- layer used one where they meant the other until MS7 phase 140: this module
-- dropped the mended fence by column, "Thena.View.Statement" found the unit under
-- the cursor by column, and neither was wrong until an entry was written over more
-- than one line. **It is defined once here and imported**, so there is one
-- conversion and nothing to keep in step.
offsetIn :: String -> Pos -> Int
offsetIn text (Pos l c) = lineStart + c - 1
  where
    starts = scanl (\acc ln -> acc + length ln + 1) 0 (lines text)
    lineStart = case drop (l - 1) starts of
      o : _ -> o
      -- **Cannot arise** — a position comes from lexing this text. Answered
      -- rather than crashed, because this is a view.
      []    -> 0

-- | **A line being typed, lexed** — the tokens of 'tokensView' before they become
-- views, for a caller that needs the real 'Spanned' stream (phase 140: the entry
-- split runs 'Thena.Surface.Layout.layoutFile' over it, and that takes tokens).
--
-- An unclosed region fails 'lexSpanned' outright, which is the ordinary state of a
-- line the moment someone types @LC\`@, so a fence is appended and the lex
-- retried; the tokens the fence itself produced are then dropped. **Dropped by
-- offset, not by column** — see 'offsetIn'. **And not by count**: a fence closes a
-- region and so produces a 'Thena.Syntax.Lexer.TTagClose' /and/ flushes the raw
-- chunk before it, and that chunk is real.
mendedTokens :: String -> Either Pos [Spanned]
mendedTokens line = case attempt line of
  Right ts -> Right ts
  Left e   -> case tryFences ["`", "⟩"] of
    Just ts -> Right ts
    Nothing -> Left (whereOf e)
  where
    whereOf (LexError p _) = p

    tryFences fs = case fs of
      []     -> Nothing
      f : rest -> case attempt (line ++ f) of
        Right ts -> Just (filter (within (length line)) ts)
        Left _   -> tryFences rest

    within n (Spanned p _ _) = offsetIn line p < n

    attempt = lexSpanned
viewOf :: Spanned -> TokenView
viewOf (Spanned (Pos l c) t src) = TokenView l c src (kindOf t)

kindOf :: Token -> TokenKind
kindOf t = case t of
  -- The binders are keywords whichever way they are written.
  TLambda       -> AKeyword
  TForall       -> AKeyword
  TLet          -> AKeyword
  TIn           -> AKeyword
  TElim         -> AKeyword
  TTrusted      -> AKeyword
  TWhere        -> AKeyword
  TData         -> AKeyword
  TModule       -> AKeyword
  TDo           -> AKeyword
  TRule         -> AKeyword
  TLanguage     -> AKeyword
  TContext      -> AKeyword
  TJudgment     -> AKeyword
  -- MS8 phase 158: the fourth block word (§4.8).
  TNotation     -> AKeyword
  TWhen         -> AKeyword

  TQuery        -> AHole
  TGuessed      -> AHole
  TPending      -> AHole

  TIdent _      -> AnIdentifier
  TNumber _     -> ANumber
  TUniverse _   -> ANumber
  TUniverseOpen -> ANumber
  TString _     -> AText
  TChar _       -> ACharacter
  TRegex _      -> ARegexLiteral

  TTagOpen _     -> ATag
  TTagOpenAt _ _ -> ATag
  TTagClose      -> ATag
  TRaw _         -> AnObjectText
  TEscapeOpen    -> AnEscape
  TEscapeClose   -> AnEscape
  -- A block body is another language's text, exactly as a region's is, and
  -- 'lexSpanned' never makes one anyway: 'tokensView' colours a line, and only
  -- 'lexModule' takes a block whole. No kind of its own for something no caller
  -- can produce.
  TBlock _ _     -> AnObjectText

  -- Everything else is fixed notation. **Written out rather than left to a
  -- wildcard**: a new token then fails @-Wall@ here and has to be classified,
  -- which is the whole reason the frontend is not doing this itself.
  TArrow        -> APunctuation
  TLParen       -> APunctuation
  TRParen       -> APunctuation
  TLBrace       -> APunctuation
  TRBrace       -> APunctuation
  TLBracket     -> APunctuation
  TRBracket     -> APunctuation
  TSemi         -> APunctuation
  TColon        -> APunctuation
  TComma        -> APunctuation
  TEquals       -> APunctuation
  TTurnstile    -> APunctuation
  TEquate       -> APunctuation
  TOpenQuote    -> APunctuation
  TCloseQuote   -> APunctuation
  TNeck         -> APunctuation
  TSpread       -> APunctuation
  TDashes       -> APunctuation
