-- | Thena's own token classes, as 'Regex' values (MS7 phase 147).
--
-- **Moved out of "Thena.Language.Instral" by this phase**, unchanged, because
-- the surface and core advising grammars in "Thena.Language.Builtin" want the
-- same ones and neither module may import the other. No object language
-- declares these: they are the lexemes of Thena's own languages, which is why
-- they are written here rather than read out of a @language@ block.
--
-- **These are the /advising/ spellings and they are deliberately narrower than
-- "Thena.Syntax.Lexer"'s.** The lexer's @$idstart@ is a letter, @_@, or any
-- non-reserved character above ASCII, so @Γ⊢@ is one identifier to it and is
-- not one here. Narrower is the invariant: an advising grammar may accept less
-- than the running one and never more (@.claude\/RULINGS.md@). Widening these
-- is safe to do later and would need the inclusion test in
-- "Thena.Language.BuiltinTests" re-run, not rewritten.
module Thena.Language.Lexemes
  ( identRegex
  , numberRegex
  , stringRegex
  , charRegex
  , regexRegex
  , universeRegex
  ) where

import Thena.Language.Regex (Regex, parseRegex)

identRegex :: Regex
identRegex = regex "[a-zA-Z_][a-zA-Z0-9_'-]*"

numberRegex :: Regex
numberRegex = regex "-?[0-9]+"

stringRegex :: Regex
stringRegex = regex "\"[^\"]*\""

charRegex :: Regex
charRegex = regex "'[^']'"

-- | A regular expression literal (MS6 phase 100), @\/…\/@, with @\\\/@ allowed
-- inside it — which the lexer allows and a golden transcript uses
-- (@:core \/a\\\/b\/@), so the narrower @\/[^\/]+\/@ the first cut had would have
-- failed this phase's own currency test.
regexRegex :: Regex
regexRegex = regex "/([^/\\\\]|\\\\.)+/"

-- | @Type0@ or @Type₀@ — the lexer's @\@universe@, which is @\"Type\"@ followed
-- by ASCII digits or subscript ones. **@Type@ alone is not this**: it is
-- 'Thena.Syntax.Lexer.TUniverseOpen', a universe whose level is inferred, and
-- the grammars write it as a literal.
universeRegex :: Regex
universeRegex = regex "Type([0-9]+|[₀-₉]+)"

-- | **Total by construction**: every expression above is a constant of this
-- module and is parsed at every call, so a typo fails every test rather than
-- waiting for a rare input.
regex :: String -> Regex
regex src = case parseRegex src of
  Right r -> r
  Left _  -> error ("Thena.Language.Lexemes: bad built-in regex " ++ show src)
