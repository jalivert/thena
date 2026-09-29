-- | The offer at the cursor of a REPL line, **with recovery** (MS7 phase 138,
-- his design of 2026-09-29).
--
-- **The problem.** Phase 137 gave @instral@ a grammar whose slots are named
-- after the type they want, so @fill@'s slot is a different nonterminal from
-- @goto@'s. That narrows well and it refuses hard: write a tagged term literal
-- where the slot wants a @Name@ and the chart has no items at all, so the user
-- gets nothing exactly where they most want help.
--
-- **The move that does not work.** Widen the grammar so every slot accepts every
-- operand shape. His objection, and it is right: the TUI then cannot tell what
-- is /correct here/ from what is merely /tolerated/, and the offer that matters
-- drowns in the ones that do not.
--
-- **His design instead: a recovery /mode/, not a recovery rule.** One sentence —
-- *if the whole-line question has no answer at the cursor, ask a narrower
-- question about the unit the cursor is standing in.*
--
-- Why that is principled rather than a fudge:
--
-- * **The grammar does not change and does not lie.** It still says
--   @goto LC\`@ has no reading, because it has none. Nothing inside
--   "Thena.Language.Earley" learns to forget where it is.
-- * **Recovery is a second question**, asked here, above the parser. There is
--   precedent one phase back: 'Thena.View.Tokens.tokensView' asks the lexer and,
--   on failure, asks again with a fence appended.
-- * **The type narrowing survives as a real filter**, because the grammar was
--   never widened.
-- * @LC\`…\` atta@ and a bare @LC\`@ on an empty line both fall out of the one
--   rule rather than needing cases of their own.
--
-- **And the answer says it was recovered**, so the TUI can draw it differently —
-- his words: a different background, and a red underline under the whole line,
-- meaning /this will not run, but here is the help anyway/. That is his second
-- design principle exactly: do not prevent the strange thing, show what it will
-- cause.
--
-- **The unit is lexical, not space-delimited.** His first sketch split the line
-- on spaces, which fails on the case it exists for — @LC\`( λ x )\`@ has spaces
-- inside it. 'Thena.View.Tokens' knows where every token starts /and how far it
-- runs/ (phase 136), and already copes with an unclosed literal, so the unit is
-- a lookup rather than a guess.
module Thena.View.Statement
  ( statementOffer
  ) where

import Data.List (find, isPrefixOf)

import Thena.Language.Grammar (Grammar)
import Thena.Language.Instral (instralRules, statementHead)
import qualified Thena.Language.Earley as E
import Thena.Rules (RuleBase)
import Thena.View.Chart
  ( OfferView (..)
  , RecoveryView (..)
  , SymbolView (..)
  , Written (..)
  , displayOffer
  , offerAt
  )
import Thena.View.Tokens (TokenKind (..), TokenView (..), tokensView)

-- | The offer at the cursor of a REPL line.
--
-- The ordinary path is phase 137's: the @instral@ grammar, derived from the op
-- table and these bases. Recovery is tried **only** when that path reports
-- 'offeredStuck' — which is phase 134's field, and is exactly the condition
-- \"the text left of the cursor did not read\".
statementOffer :: [Grammar] -> [RuleBase] -> [Written] -> [Written] -> OfferView
statementOffer gs bs before after
  | Nothing <- offeredStuck whole = whole
  | otherwise                     = maybe whole id (recover gs bs before after)
  where
    whole = offerAt (instralRules bs) (E.StartAt statementHead) before after

-- | Ask about the unit the cursor is standing in.
--
-- 'Nothing' when there is no unit to ask about — an empty line, or a line whose
-- lexing fails for a reason no fence can mend. The caller then keeps the
-- unrecovered answer, which still carries 'offeredStuck' and so still says
-- something.
recover :: [Grammar] -> [RuleBase] -> [Written] -> [Written] -> Maybe OfferView
recover gs bs before after = do
  ts <- either (const Nothing) Just (tokensView line)
  unit <- unitAt cursor ts
  case unit of
    InsideLiteral lang prod open close ->
      let innerLeft  = slice open cursor
          innerRight = slice cursor close
       in case displayOffer gs lang prod [WrittenText innerLeft] [WrittenText innerRight] of
            Left _  -> Nothing
            Right o -> Just o
              { offeredRecovered =
                  Just (RecoveryView (open + 1) innerLeft (Just lang)) }
    BareWord start ->
      let word = slice start cursor
          -- **Asked at the start of the unit, not at the cursor, and then
          -- filtered by what has been typed.** A statement word is a
          -- 'E.Literal', and the chart matches one all or nothing: after @att@
          -- no item has moved, so asking at the cursor answers nothing at all —
          -- which is why @attack@ completed and @att@ did not. Asking where the
          -- word begins gives every word that may stand there, and the prefix
          -- says which of them the user is already writing.
          o = offerAt (instralRules bs) (E.StartAt statementHead) [] []
       in Just o
            { offeredOptions     = filter (startsWith word) (offeredOptions o)
            , offeredWanted      = filter (startsWith word) (offeredWanted o)
            , offeredProductions = offeredProductions o
            , offeredStuck       = Nothing
            , offeredRecovered   = Just (RecoveryView (start + 1) word Nothing)
            }
  where
    line   = textOf before ++ textOf after
    cursor = length (textOf before)
    slice from to = take (to - from) (drop from line)

-- | What the cursor is standing in. Offsets are from zero, into 'line'.
data Unit
  = InsideLiteral String (Maybe String) Int Int
    -- ^ the language, the production if the tag named one, the offset just after
    -- the opening tag, and the offset of the closing fence (or the line's end
    -- when it is not closed yet, which is the ordinary state of a line being
    -- typed).
  | BareWord Int
    -- ^ the offset the word under the cursor starts at.

-- | Which unit an offset falls in.
--
-- **A tagged term literal wins over the tokens inside it**, which is the whole
-- reason the unit is lexical: the literal's own text contains spaces and would
-- otherwise be several units.
unitAt :: Int -> [TokenView] -> Maybe Unit
unitAt cursor ts = case find inside (literals ts) of
  Just (lang, prod, open, close) -> Just (InsideLiteral lang prod open close)
  Nothing -> BareWord . startOf <$> find covers ts
  where
    inside (_, _, open, close) = cursor >= open && cursor <= close
    covers t = cursor > startOf t && cursor <= startOf t + length (tokenViewText t)
    startOf t = tokenViewColumn t - 1

-- | Every tagged term literal in the line: its language, the production its tag
-- named, where its text begins and where its closing fence is.
--
-- An opening tag is an 'ATag' of more than one character — @LC\`@, @LC[var]\`@ —
-- and a closing fence is an 'ATag' of exactly one. A literal left unclosed runs
-- to the end of the line, which is what a line being typed looks like.
literals :: [TokenView] -> [(String, Maybe String, Int, Int)]
literals ts = go ts
  where
    end = case reverse ts of
      []    -> 0
      t : _ -> tokenViewColumn t - 1 + length (tokenViewText t)

    go [] = []
    go (t : rest)
      | tokenViewKind t == ATag, length (tokenViewText t) > 1 =
          let open  = tokenViewColumn t - 1 + length (tokenViewText t)
              close = case break closer rest of
                (_, c : _) -> tokenViewColumn c - 1
                (_, [])    -> end
              (lang, prod) = tagParts (tokenViewText t)
           in (lang, prod, open, close) : go (drop 1 (dropWhile (not . closer) rest))
      | otherwise = go rest

    closer t = tokenViewKind t == ATag && length (tokenViewText t) == 1

-- | Does this offered symbol begin with what the user has typed?
--
-- **Only a literal can be filtered.** A token class or a nonterminal says what
-- /kind/ of thing may stand here, and a prefix cannot rule one out — @att@ may
-- still be the start of a name. Those stay in the list.
startsWith :: String -> SymbolView -> Bool
startsWith typed sym = case sym of
  ALiteralSymbol w -> typed `isPrefixOf` w
  _                -> True

-- | @LC\`@ and @LC[var]\`@ split into the language and the production it named.
tagParts :: String -> (String, Maybe String)
tagParts tag = case break (== '[') (init tag) of
  (lang, '[' : rest) -> (lang, Just (takeWhile (/= ']') rest))
  (lang, _)          -> (lang, Nothing)

-- | A region's text, as the lexer would see it.
--
-- **A splice contributes nothing**, because a REPL line has none: the frontend
-- holds one run of text either side of the cursor. If one ever arrives here it
-- is skipped rather than guessed at.
textOf :: [Written] -> String
textOf = concatMap one
  where
    one w = case w of
      WrittenText t      -> t
      WrittenPlaceholder -> "\9608"
      WrittenSplice      -> ""
