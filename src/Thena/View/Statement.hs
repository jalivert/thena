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
import Thena.Driver (entryBindings)
import Thena.Instral.Type (Ty)
import Thena.Instral.Commands (isCommandLine)
import Thena.Language.Instral
  (commandHead, commandRules, instralRules, standsAt, statementHead)
import qualified Thena.Language.Earley as E
import Thena.Rules (RuleBase)
import Thena.View.Chart
  ( BoundView (..)
  , OfferView (..)
  , RecoveryView (..)
  , SymbolView (..)
  , Written (..)
  , StuckView (..)
  , displayOffer
  , offerAt
  )
import Thena.View.Entry (Split (..), splitEntry)
import Thena.View.Type (displayType)
import Thena.Syntax.Lexer (Pos (..))
import Thena.View.Tokens
  (TokenKind (..), TokenView (..), offsetIn, tokensView)

-- | The offer at the cursor of a REPL line.
--
-- The ordinary path is phase 137's: the @instral@ grammar, derived from the op
-- table and these bases. Recovery is tried **only** when that path reports
-- 'offeredStuck' — which is phase 134's field, and is exactly the condition
-- \"the text left of the cursor did not read\".
statementOffer :: [Grammar] -> [RuleBase] -> [Written] -> [Written] -> OfferView
statementOffer gs bs before after = answer { offeredBound = bound }
  where
    text   = textOf before ++ textOf after
    cursor = length (textOf before)

    -- **The entry is cut at the cursor's own instruction** (MS7 phase 140). The
    -- chart answers about one statement read from the start of what it is given,
    -- so an entry of three instructions answered nothing at all until the two
    -- above were taken off the front. 'splitEntry' finds the cut with the real
    -- layout pass; @(\"\", 0)@ is the single-instruction case every earlier phase
    -- saw, and the fallback when the text does not lay out.
    (prefix, at)
      | asCommand = ("", 0)
      | otherwise = case splitEntry text cursor of
          Just (Split p o) -> (p, o)
          Nothing          -> ("", 0)

    before' = dropWritten at before

    -- **A @:@-line is asked about at its own head, and is never split** (MS7 phase
    -- 142). A command is a whole line: @;@ is not a separator in one and a newline
    -- ends it, so the entry machinery does not apply. The discriminator is the
    -- driver's own, shared rather than copied.
    asCommand = isCommandLine (textOf before)

    head' | asCommand = commandHead
          | otherwise = statementHead

    -- **Each line is asked against the rules that could answer it, and no
    -- others** — see 'commandRules' for the measurement that forced this.
    rules | asCommand = commandRules gs
          | otherwise = instralRules gs bs

    whole
      | asCommand = offerAt rules (E.StartAt commandHead) before after
      | otherwise = offerAt rules (E.StartAt statementHead) before' after

    answer
      | Nothing <- offeredStuck whole = shift whole
      | otherwise = maybe (shift whole) shift (recover gs bs rules head' before' after)

    -- **Positions are reported against the whole entry**, not against the
    -- instruction the question was asked about: the frontend passed the entry and
    -- a completion replaces characters of it.
    shift o
      | at == 0   = o
      | otherwise = o
          { offeredRecovered =
              fmap
                (\r -> r
                   { recoveredColumn = recoveredColumn r + at
                   -- **The span shifts with the column.** It did not, at first, and
                   -- the slice it named on a two-instruction entry was the text of
                   -- the instruction above — the kind of wrong a frontend draws
                   -- rather than crashes on.
                   , recoveredSpan =
                       let (a, b) = recoveredSpan r in (a + at, b + at)
                   })
                (offeredRecovered o)
          , offeredStuck =
              fmap (\k -> k { stuckAt = stuckAt k + at }) (offeredStuck o)
          }

    -- **What the lines above bound, kept to what may stand here.** The types come
    -- from the type checker over those lines ('Thena.Driver.entryBindings'); which
    -- of them fit is 'standsAt', asked against the slots this offer named. A
    -- frontend is handed the answer and never the rule.
    bound =
      [ BoundView n (displayType t)
      | (n, t) <- if null prefix then [] else entryBindings gs bs prefix
      , fits t
      ]

    slots = [ nm | ANonterminalSymbol nm <- offeredOptions answer ++ offeredWanted answer ]

    fits :: Ty -> Bool
    fits t = any (standsAt t) slots

-- | Drop this many characters from the front of a run list.
--
-- **The runs are cut, not flattened.** A 'WrittenPlaceholder' is one character
-- and a 'WrittenSplice' is none, which is what 'textOf' says, so the count and
-- the list stay in step.
dropWritten :: Int -> [Written] -> [Written]
dropWritten n ws
  | n <= 0 = ws
  | otherwise = case ws of
      [] -> []
      WrittenText t : rest
        | length t > n -> WrittenText (drop n t) : rest
        | otherwise    -> dropWritten (n - length t) rest
      WrittenPlaceholder : rest -> dropWritten (n - 1) rest
      WrittenSplice : rest      -> dropWritten n rest

-- | Ask about the unit the cursor is standing in.
--
-- 'Nothing' when there is no unit to ask about — an empty line, or a line whose
-- lexing fails for a reason no fence can mend. The caller then keeps the
-- unrecovered answer, which still carries 'offeredStuck' and so still says
-- something.
recover
  :: [Grammar] -> [RuleBase] -> [E.Rule] -> String -> [Written] -> [Written]
  -> Maybe OfferView
recover gs _bs rules head' before after = do
  ts <- either (const Nothing) Just (tokensView line)
  unit <- unitAt cursor (atOffsets line ts)
  case unit of
    InsideLiteral l ->
      let innerLeft  = slice (litOpen l) cursor
          innerRight = slice cursor (litClose l)
       in case displayOffer gs (litLang l) (litProd l)
                 [WrittenText innerLeft] [WrittenText innerRight] of
            Left _  -> Nothing
            Right o -> Just o
              { offeredRecovered =
                  Just (RecoveryView (litOpen l + 1) innerLeft (Just (litLang l))
                          (litFrom l + 1, litTo l + 1)) }
    -- **A @:@-command word, which a bare word cannot serve** (MS7 phase 142).
    -- @:inf@ lexes as two tokens, @:@ and @inf@, so the bare-word unit would ask
    -- about @inf@ and filter the command words by it — and none of them starts
    -- with @inf@. @:where@ is worse: its second token is a /keyword/, not an
    -- identifier. So the unit is the colon and whatever follows it, together.
    CommandWord start stop ->
      let typed = slice start cursor
          o = offerAt rules (E.StartAt commandHead) [] []
       in Just o
            { offeredOptions     = filter (startsWith typed) (offeredOptions o)
            , offeredWanted      = filter (startsWith typed) (offeredWanted o)
            , offeredStuck       = Nothing
            , offeredRecovered =
                Just (RecoveryView (start + 1) typed Nothing (start + 1, stop + 1))
            }
    BareWord start stop ->
      let word = slice start cursor
          -- **Asked at the start of the unit, not at the cursor, and then
          -- filtered by what has been typed.** A statement word is a
          -- 'E.Literal', and the chart matches one all or nothing: after @att@
          -- no item has moved, so asking at the cursor answers nothing at all —
          -- which is why @attack@ completed and @att@ did not. Asking where the
          -- word begins gives every word that may stand there, and the prefix
          -- says which of them the user is already writing.
          -- **Context-free for a statement, and context-ful inside a
          -- @:@-command.** Phase 138's reason for the empty context stands for a
          -- statement: @LC\`x\` atta@ has no reading up to the word, so asking
          -- with it answers nothing. A command line is different — @:step @ reads
          -- perfectly — so there the text before the word is used, and @:step o@
          -- offers @on@ and @off@ instead of nothing.
          ctx | isCommandLine line = [WrittenText (take start line)]
              | otherwise          = []
          o = offerAt rules (E.StartAt head') ctx []
       in Just o
            { offeredOptions     = filter (startsWith word) (offeredOptions o)
            , offeredWanted      = filter (startsWith word) (offeredWanted o)
            , offeredProductions = offeredProductions o
            , offeredStuck       = Nothing
            , offeredRecovered =
                Just (RecoveryView (start + 1) word Nothing (start + 1, stop + 1))
            }
  where
    line   = textOf before ++ textOf after
    cursor = length (textOf before)
    slice from to = take (to - from) (drop from line)

-- | Each token with **its offset into the whole text**, which is not its column.
--
-- @tokensView@ reports a line and a column, and a column restarts at 1 on every
-- line — so an entry written over several lines had every offset after the first
-- newline short by as much as the lines above it ran. Before MS7 phase 140 this
-- function did not exist and the column was used as the offset directly, which
-- was right only for a single-line entry and silently wrong for the multi-line
-- form the offside rule allows (@:\{ … :\}@ at the prompt, or a statement
-- continued on an indented line).
--
-- **The line was always there to be read** — 'tokenViewLine' is as old as
-- 'tokenViewColumn'; nothing needed to be reported that was not already.
atOffsets :: String -> [TokenView] -> [(Int, TokenView)]
atOffsets text ts =
  [ (offsetIn text (Pos (tokenViewLine t) (tokenViewColumn t)), t) | t <- ts ]

-- | What the cursor is standing in. Offsets are from zero, into 'line'.
data Unit
  = InsideLiteral Literal
  | BareWord Int Int
    -- ^ the offsets the word under the cursor starts and ends at.
  | CommandWord Int Int
    -- ^ the offsets the colon of a @:@-command word starts and ends at. **The colon
    -- is part of the unit**, because a command word is spelled with it and the
    -- offer's literals carry it.

-- | A tagged term literal the cursor is standing in.
--
-- **Two pairs of offsets, because two questions are being asked** (MS7 phase 143).
-- 'litOpen' and 'litClose' bound the /content/, which is what the object grammar is
-- asked about. 'litFrom' and 'litTo' bound the /literal/, tag and fences included,
-- which is what a frontend underlines. Before this phase only the content pair
-- existed and the tag's own offset was computed and dropped.
data Literal = Literal
  { litLang  :: String
  , litProd  :: Maybe String
    -- ^ the production the tag named, as in @LC[var]\`@.
  , litOpen  :: Int   -- ^ just after the opening tag.
  , litClose :: Int   -- ^ the closing fence, or the line's end when unclosed.
  , litFrom  :: Int   -- ^ the tag's own first character.
  , litTo    :: Int
    -- ^ one past the literal's last character — past the closing fence when there is
    -- one, and the line's end when there is not.
  }

-- | Which unit an offset falls in.
--
-- **A tagged term literal wins over the tokens inside it**, which is the whole
-- reason the unit is lexical: the literal's own text contains spaces and would
-- otherwise be several units.
unitAt :: Int -> [(Int, TokenView)] -> Maybe Unit
unitAt cursor ts
  -- **A command word wins, and can only be at the front.** It is tried first
  -- because its second token is an ordinary word that 'covers' would also match,
  -- and answering @inf@ where the unit is @:inf@ is the whole bug.
  | Just (at, to) <- commandWordAt cursor ts = Just (CommandWord at to)
  | otherwise = case find inside (literals ts) of
      Just l  -> Just (InsideLiteral l)
      Nothing -> (\(at, t) -> BareWord at (at + length (tokenViewText t)))
                   <$> find covers ts
  where
    inside l = cursor >= litOpen l && cursor <= litClose l
    covers (at, t) = cursor > at && cursor <= at + length (tokenViewText t)

-- | The offset of a @:@-command word the cursor is standing in, if it is.
--
-- The colon has to be the line's first token and the word has to sit against it
-- with no space, which is the driver's own reading: it splits the first word off at
-- a space and dispatches on it. A bare @:@ with the cursor after it counts, so
-- typing the colon alone already offers every command.
commandWordAt :: Int -> [(Int, TokenView)] -> Maybe (Int, Int)
commandWordAt cursor ts = case ts of
  (at, t) : rest
    | tokenViewText t == ":" -> case rest of
        (at', t') : _
          | at' == at + 1
          , cursor > at
          , cursor <= at' + length (tokenViewText t') ->
              Just (at, at' + length (tokenViewText t'))
        _ | cursor == at + 1 -> Just (at, at + 1)
        _ -> Nothing
  _ -> Nothing

-- | Every tagged term literal in the line: its language, the production its tag
-- named, where its text begins and where its closing fence is.
--
-- An opening tag is an 'ATag' of more than one character — @LC\`@, @LC[var]\`@ —
-- and a closing fence is an 'ATag' of exactly one. A literal left unclosed runs
-- to the end of the line, which is what a line being typed looks like.
literals :: [(Int, TokenView)] -> [Literal]
literals ts = go ts
  where
    end = case reverse ts of
      []          -> 0
      (at, t) : _ -> at + length (tokenViewText t)

    go [] = []
    go ((at, t) : rest)
      | tokenViewKind t == ATag, length (tokenViewText t) > 1 =
          let open = at + length (tokenViewText t)
              -- **The fence's own offset, and one past it.** An unclosed literal has
              -- no fence, so both are the line's end — which is the ordinary state
              -- of a literal being typed, and the span simply runs to where the text
              -- stops.
              (close, stop) = case break closer rest of
                (_, (c, _) : _) -> (c, c + 1)
                (_, [])         -> (end, end)
              (lang, prod) = tagParts (tokenViewText t)
           in Literal lang prod open close at stop
                : go (drop 1 (dropWhile (not . closer) rest))
      | otherwise = go rest

    closer (_, t) = tokenViewKind t == ATag && length (tokenViewText t) == 1

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
