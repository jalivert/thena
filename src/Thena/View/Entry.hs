-- | A REPL entry as **several instructions**, and what the ones above the cursor
-- bound (MS7 phase 140).
--
-- **The entry is the unit and a line is the degenerate case** — @Thena.Driver@'s
-- @instralEntry@ says so, and this module is the same fact seen from the offer's
-- side. A prompt entry may be written over several lines: instructions at the
-- entry's own column are separate, and a line indented past it continues the one
-- above. @:\{ … :\}@ is how a terminal reads such an entry one line at a time; a
-- frontend holding a buffer simply puts the newlines in.
--
-- **What the offer needed and did not have.** The chart answers /what may stand
-- at this cursor/ for one statement, read from the start of the text. Given an
-- entry of three instructions it therefore answered nothing at all: the text left
-- of the cursor does not read as one statement, so every field came back empty
-- with 'Thena.View.Chart.offeredStuck' set. Measured before this phase,
-- @h = here@ then @goto @ offered nothing and did not even recover.
--
-- **Why the offside rule is not reimplemented here.** It would be the one thing
-- this side must not do — a second copy of a layout rule drifts from the first,
-- and the drift is silent. 'Thena.Surface.Layout.layoutFile' already inserts a
-- positioned 'Thena.Syntax.Lexer.TSemi' between an entry's instructions, so the
-- boundaries are read off the real pass. This module finds them; it does not
-- decide them.
module Thena.View.Entry
  ( Split (..)
  , splitEntry
  ) where

import Thena.Surface.Layout (layoutFile)
import Thena.Syntax.Lexer (Located (..), Spanned (..), Token (..))
import Thena.View.Tokens (mendedTokens, offsetIn)

-- | An entry cut at the cursor.
data Split = Split
  { splitBefore :: String
    -- ^ **the instructions wholly above the cursor's own**, as text, ready to be
    -- read and typed by the engine. Empty when the cursor is in the first
    -- instruction, which is the single-statement case every earlier phase saw.
  , splitAt' :: Int
    -- ^ the offset the cursor's own instruction starts at, counting from zero
    -- into the whole entry — so the offer's answers can be reported against the
    -- text the frontend passed rather than against the fragment.
  }
  deriving (Eq, Show)

-- | Cut an entry into the instructions above the cursor and the one it is in.
--
-- 'Nothing' when the entry does not lex or does not lay out — the caller then
-- treats the whole text as one instruction, which is what it did before this
-- phase and is never worse.
--
-- **Only the entry's own level counts.** A @TSemi@ inside a nested block belongs
-- to that block, so the walk tracks depth and splits at depth one only; an entry
-- is wrapped in exactly one implicit block by 'layoutFile'.
splitEntry :: String -> Int -> Maybe Split
splitEntry text cursor = do
  -- **The mended lex, not the raw one.** A line with @LC\`@ open on it does not
  -- lex at all, and that is the ordinary state of a line being typed — so an
  -- entry whose last instruction is half a literal must still split, or the
  -- bound names go missing exactly where a completion is wanted.
  ts <- either (const Nothing) Just (mendedTokens text)
  ls <- either (const Nothing) Just (layoutFile [ Located p t | Spanned p t _ <- ts ])
  let written = [ offsetIn text p | Spanned p TSemi _ <- ts ]
      -- **An instruction begins after an explicit @;@ and at an inserted one.**
      -- A @;@ the user wrote is a character of the text, so the instruction after
      -- it starts one further on; the layout pass's own separator has no text and
      -- sits exactly where the next instruction starts. Told apart by asking the
      -- lexed stream — before layout ran — whether a @;@ is really there.
      beginsAt o = if o `elem` written then o + 1 else o
      cuts = [ b | o <- separators ls, let b = beginsAt o, b <= cursor ]
  pure $ case reverse cuts of
    []    -> Split "" 0
    o : _ -> Split (take o text) o
  where
    -- The offsets at which an instruction begins, after the first: every
    -- separator the layout pass inserted at the entry's own depth.
    separators = go (0 :: Int)
      where
        go _ [] = []
        go d (Located p t : rest) = case t of
          TLBrace -> go (d + 1) rest
          TRBrace -> go (d - 1) rest
          TSemi | d == 1 -> offsetIn text p : go d rest
          _       -> go d rest
