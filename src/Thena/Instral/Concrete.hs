-- | The named, unresolved trees `instral` is written as (MS5 phase 61a).
--
-- **`instral` is the instruction language, and since the 2026-09-11 reversal it
-- is the rule language too** — a rule is a function with a head, a function is a
-- rule with one clause and no head, so there is one language with two levels:
-- **declarations** (rules, and later functions) and **statements** (rule bodies,
-- @do@ blocks, REPL entries). @discussion\/the-five-languages.md@ §1.1 is the
-- reversal and §0b's tables are the map.
--
-- **These trees moved out of "Thena.Syntax.Concrete"**, where they had sat since
-- phase 21 next to a type called @Raw@ that they never mentioned. One module
-- named for one language cannot hold the syntax of three without the next reader
-- having to work out which is which.
--
-- **It imports nothing, and must keep importing nothing** (@PLAN-interface.md@
-- §2.5): "Thena.Syntax.Lexer" and "Thena.Syntax.Parser" sit beside @Core@ and
-- between them import only the concrete-syntax modules, which is what keeps
-- "Thena.Errors"' /nothing above Core/ rule true.
--
-- The constructors keep their @Raw@ prefix. It no longer names the type they
-- used to live beside; it says /named and unresolved/, which is what they are —
-- an op word here is a 'String' and becomes a 'Thena.Ops.Op' only in
-- "Thena.Rules".
module Thena.Instral.Concrete
  ( RawRule (..)
  , RawInstr (..)
  , RawOp (..)
  , RawOperand (..)
  , RawTest (..)
  ) where

import Thena.Syntax.Concrete (Raw)

-- | A written rule (§8, phase 21) — @rule ‹name› (‹params›) :- when ‹tests› then ‹body›@.
--
-- Named and unresolved like every other tree here: the tests and the op words
-- are 'String's, and turning them into 'Thena.Ops.Test' and 'Thena.Ops.Op' is
-- "Thena.Rules"'s job. The parser cannot do it, for the same reason it cannot
-- produce a 'Thena.Core.Term.Core': the op words are not lexer keywords — if
-- they were, @solve@ and @type@ would stop being usable identifiers in terms —
-- so the grammar sees an @ident@ and only resolution knows which op it names.
--
-- **@:-@ separates the head from the conditions, and both sides of it are
-- deliberately empty for now.** DECIDED by the user 2026-08-25: pattern
-- matching on the focused term and on the goal is coming, and it will attach to
-- the head, left of @:-@ or right of it. @when@ stays underneath whatever
-- arrives — it is the low-level, manual way to ask whether a rule applies.
data RawRule = RawRule String [String] [RawTest] [RawInstr]
  deriving (Eq, Show)

-- | @‹name› = ‹op› ‹args›@ or @‹op› ‹args›@ — 'Thena.Ops.Instr''s two cases, written.
data RawInstr
  = RawBind String RawOp
  | RawDo   RawOp
  deriving (Eq, Show)

-- | An op word and the arguments written after it, both unresolved.
--
-- One shape for every op, however the op's own arguments are typed: @cross
-- type@, @arg 2@ and @call try t@ all parse to this and are told apart in
-- resolution. That is what keeps the grammar to two productions.
data RawOp = RawOp String [RawOperand]
  deriving (Eq, Show)

-- | One written test in a rule's head: a word, and whatever was written after
-- it (MS4 phase 47).
--
-- **The same shape 'RawOp' has, for the same reason** — which word names a test
-- and whether it was given the right number of operands is resolution's
-- question, not the parser's (§2.5, the parser is shallow).
--
-- A head is a /run/ of tests with nothing between them, so a test that takes
-- operands is written in parentheses — @when focus-is-hole (surface-is-name t)@
-- — and a bare word is a test of no operands. Without the brackets
-- @when focus-is-hole goal-type-is-pi@ would read as one test applied to
-- another word.
data RawTest = RawTest String [RawOperand]
  deriving (Eq, Show)

-- | What may be written as an argument: a name, a position, or text.
--
-- **No term literal, and that is a boundary rather than an omission.** A term
-- would have to be resolved in a context, and a rule is written where there is
-- no context — no proof is in progress and no focus exists.
--
-- 'RawText' arrives at phase 22b, at the user's instruction: *"Rules absolutely
-- need a string literal."* Without it @say@, @ask@ and @concat@ had keywords
-- that resolved and no way to be given anything to say.
data RawOperand
  = RawQuoted Raw
    -- ^ @⌜ t ⌝@ — **a core term written in corners** (MS5 phase 62).
    --
    -- The same operand a @core@ region denotes, by the other spelling. It holds
    -- a parsed tree rather than raw text because **Core shares Thena's lexer**:
    -- a region carries text so that a /foreign/ language may keep its own
    -- lexical rules, and Core has no need of that
    -- (@discussion\/the-five-languages.md@ §7b, the permanent entry).
  | RawRegion String String
    -- ^ @tag\`…\`@ — a **tagged region** (MS5 phase 61b): the tag, and the raw
    -- text between the fences. Which language the text is in is the tag's to
    -- say, and the text is parsed by that tag's parser during resolution.
    --
    -- **The text is raw and not tokens**, because an embedded language has its
    -- own lexical rules (@discussion\/the-five-languages.md@ §6.9). The lexer
    -- found the extent; nothing here has looked inside.
  | RawRef String
  | RawPos Int
  | RawText String
  deriving (Eq, Show)
