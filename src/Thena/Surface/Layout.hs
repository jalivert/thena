-- | The offside rule for the surface language (MS4 phase 40).
--
-- **A pass over the token stream, and only the surface language's.** The user,
-- 2026-08-21: /"Surface will be using Haskell's implicit rules for inserting
-- @{@ and @,@ and @}@ but doing all that for a parser for the development
-- calculus is a massive overkill."/ So this module sits between
-- "Thena.Syntax.Lexer" and "Thena.Surface.Parser" and nothing else calls it.
--
-- **Implicit and explicit must agree**, which is his condition, 2026-09-01:
-- /"if implicit works, explicit has to work too."/ The grammar therefore sees
-- **only** explicit @{@, @;@ and @}@ — this pass inserts them, and a program
-- that writes them itself passes through untouched. Whichever way a block is
-- written, the parser cannot tell.
--
-- The algorithm is the Haskell Report's §10.3 @L@ function, with one deliberate
-- departure — see 'closesBlock'.
module Thena.Surface.Layout
  ( LayoutError (..)
  , layout
  , layoutKeyword
  ) where

import Thena.Syntax.Lexer (Located (..), Pos (..), Token (..))

-- | Why a token stream could not be laid out.
data LayoutError
  = UnmatchedClose Pos
    -- ^ an explicit @}@ where the innermost block is implicit. The user wrote
    -- a brace that closes something they did not open.
  | MissingClose Pos
    -- ^ input ended inside an explicit block.
  deriving (Eq, Show)

-- | A keyword after which a block may open.
--
-- **One list, extended as phases add constructs**: @let@ is the only one the
-- surface language has at phase 40. @where@ arrives with declarations (42) and
-- modules (43), and @do@ with the instruction block (45). Adding one is adding
-- a line here — the machinery below does not change.
layoutKeyword :: Token -> Bool
layoutKeyword t = case t of
  TLet   -> True
  -- **Added at phase 43**, and it serves both users at once: a module's
  -- declaration block and a datatype's constructor block are both introduced by
  -- @where@, so neither needs a rule of its own. An explicit @{@ after it still
  -- passes through — 'mark' declines to open a block the user opened.
  TWhere -> True
  -- **Added at phase 45**, the third and last one phase 40 named. Its block is
  -- the instruction language rather than the surface one, which changes nothing
  -- here: layout is about columns, not about what the tokens mean.
  TDo    -> True
  _      -> False

-- | Tokens that close an implicit block by appearing.
--
-- **This is the Report's @parse-error(t)@ side condition, replaced by a list,
-- and it is the phase's one deliberate departure.** The Report closes an
-- implicit block when the *parser* cannot continue, which needs the parser to
-- answer a question mid-lex; the motivating case is @let x = 1 in x@ on one
-- line, where nothing about @in@'s column closes the block and only the failing
-- parse does.
--
-- Naming the tokens instead is sound here because the surface language is small
-- enough to enumerate them: an implicit block is only ever ended by @in@, by a
-- bracket that closes something opened outside it, or by the end of the input.
-- **If a construct is ever added whose block ends some other way, this list is
-- what has to grow** — and the failure is a parse error, not silence.
closesBlock :: Token -> Bool
closesBlock t = case t of
  TIn -> True
  _   -> False

-- | What the algorithm is standing inside.
data Context
  = Explicit      -- ^ the user wrote @{@; the Report's @0@
  | Paren         -- ^ the user wrote @(@ (MS4 phase 43)
  | Implicit Int  -- ^ opened by the offside rule, at this column
  deriving (Eq, Show)

-- | A marker the pre-pass inserts, then the main pass consumes.
data Item
  = Tok (Located Token)
  | Open Pos Int   -- ^ the Report's @{n}@: a block may open at this column
  | Line Pos Int   -- ^ the Report's @\<n\>@: a line begins at this column

-- | Insert the braces and semicolons the offside rule implies.
--
-- A stream that is already explicit passes through unchanged, which is what
-- makes the two spellings one language rather than two.
layout :: [Located Token] -> Either LayoutError [Located Token]
layout = run [] . mark

-- | The Report's two markers.
--
-- @{n}@ goes after a layout keyword unless the user opened a brace themselves;
-- @\<n\>@ goes before the first token of every line after the first. A token
-- that follows a layout keyword on the /same/ line still opens a block — at its
-- own column — which is what lets @let x = a in x@ be written on one line.
mark :: [Located Token] -> [Item]
mark []           = []
mark (t : ts)     = Tok t : go t ts
  where
    go _ [] = []
    go (Located (Pos pl _) pk) (u@(Located q@(Pos l c) _) : us)
      | layoutKeyword pk && not (isOpenBrace u) = Open q c : Tok u : go u us
      | l /= pl                                 = Line q c : Tok u : go u us
      | otherwise                               = Tok u : go u us

    isOpenBrace (Located _ TLBrace) = True
    isOpenBrace _                   = False

-- | The Report's @L@, over 'Context' rather than over @[Int]@.
run :: [Context] -> [Item] -> Either LayoutError [Located Token]
run cs is = case (is, cs) of
  -- @L ({n} : ts) (m : ms)@ — a block opens if it is indented past the one
  -- around it. A block that is not gets an empty one, which is the Report's
  -- @{ }@ and gives a parse error at the right place rather than a silent
  -- reparent.
  (Open p n : ts, Implicit m : ms)
    | n > m     -> (at p TLBrace :) <$> run (Implicit n : Implicit m : ms) ts
    | otherwise -> ([at p TLBrace, at p TRBrace] ++) <$> run (Implicit m : ms) (Line p n : ts)
  (Open p n : ts, ms)
    | n > 0     -> (at p TLBrace :) <$> run (Implicit n : ms) ts
    | otherwise -> ([at p TLBrace, at p TRBrace] ++) <$> run ms (Line p n : ts)

  -- @L (\<n\> : ts) (m : ms)@ — same column is a new item, less is the end of
  -- the block, more is a continuation line and says nothing.
  (Line p n : ts, Implicit m : ms)
    -- **A line that begins with a closing token is not a new item.** Without
    -- this, @let x = a@ / @    in y@ — @in@ at the bindings' own column — would
    -- get a @;@ from this rule and then a @}@ from 'closesBlock', leaving a
    -- trailing separator. Haskell's grammar tolerates that; ours does not, and
    -- the one-item lookahead is cheaper than a grammar that accepts a list
    -- ending in @;@.
    | n == m, closingNext ts -> run (Implicit m : ms) ts
    | n == m    -> (at p TSemi :) <$> run (Implicit m : ms) ts
    | n <  m    -> (at p TRBrace :) <$> run ms (Line p n : ts)
  (Line _ _ : ts, ms) -> run ms ts

  -- **Brackets are tracked, not merely recognised** (MS4 phase 43). Before it,
  -- 'closesBlock' named @)@ and @}@, so /every/ close ended the block it was in
  -- — and the first real file found that at once:
  --
  -- > module Arith where
  -- > plus = \\ m n -> elim Nat () (\\ k -> Nat) …
  --
  -- the @)@ of @()@ closed the module. That was invisible while layout only ran
  -- on a @let@ and on one REPL argument at a time, which is
  -- @ms4\/CLOSEOUT.md@ 5 arriving exactly where it said it would.
  --
  -- A bracket opened inside a block is therefore its own context, and its close
  -- is ordinary. Only a close with no opener of its own reaches an implicit
  -- block.
  (Tok t@(Located _ TLParen) : ts, ms) -> (t :) <$> run (Paren : ms) ts
  (Tok t@(Located _ TRParen) : ts, Paren : ms) -> (t :) <$> run ms ts

  (Tok t@(Located _ TLBrace) : ts, ms) -> (t :) <$> run (Explicit : ms) ts
  (Tok t@(Located _ TRBrace) : ts, Explicit : ms) -> (t :) <$> run ms ts

  -- **An unmatched close ends the implicit block and is looked at again**, so
  -- one @)@ can close several — which is what a bracket opened outside them
  -- means, and it terminates because each step pops a context. This is the one
  -- place re-processing is right; see 'closesBlock' for the case where it is
  -- not.
  (Tok (Located p k) : _, Implicit _ : ms)
    | k == TRParen, Paren    `elem` ms -> reclose p
    | k == TRBrace, Explicit `elem` ms -> reclose p
  (Tok (Located p TRBrace) : _, Implicit _ : _) -> Left (UnmatchedClose p)

  -- 'closesBlock' stands in for the Report's @parse-error(t)@.
  -- **Exactly one block per closing token**, and the token is then emitted
  -- rather than reconsidered. Re-processing it would cascade: in
  --
  -- > let x = let y = a
  -- >             in y
  -- >  in x
  --
  -- the inner @in@ would close the inner block, be looked at again, and close
  -- the outer one too. The Report does not have this problem because
  -- @parse-error(t)@ stops asking as soon as the parser can continue — one
  -- close is exactly what "the parser can continue" means here.
  (Tok t@(Located p k) : ts, Implicit _ : ms)
    | closesBlock k -> ((at p TRBrace :) . (t :)) <$> run ms ts

  (Tok t : ts, ms) -> (t :) <$> run ms ts

  -- The end: implicit blocks close, an explicit one is an error. An unclosed
  -- @(@ is left to the parser, which has a better message for it than layout
  -- could invent.
  ([], Implicit _ : ms) -> (at endOfInput TRBrace :) <$> run ms []
  ([], Paren : ms)      -> run ms []
  ([], Explicit : _)    -> Left (MissingClose endOfInput)
  ([], [])              -> Right []
  where
    -- Close the implicit block and put the token back.
    reclose p = case (is, cs) of
      (_, _ : ms) -> (at p TRBrace :) <$> run ms is
      _           -> Left (UnmatchedClose p)

-- | Does the next token end a block by appearing? See 'closesBlock'.
closingNext :: [Item] -> Bool
closingNext (Tok (Located _ k) : _) = closesBlock k
closingNext _                       = False

at :: Pos -> Token -> Located Token
at = Located

-- | Inserted tokens at the end of input have no source position of their own.
endOfInput :: Pos
endOfInput = Pos 0 0
