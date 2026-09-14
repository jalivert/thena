-- | The offside rule for the surface language (MS4 phase 40).
--
-- **A pass over the token stream.** The user, 2026-08-21: /"Surface will be
-- using Haskell's implicit rules for inserting @{@ and @,@ and @}@ but doing
-- all that for a parser for the development calculus is a massive overkill."/
-- So it sits between "Thena.Syntax.Lexer" and a parser, and the development
-- calculus is still not one of its customers.
--
-- **Since MS5 phase 75 a rule file is** — his ruling, 2026-09-13: /"the ideal
-- solution would be to give the rule-base a simple layout too, exactly like
-- Haskell"/. One pass and one keyword set serve both languages, because layout
-- is about columns and not about what the tokens mean. The module keeps its
-- name; see @ms5\/CLOSEOUT.md@ for the note on that.
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
  , layoutFile
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
  --
  -- **It gives a RULE BODY the offside rule too, since MS5 phase 85** — that
  -- was @then@\'s job from phase 75 until @then@ stopped being a word. One
  -- keyword now opens every block of instructions there is.
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

-- | 'layout', with the whole stream wrapped in one block (MS5 phase 75).
--
-- **A rule file is one block and nothing in the file opens it** — its header is
-- read textually and blanked before the lexer runs, so there is no @where@ token
-- for 'mark' to hang a block on. Opening one around the stream is what supplies
-- it, and everything else follows from the ordinary rules: a declaration at the
-- block's column gets a @;@, an indented line is a continuation, and the end of
-- input closes the block.
--
-- **The column is the first token's, which is Haskell's rule and not "column
-- 1"** — his /"exactly like Haskell"/, 2026-09-13. Every file anyone writes
-- starts its declarations in column 1 and is unaffected; what changes is that
-- the invariant is now /every declaration at the same column as the first/
-- rather than /every declaration at column 1/, which is strictly stronger,
-- since a second declaration at a different column is a parse error either way
-- and a whole file written indented is no longer a special case to refuse.
--
-- **It is also what makes an empty rule body an empty BLOCK.** Without an
-- enclosing block, @then@ at the end of a line opens one at the /next/ token's
-- column — the next declaration — and swallows the rest of the file. With a
-- block around it the Report's own rule fires instead: a block that is not
-- indented past the one around it is @{ }@, and the line is looked at again.
-- Two clauses of the shipped base have an empty body, so this is not a corner.
layoutFile :: [Located Token] -> Either LayoutError [Located Token]
layoutFile []                       = Right [at endOfInput TLBrace, at endOfInput TRBrace]
layoutFile ts@(Located p@(Pos _ c) _ : _) = run [] (Open p c : mark ts)

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
    -- **A layout keyword with nothing after it opens an empty block** (MS4
    -- phase 54). The Report\'s @{n}@ takes the column of the next token, and
    -- with no next token there is none — so without this, @data Empty : Type
    -- where@ at the end of a file emitted no @{@ at all and the module\'s own
    -- closing brace arrived where the grammar wanted an opening one:
    -- @0:0: unexpected }@. Column 0 is what makes 'run' answer with @{ }@ and
    -- then close every block that is still open.
    go (Located _ pk) []
      | layoutKeyword pk = [Open endOfInput 0]
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
    -- **A line that begins with an explicit @;@ is a continuation, whatever
    -- its column** (MS5 phase 75). The offside rule must not fire for it: the
    -- separator is already written, so there is nothing to insert, and the line
    -- is plainly part of the block whether it is indented past the block's
    -- column or — as every rule file written before this phase does it —
    -- short of it:
    --
    -- > then n = fresh-name "refined"
    -- >    ; x = define n t
    --
    -- Without this, @;@ at column 4 against a block opened at column 8 is
    -- offside, the block closes, and the @;@ is a stray token. That is the
    -- whole of the shipped base, so the choice is between reformatting every
    -- rule ever written and saying what a leading @;@ means. **It is the same
    -- kind of departure 'closesBlock' already is**, and the same justification:
    -- the Report defers to @parse-error(t)@ where we name the token.
    | semiNext ts -> run (Implicit m : ms) ts
    | n == m, closingNext ts -> run (Implicit m : ms) ts
    | n == m    -> (at p TSemi :) <$> run (Implicit m : ms) ts
    -- **A closing token that is ALSO offside closes the blocks it is offside
    -- of, and then closes no more** (2026-09-13). The offside rule and
    -- 'closesBlock' were both firing for the same @in@, so
    --
    -- > let x = let y = a
    -- >          in y
    -- >  in x
    --
    -- emitted two @}@ before the inner @in@: the column rule closed the inner
    -- block and @in@ then closed the outer one as well, leaving the inner @let@
    -- without its @in@ — @2:11: unexpected }@. It is the ordinary Haskell
    -- spelling of a nested @let@ and nothing in the suite wrote one.
    --
    -- **The Report has no such case and the reason is instructive**:
    -- @parse-error(t)@ stops asking the moment the parser can continue, and
    -- once the column rule has closed the inner block the parser /can/ — the
    -- @in@ is the inner @let@'s. Standing in a list of tokens for
    -- @parse-error(t)@ loses exactly that, so the condition has to be said
    -- here instead. See 'closesBlock', whose note describes the case one column
    -- over — an @in@ indented /past/ the block, where the column rule fires not
    -- at all and one close is right.
    | n < m, closingNext ts ->
        let (k, ms') = offside n (Implicit m : ms)
         in (replicate k (at p TRBrace) ++) <$> emitClosing ms' ts
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
    -- Every implicit block this column is offside of, and how many there are.
    offside n (Implicit m : ms)
      | n < m = let (k, ms') = offside n ms in (k + 1, ms')
    offside _ ms = (0 :: Int, ms)

    -- The closing token itself, emitted without a close of its own — the
    -- @Line@ above has already done it.
    emitClosing ms (Tok t : ts) = (t :) <$> run ms ts
    emitClosing ms ts           = run ms ts

    -- Close the implicit block and put the token back.
    reclose p = case (is, cs) of
      (_, _ : ms) -> (at p TRBrace :) <$> run ms is
      _           -> Left (UnmatchedClose p)

-- | Does the next token end a block by appearing? See 'closesBlock'.
closingNext :: [Item] -> Bool
closingNext (Tok (Located _ k) : _) = closesBlock k
closingNext _                       = False

-- | Does this line begin with an explicit separator? See the @Line@ case that
-- uses it (MS5 phase 75).
semiNext :: [Item] -> Bool
semiNext (Tok (Located _ TSemi) : _) = True
semiNext _                           = False

at :: Pos -> Token -> Located Token
at = Located

-- | Inserted tokens at the end of input have no source position of their own.
endOfInput :: Pos
endOfInput = Pos 0 0
