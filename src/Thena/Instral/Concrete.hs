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
  ( RawDecl (..)
  , RawFunction (..)
  , RawLanguage (..)
  , RawProduction (..)
  , RawGItem (..)
  , RawRhs (..)
  , RawBody (..)
  , RawSignature (..)
  , RawTy (..)
  , RawRule (..)
  , RawPattern (..)
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
data RawRule = RawRule String [RawPattern] [RawTest] [RawInstr]
  deriving (Eq, Show)

-- | A written parameter (MS5 phase 82) — @x@, @_@, @[a, ...rest]@, @(x, y)@,
-- @some x@, @none@, or a literal.
--
-- **Unresolved like everything else here, and it barely needs to be**: a
-- pattern over @instral@'s own data mentions no op word, no tag and no global,
-- so 'Thena.Rules.resolvePattern' is a rename from 'String' to
-- 'Thena.Ops.Name'. It is a separate tree anyway, because stages b and c of
-- @discussion\/pattern-matching.md@ add a Surface pattern and a Core one, and
-- both of those /do/ need resolving.
--
-- **@...@ prefixes any list pattern**, so the tail is a 'RawPattern'. It lexes
-- without reserving anything: @.@ is an @\$idchar@ but not an @\$idstart@, so no
-- identifier has ever begun with a dot and @...rest@ is two tokens.
data RawPattern
  = RawPWord String
    -- ^ a bare word. **Which of five things it is, is resolution's question** —
    -- a variable, @_@, @true@, @false@ or @none@ — for the same reason an
    -- operand's @true@ is: one lexer serves every language, so none of them is
    -- a keyword and the grammar sees an @ident@.
  | RawPApp String [RawPattern]
    -- ^ @(some x)@. **Parenthesised, because an untagged compound argument is**
    -- (§6.0.1) — bare, @f some x@ could not be told from two parameters.
  | RawPInt Int
  | RawPChar Char
  | RawPText String
  | RawPList [RawPattern] (Maybe RawPattern)
  | RawPPair RawPattern RawPattern
  deriving (Eq, Show)

-- | What a rule-base file is a list of (MS5 phase 67).
--
-- **A signature is a declaration of its own, not something on a rule's line** —
-- his choice, 2026-09-12. It has to be: a callable has several clauses and one
-- type, so a type written on a clause would be written once and read as
-- belonging to all of them, or written on each and able to disagree.
data RawDecl
  = DeclRule RawRule
  | DeclSignature RawSignature
  | DeclFunction RawFunction
  | DeclLanguage RawLanguage
  deriving (Eq, Show)

-- | @‹name› ‹params› = ‹expression›@ — a global function (MS5 phase 68a).
--
-- **No keyword** — his choice, 2026-09-12: *like Haskell. no keyword, name,
-- parameters, =, expression.* It needs none, because @rule@ and @signature@ are
-- keywords and a declaration beginning with a plain word can only be this.
--
-- **A function is a rule with one clause and no head** — his §1.1 — and that is
-- how it is built rather than how it is described: 'Thena.Rules.resolveFunction'
-- answers with an ordinary 'Thena.Ops.Rule' whose body ends in @return@. Nothing
-- in the engine knows the difference, which is the point of there being one
-- language.
data RawFunction = RawFunction String [RawPattern] RawBody
  deriving (Eq, Show)

-- | @language ‹Name› where { ‹productions› }@ (MS5 phase 69).
--
-- **The minimal grammar notation** — his ruling, 2026-09-12, over branding
-- object terms with the Surface parser: build it now so the generated-parser
-- path is exercised, and let MS6's grammar sub-language (§7) replace it.
data RawLanguage = RawLanguage String [RawProduction]
  deriving (Eq, Show)

-- | @‹constructor› : ‹item›…@
data RawProduction = RawProduction String [RawGItem]
  deriving (Eq, Show)

-- | A quoted terminal, or a word.
--
-- **Which word it is, is resolution's question**, exactly as an op word is: the
-- language's own name is a recursive slot, @name@ is a bare identifier, and
-- anything else is a mistake. The parser cannot tell, because it does not know
-- what the language is called.
data RawGItem
  = GTerminal String
  | GWord String
  deriving (Eq, Show)

-- | What stands right of an @=@ — in a function declaration and in a binding
-- inside a body, which are the same question (MS5 phase 68a).
--
-- **Two cases and not one, because an op application is not an operand.** A
-- word followed by arguments is an op or a call; everything else is a value
-- written down. Until this phase only the first was allowed after @=@, which is
-- why @x = [1, 2]@ was unwritable (@ms5\/CLOSEOUT.md@ 3, his ruling that it
-- waits for this phase).
data RawRhs
  = RhsOp RawOp        -- ^ @concat x x@ — an op or a call
  | RhsValue RawOperand -- ^ @[1, 2]@, @(a, b)@, @42@, @⌜ t ⌝@
  deriving (Eq, Show)

-- | What stands right of a function's @=@ or a lambda's @->@ (MS5 phase 75b).
--
-- **Two shapes, and the first is the second written short.** @f x = e@ is one
-- expression; @f x = do ‹block›@ is a block of instructions that says @return@
-- itself, which is what lets a function have locals at all.
--
-- **@do@ is his choice of opener**, 2026-09-13, over making @=@ a layout
-- keyword: @=@ is not one in Haskell either, and here it would reach into the
-- surface language's @let x = e@ bindings. @do@ is already a layout keyword and
-- already means /a block of instructions/, so the block's braces arrive from
-- the offside rule with nothing added to it.
--
-- **It is a separate type from 'RawRhs' on purpose.** A block is a body and not
-- an expression: @n = do ‹block›@ inside a body would be a different thing —
-- 'Thena.Ops.Block', whose @return@ ends the block and drops the value — and
-- giving 'RawRhs' the constructor would put an unreachable case in every
-- function that matches one.
data RawBody
  = BodyRhs RawRhs       -- ^ @f x = concat x x@
  | BodyBlock [RawInstr] -- ^ @f x = do ‹block›@
  deriving (Eq, Show)

-- | @signature ‹name› : ‹type›@ — a rule's declared type (MS5 phase 67).
--
-- **The arity is in the type, not written separately.** A signature's arrow
-- chain has one link per parameter and ends in the result, so
-- @signature f : Core -> Surface -> ()@ is the signature of @f@ at arity two,
-- and it says nothing about an @f@ of another arity — which is a different
-- callable ('Thena.Rules.clauses' dispatches on both).
data RawSignature = RawSignature String RawTy
  deriving (Eq, Show)

-- | A written type. Resolved into 'Thena.Instral.Type.Ty' by "Thena.Rules".
--
-- **A capitalised name is a type constructor and a lowercase one is a
-- variable**, which is the only rule the reader has to know and the one every
-- language with a type syntax uses. It is why nothing needs a @forall@: a
-- signature's variables are exactly its lowercase names.
data RawTy
  = RawTyCon String [RawTy]  -- ^ @Core@, @List a@, @Option Surface@
  | RawTyVar String          -- ^ @a@
  | RawTyPair RawTy RawTy    -- ^ @(a, b)@
  | RawTyUnit                -- ^ @()@ — an op or a rule that leaves nothing
  | RawTyArrow RawTy RawTy   -- ^ @A -> B@
  | RawTyGroup RawTy
    -- ^ @(‹type›)@ — **the parentheses, kept** (2026-09-12).
    --
    -- Dropping them made @a -> (b -> c)@ the same tree as @a -> b -> c@, so a
    -- signature could name a function /parameter/ and never a function
    -- /result/: 'Thena.Rules.resolveSignature' splits the top-level arrow chain
    -- into parameters and a result, and a result that had been in parentheses
    -- was indistinguishable from one more parameter. Inference makes such a
    -- type readily — @mk s = \\ z -> concat s z@ is a @String@ giving a
    -- @String -> String@ — so the declared half of the type system could not
    -- say what the inferred half works out.
    --
    -- Everything else about a group is nothing: 'Thena.Rules.resolveTyIn'
    -- unwraps it. It exists so that the arrow chain can stop at one.
  deriving (Eq, Show)

-- | @‹name› = ‹op› ‹args›@ or @‹op› ‹args›@ — 'Thena.Ops.Instr''s two cases, written.
data RawInstr
  = RawBind RawPattern RawRhs
    -- ^ **The left is a PATTERN since MS5 phase 84** — stage d of
    -- @discussion\/pattern-matching.md@. A plain name is 'RawPWord', so every
    -- binding that could be written before still parses to what it did.
  | RawDo   RawOp
  | RawAnnot String RawTy
    -- ^ **@n : Ty@, a local's declared type** (MS5 phase 77). It is written as
    -- a line of its own, above the binding it is about, which is the spelling a
    -- top-level signature uses one level up — his uniformity. It is not an
    -- instruction: resolution attaches it to the binding that follows and
    -- nothing of it reaches 'Thena.Ops.Instr' but the type.
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
  | RawNested String [RawOperand]
    -- ^ @(‹word› ‹operands…›)@ — **an operand that is itself a call** (MS5
    -- phase 63): @some-rule (f a) b@ is one call and one variable.
    --
    -- It is written in parentheses because an untagged compound argument needs
    -- them — without, nobody can tell one argument from two
    -- (@discussion\/the-five-languages.md@ §6.0.1).
    --
    -- **Resolution turns it back into a statement**: the nested call becomes a
    -- binding in front of the instruction that wanted it, and the operand
    -- becomes a reference to that binding. So it is sugar with a fixed
    -- evaluation order — left to right, innermost first — and not a new kind of
    -- value.
  | RawLambda [RawPattern] RawBody
    -- ^ @\\ x y -> ‹expression›@ — **a lambda** (MS5 phase 68b).
    --
    -- **It is an operand and not a right-hand side of its own**, so that
    -- @t = \\ x -> e@ and @f (\\ x -> e)@ are the same thing in two places. Like
    -- 'RawNested', resolution lifts it into a binding in front of the
    -- instruction that wanted it — a closure has to capture the environment it
    -- is made in, which is a thing that happens at run time, so it cannot be a
    -- literal.
  | RawRef String
  | RawPos Int
    -- ^ a numeral. **It is a /position/ only where a field word wants one** —
    -- @arg 2@, @param 0@ — and an 'Thena.Ops.VInt' literal everywhere else (MS5
    -- phase 64). The parser cannot tell the two apart, for the reason it cannot
    -- tell an op word from a rule name: which it is depends on the word in
    -- front, which is resolution's question.
  | RawText String
  | RawChar Char
    -- ^ @'c'@ (MS5 phase 64).
  | RawList [RawOperand]
    -- ^ @[a, b, c]@ (MS5 phase 65).
  | RawPairOf RawOperand RawOperand
    -- ^ @(a, b)@ (MS5 phase 65).
  deriving (Eq, Show)
