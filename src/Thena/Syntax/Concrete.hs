-- | The named, unresolved tree the parser produces (§2.5).
--
-- It is not 'Thena.Core.Term.Core' and cannot be: which of @Bound@, @Free@ and
-- @Global@ a written name denotes depends on the context it is written in, and
-- that is "Thena.Syntax.Resolve"'s job. Nor is it always a term — the same tree
-- doubles as the syntax for a development (§2.7), and which fragment a raw tree
-- denotes is also resolution's job.
--
-- The constructors are prefixed @Raw@ so that a module importing this and
-- "Thena.Core.Term" together — 'Thena.Syntax.Resolve' does — needs no qualified
-- import, and so that "a raw lam" and "a core lam" are distinguishable said out
-- loud.
module Thena.Syntax.Concrete
  ( Raw (..)
  , RawBinder (..)
  , RawConstraint (..)
  , RawData (..)
  , RawConstructor (..)
  , RawRule (..)
  , RawInstr (..)
  , RawOp (..)
  , RawOperand (..)
  ) where

-- | A written term, or a written development. One tree for both fragments
-- (§2.7): 'RawClaim', 'RawGuess' and 'RawPending' can only resolve to
-- development components, everything else can appear in either, and nothing
-- here records which was meant.
--
-- Names are 'String' and undistinguished. @RawName \"x\"@ may become a
-- 'Thena.Core.Term.Bound', a 'Thena.Core.Term.Free' or a
-- 'Thena.Core.Term.Global'; the tree cannot say which and does not try.
data Raw
  = RawName String
  | RawUniverse Int
  | RawUniverseOpen              -- ^ @Type@ — a universe whose level is inferred
  | RawAt String [Int]           -- ^ @foo {0 1}@ — a global at level arguments

  | RawLam [RawBinder] Raw       -- ^ @λ (x : S) (y : T) -> b@
  | RawPi [RawBinder] Raw        -- ^ @∀ (x : S) (y : T) -> B@
  | RawArrow Raw Raw             -- ^ @S -> B@, the non-dependent case
  | RawApp Raw Raw
  | RawLet String Raw Raw Raw    -- ^ @let x = s : S in t@
  | RawClaim String Raw Raw      -- ^ @let ? x : S in p@
  | RawGuess String Raw Raw Raw  -- ^ @let ? x : S ≐ (g) in p@
  | RawPending RawConstraint Raw -- ^ @κ ▸ p@
  | RawQuote Raw                 -- ^ @⌜ t ⌝@
  | RawElim String [Int] [Raw] Raw [Raw] [Raw] Raw
    -- ^ @elim d (params) motive (methods) (indices) target@ (§2.6, phase 7) —
    -- positional, and in exactly 'Thena.Core.Term.Core''s own field order for
    -- 'Thena.Core.Term.Eliminate', so where a field goes needs no name.
  deriving (Eq, Show)

-- | @(x : S)@ — one parenthesised binding. Always annotated: there is no
-- inference at this level, and a binder with no type is a parse error rather
-- than a hole (§2.6).
data RawBinder = RawBinder String Raw
  deriving (Eq, Show)

-- | @Ξ ⊢ s ≟ t : T@ — the binders, then the two sides, then the type.
data RawConstraint = RawConstraint [RawBinder] Raw Raw Raw
  deriving (Eq, Show)

-- | @data D (p : P) : I -> Type_l { c : T ; c' : T' }@ — the name, the
-- parameters, the type former's type, the constructors (§2.7, decided by the
-- user planning phase 6).
--
-- A declaration is not a term, so it is not a case of 'Raw'. The type is kept
-- whole rather than split into indices and a universe: the split is a shape
-- check and belongs with the other ones in "Thena.Syntax.Resolve".
data RawData = RawData String [RawBinder] Raw [RawConstructor]
  deriving (Eq, Show)

-- | @c : T@ — one constructor of a 'RawData', with its type written out in
-- full. Splitting that type into arguments and a return index is a shape check,
-- and happens in "Thena.Syntax.Resolve" with the others.
data RawConstructor = RawConstructor String Raw
  deriving (Eq, Show)

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
data RawRule = RawRule String [String] [String] [RawInstr]
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
  = RawRef String
  | RawPos Int
  | RawText String
  deriving (Eq, Show)
