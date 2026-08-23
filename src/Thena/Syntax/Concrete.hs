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
  | RawLam [RawBinder] Raw       -- ^ @λ (x : S) (y : T) -> b@
  | RawPi [RawBinder] Raw        -- ^ @∀ (x : S) (y : T) -> B@
  | RawArrow Raw Raw             -- ^ @S -> B@, the non-dependent case
  | RawApp Raw Raw
  | RawLet String Raw Raw Raw    -- ^ @let x = s : S in t@
  | RawClaim String Raw Raw      -- ^ @let ? x : S in p@
  | RawGuess String Raw Raw Raw  -- ^ @let ? x : S ≐ (g) in p@
  | RawPending RawConstraint Raw -- ^ @κ ▸ p@
  | RawQuote Raw                 -- ^ @⌜ t ⌝@
  | RawElim String [Raw] Raw [Raw] [Raw] Raw
    -- ^ @elim d (params) motive (methods) (indices) target@ (§2.6, phase 7) —
    -- positional, and in exactly 'Thena.Core.Term.Core'\'s own field order for
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
