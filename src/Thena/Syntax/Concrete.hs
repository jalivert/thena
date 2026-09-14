-- | The named, unresolved tree the parser produces (§2.5) — the Development
-- Calculus and the Core terms inside it.
--
-- **`instral`'s concrete syntax moved out at MS5 phase 61a**, to
-- "Thena.Instral.Concrete". @RawInstr@ and its neighbours never referred to
-- 'Raw' and had nothing to do with it; keeping them here meant one module named
-- for one language holding the syntax of three, which is the confusion the
-- standing rule forbids. **What is left is still two languages in one type** —
-- see 'Raw' — and that is not a module boundary but a type split, owed to the
-- phase that retires the DC's spelling.
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
  , splicesIn
  , nameSplicesIn
  , RawBinder (..)
  , RawIdent (..)
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
  | RawUniverseOpen              -- ^ @Type@ — a universe whose level is inferred
  | RawAt RawIdent [Int]         -- ^ @foo {0 1}@ — a global at level arguments

  | RawLam [RawBinder] Raw       -- ^ @λ (x : S) (y : T) -> b@
  | RawPi [RawBinder] Raw        -- ^ @∀ (x : S) (y : T) -> B@
  | RawArrow Raw Raw             -- ^ @S -> B@, the non-dependent case
  | RawApp Raw Raw
  | RawLet RawIdent Raw Raw Raw  -- ^ @let x = s : S in t@
  | RawClaim RawIdent Raw Raw    -- ^ @let ? x : S in p@
  | RawGuess RawIdent Raw Raw Raw -- ^ @let ? x : S ≐ (g) in p@
  | RawPending RawConstraint Raw -- ^ @κ ▸ p@
  | RawQuote Raw                 -- ^ @⌜ t ⌝@
  | RawSplice String
    -- ^ **@${x}@ — a hole in a written term, filled from the binding @x@ when
    -- the instruction runs** (MS5 phase 81, his design).
    --
    -- **A splice always supplies a nonterminal** — his observation, and it is
    -- what makes this cheap: a splice stands where a /term/ stands, so the
    -- template parses once, at load, into a term with holes, and what each hole
    -- wants is known from where it sits rather than from a pass of its own.
    --
    -- **It names a binding rather than holding an expression**, which costs
    -- nothing: a nested call in an operand is already lifted into a binding of
    -- its own (MS5 phase 63), so @${f a}@ would be written as two lines
    -- whatever this said. It also keeps "Thena.Syntax.Concrete" from importing
    -- "Thena.Instral.Concrete", which imports this module.
  | RawElim RawIdent [Int] [Raw] Raw [Raw] [Raw] Raw
    -- ^ @elim d (params) motive (methods) (indices) target@ (§2.6, phase 7) —
    -- positional, and in exactly 'Thena.Core.Term.Core''s own field order for
    -- 'Thena.Core.Term.Eliminate', so where a field goes needs no name.
  deriving (Eq, Show)

-- | @(x : S)@ — one parenthesised binding. Always annotated: there is no
-- inference at this level, and a binder with no type is a parse error rather
-- than a hole (§2.6).
-- | A NAME in the source, which may itself be spliced (MS5 phase 88).
--
-- **His principle, applied all the way**: /a splice supplies a nonterminal/.
-- Phase 81 built the production at one nonterminal — a 'Raw' term — so
-- @core\`${d} -> ${d}\`@ worked and @core\`λ (${n} : ${d}) -> ${d}\`@ was a
-- parse error, because a binder's name is a position where the grammar wants a
-- /name/ and there was no splice production there.
--
-- **Every position where the grammar wants a name now takes one**: a λ or ∀
-- binder, a @let@, a claim, a guess, an @elim@\'s datatype and a global at
-- level arguments. What the position wants decides what the binding must hold —
-- a 'Thena.Instral.Type.TName' here, where a term position wants a
-- 'Thena.Instral.Type.TCore' — so nothing has to be annotated and the two
-- readings cannot be confused.
data RawIdent
  = RawWord   String  -- ^ written down
  | RawIdentSplice String
    -- ^ @${x}@ — the name comes from the binding @x@ when the instruction runs.
  deriving (Eq, Show)

data RawBinder = RawBinder RawIdent Raw
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

-- | Every binding a written term splices, outermost first (MS5 phase 81).
--
-- The twin of 'Thena.Surface.Concrete.blocksIn': one walk over the tree that is
-- not resolution, so that @validate@ can see an unbound name inside a template
-- and inference can ask what each splice must be.
-- | Just the splices that stand in a NAME position (MS5 phase 88).
--
-- **The position is what decides**, so this is a second walk rather than a flag
-- on the first: a hole reached through 'RawIdentSplice' wants a name and one
-- reached through 'RawSplice' wants a term, and no position accepts both.
-- 'Thena.Engine' fills each from its own list and
-- "Thena.Instral.Infer" types each against its own type.
nameSplicesIn :: Raw -> [String]
nameSplicesIn t = case t of
  RawSplice _        -> []
  RawLam bs b        -> concatMap binder bs ++ nameSplicesIn b
  RawPi bs b         -> concatMap binder bs ++ nameSplicesIn b
  RawArrow a b       -> nameSplicesIn a ++ nameSplicesIn b
  RawApp f x         -> nameSplicesIn f ++ nameSplicesIn x
  RawLet n v ty b    -> named n ++ nameSplicesIn v ++ nameSplicesIn ty ++ nameSplicesIn b
  RawClaim n ty p    -> named n ++ nameSplicesIn ty ++ nameSplicesIn p
  RawGuess n ty g p  -> named n ++ nameSplicesIn ty ++ nameSplicesIn g ++ nameSplicesIn p
  RawPending _ p     -> nameSplicesIn p
  RawQuote q         -> nameSplicesIn q
  RawElim d _ ps m ms is tg ->
    named d ++ concatMap nameSplicesIn ps ++ nameSplicesIn m
      ++ concatMap nameSplicesIn ms ++ concatMap nameSplicesIn is ++ nameSplicesIn tg
  RawName _          -> []
  RawUniverse _      -> []
  RawUniverseOpen    -> []
  RawAt n _          -> named n
  where
    binder (RawBinder n ty) = named n ++ nameSplicesIn ty

    named i = case i of { RawIdentSplice x -> [x] ; RawWord _ -> [] }

-- | **Every splice the template waits for, term and NAME alike** (MS5 phase 88
-- widened it). A name splice is filled from the same environment and refused
-- the same way if the binding is missing; what differs is only the /type/ the
-- position demands, which "Thena.Instral.Infer" reads off the position.
splicesIn :: Raw -> [String]
splicesIn t = case t of
  RawSplice x        -> [x]
  RawLam bs b        -> concatMap binder bs ++ splicesIn b
  RawPi bs b         -> concatMap binder bs ++ splicesIn b
  RawArrow a b       -> splicesIn a ++ splicesIn b
  RawApp f x         -> splicesIn f ++ splicesIn x
  RawLet n v ty b    -> named n ++ splicesIn v ++ splicesIn ty ++ splicesIn b
  RawClaim n ty p    -> named n ++ splicesIn ty ++ splicesIn p
  RawGuess n ty g p  -> named n ++ splicesIn ty ++ splicesIn g ++ splicesIn p
  RawPending _ p     -> splicesIn p
  RawQuote q         -> splicesIn q
  RawElim d _ ps m ms is tg ->
    named d ++ concatMap splicesIn ps ++ splicesIn m ++ concatMap splicesIn ms
      ++ concatMap splicesIn is ++ splicesIn tg
  RawName _          -> []
  RawUniverse _      -> []
  RawUniverseOpen    -> []
  RawAt n _          -> named n
  where
    binder (RawBinder n ty) = named n ++ splicesIn ty

    named i = case i of { RawIdentSplice x -> [x] ; RawWord _ -> [] }
