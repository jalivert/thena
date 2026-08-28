-- | Universe levels, as an algebra rather than a number (MS3 phase 28).
--
-- @Level@ was @newtype Level Int@ through MS1 and MS2, which is why §2 of
-- @discussion\/universe-polymorphism.md@ lists four places where finished code
-- is bent out of shape: @Eq@ stuck at @Type₀@, no-confusion skipping anything
-- above it, one eliminator per motive level, and a size restriction that is an
-- @Int@ comparison. All four have the same cause and this module is the start
-- of removing it.
--
-- **This module exists separately from "Thena.Core.Term", and the reason is the
-- central finding of MS3: levels are context-free.** 'Level' contains no
-- 'Thena.Core.Term.Core', so nothing here needs to traverse a term and there is
-- no import cycle — the situation that forced @Core.Scope@ to be merged into
-- @Core.Term@ (§2.5) simply does not arise. §2.5's own guiding principle then
-- applies in the other direction: everything cooperating to maintain the
-- normal-form invariant lives here, and nothing else needs to.
--
-- **The constructors are exported and the normal form is NOT enforced by the
-- type.** A non-normalised 'Level' is not an invalid state, only a
-- non-canonical one, so §3.4's line — representable is not the same as well
-- formed — says not to reach for a hidden constructor here. 'Eq' does the
-- normalising instead, exactly as @Eq Core@ is hand-written rather than derived.
module Thena.Core.Level
  ( Level (..)
  , LevelVar (..)
  , levelOfNat
  , levelSuc
  , levelMax
  , Normal (..)
  , normalise
  , levelLeq
  , levelVarsIn
  , substLevel
  , instantiateLevels
  ) where

import Data.List (nub, sortOn)

-- | A universe level.
--
-- @LMax@ is kept **lazy** — it is a constructor, not a computation. Under a
-- fixed hierarchy one could evaluate @max@ on the spot, and 'Thena.Core.Typing'
-- did; under polymorphism @max ℓ 0@ has no value until @ℓ@ does, so the
-- expression has to survive in the term. That is the *computed* form, and
-- choosing it over Brady's *constrained* one is what
-- @discussion\/level-binders-and-constraints.md@ §5 settles, on volume: a fresh
-- level variable and two constraints per Π is not viable on the chain.
--
-- The stated price, accepted knowingly, is that @max@ comes back — see
-- 'levelLeq'.
data Level
  = LZero
  | LSuc Level
  | LMax Level Level
  | LVar LevelVar
  deriving (Show)

-- | A level variable, and **whether it may be solved**.
--
-- 'LRigid' is a definition's prenex level parameter (phase 29): universally
-- quantified, so unification may **not** instantiate it. 'LMeta' is an unknown
-- (phase 33): unification **must** be free to. Conflating the two is how a
-- checker silently instantiates a @∀@-bound variable, so they are separate
-- constructors and every site that cares is made to say which it means.
--
-- **The distinction has to be syntactic here, where for terms it does not**,
-- and the reason is MS3's central finding. A term variable is one constructor,
-- 'Thena.Core.Term.Free', because its standing is looked up in the chain —
-- 'Thena.Core.Unify' does exactly that, asking whether a @Var@ is @KHole@,
-- @KGuess@ or @KRigid@. **Levels have no chain** (they are context-free, so
-- they need no binder on it), so there is nowhere to look anything up and the
-- standing must travel with the variable.
--
-- The split is one level down from 'Level' deliberately — the user's call,
-- 2026-08-28. 'normalise' and 'Normal' are indifferent to it, and they are the
-- delicate code; splitting 'Level' itself would fork the normaliser's variable
-- handling and force @Normal@ to carry two lists, for a distinction neither
-- cares about. The sites that do care destructure here instead.
--
-- **Generalisation at @qed@ is therefore a rewrite**: each still-unsolved
-- 'LMeta' becomes an 'LRigid' in the definition's parameter list. That is R2 of
-- @discussion\/level-binders-and-constraints.md@ §2 said out loud.
--
-- **Both @Int@s come from the same counter as 'Thena.Core.Term.Var'** — MS2
-- closeout 4f, the user's decision: one counter across every sort, so a name
-- that has reached the user inside a message can never be reissued as a
-- different kind of thing. It is also what makes naming safe without de Bruijn
-- indices here: every level variable is globally unique, so substituting one
-- away cannot capture another.
--
-- `[for phase 33]` The counter guarantee stops two variables colliding; it does
-- not stop an @LRigid@'s @Int@ being handed to the solver as though it were an
-- @LMeta@'s. If that turns out to be a live hazard, the fix is a newtype around
-- a meta's identity so the solver's substitution cannot take a rigid one — but
-- that is the solver's phase to judge, not this one's.
--
-- Neither sort binds anything, neither has a 'Thena.Core.Context.Entry', and
-- neither ever enters Γ.
data LevelVar
  = LRigid Int
  | LMeta Int
  deriving (Eq, Ord, Show)

-- | @Level@ equality is equality of normal forms, never structural:
-- @max 0 (suc 0)@ and @suc 0@ are the same level.
instance Eq Level where
  a == b = normalise a == normalise b

-- | The literal level @n@ — what a written @Typeₙ@ resolves to.
levelOfNat :: Int -> Level
levelOfNat n
  | n <= 0    = LZero
  | otherwise = LSuc (levelOfNat (n - 1))

-- | @suc@, as a function, so callers need not import the constructor.
levelSuc :: Level -> Level
levelSuc = LSuc

-- | The join. Agda spells it @⊔@ — binary, @infixl 6@ — and its builtin pragma
-- is @LEVELMAX@; read from Agda 2.8.0's own @Agda\/Primitive.agda@.
levelMax :: Level -> Level -> Level
levelMax = LMax

-- --------------------------------------------------------------------------
-- The normal form
-- --------------------------------------------------------------------------

-- | A level in normal form: a constant, and a set of variables each with an
-- offset, all combined by @max@.
--
-- @Normal c vs@ denotes @max c (max { v + k | (v, k) <- vs })@. This is the
-- representation §4 of the companion write-up calls for — /"a constant offset
-- plus a set of (variable, offset) pairs, combined by max"/ — and it is what
-- Agda uses internally, minus the library façade.
--
-- **Invariants**, all established by 'normalise' and relied on by 'Eq':
--
--   * @vs@ is sorted by variable and each variable appears once, carrying its
--     largest offset — @max (v+2) (v+5)@ is @v+5@;
--   * the constant is @0@ whenever some @k >= c@, because @v + k >= k >= c@
--     makes it redundant. Without this @max 3 (v+5)@ and @v+5@ would compare
--     unequal despite denoting the same level.
data Normal = Normal Int [(LevelVar, Int)]
  deriving (Eq, Ord, Show)

-- | Evaluate a level to its normal form. Total, and cheap.
normalise :: Level -> Normal
normalise = canon . go
  where
    go l = case l of
      LZero    -> Normal 0 []
      LVar v   -> Normal 0 [(v, 0)]
      LSuc a   -> bump (go a)
      LMax a b -> join (go a) (go b)

    bump (Normal c vs) = Normal (c + 1) [(v, k + 1) | (v, k) <- vs]

    join (Normal c vs) (Normal d ws) = Normal (max c d) (foldl' insert vs ws)

    insert acc (v, k) = case lookup v acc of
      Just k' | k' >= k -> acc
      Just _            -> (v, k) : filter ((/= v) . fst) acc
      Nothing           -> (v, k) : acc

-- | Impose the two canonicity invariants 'Normal' documents.
canon :: Normal -> Normal
canon (Normal c vs)
  | any ((>= c) . snd) vs = Normal 0 sorted
  | otherwise             = Normal c sorted
  where
    sorted = sortOn fst vs

-- --------------------------------------------------------------------------
-- Comparison
-- --------------------------------------------------------------------------

-- | Is the first level less than or equal to the second?
--
-- Three answers, and **which reading applies is decided by the sort of variable
-- involved** — the user's ruling of 2026-08-28, and it resolves what phase 28
-- deliberately left open:
--
--   * an 'LRigid' is a definition's prenex parameter, **universally
--     quantified**, so the question is **validity**: does it hold for /every/
--     instantiation? That is decidable.
--   * an 'LMeta' is an unknown to be solved, so the question is a
--     **constraint**, and the answer is @Nothing@ — postpone, retry once
--     something is solved, refuse only what survives to the end.
--
-- They were only ever in tension because the sorts had not been separated.
--
-- **Phase 28 answered @Nothing@ for anything with a variable in it**, which was
-- right while nothing could build one and wrong the moment datatypes gained
-- parameters: the size restriction (@Thena.Global.Declare@) is the only caller,
-- it treats @Nothing@ as refusal, and a polymorphic datatype would have been
-- refused outright.
--
-- **The shape of the difficulty is §6.1 of
-- @discussion\/level-binders-and-constraints.md@**, and it is why the left
-- decomposes and the right does not:
--
-- > max a b <= c    <=>   a <= c  &&  b <= c        decomposes, nothing guessed
-- > c <= max a b    <=>   c <= a  ||  c <= b        a DISJUNCTION
levelLeq :: Level -> Level -> Maybe Bool
levelLeq a b = leqNormal (normalise a) (normalise b)

-- | The left is a @max@, so it decomposes: every component must fit under the
-- right, and splitting it up guesses nothing.
leqNormal :: Normal -> Normal -> Maybe Bool
leqNormal (Normal c vs) rhs =
  combine (atMost (Left c) rhs : [atMost (Right p) rhs | p <- vs])
  where
    -- **False beats undecided beats true.** One component that can never fit
    -- refutes the whole thing however the others turn out.
    combine rs
      | Just False `elem` rs = Just False
      | Nothing    `elem` rs = Nothing
      | otherwise            = Just True

-- | One indecomposable component of the left, against the whole right.
--
-- @Left c@ is the constant; @Right (v, k)@ is @v + k@.
atMost :: Either Int (LevelVar, Int) -> Normal -> Maybe Bool
atMost lhs (Normal d ws) = case lhs of
  -- A constant is dominated exactly when it is dominated with every variable at
  -- its smallest, which is zero — variables only grow from there.
  Left c
    | c <= floorOf   -> Just True
    | rightHasMeta   -> Nothing      -- a meta could yet be large enough
    | otherwise      -> Just False

  -- **Only the same variable can dominate a variable**, and that is the whole
  -- of it: a rigid @v@ ranges over every level, so no constant and no /other/
  -- variable bounds it. @v + k <= v + k'@ reduces to @k <= k'@ and the variable
  -- cancels.
  Right (v, k)
    | any (\(w, k') -> w == v && k <= k') ws -> Just True
    | isMeta v     -> Nothing        -- @v@ itself could yet be small
    | rightHasMeta -> Nothing        -- or something on the right could be large
    | otherwise    -> Just False
  where
    floorOf      = maximum (d : map snd ws)
    rightHasMeta = any (isMeta . fst) ws

isMeta :: LevelVar -> Bool
isMeta v = case v of
  LMeta _  -> True
  LRigid _ -> False

-- --------------------------------------------------------------------------
-- Substitution — what instantiating a scheme does
-- --------------------------------------------------------------------------

-- | Every level variable a level mentions, without duplicates, in first-seen
-- order.
levelVarsIn :: Level -> [LevelVar]
levelVarsIn l = nub (go l)
  where
    go x = case x of
      LZero    -> []
      LSuc a   -> go a
      LMax a b -> go a ++ go b
      LVar v   -> [v]

-- | Replace level variables by levels, everywhere at once.
--
-- **No capture is possible and no freshening is needed.** 'Level' has no binder
-- of its own — prenex means the only binder is the definition's head — and
-- every 'LevelVar' carries an @Int@ from the one global counter, so two
-- variables are equal exactly when they are the same variable. The second
-- dividend from MS2 closeout 4f.
substLevel :: [(LevelVar, Level)] -> Level -> Level
substLevel sub = go
  where
    go l = case l of
      LZero    -> LZero
      LSuc a   -> LSuc (go a)
      LMax a b -> LMax (go a) (go b)
      LVar v   -> case lookup v sub of
        Just l' -> l'
        Nothing -> l

-- | Instantiate a prenex scheme: pair its parameters with the arguments given
-- and substitute.
--
-- @Nothing@ when the counts do not match — prenex is all-or-nothing, so there
-- is no partial instantiation to allow, and the caller names the definition
-- when it reports this.
instantiateLevels :: [LevelVar] -> [Level] -> Maybe [(LevelVar, Level)]
instantiateLevels ps as
  | length ps == length as = Just (zip ps as)
  | otherwise              = Nothing
