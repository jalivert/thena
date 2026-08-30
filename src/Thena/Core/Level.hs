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
  , freshLevelMeta
  , freshLevelRigid
  , levelSuc
  , levelMax
  , Normal (..)
  , normalise
  , levelLeq
  , levelVarsIn
  , substLevel
  , instantiateLevels
    -- * Obligations and their solver (phase 33)
  , Obligation (..)
  , Unmet (..)
  , solveLevels
  , substObligation
  , LevelUnification (..)
  , unifyLevels
  , metasIn
  , loneMeta
  , levelVarName
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

-- | A level variable's display name, numbered from the shared counter.
--
-- **A meta wears the @?@ and a rigid parameter does not** — the same convention
-- the development already uses, where @? x@ is a hole and a bare name is a
-- hypothesis. A reader who knows what @?@ means in @:show@ knows what it means
-- here.
--
-- **Here rather than in "Thena.Repl", where display otherwise lives**, because
-- two modules need the spelling and there is nothing to look a level variable's
-- name up in: unlike a 'Thena.Core.Term.Var', which the development names, a
-- 'LevelVar' /is/ its number. "Thena.Engine" names the metas @unify@ solved in
-- the message it builds, and a second copy of this would be a second spelling.
-- **A rigid's number is a subscript** — the user's call, 2026-08-30. @ℓ231@
-- reads as a level *expression* because a level is a number; @ℓ₂₃₁@ reads as a
-- name with an index on it, which is what it is. A meta keeps its digits: the
-- @?@ already says it is not a name, and its number is the one thing a reader
-- has to carry between two messages.
levelVarName :: LevelVar -> String
levelVarName v = case v of
  LRigid i -> "ℓ" ++ subscript i
  LMeta  i -> "?ℓ" ++ show i

-- | Digits as their subscript forms. Negative numbers cannot arise — every
-- variable is minted from a counter that starts at zero.
subscript :: Int -> String
subscript = map sub . show
  where
    sub c = toEnum (fromEnum '₀' + (fromEnum c - fromEnum '0'))

-- | Mint a level meta from the shared counter — what a written bare @Type@
-- resolves to (MS3 phase 33).
--
-- The level-sort twin of 'Thena.Core.Term.fresh', and it takes and returns the
-- same 'Int': MS2 closeout 4f is the user's decision that there is **one
-- counter across every sort**, so a name that has reached the user inside a
-- message can never be reissued as a different kind of thing. That is also what
-- makes 'substLevel' capture-free — see its note.
freshLevelMeta :: Int -> (LevelVar, Int)
freshLevelMeta n = (LMeta n, n + 1)

-- | Mint a prenex level parameter from the shared counter — what generalisation
-- turns a surviving meta into (MS3 phase 33b).
--
-- Beside 'freshLevelMeta' and drawing from the same counter, for the same
-- reason: MS2 closeout 4f. **A meta is not rewritten to a rigid of its own
-- number** — @?ℓ7@ may already have reached the user in a message, and @ℓ7@
-- would be that number said about a different kind of thing.
freshLevelRigid :: Int -> (LevelVar, Int)
freshLevelRigid n = (LRigid n, n + 1)

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

-- --------------------------------------------------------------------------
-- Obligations, and the pass that discharges them (phase 33)
-- --------------------------------------------------------------------------

-- | @AtMost l k@ — the deferred reading of @l ≤ k@.
--
-- **This is what conversion hands back instead of failing** (phase 33). Under
-- typical ambiguity a subsumption may involve a level that is not yet known, so
-- 'levelLeq' answers @Nothing@; refusing there would make a meta a term nothing
-- can be checked against. The relation is recorded instead and decided by the
-- pass below.
--
-- **Nothing stores one during a proof.** @discussion\/level-binders-and-constraints.md@
-- §4 is the decision — obligations are re-collected by re-checking, because
-- re-checking the finished development regenerates precisely the ones that
-- should apply. So an @Obligation@ lives only as long as the check that
-- produced it.
data Obligation = AtMost Level Level
  deriving (Eq, Show)

-- | An obligation no instantiation could ever satisfy.
--
-- **The only way the pass fails** (MS3 phase 33b). It had a second constructor,
-- @Undetermined@, for an obligation the pass could neither discharge nor refute
-- — and that is no longer a failure: it is the **residue**, and generalisation
-- stores it on the definition rather than refusing it. What is left here is a
-- mistake in the term, which is what the message says.
data Unmet = Refuted Level Level
  deriving (Eq, Show)

-- | Discharge what can be discharged, refuse what can never hold, and hand back
-- the rest.
--
-- **A worklist run to a fixpoint** — the user's decision of 2026-08-27:
-- /"sometimes some of those @c@ or @a@ or @b@s could solve and make the
-- constraint trivially solvable"/. One round asks 'levelLeq' of everything
-- pending; what it decides is discharged or refuted, and what it cannot is
-- looked at for a solution. Two kinds are found, and either restarts the round:
--
--   * **forced** — a meta whose bounds have met ('forced');
--   * **equated** — two metas each bounded by the other, which is an equality
--     however it was written ('equated').
--
-- **It never guesses.** A bound is only read off an obligation one of whose
-- sides is a constant, and an equality only off a relation that was stated both
-- ways. So every solution it finds is the only one there was, which is what
-- makes the residue order-independent.
--
-- **The residue is not a failure — phase 33b.** What a round can neither decide
-- nor solve is handed back for generalisation to store on the definition, which
-- is §4's call-site machinery: the constraint list in the environment plus the
-- level arguments in the term are what let @qed@ re-derive it at every use.
-- Phase 33 refused it instead, because there was nothing yet to store it on.
--
-- **It terminates without a guard.** Every solution replaces a meta everywhere,
-- so the number of distinct metas among the pending obligations strictly
-- decreases; a round that solves nothing stops.
--
-- **It returns what it solved as well as what is left**, because the caller owns
-- the terms the metas came from and has to write the solutions into them.
solveLevels :: [Obligation] -> Either Unmet ([(LevelVar, Level)], [Obligation])
solveLevels obs = case sift obs of
  Left u        -> Left u
  Right pending -> case solutions pending of
    []  -> Right ([], pending)
    sub -> do
      (rest, residue) <- solveLevels (map (over sub) pending)
      Right (sub ++ rest, residue)
  where
    -- **A constant solution first, an equality only when there is none.** The
    -- two can name the same meta — @2 ≤ ?m@ and @?m ≤ 2@ are both bounds that
    -- meet and a relation stated both ways — and taking either alone is right
    -- where taking both would substitute twice.
    solutions p = case forced p of
      [] -> equated p
      sub -> sub

    over sub (AtMost l k) = AtMost (substLevel sub l) (substLevel sub k)

    -- One round's decisions: refuted stops everything, decided is dropped,
    -- undecided comes back for the solver to look at.
    sift []                    = Right []
    sift (o@(AtMost l k) : os) = case levelLeq l k of
      Just False -> Left (Refuted l k)
      Just True  -> sift os
      Nothing    -> (o :) <$> sift os

-- | Apply a level substitution to an obligation — what instantiating a
-- definition's scheme does to its stored constraints at a use site.
substObligation :: [(LevelVar, Level)] -> Obligation -> Obligation
substObligation sub (AtMost l k) = AtMost (substLevel sub l) (substLevel sub k)

-- | Metas that two obligations state to be equal — @l ≤ k@ and @k ≤ l@ — where
-- one side is a lone meta.
--
-- **Written as two inequalities because that is how conversion says an
-- equality** (phase 33): a Π's domain is invariant, so an undecided equality is
-- owed both ways round. Reading them back as one substitution is what keeps
-- generalisation from producing @foo {ℓ0 ℓ1}@ with @ℓ0 ≤ ℓ1@ and @ℓ1 ≤ ℓ0@
-- where @foo {ℓ0}@ was meant — which is the ordinary shape of
-- @∀ (A : Type) -> A -> A@.
--
-- At most one is returned per round; the fixpoint finds the next.
equated :: [Obligation] -> [(LevelVar, Level)]
equated obs =
  take 1
    [ (v, k)
    | AtMost l k <- obs
    , AtMost k' l' <- obs
    , normalise k == normalise k', normalise l == normalise l'
    , Just v <- [loneMeta l]
    , v `notElem` metasIn k
    ]

-- | The metas whose lower and upper bounds have met, read off the pending
-- obligations. Empty when nothing is forced, which is what ends the fixpoint.
--
-- A bound is derived only where one side of the relation is a constant:
--
-- > ?m + j ≤ d          gives  ?m ≤ d - j        (and refutes if d < j)
-- > c ≤ ?m + j          gives  ?m ≥ c - j
--
-- Everything else — a relation between two metas, a @max@ on the right with
-- more than one term — bounds nothing and is left for a later round, when a
-- substitution may have collapsed it.
--
-- **A meta whose bounds have crossed is solved to its lower bound anyway**, so
-- that the next round's 'levelLeq' reports a 'Refuted' obligation the user can
-- read rather than an 'Undetermined' one that says nothing.
forced :: [Obligation] -> [(LevelVar, Level)]
forced obs =
  [ (v, levelOfNat lo)
  | v <- nub (map fst bounds)
  , let lo = maximum (0 : [b | (w, Lower b) <- bounds, w == v])
  , let his = [b | (w, Upper b) <- bounds, w == v]
  , not (null his)
  , lo >= minimum his
  ]
  where
    bounds = concatMap boundsOf obs

data Bound = Lower Int | Upper Int
  deriving (Eq, Show)

-- | The constant bounds one obligation puts on a meta.
boundsOf :: Obligation -> [(LevelVar, Bound)]
boundsOf (AtMost l k) = case (normalise l, normalise k) of
  -- The right is a constant, so every variable on the left is bounded above.
  (Normal _ vs, Normal d []) ->
    [ (v, Upper (d - j)) | (v, j) <- vs, isMeta v ]

  -- The right is a single variable term. The left's constant must fit under it
  -- whenever it does not already fit under the right's own constant.
  (Normal c [], Normal d [(w, j)])
    | c > d, isMeta w -> [(w, Lower (c - j))]

  _ -> []

-- --------------------------------------------------------------------------
-- Level unification — what "Thena.Core.Unify" does with two universes
-- --------------------------------------------------------------------------

-- | The three answers a level equation has.
--
-- **@LevelsStuck@ is not a failure**, and that is the user's decision of
-- 2026-08-27: /a level obligation does not block/ — solve if possible,
-- otherwise proceed, because the final pass re-derives everything. A 'Clash' is
-- different in kind: no instantiation of any variable makes @Type₀@ and
-- @Type₁@ the same, so nothing is being deferred and the unifier must fail.
data LevelUnification
  = LevelsSolved [(LevelVar, Level)]
  | LevelsStuck
  | LevelsClash Level Level
  deriving (Eq, Show)

-- | Unify level equations, solving metas left to right.
--
-- Solutions found early are substituted into what is left, which is the
-- Optimist's lemma in the small: @[?a, ?a] ≟ [0, 0]@ solves once and then
-- checks. Takes the pairs already zipped, because every caller has checked that
-- the two lists are the same length and has its own clash to report if not.
unifyLevels :: [(Level, Level)] -> LevelUnification
unifyLevels = go [] False
  where
    go sub stuck [] = if stuck then LevelsStuck else LevelsSolved sub
    go sub stuck ((a, b) : rest) =
      case one (substLevel sub a) (substLevel sub b) of
        LevelsClash x y  -> LevelsClash x y
        LevelsStuck      -> go sub True rest
        LevelsSolved s   -> go (compose s sub) stuck rest

    compose s sub = s ++ [ (v, substLevel s l) | (v, l) <- sub ]

-- | One level equation.
--
-- A lone meta is solved by the other side; anything else either has no variable
-- in it at all — in which case the normal forms decide it — or is stuck.
one :: Level -> Level -> LevelUnification
one a b
  | a == b = LevelsSolved []
  | otherwise = case (loneMeta a, loneMeta b) of
      (Just v, _) | v `notElem` levelVarsIn b -> LevelsSolved [(v, b)]
      (_, Just w) | w `notElem` levelVarsIn a -> LevelsSolved [(w, a)]
      _ | rigidOnly a && rigidOnly b -> LevelsClash a b
        | otherwise                  -> LevelsStuck
  where
    rigidOnly l = not (any isMeta (levelVarsIn l))

-- | The level that is exactly one meta, with no offset and no join.
--
-- Exported for "Thena.Global.Declare" as well as used here: a declared universe
-- written as a bare @Type@ is exactly this, and that is what makes it the one
-- that gets computed rather than checked (phase 33c).
loneMeta :: Level -> Maybe LevelVar
loneMeta l = case normalise l of
  Normal 0 [(v, 0)] | isMeta v -> Just v
  _                            -> Nothing

-- | Every level meta a level mentions.
metasIn :: Level -> [LevelVar]
metasIn = filter isMeta . levelVarsIn
