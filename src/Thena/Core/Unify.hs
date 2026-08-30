-- | Unification (§6): recursive decomposition, Miller patterns, and deferral
-- as a @Pending@ link in the chain.
--
-- **Above "Thena.Development.Cursor" in the layering, and it keeps the @Core.@
-- prefix** — decided by the user 2026-08-22, closing @AGENDA.md@ item 18b. The
-- prefix describes what it unifies, core terms, not where it sits. It has to
-- sit here: §7.4 makes @unify@ the one core operation that takes the
-- development rather than a 'Context', because it /writes/ — it promotes holes
-- and posts constraints, and it must know which variables are solvable and in
-- what order they were bound.
--
-- **The store is the development** (§6.4). There is no structure beside it, no
-- blocker tags, and no sweep on @regret@: a postponed constraint is a link in
-- the chain, so it backtracks, undoes and is discarded with the guess that
-- contains it, for free.
module Thena.Core.Unify
  ( UnifyResult (..)
  , unify
  , blockers
  , constraintsOf
  ) where

import Data.List (nub)

import Thena.Core.Context (Context, Entry (..), entryVar, lamOver, substLevelsInEntry)
import Thena.Core.Reduce (whnf)
import Thena.Core.Level
  ( LevelUnification (..)
  , LevelVar
  , unifyLevels
  )
import Thena.Core.Term
  ( Core (..)
  , Ident
  , Var
  , close
  , freeVars
  , fresh
  , instantiate
  , open
  , substLevelsIn
  )
import Thena.Core.Typing (infer)
import Thena.Development.Component (Component (..), forget)
import Thena.Development.Cursor
  ( Cursor
  , Focus (..)
  , Path (..)
  , Step (..)
  , below
  , context
  , focus
  , overComponents
  , overConstraints
  , overLevels
  , postConstraint
  , prefix
  , rebuild
  )
import Thena.Development.Partial (Constraint (..), Partial (..))
import Thena.Errors (FailReason (..))
import Thena.Global.Env (GlobalEnv)

-- | Three-way, as a returned value — never a Haskell exception (§6.2). The
-- tactic engine has to inspect it, because failure routes through the frame
-- stack (§7.3), and an exception would bypass the frames entirely.
--
-- The payloads are what the deliverable needs and nothing more: which holes
-- became definitions, **which level metas were solved** (MS3 phase 33), and
-- what is still parked. None is stored anywhere — the holes and the levels are
-- read off what changed and the constraints are read off the development, which
-- is where they live.
--
-- The levels are a separate list rather than folded in with the holes because
-- they are a different sort: a hole becomes a component and a level meta becomes
-- part of every term that mentioned it. They are reported together all the same
-- — what the caller wants to say is /what got solved/.
data UnifyResult
  = Solved   [Var] [LevelVar]
    -- ^ holes and level metas instantiated, nothing left parked
  | Deferred [Var] [LevelVar] [Constraint]
    -- ^ the same, and what still waits
  | Failed   FailReason           -- ^ structurally impossible; triggers unwind
  deriving (Eq, Show)

-- | Unify two terms at a type, rewriting the development.
--
-- **All or nothing.** On 'Failed' the development comes back exactly as it went
-- in. Sub-problems are solved in sequence and a later one may depend on an
-- earlier one's solution (the Optimist's lemma, @OLEG.md@), so a failure part
-- way through would otherwise leave half a substitution the user cannot see the
-- cause of. Θ ⊑ Θ' still holds — trivially — and the machine's unwind is not
-- asked to clean up after a partial success.
--
-- The type is an argument. §7.4's signature omits it, which is not writable:
-- a deferred equation is @Equate Ξ s t T@ and something has to supply the @T@.
-- The caller has it — conversion and unification are only ever called with a
-- common expected type (§5.2) — so it is passed rather than re-derived.
--
-- The counter is taken and returned for phase 8's reason, and it is genuinely
-- needed here: decomposing under a Π or a λ mints the binder that goes into Ξ.
unify
  :: GlobalEnv -> Cursor -> Int -> Core -> Core -> Core
  -> (UnifyResult, Cursor, Int)
unify env cur n s t ty =
  case work env (St cur n [] []) (Equate [] s t ty) >>= wake env of
    Left (reason, n') -> (Failed reason, cur, n')
    Right st ->
      let solved = reverse (stSolved st)
          levels = reverse (stLevels st)
          parked = constraintsOf (rebuild (stCur st))
       in ( if null parked
              then Solved solved levels
              else Deferred solved levels parked
          , stCur st
          , stNames st
          )

-- | Which holes a parked constraint is waiting on.
--
-- **Derived, never stored** (§6.1): the blocking holes /are/ the free variables
-- it mentions that are still unsolved, so a tag would be a cache with a
-- staleness problem and nothing else.
blockers :: Cursor -> Constraint -> [Var]
blockers cur k =
  [ x | x <- mentions k, Just kind <- [lookup x (kinds cur)], unsolved kind ]
  where
    unsolved KHole {} = True
    unsolved KGuess   = True
    unsolved KRigid   = False

-- | Every constraint in the development, root first.
constraintsOf :: Partial -> [Constraint]
constraintsOf p = case p of
  Trailing _     -> []
  Under _ rest   -> constraintsOf rest
  Pending k rest -> k : constraintsOf rest

-- --------------------------------------------------------------------------
-- The state carried while solving
-- --------------------------------------------------------------------------

data St = St
  { stCur    :: Cursor
  , stNames  :: Int
  , stSolved :: [Var]        -- ^ newest first; reversed on the way out
  , stLevels :: [LevelVar]   -- ^ the level metas solved, same convention
  }

-- | A failure carries the counter, because a variable minted on the way to it
-- may already have reached the user inside a reason (§7.4).
type Attempt a = Either (FailReason, Int) a

-- --------------------------------------------------------------------------
-- What the chain says about a variable
-- --------------------------------------------------------------------------

-- | A variable's standing, from unification's point of view.
--
-- 'KHole' is the only solvable one — a /bare/ hole, §4.0 G2's "promotes bare
-- holes only". 'KGuess' is a blocked neutral and never solved (§6.3): the
-- equation defers instead, and the user's work in progress is left alone.
data Kind = KHole Ident Core | KGuess | KRigid
  deriving (Eq, Show)

-- | Every chain variable, with its standing.
kinds :: Cursor -> [(Var, Kind)]
kinds = map (\(_, x, k) -> (x, k)) . chain

-- | The chain, as @(position, variable, standing)@ triples, root first.
--
-- **Position is an index into the path, then the focus, then what is below.**
-- That is the order the chain binds in, and it is the whole of what
-- unification needs position for: a solution for a hole at index @i@ may
-- mention only variables at indices below @i@ (§6.4's dependency order). A
-- 'Past' link occupies an index and declares nothing, which is what keeps these
-- indices aligned with 'postConstraint'\'s count.
--
-- **A guess's body is not walked.** Nothing in MS1 builds a guess (phase 17),
-- and §6.3 already makes the guess itself a blocked neutral, so a constraint
-- mentioning something inside one defers on the guess's own variable. Stated as
-- a limit rather than left to be discovered.
chain :: Cursor -> [(Int, Var, Kind)]
chain cur = index 0 (above ++ here ++ under)
  where
    above = map ofStep (toList' (prefix cur))
    here  = case focus cur of
      OnComponent c  -> [Just (kindOf c)]
      OnConstraint _ -> [Nothing]
      OnTerm {}      -> [Nothing]
    under = maybe [] links (below cur)

    ofStep s = case s of
      Along c             -> Just (kindOf c)
      Past _              -> Nothing
      IntoGuess x _ _ _   -> Just (x, KGuess)

    links p = case p of
      Trailing _     -> []
      Under c rest   -> Just (kindOf c) : links rest
      Pending _ rest -> Nothing : links rest

    index _ []             = []
    index i (Nothing : es) = index (i + 1) es
    index i (Just (x, k) : es) = (i, x, k) : index (i + 1) es

    toList' Here     = []
    toList' (p :> s) = toList' p ++ [s]

kindOf :: Component -> (Var, Kind)
kindOf c = case c of
  Assume x _ _    -> (x, KRigid)
  Define x _ _ _  -> (x, KRigid)
  Claim  x i ty   -> (x, KHole i ty)
  Guess  x _ _ _  -> (x, KGuess)

-- | The context every core operation is called in here: Γ at the focus, the
-- focused component, and everything below.
--
-- Wider than Γ on purpose. δ must be able to unfold a definition wherever it
-- sits, and unification does not use this context for scope — scope is
-- 'chain'\'s positions, which is §7.4's reason for @unify@ taking the
-- development in the first place.
whole :: Cursor -> Context
whole cur = context cur ++ here ++ under
  where
    here = case focus cur of
      OnComponent c -> [forget c]
      _             -> []
    under = maybe [] (map forget . components) (below cur)

components :: Partial -> [Component]
components p = case p of
  Trailing _     -> []
  Under c rest   -> c : components rest
  Pending _ rest -> components rest

-- --------------------------------------------------------------------------
-- Solving one equation
-- --------------------------------------------------------------------------

work :: GlobalEnv -> St -> Constraint -> Attempt St
work env st (Equate xi s t ty)
  | s == t    = Right st
  | otherwise =
      let ctx = whole (stCur st) ++ xi
          s'  = whnf env ctx s
          t'  = whnf env ctx t
       in if s' == t'
            then Right st
            else match env st ctx (Equate xi s' t' ty)

-- | Both sides are in whnf. Which rule applies is decided by the two heads
-- (§6.1): a blocked head defers, a flex head against a rigid one is the pattern
-- case, flex against flex defers, and rigid against rigid decomposes.
match :: GlobalEnv -> St -> Context -> Constraint -> Attempt St
match env st ctx k@(Equate _ s t _) =
  case (headOf st ctx s, headOf st ctx t) of
    (HBlocked, _) -> park env st k
    (_, HBlocked) -> park env st k
    (HFlex {}, HFlex {}) -> park env st k      -- flex-flex is deferred (§6.1)
    (HFlex x i, _) -> flexRigid env st ctx k x i (spineArgs s) t
    (_, HFlex y i) -> flexRigid env st ctx k y i (spineArgs t) s
    (HRigid, HRigid) -> rigidRigid env st ctx k

data Head = HFlex Var Int | HBlocked | HRigid

headOf :: St -> Context -> Core -> Head
headOf st ctx t = case spineHead t of
  Free x -> case [ (i, kind) | (i, y, kind) <- chain (stCur st), y == x ] of
    (i, KHole _ _) : _ -> HFlex x i
    (_, KGuess)    : _ -> HBlocked
    _                  -> HRigid          -- a Ξ or term binder, or an assumption
  -- An 'Eliminate' still standing after whnf means ι did not fire, so its
  -- target is neutral. If that target's own head can still change — a hole, a
  -- guess — the elimination can still compute and nothing may be concluded
  -- from its shape.
  Eliminate _ _ _ _ _ _ tgt -> case headOf st ctx tgt of
    HRigid -> HRigid
    _      -> HBlocked
  _ -> HRigid

spineHead :: Core -> Core
spineHead (App f _) = spineHead f
spineHead t         = t

spineArgs :: Core -> [Core]
spineArgs = go []
  where
    go as (App f a) = go (a : as) f
    go as _         = as

-- --------------------------------------------------------------------------
-- The pattern case
-- --------------------------------------------------------------------------

-- | @?h x⃗ ≟ t@ where @x⃗@ are distinct locally-bound variables: Miller's
-- pattern fragment, whose solution is @?h := λ x⃗ . t@ and is the most general
-- one.
--
-- "Locally bound" means not declared in the chain at all — a Ξ binder minted
-- while decomposing under a Π or a λ, or a binder the focus is standing under.
-- A chain variable in argument position is not a pattern argument: abstracting
-- it would change what the hole means.
--
-- Outside the fragment the equation defers rather than failing. That is not a
-- weaker answer, it is the right one: an argument that is not a variable today
-- may reduce to one once some other hole is solved.
flexRigid
  :: GlobalEnv -> St -> Context -> Constraint -> Var -> Int -> [Core] -> Core
  -> Attempt St
flexRigid env st ctx k x i args rhs = case patternArgs (kinds (stCur st)) ctx args of
  Nothing -> park env st k
  Just es
    | x `elem` freeVars rhs -> Left (OccursCheck ctx x rhs, stNames st)
    | otherwise ->
        let sol = demote st i (lamOver es rhs)
         in case scopeCheck st i sol of
              OutOfScope y -> Left (ScopeViolation ctx x y, stNames st)
              MightCome    -> park env st k
              InScope      -> Right (solve x sol st)

-- | The arguments as a telescope, if every one is a distinct variable that is
-- local to the equation. The entries come from the live context, so the
-- abstraction gets the types the binders actually have.
--
-- **Local means not declared in the chain.** A chain variable in argument
-- position is not a pattern argument: @?f a@ where @a@ is a component of the
-- development is not Miller's @?f x⃗@, and abstracting @a@ would change what the
-- hole means — it would answer a different question from the one asked. The
-- first draft omitted this check and happily solved @?f a ≟ zero@ with
-- @λ a. zero@, which is a solution to no equation anybody wrote.
patternArgs :: [(Var, Kind)] -> Context -> [Core] -> Maybe Context
patternArgs table ctx as = do
  vs <- mapM variable as
  if distinct vs && all local vs then mapM entry vs else Nothing
  where
    variable (Free v) = Just v
    variable _        = Nothing

    local v = v `notElem` map fst table

    entry v = case [ e | e <- ctx, entryVar e == v ] of
      e : _ -> Just e
      []    -> Nothing

    distinct vs = length (nub vs) == length vs

data Scope = InScope | MightCome | OutOfScope Var

-- | Unfold, inside the solution, every definition bound at or after the hole.
--
-- A definition's /meaning/ does not depend on where it sits — only its name
-- does — so a solution mentioning one that is out of position is not ill-founded
-- once the name is replaced by what it stands for. Without this, an equation
-- parked on a hole and woken after that hole became a definition would fail a
-- scope check it had every right to pass: @?h ≟ succ ?k@ with @h@ before @k@
-- waits, and then @?k := zero@ makes it @h = succ zero@, not an error.
--
-- It terminates because a definition's value only mentions things bound before
-- it, so each pass moves strictly leftwards.
demote :: St -> Int -> Core -> Core
demote st i = go (100 :: Int)
  where
    table = chain (stCur st)
    values = definitionsOf (rebuild (stCur st))

    go 0 t = t
    go fuel t =
      let outOfPlace =
            [ (x, v) | (j, x, _) <- table, j >= i, Just v <- [lookup x values]
            , x `elem` freeVars t ]
       in case outOfPlace of
            [] -> t
            xs -> go (fuel - 1) (foldl (\u (x, v) -> substFree x v u) t xs)

-- | Every definition in the chain, with its value.
definitionsOf :: Partial -> [(Var, Core)]
definitionsOf p = case p of
  Trailing _              -> []
  Pending _ rest          -> definitionsOf rest
  Under (Define x _ v _) rest -> (x, v) : definitionsOf rest
  Under _ rest            -> definitionsOf rest

-- | Substitute a free variable throughout a term: 'close' then 'instantiate',
-- the same composition "Thena.Core.Reduce" makes rather than a new primitive.
substFree :: Var -> Core -> Core -> Core
substFree x v t = instantiate v (close x t)

-- | May a hole at position @i@ be solved with this term?
--
-- Everything the term mentions must be bound before @i@ (§6.4's dependency
-- order). When something is not:
--
--   * if it is itself a hole or a guess, the answer is not "no" but "not yet" —
--     solving it may put something in scope there — so the equation defers;
--   * if it is rigid, nothing will ever change and this is a real
--     'ScopeViolation'. Repairing it would mean moving a declaration leftwards,
--     which is a tactic's decision, not a unifier's — see "Thena.Errors".
scopeCheck :: St -> Int -> Core -> Scope
scopeCheck st i sol = go (freeVars sol)
  where
    table = chain (stCur st)

    go [] = InScope
    go (y : ys) = case [ (j, kind) | (j, z, kind) <- table, z == y ] of
      (j, kind) : _
        | j < i     -> go ys
        | otherwise -> case kind of
            KRigid -> OutOfScope y
            _      -> MightCome
      [] -> OutOfScope y    -- a local binder that escaped its abstraction

-- | Promote the hole: @? x : S@ becomes @x = t : S@ (§4.0 G2), everywhere in
-- the development at once, with the focus intact.
--
-- **No substitution through the development.** Once the component has a value,
-- δ unfolds it on demand (§5.1), which is McBride's own answer — explanations
-- are activated by putting them in the context, not by propagating them through
-- terms. It is also why @regret@ needs no sweep (§6.1).
solve :: Var -> Core -> St -> St
solve x t st = st
  { stCur    = overComponents promote (stCur st)
  , stSolved = x : stSolved st
  }
  where
    promote c = case c of
      Claim y i ty | y == x -> Define y i t ty
      _                     -> c

-- --------------------------------------------------------------------------
-- Rigid-rigid decomposition
-- --------------------------------------------------------------------------

-- | Replace a problem by the problems it decomposes into, solved in sequence —
-- §6.4's splices, and the Optimist's lemma is what licenses doing it greedily
-- and in order.
--
-- **Level arguments are solved before the term arguments** (MS3 phase 33). A
-- level is not a 'Core', so it cannot become a sub-problem; it is an equation in
-- the level algebra, and 'unifyLevels' either solves it, clashes, or is stuck.
--
--   * **solved** — the solution is pushed through the whole development with
--     'overLevels' and the problem is /restarted/. A level meta has no component
--     to be promoted, so there is nowhere to record @?ℓ := 0@ but the terms that
--     mention it (§4); restarting is what keeps the equation in hand from
--     carrying a variable the development no longer has. It terminates because
--     each restart removes at least one meta.
--   * **stuck** — @max ?a ?b ≟ 3@ and its like. **It proceeds**, which is the
--     user's decision of 2026-08-27: /a level obligation does not block/, and
--     the pass at @qed@ re-derives everything. The cost is that the error
--     arrives there rather than at the line.
--   * **clash** — no instantiation makes @Type₀@ and @Type₁@ the same, so this
--     is an ordinary mismatch and fails here.
rigidRigid :: GlobalEnv -> St -> Context -> Constraint -> Attempt St
rigidRigid env st ctx k@(Equate xi s t ty) = case levelPairs of
  Just (eqs, clash) -> case unifyLevels eqs of
    LevelsClash _ _  -> Left (clash, stNames st)
    LevelsStuck      -> structural
    LevelsSolved []  -> structural
    LevelsSolved sub ->
      work env st { stCur    = overLevels sub (stCur st)
                  , stLevels = reverse (map fst sub) ++ stLevels st
                  }
                  (pushed sub k)
  Nothing -> structural
  where
    -- The level arguments two matching heads must agree on, and what to report
    -- if they cannot. @Nothing@ for a node that carries no levels.
    levelPairs = case (s, t) of
      (Universe a, Universe b) -> Just ([(a, b)], UniverseMismatch a b)
      -- **A neutral 'Global' carries level arguments too**, and they are
      -- unified like a former's rather than compared. It reaches here whenever
      -- @whnf@ leaves one standing — an under-applied former wrapper, or a
      -- constant with no body — and until this was added @Eq {?l} ≟ Eq {0}@
      -- fell through to a 'Mismatch' that no level could ever have been at
      -- fault for. Found reviewing MS3.
      (Global f ks, Global g ls)
        | f == g, length ks == length ls -> Just (zip ks ls, Mismatch ctx s t)
      (Canonical f ks _, Canonical g ls _)
        | f == g, length ks == length ls -> Just (zip ks ls, Mismatch ctx s t)
      (Eliminate d ks _ _ _ _ _, Eliminate d' ls _ _ _ _ _)
        | d == d', length ks == length ls -> Just (zip ks ls, Mismatch ctx s t)
      _ -> Nothing

    pushed sub (Equate xi' a b ty') =
      Equate (map (substLevelsInEntry sub) xi')
             (substLevelsIn sub a) (substLevelsIn sub b) (substLevelsIn sub ty')

    structural = case (s, t) of
      -- **Reached only when 'levelPairs' has already settled the levels** —
      -- solved to equal, or stuck and therefore proceeding. There is nothing
      -- left for this case to compare, and comparing again would refuse the
      -- stuck case that the decision above says to let through.
      (Universe _, Universe _) -> Right st

      -- A neutral reference has no sub-terms, so like a universe it is
      -- finished once 'levelPairs' has settled its levels.
      (Global f ks, Global g ls)
        | f == g, length ks == length ls -> Right st

      (Pi i dom sc, Pi _ dom' sc') -> binder i dom sc dom' sc'
      (Lam i dom sc, Lam _ dom' sc') -> binder i dom sc dom' sc'

      (App f a, App g b) -> sequential [(f, g), (a, b)]

      (Canonical f ks as, Canonical g ls bs)
        | f == g, length ks == length ls, length as == length bs -> sequential (zip as bs)

      (Eliminate d ks ps m ms is tgt, Eliminate d' ls ps' m' ms' is' tgt')
        | d == d'
        , length ks == length ls
        , length ps == length ps'
        , length ms == length ms'
        , length is == length is' ->
            sequential (zip ps ps' ++ [(m, m')] ++ zip ms ms' ++ zip is is' ++ [(tgt, tgt')])

      _ -> Left (Mismatch ctx s t, stNames st)

    -- Sub-problems inherit the enclosing type. It is display-and-recheck
    -- information (§6.4) and only matters if the sub-problem is parked, where
    -- 'park' infers a better one; carrying the parent's is the fallback, and it
    -- is reached only for a term @check@ would already have rejected.
    sequential = foldl one (Right st)
      where
        one acc (a, b) = acc >>= \st' -> work env st' (Equate xi a b ty)

    -- One fresh binder, opened on both sides and added to Ξ. This is where the
    -- name counter is spent, and Miller's mixed prefix is exactly this list.
    binder i dom sc dom' sc' = do
      st1 <- work env st (Equate xi dom dom' ty)
      let (x, n1) = fresh (stNames st1)
          xi'     = xi ++ [Hypothesis x i dom]
      work env st1 { stNames = n1 } (Equate xi' (open x sc) (open x sc') ty)

-- --------------------------------------------------------------------------
-- Parking
-- --------------------------------------------------------------------------

-- | Defer the equation as a @Pending@ link in the chain, at the **minimal legal
-- position** — immediately below the last component it mentions.
--
-- **Decided by the user 2026-08-22**, closing @AGENDA.md@ item 16 q1. The
-- argument is retraction rather than generality: §6.4 says an undischarged
-- constraint may not be dropped, and a constraint parked deeper than it needs
-- to be can end up inside a guess whose @regret@ then discards it. Minimal-legal
-- puts it inside a guess exactly when it mentions something bound there, which
-- is when it should die with it.
--
-- The stored type is inferred from the left-hand side where that works, because
-- decomposition is untyped and a sub-problem's type is not the parent's.
park :: GlobalEnv -> St -> Constraint -> Attempt St
park env st k@(Equate xi s _ ty)
  | k' `elem` constraintsOf (rebuild (stCur st)) = Right st
  | otherwise = Right st { stCur = postConstraint position k' (stCur st), stNames = n1 }
  where
    -- Level obligations are dropped, as everywhere outside the checking pass;
    -- "Thena.Core.Typing"'s header says why once.
    (ty', n1) = case infer env (whole (stCur st) ++ xi) (stNames st) s of
      (Right inferred, _, n) -> (inferred, n)
      (Left _,         _, n) -> (ty, n)

    k' = Equate xi s (equateRight k) ty'

    equateRight (Equate _ _ r _) = r

    -- One past the last position the constraint mentions; 0 when it mentions
    -- nothing bound in the chain.
    position = case [ i | (i, x, _) <- chain (stCur st), x `elem` mentions k ] of
      [] -> 0
      is -> maximum is + 1

-- | The chain variables a constraint mentions — its terms and Ξ's own types,
-- less the variables Ξ binds.
mentions :: Constraint -> [Var]
mentions (Equate xi s t ty) =
  nub (concatMap ofEntry xi ++ freeVars s ++ freeVars t ++ freeVars ty)
    `without` map entryVar xi
  where
    ofEntry e = case e of
      Hypothesis _ _ a   -> freeVars a
      Definition _ _ v a -> freeVars v ++ freeVars a

    without vs ws = [ v | v <- vs, v `notElem` ws ]

-- --------------------------------------------------------------------------
-- Wake-up, to fixpoint
-- --------------------------------------------------------------------------

-- | §4.0 G1's root-down pass, run until nothing more moves: every parked
-- constraint is retried, and one that has become solvable stops being a link.
--
-- A retry removes the link first and then solves it, so a constraint that
-- decomposes is genuinely replaced by the problems it decomposes into (§6.4),
-- each parked at its own minimal legal position. Progress is measured as "a
-- hole was solved, or there is one fewer constraint"; a sweep that achieves
-- neither is the fixpoint.
--
-- The focused constraint is not retried. 'overConstraints' cannot delete it —
-- the focus would have nowhere to stand — and G1 is explicit that the pass
-- leaves the focus alone.
wake :: GlobalEnv -> St -> Attempt St
wake env = loop
  where
    loop st
      | null (pending st) = Right st
      | otherwise = do
          st' <- foldl retry (Right st) (pending st)
          if progressed st st' then loop st' else Right st'

    pending st =
      [ k | k <- constraintsOf (rebuild (stCur st)), not (isFocused st k) ]

    isFocused st k = case focus (stCur st) of
      OnConstraint j -> j == k
      _              -> False

    retry acc k = acc >>= \st ->
      let dropped = st { stCur = overConstraints (\j -> if j == k then Nothing else Just j) (stCur st) }
       in work env dropped k

    progressed a b =
      length (stSolved b) > length (stSolved a)
        || length (pending b) < length (pending a)
