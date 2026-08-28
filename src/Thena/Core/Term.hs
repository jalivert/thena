-- | The core language: its terms, the names that appear in them, and the
-- opaque 'Scope' that carries a binder's body.
--
-- This module spends two of the three places the project uses levelOfNat 1
-- enforcement (@PLAN.md@ §3.4, §2.5):
--
--   * 'Scope' — only 'close' builds one; only 'open' and 'instantiate' take one
--     apart. A dangling de Bruijn index is therefore unconstructible.
--   * 'Var' — only 'fresh' mints one, which makes §3.2's "globally unique"
--     structural rather than a convention followed by hand.
--
-- 'Scope' is declared here rather than in a module of its own because 'Core'
-- mentions it and 'close' must traverse 'Core': two modules would import each
-- other. Decided 2026-08-21; §2.5 and @AGENDA.md@ item 20a carry the argument.
module Thena.Core.Term
  ( -- * Names
    Var
  , fresh
  , Ident (..)
  , GlobalName (..)

    -- * Terms
  , Core (..)
  , Scope  -- NB: the type only. Hiding 'MkScope' is the point of the module.

    -- * Binding
  , close
  , open
  , instantiate
  , freeVars
  , globalsIn
  ) where

import Data.List (nub)

import Thena.Core.Level (Level)

-- | A reference to a binding, globally unique within a session.
--
-- The constructor is not exported: 'fresh' is the only way to make one, so
-- nothing can write @Var 3@ and collide with a live binding (§2.5).
newtype Var = Var Int
  deriving (Eq, Ord, Show)

-- | Mint a variable from the session's name counter and give the counter back.
--
-- The counter is an 'Int' held in the outer state and threaded by hand. There is
-- deliberately no supply type, no monad and no newtype around it (§3.5,
-- @PREPLAN.md@ standing rule 7).
fresh :: Int -> (Var, Int)
fresh n = (Var n, n + 1)

-- | What the user calls a binding. Display only, no semantic content (§3.2) —
-- which is exactly why 'Eq' on 'Core' ignores it.
--
-- 'Eq' here is real, and phase 2's resolver depends on that: it looks a written
-- name up in the context by comparing identifiers.
newtype Ident = Ident String
  deriving (Eq, Ord, Show)

-- | A name in the global environment (§3.6, decided 2026-08-11).
--
-- Flat. No namespace tag — the node position already says which kind of thing is
-- being named, so a tag would be data derivable from its own context and able to
-- disagree with it. One namespace, shared with generated names.
newtype GlobalName = GlobalName String
  deriving (Eq, Ord, Show)

-- | The body of a binder, with the bound variable replaced by a de Bruijn index.
--
-- The constructor is not exported. 'close' is the only way in and 'open' and
-- 'instantiate' are the only ways out, which is what makes a dangling index
-- unconstructible (§3.4).
newtype Scope a = MkScope a
  deriving (Eq, Show)

-- | The core language (§3.6). Settled and closed: no later phase adds a
-- constructor here.
data Core
  = Bound Int                          -- ^ a binder inside this term
  | Free Var                           -- ^ a component in the context
  | Global GlobalName [Level]          -- ^ a definition, at level arguments
  | Universe Level
  | Pi Ident Core (Scope Core)         -- ^ @Π x : S . B@
  | Lam Ident Core (Scope Core)        -- ^ @λ x : S . b@
  | App Core Core
  | Let Ident Core Core (Scope Core)   -- ^ @x = s : S . t@
  | Canonical GlobalName [Level] [Core] -- ^ saturated former, at level arguments
  | Eliminate                          -- ^ saturated use of an eliminator
      { eliminated :: GlobalName
      , levels     :: [Level]
      , parameters :: [Core]
      , motive     :: Core
      , methods    :: [Core]
      , indices    :: [Core]
      , target     :: Core
      }
  deriving (Show)

-- | Alpha-equivalence (§3.5).
--
-- Written out rather than derived because 'Pi', 'Lam' and 'Let' carry an
-- 'Ident', and a derived instance would compare display names — making
-- @λ x:A. x@ and @λ y:A. y@ unequal. Every other field is compared
-- structurally, with no renaming and no environment: that is what the de Bruijn
-- scopes buy, and it holds only because 'Canonical' is saturated, so a former
-- application has exactly one spelling (§12 invariant 6).
--
-- The final catch-all makes a missing case compare 'False' rather than warn.
-- That is tolerable only because 'Core' is closed (§3.6) — if a constructor is
-- ever added, this instance is the first place to look.
instance Eq Core where
  Bound i        == Bound j          = i == j
  Free x         == Free y           = x == y
  Global f ks    == Global g ls      = f == g && ks == ls
  Universe k     == Universe l       = k == l
  Pi _ s b       == Pi _ s' b'       = s == s' && b == b'
  Lam _ s b      == Lam _ s' b'      = s == s' && b == b'
  App f a        == App g c          = f == g && a == c
  Let _ v s b    == Let _ v' s' b'   = v == v' && s == s' && b == b'
  Canonical f _ as == Canonical g _ bs   = f == g && as == bs
  Eliminate d _ ps m ms is t == Eliminate d' _ ps' m' ms' is' t' =
    d == d' && ps == ps' && m == m' && ms == ms' && is == is' && t == t'
  _ == _ = False

-- | Abstract a free variable: every @'Free' x@ becomes the index of the binder
-- being built. The @abstract@ of §3.4.
close :: Var -> Core -> Scope Core
close x = MkScope . go 0
  where
    go :: Int -> Core -> Core
    go d t = case t of
      Bound i        -> Bound i
      Free y         -> if y == x then Bound d else Free y
      Global g ls    -> Global g ls
      Universe k     -> Universe k
      Pi i s b       -> Pi i (go d s) (under d b)
      Lam i s b      -> Lam i (go d s) (under d b)
      App f a        -> App (go d f) (go d a)
      Let i v s b    -> Let i (go d v) (go d s) (under d b)
      Canonical f ls as -> Canonical f ls (map (go d) as)
      Eliminate dn ls ps m ms is tgt ->
        Eliminate dn ls (map (go d) ps) (go d m) (map (go d) ms)
                  (map (go d) is) (go d tgt)

    under :: Int -> Scope Core -> Scope Core
    under d (MkScope b) = MkScope (go (d + 1) b)

-- | Replace the variable a 'Scope' binds with a term. The @instantiate@ of §3.4.
--
-- **No shifting.** Everything free is a 'Free' and never a 'Bound', so nothing
-- in the substituted term can be captured and nothing needs renumbering. This is
-- the bug class §11 says locally nameless removes, and it is removed by there
-- being no function here to get wrong.
--
-- An index greater than the current depth would be dangling, and cannot occur:
-- a 'Scope' is only ever built by 'close', which abstracts one variable.
instantiate :: Core -> Scope Core -> Core
instantiate v (MkScope body) = go 0 body
  where
    go :: Int -> Core -> Core
    go d t = case t of
      Bound i        -> if i == d then v else Bound i
      Free y         -> Free y
      Global g ls    -> Global g ls
      Universe k     -> Universe k
      Pi i s b       -> Pi i (go d s) (under d b)
      Lam i s b      -> Lam i (go d s) (under d b)
      App f a        -> App (go d f) (go d a)
      Let i w s b    -> Let i (go d w) (go d s) (under d b)
      Canonical f ls as -> Canonical f ls (map (go d) as)
      Eliminate dn ls ps m ms is tgt ->
        Eliminate dn ls (map (go d) ps) (go d m) (map (go d) ms)
                  (map (go d) is) (go d tgt)

    under :: Int -> Scope Core -> Scope Core
    under d (MkScope b) = MkScope (go (d + 1) b)

-- | Open a 'Scope' with a variable. The move the cursor makes descending under a
-- binder (§3.5, §4.6), and what conversion does to compare two binders' bodies
-- (§5.2).
open :: Var -> Scope Core -> Core
open x = instantiate (Free x)

-- | The free variables of a term, in order of first occurrence, without repeats.
--
-- Here because it is what makes the 'close'/'open' round-trip test mean
-- anything: a 'close' and an 'open' that both did nothing would satisfy the
-- round trip by themselves. §3.4's scope check for @fill@ wants this too, from
-- phase 4.
freeVars :: Core -> [Var]
freeVars = nub . go
  where
    go :: Core -> [Var]
    go t = case t of
      Bound _                     -> []
      Free y                      -> [y]
      Global _ _                  -> []
      Universe _                  -> []
      Pi _ s (MkScope b)          -> go s ++ go b
      Lam _ s (MkScope b)         -> go s ++ go b
      App f a                     -> go f ++ go a
      Let _ v s (MkScope b)       -> go v ++ go s ++ go b
      Canonical _ _ as              -> concatMap go as
      Eliminate _ _ ps m ms is tgt  ->
        concatMap go ps ++ go m ++ concatMap go ms ++ concatMap go is ++ go tgt

-- | The global names a term mentions, in order of first occurrence, without
-- repeats.
--
-- Here for the same reason 'freeVars' is: it must see inside a 'Scope', and
-- 'MkScope' is not exported. Phase 6's strict-positivity check is what wants
-- it — "does the datatype being declared occur in this constructor argument's
-- domain?" is exactly this question, and asking it by opening every binder
-- would mint display variables for no reason (§3.7).
globalsIn :: Core -> [GlobalName]
globalsIn = nub . go
  where
    go :: Core -> [GlobalName]
    go t = case t of
      Bound _                     -> []
      Free _                      -> []
      Global g _                  -> [g]
      Universe _                  -> []
      Pi _ s (MkScope b)          -> go s ++ go b
      Lam _ s (MkScope b)         -> go s ++ go b
      App f a                     -> go f ++ go a
      Let _ v s (MkScope b)       -> go v ++ go s ++ go b
      Canonical g _ as              -> g : concatMap go as
      Eliminate d _ ps m ms is tgt  ->
        d : (concatMap go ps ++ go m ++ concatMap go ms ++ concatMap go is ++ go tgt)
