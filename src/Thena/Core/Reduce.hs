-- | Reduction: the contraction schemes of §5.1, and @whnf@.
--
-- Below "Thena.Core.Convert" and "Thena.Core.Typing" in the layering (§2.5),
-- and **must not import "Thena.Global.Declare"** — that is the entire reason
-- @Global@ is split into @Env@ (data only) and @Declare@ (checking and
-- generation), so that δ can unfold a global and ι can read an inductive
-- definition without this module needing to know how either was checked.
module Thena.Core.Reduce
  ( whnf
  ) where

import Data.List (find)

import Thena.Core.Level (Level)
import Thena.Core.Context (Context, Entry (..), entryType, entryVar)
import Thena.Core.Term (Core (..), GlobalName, Var, close, instantiate)
import Thena.Global.Env
  ( ConstructorDefinition (..)
  , Definition (..)
  , GlobalEnv
  , InductiveDefinition (..)
  , formerArity
  , lookupDefinition
  , lookupInductive
  , recursiveArgument
  )

-- | Reduce to weak head normal form (§5.1): β, δ (all three forms), ν, and ι.
--
-- Never descends under a binder — a 'Pi' or 'Lam' is already whnf, whatever
-- its domain or body contain, and nothing here opens either 'Scope'.
-- Total: an ill-formed redex (@App@ of a saturated 'Canonical', an
-- 'Eliminate' whose target never settles) is left as the neutral term it
-- is, per §3.4 — whnf does not decide well-formedness, @check@ does.
--
-- **Two facts phase 8's conversion depends on, recorded here because they are
-- properties of this function and nowhere else:**
--
--   * A 'Let' is never returned at the head. Every 'Let' this function meets
--     is substituted away, so conversion needs no @Let@-head case.
--   * @'App' ('Global' g) …@ /is/ a legal whnf when @g@ is an under-applied
--     former wrapper — see 'formerArity' and the note on δ below. Conversion
--     must therefore be prepared to meet one, and its η rule (§5.2) is what
--     carries it: comparing @cons A@ against
--     @λ n a as -> ‹cons A n a as›@ opens the lambda and applies the spine
--     until it saturates, at which point δ fires on both sides and they meet
--     at the 'Canonical'. **That is a proof obligation for phase 8, not a
--     discharged fact.**
whnf :: GlobalEnv -> Context -> Core -> Core
whnf env ctx = go 0
  where
    -- @nargs@ is how many arguments are already waiting to be applied to the
    -- term in hand. Only δ on a former wrapper reads it; every other case
    -- passes it along unchanged (the term stays in the same application
    -- position) or resets it to 0 (a subterm in argument position).
    go nargs t = case t of
      Bound _        -> t          -- never the top of a term whnf is asked about
      Free x         -> case find ((== x) . entryVar) ctx of
        Just (Definition _ _ val _) -> go nargs val
        _                            -> t   -- a 'Hypothesis', or not in scope: neutral

      -- δ's third form, with ONE condition on it: a generated former wrapper
      -- does not unfold until it has all its arguments. DECIDED by the user
      -- 2026-08-22.
      --
      -- The reason is not legibility, though it buys that too (@cons A@ stays
      -- @cons A@ instead of becoming a three-binder lambda around a
      -- 'Canonical'). It is that unfolding an under-applied wrapper does no
      -- useful work: it exposes no ι-redex — an ι target is a value of the
      -- datatype and so is saturated by construction — and nothing else can
      -- consume the result either. §11's "a whnf that leaves work undone is
      -- an incorrect whnf" has a mirror image, and this is it.
      --
      -- Ordinary definitions — proved theorems, the prelude — are not formers,
      -- get 'Nothing' from 'formerArity', and unfold unconditionally as
      -- before.
      Global g _
        | Just k <- formerArity g env, nargs < k -> t
        | otherwise -> case lookupDefinition g env of
            Just d  -> go nargs (definitionBody d)
            Nothing -> t                    -- a constant with no body: neutral

      Universe _ -> t
      Pi {}      -> t
      Lam {}     -> t
      Canonical {} -> t

      App f a -> case go (nargs + 1) f of
        Lam i dom sc -> go nargs (Let i a dom sc)  -- β: produces a definition
        f'           -> App f' a

      -- δ on a term-level 'Let': the net effect of "δ, iterated, then ν" from
      -- table 2.1 is a substitution, and 'instantiate' is already exactly that
      -- operation — the same one 'open' uses. No fresh variable, no context
      -- extension: with the bound occurrences gone there is no leftover
      -- binding for ν to dispose of, so ν costs nothing extra to implement.
      Let _ val _ sc -> go nargs (instantiate val sc)

      -- The target stands in argument position, so it starts its own count.
      Eliminate d ls ps m ms is tgt ->
        let tgt' = go 0 tgt
         in case tgt' of
              Canonical cg _ cargs
                | Just result <- iota env d ls ps m ms cg cargs -> go nargs result
              _ -> Eliminate d ls ps m ms is tgt'

-- --------------------------------------------------------------------------
-- ι — computed from the inductive-definition record, not generated (§3.7)
-- --------------------------------------------------------------------------

-- | One ι-step: the method for the matched constructor, applied to its
-- arguments and then to one recursive call per recursive argument (thesis
-- §4.1.1, §4.1.4; @OLEG.md@).
--
-- Takes no indices: the general rule
-- @FamElim P m⃗ a⃗ᵢ (cᵢ x⃗ y⃗) ⟶ι mᵢ x⃗ y⃗ …@ does not mention the eliminate's own
-- @a⃗ᵢ@ on the right — matching indices against the target's is @check@'s job
-- (phase 8), not the reducer's.
--
-- 'Nothing' — meaning "no ι-redex here, leave the 'Eliminate' stuck" — when
-- @d@ or @cg@ do not name what they claim, when there is no method for the
-- matched constructor, or when the target 'Canonical' is **not saturated**.
--
-- The saturation check is the one that is not about typos. §12 invariant 6
-- makes "every 'Canonical' carries exactly its parameters and its own
-- arguments" an invariant, and nothing the user can type breaks it — the
-- resolver never builds a 'Canonical' (§3.6) and every generated wrapper is
-- saturated by construction (§3.7). But this function claims to be total on
-- arbitrary input, and without the check it does not merely fail to reduce:
-- it applies the method to whatever arguments happen to be there and returns
-- a **wrong reduct**. @Eliminate "Nat" [] P [mz,ms] [] (Canonical "succ" [])@
-- would give @ms@ — the successor method with neither its argument nor its
-- recursive call. Phase 9's unifier and phase 12's kernel both build 'Core'
-- programmatically, so "unreachable today" is not a reason to leave a wrong
-- answer reachable at all.
iota
  :: GlobalEnv -> GlobalName -> [Level] -> [Core] -> Core -> [Core]
  -> GlobalName -> [Core]
  -> Maybe Core
iota env d ls ps m ms cg cargs = do
  def          <- lookupInductive d env
  (idx, con)   <- findConstructor cg (inductiveConstructors def)
  method       <- atIndex idx ms
  let np      = length (inductiveParameters def)
      ownArgs = drop np cargs
  if length cargs /= np + length (constructorArguments con)
    then Nothing
    else Just (foldl App method (ownArgs ++ recursiveCalls def ls ps m ms con ownArgs))

-- | One recursive call per recursive argument, in argument order — the
-- general dependent-family ι-rule:
-- @FamElim P m⃗ a⃗ᵢ (cᵢ x⃗ y⃗) ⟶ι mᵢ x⃗ y⃗ (FamElim P m⃗ a⃗₁ y₁) … (FamElim P m⃗ a⃗ₙ yₙ)@
--
-- Which arguments are recursive, and each one's own indices @a⃗ⱼ@, are read
-- off 'constructorArguments'\' stored types — never a second table (§3.7).
--
-- **Which arguments are recursive is decided by 'recursiveArgument', shared
-- with the eliminator's type** (phase 8). It has to be shared: if ι and the
-- eliminator's typing rule disagreed about which arguments are recursive, a
-- datatype would reduce by a rule its own eliminator is not typed for. That
-- function also carries the standing caveat — the classification is complete
-- only while "Thena.Global.Declare" rejects higher-order recursion.
-- Those stored types are written against the *declaration's own* formal
-- variables — the parameter telescope's and the earlier arguments' — so the
-- substitution seeds itself with the parameters (formal var ↦ @ps@, the
-- actual ones this elimination supplies) and then grows one entry at a time
-- as the telescope is walked, using 'close' then 'instantiate' to replace one
-- 'Free' variable throughout a type — the same two primitives 'whnf' itself
-- uses, composed instead of a new one written for this.
recursiveCalls
  :: InductiveDefinition -> [Level] -> [Core] -> Core -> [Core]
  -> ConstructorDefinition -> [Core]
  -> [Core]
recursiveCalls def ls ps m ms con = go (constructorArguments con) seed
  where
    dn   = inductiveName def
    np   = length (inductiveParameters def)
    seed = zip (map entryVar (inductiveParameters def)) ps

    go []       _     []       = []
    go (e : es) subst (a : as) =
      let ty' = foldl (\ty (x, v) -> substFree x v ty) (entryType e) subst
          rest = go es ((entryVar e, a) : subst) as
       in case recursiveArgument dn np ty' of
            Just is -> Eliminate dn ls ps m ms is a : rest
            Nothing -> rest
    go _ _ _ = []   -- mismatched arities: not a saturated value of this constructor

-- | Substitute a free variable throughout a term. Not new machinery: 'close'
-- abstracts every occurrence of @x@ to a bound index, and 'instantiate'
-- immediately fills that index back in with @v@ — exactly what 'open' does
-- with @Free x@ in @v@'s place, generalised to an arbitrary replacement.
substFree :: Var -> Core -> Core -> Core
substFree x v t = instantiate v (close x t)

findConstructor :: GlobalName -> [ConstructorDefinition] -> Maybe (Int, ConstructorDefinition)
findConstructor cg = go 0
  where
    go _ []       = Nothing
    go i (c : cs)
      | constructorName c == cg = Just (i, c)
      | otherwise                = go (i + 1) cs

atIndex :: Int -> [a] -> Maybe a
atIndex i xs
  | i < 0     = Nothing
  | otherwise = case drop i xs of
      x : _ -> Just x
      []    -> Nothing
