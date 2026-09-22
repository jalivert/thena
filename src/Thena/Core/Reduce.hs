-- | Reduction: the contraction schemes of §5.1, and @whnf@.
--
-- Below "Thena.Core.Convert" and "Thena.Core.Typing" in the layering (§2.5),
-- and **must not import "Thena.Global.Declare"** — that is the entire reason
-- @Global@ is split into @Env@ (data only) and @Declare@ (checking and
-- generation), so that δ can unfold a global and ι can read an inductive
-- definition without this module needing to know how either was checked.
module Thena.Core.Reduce
  ( whnf
  , PrimitiveRule (..)
  , primitiveNames
  ) where

import Data.List (find)

import Thena.Core.Level (Level (..), LevelVar, instantiateLevels)
import Thena.Core.Context (Context, Entry (..), entryType, entryVar)
import Thena.Core.Term
  ( Core (..)
  , GlobalName (..)
  , Literal (..)
  , Var
  , Ident (..)
  , close
  , fresh
  , instantiate
  , primitiveType
  , substLevelsIn
  )
import Thena.Global.Env
  ( ConstructorDefinition (..)
  , Definition (..)
  , GlobalEnv
  , InductiveDefinition (..)
  , Constant (..)
  , formerArity
  , lookupConstant
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
      Primitive _    -> t          -- a literal is already a value (MS6 phase 97a)
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
      -- **δ substitutes the level arguments into the body** (MS3 phase 31d).
      -- A polymorphic definition's body is written over its own level
      -- parameters, so unfolding @Eq {0}@ without substituting hands back a
      -- body that still mentions @ℓ@ — and every later comparison then sees a
      -- rigid parameter where a concrete level belongs.
      Global g ls
        | Just k <- formerArity g env, nargs < k -> t
        | otherwise -> case lookupDefinition g env of
            Just d  -> go nargs (atLevels (definitionLevels d) ls (definitionBody d))
            Nothing -> t                    -- a constant with no body: neutral

      Universe _ -> t
      Pi {}      -> t
      Lam {}     -> t
      Canonical {} -> t

      App f a -> case go (nargs + 1) f of
        Lam i dom sc -> go nargs (Let i a dom sc)  -- β: produces a definition
        -- **The primitives' rule** (MS6 phase 97b): a known primitive applied
        -- to two literals computes, and to anything else stays neutral. It sits
        -- here rather than in the 'Global' case because it fires on the
        -- /saturated/ application, exactly as ι does on a saturated target.
        f'
          | Just u <- primitiveStep env (whnf env ctx) f' a -> go nargs u
          | otherwise                        -> App f' a

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
-- The primitives' rule (MS6 phase 97b)
-- --------------------------------------------------------------------------

-- | The primitive functions the system computes with, and the rule each
-- computes by.
--
-- **This list is the whole of what @primitive@ may declare.** A name absent
-- from it has no rule, so the driver refuses the declaration rather than
-- installing a constant that would sit there as an axiom
-- (@ms6\/SPEC.md@ §2.1).
primitiveNames :: [(GlobalName, PrimitiveRule)]
primitiveNames =
  [ (GlobalName ("eq" ++ p), Comparing (GlobalName p)) | p <- ["String", "Char", "Int"] ]
  ++ [ (GlobalName ("dec" ++ p), Deciding (GlobalName p)) | p <- ["String", "Char", "Int"] ]
  ++ [ (GlobalName "appendString", Appending) ]

-- | What a primitive computes, and so what type the driver will accept it at
-- ('Thena.Driver.checkedPrimitive').
data PrimitiveRule
  = Comparing GlobalName
    -- ^ @P -> P -> B@ for this @P@: the first constructor of @B@ for literals
    -- that agree, the second for literals that differ (MS6 phase 97b)
  | Deciding GlobalName
    -- ^ @(a b : P) -> D (Eq P a b)@ for this @P@, with @D@ a datatype of one
    -- parameter and two constructors — @yes : A -> D A@ and
    -- @no : (A -> E) -> D A@. Two literals answer with **the evidence**, not
    -- only the verdict (MS6 phase 109a, his choice on @ms6\/CLOSEOUT.md@ 32):
    -- a proof that eliminates the same @decP y x@ on names it does not know
    -- gets @Eq P y x@ in one branch and its refutation in the other, which
    -- @Comparing@ cannot give
  | Appending
    -- ^ @String -> String -> String@: the two literals, one after the other
    -- (MS6 phase 105). **The one way a @String@ is built**, and generated
    -- substitution needs it: a fresh name is a name primed until it is not
    -- among the ones it must avoid (§4.7)
  deriving (Eq, Show)

-- | A primitive applied to two literals, computed; anything else is neutral.
--
-- For 'Comparing': @eqP a b@ where both arguments are literals of @P@ is the
-- first constructor of the result datatype when they agree, the second when
-- they do not.
--
-- **The two constructors come from the declared type, not from a name written
-- here.** The constant's type is @P -> P -> B@, and @B@\'s own declaration
-- says what its constructors are called — so the rule never mentions @true@ or
-- @Bool@, and a user who declares the result to be their own two-constructor
-- datatype gets the same rule. The driver has already checked that shape
-- ('Thena.Driver.checkedPrimitive'), which is why this can read it back
-- without a second opinion.
--
-- **Both arguments are reduced before they are read** — @reduce@ is 'whnf' in
-- the caller's context. Matching them as they stood left @eqString a "x"@
-- stuck when @a@ is a definition of @"x"@, which is reduction incomplete on a
-- closed term (found in phase 100, @ms6\/CLOSEOUT.md@ 7). They are reduced
-- only once the head is known to be a primitive, so no other application pays.
primitiveStep :: GlobalEnv -> (Core -> Core) -> Core -> Core -> Maybe Core
primitiveStep env reduce f arg = case f of
  App (Global g []) x
    | Just rule <- lookup g primitiveNames
    , Primitive l <- reduce x
    , Primitive r <- reduce arg -> case (rule, l, r) of
        (Comparing p, _, _)
          | primitiveType l == Global p []
          , primitiveType r == Global p []
          , Just result <- resultDatatype env g
          , (c : d : _) <- map constructorName (inductiveConstructors result) ->
              Just (Canonical (if l == r then c else d) [] [])
        (Deciding p, _, _)
          | primitiveType l == Global p []
          , primitiveType r == Global p [] -> decided env g (Primitive l) (Primitive r) (l == r)
        (Appending, LString a, LString b) -> Just (Primitive (LString (a ++ b)))
        _ -> Nothing
  _ -> Nothing

-- | What @decP a b@ is for two literals: @yes (refl P a)@ when they agree,
-- and when they differ @no@ with a refutation of @Eq P a b@.
--
-- **Every name comes from the declared type**, as 'Comparing'\'s constructors
-- do: @D@, @Eq@, their constructors, their levels and the @E@ of @no@'s
-- argument. The driver has checked the shape ('Thena.Driver.checkedPrimitive').
--
-- **The refutation is an honest closed term, and it uses @decP@ itself.** With
-- @T t@ the type @Eq P a a@ when @decP a t@ is @yes@ and @E@ when it is @no@,
--
-- > λ q. elim Eq P (λ u v r. T u -> T v) (λ c z. z) a b q (refl P a)
--
-- carries @refl P a : T a@ along @q : Eq P a b@ to @T b@, which is @E@
-- because @a@ and @b@ are literals that differ. So nothing here is trusted but
-- the verdict on two literals — the same thing 'Comparing' trusts.
decided :: GlobalEnv -> GlobalName -> Core -> Core -> Bool -> Maybe Core
decided env g a b agree = do
  c <- lookupConstant g env
  (dN, l1, eqN, l2, pty) <- case instantiateBoth (constantType c) of
    Just (App (Global dN l1) eqAB)
      | App (App (App (Global eqN l2) pty) _) _ <- eqAB -> Just (dN, l1, eqN, l2, pty)
    _ -> Nothing
  dDef <- lookupInductive dN env
  [yesC, noC] <- Just (inductiveConstructors dDef)
  eDef <- lookupInductive eqN env
  [reflC] <- Just (inductiveConstructors eDef)
  [noArg] <- Just (constructorArguments noC)
  e <- case entryType noArg of
    -- Written against @D@'s own level parameters, so instantiated at this use's.
    Pi _ _ sc -> Just (atLevels (inductiveLevels dDef) l1 (instantiate (Universe LZero) sc))
    _ -> Nothing
  let eqOf x y = App (App (App (Global eqN l2) pty) x) y
      reflOf x = Canonical (constructorName reflC) l2 [pty, x]
      -- The universe @Eq P a a@ lives in, at this use's levels.
      eqSort = atLevels (inductiveLevels eDef) l2 (Universe (inductiveLevel eDef))
      decOf x y = App (App (Global g []) x) y
      -- Variables only ever closed over again before this returns, so any
      -- distinct numbers do.
      var k = fst (fresh k)
      (u, v, r, q, cv, z, w, pv, nv) = (var 0, var 1, var 2, var 3, var 4, var 5, var 6, var 7, var 8)
      -- T t: what knowing @decP a t@ tells you.
      told t = Eliminate dN l1 [eqOf a t]
        (Lam (Ident "w") (App (Global dN l1) (eqOf a t)) (close w eqSort))
        [ Lam (Ident "p") (eqOf a t) (close pv (eqOf a a))
        , Lam (Ident "n") (arrowTo (eqOf a t) e) (close nv e) ]
        [] (decOf a t)
      motive =
        Lam (Ident "u") pty $ close u $
        Lam (Ident "v") pty $ close v $
        Lam (Ident "r") (eqOf (Free u) (Free v)) $ close r $
        Pi (Ident "_") (told (Free u)) (close r (told (Free v)))
      method = Lam (Ident "c") pty $ close cv $ Lam (Ident "z") (told (Free cv)) $ close z (Free z)
      refutation =
        Lam (Ident "q") (eqOf a b) $ close q $
          App (Eliminate eqN l2 [pty] motive [method] [a, b] (Free q)) (reflOf a)
  Just $ if agree
    then Canonical (constructorName yesC) l1 [eqOf a b, reflOf a]
    else Canonical (constructorName noC) l1 [eqOf a b, refutation]
  where
    instantiateBoth ty = case ty of
      Pi _ _ sa -> case instantiate a sa of
        Pi _ _ sb -> Just (instantiate b sb)
        _ -> Nothing
      _ -> Nothing
    arrowTo dom cod = Pi (Ident "_") dom (close (fst (fresh (-1))) cod)

-- | The datatype a declared primitive answers with, read off its own type.
resultDatatype :: GlobalEnv -> GlobalName -> Maybe InductiveDefinition
resultDatatype env g = do
  c <- lookupConstant g env
  b <- resultOf (constantType c)
  lookupInductive b env
  where
    resultOf ty = case ty of
      Pi _ _ sc   -> resultOf (instantiate (Universe LZero) sc)
      Global b [] -> Just b
      _           -> Nothing

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

-- | Instantiate a definition's level parameters in its body.
--
-- A mismatched count cannot arise from a checked term, and this leaves the body
-- alone rather than inventing a substitution — the checker is what reports the
-- arity, and δ is not the place to duplicate that judgement.
atLevels :: [LevelVar] -> [Level] -> Core -> Core
atLevels ps as body = case instantiateLevels ps as of
  Just sub -> substLevelsIn sub body
  Nothing  -> body
