-- | Reduction: the contraction schemes of Â§5.1, and @whnf@.
--
-- Below "Thena.Core.Convert" and "Thena.Core.Typing" in the layering (Â§2.5),
-- and **must not import "Thena.Global.Declare"** â that is the entire reason
-- @Global@ is split into @Env@ (data only) and @Declare@ (checking and
-- generation), so that Î´ can unfold a global and Î¹ can read an inductive
-- definition without this module needing to know how either was checked.
-- **It does import "Thena.Core.Convert", through its @.hs-boot@, and that is
-- the one place the layering bends** (MS8 phase 149). The trusted contraction's
-- side condition is full convertibility â his ruling of 2026-10-05, and not a
-- syntactic approximation â so the lower module has to ask the higher one one
-- question. See @Convert.hs-boot@ for why that is a fact about the module
-- layout and not about the design.
module Thena.Core.Reduce
  ( whnf
  , PrimitiveRule (..)
  , primitiveNames
    -- * δ’s level substitution, shared with "Thena.Core.Trust"
  , atLevels
  ) where

import Data.List (find)

import {-# SOURCE #-} Thena.Core.Convert (convert)
import Thena.Core.Level (Level (..), LevelVar, instantiateLevels)
import Thena.Core.Context (Context, Entry (..), entryType, entryVar)
import Thena.Core.Term
  ( Core (..)
  , GlobalName (..)
  , Literal (..)
  , Var
  , beyond
  , close
  , freeVars
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

-- | Reduce to weak head normal form (Â§5.1): Î², Î´ (all three forms), Î½, Î¹, the
-- primitives' rule, and the trusted contraction.
--
-- Never descends under a binder â a 'Pi' or 'Lam' is already whnf, whatever
-- its domain or body contain, and nothing here opens either 'Scope'.
-- Total: an ill-formed redex (@App@ of a saturated 'Canonical', an
-- 'Eliminate' whose target never settles) is left as the neutral term it
-- is, per Â§3.4 â whnf does not decide well-formedness, @check@ does.
--
-- **Two facts phase 8's conversion depends on, recorded here because they are
-- properties of this function and nowhere else:**
--
--   * A 'Let' is never returned at the head. Every 'Let' this function meets
--     is substituted away, so conversion needs no @Let@-head case.
--   * @'App' ('Global' g) â¦@ /is/ a legal whnf when @g@ is an under-applied
--     former wrapper â see 'formerArity' and the note on Î´ below. Conversion
--     must therefore be prepared to meet one, and its Î· rule (Â§5.2) is what
--     carries it: comparing @cons A@ against
--     @Î» n a as -> â¹cons A n a asâº@ opens the lambda and applies the spine
--     until it saturates, at which point Î´ fires on both sides and they meet
--     at the 'Canonical'. **That is a proof obligation for phase 8, not a
--     discharged fact.**
whnf :: GlobalEnv -> Context -> Core -> Core
whnf env ctx = go 0
  where
    -- @nargs@ is how many arguments are already waiting to be applied to the
    -- term in hand. Only Î´ on a former wrapper reads it; every other case
    -- passes it along unchanged (the term stays in the same application
    -- position) or resets it to 0 (a subterm in argument position).
    go nargs t = case t of
      Bound _        -> t          -- never the top of a term whnf is asked about
      Primitive _    -> t          -- a literal is already a value (MS6 phase 97a)
      Free x         -> case find ((== x) . entryVar) ctx of
        Just (Definition _ _ val _) -> go nargs val
        _                            -> t   -- a 'Hypothesis', or not in scope: neutral

      -- Î´'s third form, with ONE condition on it: a generated former wrapper
      -- does not unfold until it has all its arguments. DECIDED by the user
      -- 2026-08-22.
      --
      -- The reason is not legibility, though it buys that too (@cons A@ stays
      -- @cons A@ instead of becoming a three-binder lambda around a
      -- 'Canonical'). It is that unfolding an under-applied wrapper does no
      -- useful work: it exposes no Î¹-redex â an Î¹ target is a value of the
      -- datatype and so is saturated by construction â and nothing else can
      -- consume the result either. Â§11's "a whnf that leaves work undone is
      -- an incorrect whnf" has a mirror image, and this is it.
      --
      -- Ordinary definitions â proved theorems, the prelude â are not formers,
      -- get 'Nothing' from 'formerArity', and unfold unconditionally as
      -- before.
      -- **Î´ substitutes the level arguments into the body** (MS3 phase 31d).
      -- A polymorphic definition's body is written over its own level
      -- parameters, so unfolding @Eq {0}@ without substituting hands back a
      -- body that still mentions @â@ â and every later comparison then sees a
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
        Lam i dom sc -> go nargs (Let i a dom sc)  -- Î²: produces a definition
        -- **The primitives' rule** (MS6 phase 97b): a known primitive applied
        -- to two literals computes, and to anything else stays neutral. It sits
        -- here rather than in the 'Global' case because it fires on the
        -- /saturated/ application, exactly as Î¹ does on a saturated target.
        f'
          | Just u <- primitiveStep env (whnf env ctx) f' a -> go nargs u
          | otherwise                        -> App f' a

      -- Î´ on a term-level 'Let': the net effect of "Î´, iterated, then Î½" from
      -- table 2.1 is a substitution, and 'instantiate' is already exactly that
      -- operation â the same one 'open' uses. No fresh variable, no context
      -- extension: with the bound occurrences gone there is no leftover
      -- binding for Î½ to dispose of, so Î½ costs nothing extra to implement.
      Let _ val _ sc -> go nargs (instantiate val sc)

      -- The target stands in argument position, so it starts its own count.
      Eliminate d ls ps m ms is tgt ->
        let tgt' = go 0 tgt
         in case tgt' of
              Canonical cg _ cargs
                | Just result <- iota env d ls ps m ms cg cargs -> go nargs result
              _ -> Eliminate d ls ps m ms is tgt'

      -- **The trusted contraction** (MS8 phase 149): the claim is discharged
      -- and the node disappears when the type it claims and the type its body
      -- was checked at are convertible. Otherwise it stands as a value â the
      -- node is where the unproved obligation is written down, so leaving it
      -- there is the honest answer and not a failure to reduce.
      --
      -- **Trust is conditional â HIS, 2026-10-04**, and this is the whole of
      -- the condition. The unconditional form, which unwraps whatever the two
      -- types are, is not to be built: no mainstream system ships a typing
      -- trust that reduces unconditionally, and the one reducing form anybody
      -- does ship (Agda's @primTrustMe@) is conditional in exactly this way.
      --
      -- The node stays in the same application position, so @nargs@ passes
      -- through â @trusted (A -> B) (A -> B') f x@ is an application of
      -- whatever @f@ reduces to.
      Trusted claimed actual body
        | unwraps claimed actual -> go nargs body
        | otherwise              -> t

    -- | Is the claim discharged? **Full convertibility, decided by calling
    -- 'convert' â HIS ruling, 2026-10-05**, and not a syntactic approximation
    -- of it. Î±-equality is a fast path and nothing more, exactly as 'convert'
    -- has one of its own.
    --
    -- **IT FIRES ONLY WHEN THE OBLIGATION LIST COMES BACK EMPTY, AND THE
    -- REASON IS THE MISSING COLLECTOR.** 'convert' answers with a verdict,
    -- level obligations and a counter; 'whnf' answers with a bare 'Core', so
    -- it has nowhere to put an obligation. Every other obligation in the
    -- system is produced where there is a collector â 'convert' is called from
    -- "Thena.Core.Typing", which accumulates â and that is why the standing
    -- practice of dropping them during a proof is safe: the pass that
    -- re-checks the finished development is at a site with a pocket, so it
    -- re-derives them. **This is the one site with no pocket**, so an
    -- obligation arising here would be dropped by /every/ pass including the
    -- re-check, leaving 'Thena.Kernel.certify''s level scheme short a
    -- constraint its use sites should have owed. Declining to act on it costs
    -- nothing: the node stays, the elimination above it stays stuck, and a
    -- stuck well-typed term is a valid proof. See @HAZARDS.md@.
    --
    -- **The cost is close to zero** because an obligation arises only when a
    -- level /meta/ is in the comparison, and a written type has concrete
    -- levels. Lifting the restriction means threading obligations out of
    -- reduction, so that this site has a pocket of its own â which is a change
    -- to 'whnf''s signature and to every caller of it, and not this phase's.
    --
    -- **The counter is seeded with 'beyond' rather than threaded.** 'convert'
    -- mints variables to open binders with, and 'whnf' has no counter to give
    -- it; a variable minted below one already in play would make two distinct
    -- binders compare equal. Seeding above everything the comparison can see â
    -- the context and the two types â is what 'beyond' exists for, and it is
    -- sound here for a reason that does not generalise: **nothing minted
    -- escapes.** The verdict is a 'Bool' and the reduct is @body@, which this
    -- comparison never touches, so no variable it invented can reach a term or
    -- a message.
    unwraps claimed actual
      | claimed == actual = True
      | otherwise = case convert env ctx seed claimed actual of
          (Nothing, [], _) -> True
          _                -> False
      where
        seed = beyond (map entryVar ctx ++ freeVars claimed ++ freeVars actual)

-- --------------------------------------------------------------------------
-- The primitives' rule (MS6 phase 97b)
-- --------------------------------------------------------------------------

-- | The primitive functions the system computes with, and the rule each
-- computes by.
--
-- **This list is the whole of what @primitive@ may declare.** A name absent
-- from it has no rule, so the driver refuses the declaration rather than
-- installing a constant that would sit there as an axiom
-- (@ms6\/SPEC.md@ Â§2.1).
primitiveNames :: [(GlobalName, PrimitiveRule)]
primitiveNames =
  [ (GlobalName ("eq" ++ p), Comparing (GlobalName p)) | p <- ["String", "Char", "Int"] ]
  ++ [ (GlobalName "appendString", Appending) ]

-- | What a primitive computes, and so what type the driver will accept it at
-- ('Thena.Driver.checkedPrimitive').
data PrimitiveRule
  = Comparing GlobalName
    -- ^ @P -> P -> B@ for this @P@: the first constructor of @B@ for literals
    -- that agree, the second for literals that differ (MS6 phase 97b)
  | Appending
    -- ^ @String -> String -> String@: the two literals, one after the other
    -- (MS6 phase 105). **The one way a @String@ is built**, and generated
    -- substitution needs it: a fresh name is a name primed until it is not
    -- among the ones it must avoid (Â§4.7)
  deriving (Eq, Show)

-- | A primitive applied to two literals, computed; anything else is neutral.
--
-- For 'Comparing': @eqP a b@ where both arguments are literals of @P@ is the
-- first constructor of the result datatype when they agree, the second when
-- they do not.
--
-- **The two constructors come from the declared type, not from a name written
-- here.** The constant's type is @P -> P -> B@, and @B@\'s own declaration
-- says what its constructors are called â so the rule never mentions @true@ or
-- @Bool@, and a user who declares the result to be their own two-constructor
-- datatype gets the same rule. The driver has already checked that shape
-- ('Thena.Driver.checkedPrimitive'), which is why this can read it back
-- without a second opinion.
--
-- **Both arguments are reduced before they are read** â @reduce@ is 'whnf' in
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
        (Appending, LString a, LString b) -> Just (Primitive (LString (a ++ b)))
        _ -> Nothing
  _ -> Nothing

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
-- Î¹ â computed from the inductive-definition record, not generated (Â§3.7)
-- --------------------------------------------------------------------------

-- | One Î¹-step: the method for the matched constructor, applied to its
-- arguments and then to one recursive call per recursive argument (thesis
-- Â§4.1.1, Â§4.1.4; @OLEG.md@).
--
-- Takes no indices: the general rule
-- @FamElim P mâ aâáµ¢ (cáµ¢ xâ yâ) â¶Î¹ máµ¢ xâ yâ â¦@ does not mention the eliminate's own
-- @aâáµ¢@ on the right â matching indices against the target's is @check@'s job
-- (phase 8), not the reducer's.
--
-- 'Nothing' â meaning "no Î¹-redex here, leave the 'Eliminate' stuck" â when
-- @d@ or @cg@ do not name what they claim, when there is no method for the
-- matched constructor, or when the target 'Canonical' is **not saturated**.
--
-- The saturation check is the one that is not about typos. Â§12 invariant 6
-- makes "every 'Canonical' carries exactly its parameters and its own
-- arguments" an invariant, and nothing the user can type breaks it â the
-- resolver never builds a 'Canonical' (Â§3.6) and every generated wrapper is
-- saturated by construction (Â§3.7). But this function claims to be total on
-- arbitrary input, and without the check it does not merely fail to reduce:
-- it applies the method to whatever arguments happen to be there and returns
-- a **wrong reduct**. @Eliminate "Nat" [] P [mz,ms] [] (Canonical "succ" [])@
-- would give @ms@ â the successor method with neither its argument nor its
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

-- | One recursive call per recursive argument, in argument order â the
-- general dependent-family Î¹-rule:
-- @FamElim P mâ aâáµ¢ (cáµ¢ xâ yâ) â¶Î¹ máµ¢ xâ yâ (FamElim P mâ aââ yâ) â¦ (FamElim P mâ aââ yâ)@
--
-- Which arguments are recursive, and each one's own indices @aââ±¼@, are read
-- off 'constructorArguments'\' stored types â never a second table (Â§3.7).
--
-- **Which arguments are recursive is decided by 'recursiveArgument', shared
-- with the eliminator's type** (phase 8). It has to be shared: if Î¹ and the
-- eliminator's typing rule disagreed about which arguments are recursive, a
-- datatype would reduce by a rule its own eliminator is not typed for. That
-- function also carries the standing caveat â the classification is complete
-- only while "Thena.Global.Declare" rejects higher-order recursion.
-- Those stored types are written against the *declaration's own* formal
-- variables â the parameter telescope's and the earlier arguments' â so the
-- substitution seeds itself with the parameters (formal var â¦ @ps@, the
-- actual ones this elimination supplies) and then grows one entry at a time
-- as the telescope is walked, using 'close' then 'instantiate' to replace one
-- 'Free' variable throughout a type â the same two primitives 'whnf' itself
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
-- immediately fills that index back in with @v@ â exactly what 'open' does
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
-- alone rather than inventing a substitution â the checker is what reports the
-- arity, and Î´ is not the place to duplicate that judgement.
atLevels :: [LevelVar] -> [Level] -> Core -> Core
atLevels ps as body = case instantiateLevels ps as of
  Just sub -> substLevelsIn sub body
  Nothing  -> body
