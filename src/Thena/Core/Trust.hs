-- | Trust accounting: what a term rests on that nothing derived (MS8 phase
-- 151).
--
-- A 'Thena.Core.Term.Trusted' node asserts a type instead of deriving one, so a
-- development's verification is modulo the claims it rests on. **Making them
-- visible is the answer, not making them safe** — @spec/representation.md@ §3.6
-- — and this module is what makes them visible: every claim a term rests on,
-- classified 'Discharged', 'Pending' or 'Undischargeable', with the site each
-- verdict came from.
--
-- **It is not the kernel and it is not in it — his ruling, 2026-10-06.**
-- 'Thena.Kernel.certify' answers whether a term has a type; whether the trust
-- in it is acceptable is policy, and policy belongs to the caller. @qed@ asks
-- two questions in sequence rather than one question that grew, which is the
-- same separation that kept the level out of 'Thena.Core.Typing.infer'.
--
-- **And it is a walk over the dependency graph, not a normaliser — his, and
-- get this right or the module grows a reduction it does not need.** The
-- temptation is to reduce the term and look at which trusted nodes appear in
-- the result, which is full normalisation: refused outright
-- (@spec/semantics.md@ §5.1 keeps it as a display operation only) and able to
-- diverge, which must never sit in @qed@'s path. What is here instead is
-- bounded and uses nothing new — 'Thena.Core.Term.instantiate' for the
-- arguments, 'Thena.Core.Reduce.whnf' and 'Thena.Core.Convert.convert' for the
-- verdict, and a traversal the shape of 'Thena.Core.Term.globalsIn'.
--
-- Above "Thena.Core.Convert" in the layering, and nothing below it imports
-- this: reduction and type checking are unchanged by this phase.
module Thena.Core.Trust
  ( -- * How much trust a session permits
    TrustLevel (..)
  , permits
  , unmet

    -- * What a claim is, and what became of it
  , TrustClass (..)
  , TrustSite (..)
  , TrustClaim (..)

    -- * Asking
  , classify
  , trustIn
  ) where

import Data.List (nub)

import Thena.Core.Context (Context, Entry (..), entryVar)
import Thena.Core.Convert (convert)
import Thena.Core.Reduce (atLevels, whnf)
import Thena.Core.Term
  ( Core (..)
  , GlobalName
  , Literal
  , beyond
  , freeVars
  , fresh
  , globalsIn
  , holdsTrusted
  , instantiate
  , open
  )
import Thena.Global.Env (Definition (..), GlobalEnv, lookupDefinition)

-- ---------------------------------------------------------------------------
-- The level
-- ---------------------------------------------------------------------------

-- | How much trust a session permits — **the user chooses, the kernel does not
-- refuse. HIS RULING, 2026-10-06**, and it is the second principle again:
-- /"don't prevent them from doing their thing, make it easy to do the right
-- thing."/ A blanket refusal was considered in that conversation and dropped,
-- because a classification plus a user-set policy is strictly more informative
-- than a no.
--
-- The expected working pattern is to sit at 'NoUndischargeableTrust' and drop
-- to 'AnyTrust' for one strange thing, or to sit at 'NoTrust' and step up one
-- rung when needed. A user may switch whenever they like, including between
-- theorems.
--
-- **The level is the engine's state and not the frontend's** — it is a field of
-- 'Thena.Engine.Machine', beside 'Thena.Engine.globals'. A rule searching for a
-- proof must be able to see what it may reach for, or replaying a script under
-- @:revalidate@ would depend on a toggle nobody recorded.
data TrustLevel
  = NoTrust
    -- ^ **the only rung that is a soundness guarantee.** A 'Discharged' claim
    -- is still permitted here, and that is not a hole in the guarantee: the
    -- two types are convertible, so the body already has the type the node
    -- claims and the trust is carrying nothing. What is refused is every claim
    -- that is doing work.
  | NoUndischargeableTrust
    -- ^ a claim that can never be met is refused; one that merely has not been
    -- met yet is allowed.
    --
    -- **THIS IS NOT A SOUNDNESS GUARANTEE AND MUST NOT BE SOLD AS ONE.**
    -- Measured 2026-10-06: @Empty@ is provable using nothing but claims that
    -- are 'Discharged' at the definitions that make them — @RULINGS.md@ carries
    -- the term. It stops accidents, not adversaries.
  | AnyTrust
    -- ^ nothing is refused. The obligations and their classification are
    -- printed instead — his ruling: @qed@ reports, and so does the middle of a
    -- proof.
  deriving (Eq, Show)

-- | Does this level permit a claim of this class?
permits :: TrustLevel -> TrustClass -> Bool
permits AnyTrust               _ = True
permits NoUndischargeableTrust c = c /= Undischargeable
permits NoTrust                c = c == Discharged

-- | The claims a level does not permit — empty when the level is satisfied.
--
-- The whole of the enforcement, so that the caller that acts on it says only
-- /what/ it does about them and never /which/ they are.
unmet :: TrustLevel -> [TrustClaim] -> [TrustClaim]
unmet lvl = filter (not . permits lvl . claimClass)

-- ---------------------------------------------------------------------------
-- A claim
-- ---------------------------------------------------------------------------

-- | What became of one trusted claim — **151 classifies, it does not count.
-- HIS RULING, 2026-10-06.**
data TrustClass
  = Discharged
    -- ^ the two types are convertible, so 'Thena.Core.Reduce.whnf' would
    -- contract the node away and the trust is carrying nothing. **This is
    -- exactly the contraction's own condition**, down to declining a verdict
    -- that owes a level obligation, which is what keeps the report in step
    -- with reduction rather than beside it.
  | Pending
    -- ^ not met, and not impossible: some substitution could still make the
    -- two types agree. The ordinary state of an honest claim about names the
    -- system does not know yet.
  | Undischargeable
    -- ^ it can never be met, under any substitution, in any later session —
    -- decided by the positional test in 'hopeless'.
  deriving (Eq, Show)

-- | Which site a verdict came from — **and the report must name it, or it
-- misleads exactly where it matters. HIS, 2026-10-06.**
data TrustSite
  = AtDefinition
    -- ^ the claim was read as the definition holds it, with nothing of a use
    -- substituted in. **A partial application, a use reached through a further
    -- definition, and a node in the term under examination itself all answer
    -- this** — his list.
  | AtUse
    -- ^ the use's own arguments, term or level, were instantiated into the
    -- claim before it was classified. **The verdict that catches a lie**: in
    -- @cheatNat@'s own body the node is 'Discharged', and at the use
    -- @cheatNat zero (succ zero)@ the very same node is 'Undischargeable'.
  deriving (Eq, Show)

-- | One trusted claim a term rests on.
--
-- **The pair @(claimed, actual)@ /is/ the obligation, written down with both
-- halves visible** — his observation, 2026-10-05 — so both are here and a
-- report that showed the claim alone would hide whether the trust is still
-- load-bearing.
data TrustClaim = TrustClaim
  { claimRoute :: [GlobalName]
    -- ^ the definitions the walk went through to reach it, outermost first, and
    -- empty for a node standing in the term under examination.
  , claimSite :: TrustSite
  , claimContext :: Context
    -- ^ what the two types may mention. A node under a binder is read with that
    -- binder opened, so a printer needs this to name what it sees.
  , claimClaimed :: Core
  , claimActual  :: Core
  , claimClass   :: TrustClass
  }
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Classifying one claim
-- ---------------------------------------------------------------------------

-- | Classify one @(claimed, actual)@ pair where it stands.
--
-- **'Discharged' is the contraction's condition and not an approximation of
-- it.** 'Thena.Core.Reduce.whnf' unwraps the node when 'convert' says yes
-- /and owes nothing for it/ — see @HAZARDS.md@ on the missing collector — so
-- this reads the same three outcomes the same way. A yes that owes a level
-- obligation leaves the node standing, and a report that called it discharged
-- would be describing a term the reducer declines to produce.
classify :: GlobalEnv -> Context -> Int -> Core -> Core -> (TrustClass, Int)
classify env ctx n claimed actual = case convert env ctx n claimed actual of
  (Nothing, [], n1) -> (Discharged, n1)
  (_, _, n1)
    | hopeless env ctx claimed actual -> (Undischargeable, n1)
    | otherwise                       -> (Pending, n1)

-- | Can these two types never be made equal, by any substitution, in any later
-- session?
--
-- **Deep and positional, not shallow — HIS RULING, 2026-10-06**, and the reason
-- is a worked example:
--
-- @
-- trusted (Eq Nat zero (succ zero)) (Eq Nat zero zero) (refl Nat zero)
-- @
--
-- agrees at the head @Eq@ and clashes at argument 3, so a head-only test
-- misses it entirely.
--
-- **It answers 'True' only where it is certain, and 'False' everywhere else.**
-- A wrong 'True' calls an honest claim impossible and would have @qed@ refuse a
-- proof that is fine; a wrong 'False' only means a claim is reported as
-- 'Pending' when it could have been named as hopeless. So every shape this does
-- not positively recognise as a rigid clash — η between a λ and a spine, a
-- stuck elimination, a nested trusted node, a difference that is only in level
-- arguments — answers 'False'.
--
-- **A variable is flexible here, which is the opposite of what unification
-- means by it.** "Thena.Core.Unify"\'s @headOf@ calls an assumption rigid
-- because nothing in /that/ problem can change it; the question here is whether
-- anything ever can, and a definition's own binder is instantiated at every use
-- — which is the whole of why @cheatNat@'s body classifies differently from
-- @cheatNat zero (succ zero)@.
--
-- **The counter is seeded rather than threaded**, which is sound here for
-- 'Thena.Core.Reduce.whnf''s own stated reason: nothing minted escapes. The
-- answer is a 'Bool', and the terms a 'TrustClaim' carries are the ones handed
-- in, never the opened copies this comparison walks.
hopeless :: GlobalEnv -> Context -> Core -> Core -> Bool
hopeless env ctx claimed actual = fst (go ctx seed claimed actual)
  where
    seed = beyond (map entryVar ctx ++ freeVars claimed ++ freeVars actual)

    -- Equal terms cannot clash, and otherwise both sides are reduced before
    -- their heads are read — the same shape 'convert' has, for the same reason:
    -- a clash below a δ-step is not a clash.
    go c n s t
      | s == t    = (False, n)
      | otherwise = clash c n (whnf env c s) (whnf env c t)

    -- Both sides in whnf. Two rigid shapes with different keys can never be
    -- made equal; anything else is still open.
    clash c n s t = case (key s, key t) of
      (Just k1, Just k2)
        | k1 /= k2  -> (True, n)
        | otherwise -> positions c n s t
      _             -> (False, n)

    -- Same key, so the two are the same former with the same arity: the clash,
    -- if there is one, is at an argument.
    positions c n s t = case (s, t) of
      (Pi i dom sc, Pi _ dom' sc') -> binder c n i dom sc dom' sc'
      (Canonical _ _ as, Canonical _ _ bs) -> list c n as bs
      -- A 'Universe' has no term positions, and a difference in its level is
      -- not a clash: a level parameter is instantiated at a use exactly as a
      -- term binder is.
      (Universe _, Universe _)   -> (False, n)
      -- Equal keys means the same literal.
      (Primitive _, Primitive _) -> (False, n)
      -- A rigid spine: equal keys gave the same head and the same arity.
      _ -> list c n (snd (spine s)) (snd (spine t))

    binder c n i dom sc dom' sc' =
      let (x, n1) = fresh n
       in case go c n1 dom dom' of
            (True,  n2) -> (True, n2)
            (False, n2) ->
              go (c ++ [Hypothesis x i dom]) n2 (open x sc) (open x sc')

    list _ n []       _        = (False, n)
    list _ n _        []       = (False, n)
    list c n (a : as) (b : bs) = case go c n a b of
      (True,  n1) -> (True, n1)
      (False, n1) -> list c n1 as bs

    -- | What a substitution can never change about a term in whnf, or 'Nothing'
    -- when it can change everything.
    --
    -- A standing 'Global' head is rigid by construction: δ unfolds every
    -- definition it can, so one still here is a constant or a former wrapper
    -- waiting to saturate, and neither steps. A 'Lam' is left out on purpose —
    -- η relates one with a spine, and reimplementing that here to decide a
    -- clash is exactly the overreach the 'False'-by-default rule above exists
    -- to avoid.
    key t = case t of
      Universe _       -> Just KUniverse
      Pi {}            -> Just KPi
      Primitive l      -> Just (KLiteral l)
      Canonical g _ as -> Just (KFormer g (length as))
      _ -> case spine t of
        (Global g _, as) -> Just (KGlobal g (length as))
        _                -> Nothing

-- | What two rigid heads are compared by. Not exported: it is the positional
-- test's own vocabulary and means nothing outside it.
data Key
  = KUniverse
  | KPi
  | KLiteral Literal
  | KFormer GlobalName Int
  | KGlobal GlobalName Int
  deriving (Eq)

-- ---------------------------------------------------------------------------
-- The walk
-- ---------------------------------------------------------------------------

-- | Every trusted claim a term rests on, in order of first appearance.
--
-- **Takes and returns the name counter** (§7.4): the walk opens every binder it
-- descends under, a 'TrustClaim' carries the opened types, and those reach the
-- user — so a number shown here must not be handed out again.
--
-- **What the walk does, and the one place it earns a comment rather than being
-- obvious, is arity.** From the term under examination, an application spine
-- headed by a 'Global' with a body has the use's level arguments substituted and
-- its term arguments instantiated into that body's leading λs; the claims found
-- there are 'AtUse'. Everything else is 'AtDefinition' — a partial application,
-- a bare reference that supplies nothing, a node standing in the term itself,
-- and **a use reached through a further definition**, which is what keeps this a
-- one-hop walk rather than a normaliser.
--
-- **It terminates**, and for two reasons rather than one: the argument-threading
-- hop happens only at the outermost level, so it cannot chain, and the
-- definition-site recursion takes each global apart at most once.
trustIn :: GlobalEnv -> Context -> Int -> Core -> ([TrustClaim], Int)
trustIn env ctx n t
  | not (reaches env t) = ([], n)
  | otherwise =
      case walk (AtDefinition, []) ctx t (Walking [] [] n) of
        Walking cs _ n' -> (nub (reverse cs), n')
  where
    -- The claims found so far, newest first; the definitions already taken
    -- apart; and the counter. Threaded by hand, with no state type beyond this
    -- one — §3.5's rule, the same one 'convert' follows.
    walk here c t' w = case t' of
      Bound _     -> w
      Free _      -> w
      Universe _  -> w
      Primitive _ -> w

      Global g ls -> reference here c g ls [] w

      -- The spine is read whole, because whether the arguments reach a trusted
      -- node is a question about the application and not about its pieces.
      App {} ->
        let (h, as) = spine t'
            w1      = walks here c as w
         in case h of
              Global g ls -> reference here c g ls as w1
              _           -> walk here c h w1

      Pi i dom sc  -> under here c i dom sc (walk here c dom w)
      Lam i dom sc -> under here c i dom sc (walk here c dom w)
      -- **A 'Let' is substituted rather than opened, which is what δ followed
      -- by ν does to one** — 'Thena.Core.Reduce.whnf' has the same case for the
      -- same reason, and the substituted body holds the value, so only the
      -- ascribed type is walked separately.
      --
      -- **Opening it instead was correct and unreadable, and that is why this
      -- is written down.** Elaborating @declare honest : T ; honest = trusted T
      -- e@ leaves the claim behind a local definition, so a report that opened
      -- the 'Let' printed the claim as @C@ and the body's type as @A@ — the
      -- names of two holes, carrying none of the information the report exists
      -- to carry. The verdicts were right either way, because 'convert' reads
      -- the value out of the context; what was lost was the whole of what a
      -- user reads.
      Let _ v s sc -> walk here c (instantiate v sc) (walk here c s w)

      Canonical _ _ as -> walks here c as w
      Eliminate _ _ ps m ms is tgt ->
        walks here c (ps ++ [m] ++ ms ++ is ++ [tgt]) w

      -- **The node itself.** Its own two types are walked as well: a trusted
      -- claim about a type that itself rests on one is not a case to leave out.
      Trusted claimed actual body ->
        walks here c [claimed, actual, body] (found here c claimed actual w)

    walks here c ts w = foldl (\acc t' -> walk here c t' acc) w ts

    under here c i dom sc w =
      let (x, n1) = freshIn w
       in walk here (c ++ [Hypothesis x i dom]) (open x sc) (counting n1 w)

    -- A reference, applied or bare. Only the outermost level threads a use's
    -- arguments into a definition — that is his /"a use reached through another
    -- definition must answer definition site"/, and it is also what bounds the
    -- walk.
    reference here@(_, route) c g ls as w = case lookupDefinition g env of
      Nothing -> w
      Just d
        | not (reaches env (definitionBody d))       -> w
        | null route, Just w' <- atUse c g d ls as w -> w'
        | otherwise                                  -> atDefinition here g d w

    -- **'Nothing' when there is no use-site verdict to be had**, in which case
    -- the definition site is the honest answer. Two ways that happens, and they
    -- are his list:
    --
    --   * **the use is partially applied** — a λ is left standing after the
    --     arguments went in, so the instance is not determined and a verdict
    --     read off it would be a verdict about an argument nobody passed. A
    --     bare reference to a function is this case with no arguments at all.
    --   * **the use supplies nothing** — no level arguments and no term
    --     arguments, so what would be classified is the definition's own claim,
    --     unchanged, and calling that a use-site verdict would be a lie about
    --     where it came from.
    --
    -- **Level arguments count as a use.** A declared type's level is
    -- generalised into a prenex parameter, so @honest {0}@ sharpens its own
    -- claim without passing a single term — and that is the feature working,
    -- not a special case.
    atUse c g d ls as w
      | saturated, not (null ls) || peeled > 0 = Just (walk (AtUse, [g]) c body w)
      | otherwise                             = Nothing
      where
        (body, peeled) =
          instantiated (atLevels (definitionLevels d) ls (definitionBody d)) as
        saturated = case body of
          Lam {} -> False
          _      -> True

    -- The definition read as it holds its own claims, with its level parameters
    -- left standing and its body closed — so the context is empty and not the
    -- use's.
    atDefinition (_, route) g d w@(Walking cs seen k)
      | g `elem` seen = w
      | otherwise =
          walk (AtDefinition, route ++ [g]) [] (definitionBody d)
               (Walking cs (g : seen) k)

    found (site, route) c claimed actual (Walking cs seen k) =
      let (cls, n1) = classify env c k claimed actual
       in Walking (TrustClaim route site c claimed actual cls : cs) seen n1

    freshIn (Walking _ _ k) = fresh k
    counting k (Walking cs seen _) = Walking cs seen k

-- | Is there any trusted claim reachable from this term at all?
--
-- **A pre-pass that mints nothing, and it is not an optimisation — leave it
-- in.** 'trustIn' opens every binder it descends under, so walking a term that
-- rests on nothing would still spend one variable per binder of it and of every
-- definition it mentions; §7.4's counter is session-wide, so a /look/ would
-- renumber every level meta the session went on to mint. **That is exactly how
-- this was found**: three goldens moved by two subscripts each, with nothing in
-- them trusting anything.
--
-- Almost every term in the system rests on nothing, so almost every call stops
-- here. **It terminates** because the set of definitions already looked at only
-- grows, which is the same fact the walk's own termination rests on.
reaches :: GlobalEnv -> Core -> Bool
reaches env t0 = go [] [t0]
  where
    go _ [] = False
    go seen (t : ts)
      | holdsTrusted t = True
      | otherwise      = go (seen ++ fresh') (ts ++ bodies)
      where
        fresh' = [ g | g <- globalsIn t, g `notElem` seen ]
        bodies =
          [ definitionBody d
          | g <- fresh'
          , Just d <- [lookupDefinition g env]
          ]

-- | The claims found, the definitions already taken apart, and the name
-- counter. Not exported: 'trustIn' is the whole of what it is for.
data Walking = Walking [TrustClaim] [GlobalName] Int

-- | Peel as many leading λs as the spine has arguments, and say how many went
-- in. **'Thena.Core.Term.instantiate' and nothing else** — this is the one
-- substitution the walk performs, and it is not a reduction: nothing below the
-- λs is touched.
instantiated :: Core -> [Core] -> (Core, Int)
instantiated body [] = (body, 0)
instantiated (Lam _ _ sc) (a : rest) =
  let (b, k) = instantiated (instantiate a sc) rest in (b, k + 1)
instantiated body (_ : _) = (body, 0)

-- | An application, as its head and its arguments in written order.
spine :: Core -> (Core, [Core])
spine = go []
  where
    go as (App f a) = go (a : as) f
    go as t         = (t, as)
