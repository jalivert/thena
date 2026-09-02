-- | Conversion: judgemental equality of core terms (§5.2).
--
-- whnf-driven, with **η for functions and no η for datatypes**, and **no
-- cumulativity** — all three are stated deviations with reasons in §5.2, not
-- omissions to be tidied up later. Conversion is symmetric: there is no left
-- and no right, and 'convert' may be called with its arguments either way
-- round.
--
-- Below "Thena.Core.Typing" and above "Thena.Core.Reduce" in the layering
-- (§2.5). It knows nothing of the development, the cursor or constraints — a
-- 'Context' and two terms is the whole of its input (§7.4).
module Thena.Core.Convert
  ( convert
  , subsumes
  , Direction (..)
  ) where

import Thena.Core.Level (Level, Obligation (..), levelLeq, metasIn)
import Thena.Core.Context (Context, Entry (..))
import Thena.Core.Reduce (whnf)
import Thena.Core.Term (Core (..), fresh, open)
import Thena.Errors (Clash (..), ConversionFailure (..), Site (..))
import Thena.Global.Env (GlobalEnv)

-- | Are these two terms convertible, and if not, where and why?
--
-- 'Nothing' means yes. There is deliberately no positive justification
-- alongside it — 'Thena.Errors.ConversionFailure' says why not.
--
-- **Takes and returns the name counter.** η and the binder cases both open a
-- 'Thena.Core.Term.Scope', and only 'Thena.Core.Term.fresh' mints the variable
-- to open it with (§3.5). The counter is returned on the failing branch too:
-- a variable minted here reaches the user inside a 'HeadsDiffer', and §7.4's
-- rule for the counter is that a name already shown must never be handed out
-- again.
--
-- **The syntactic fast path is sound, not complete** (§5.2): @'Eq' 'Core'@ is
-- α-equivalence, so equal implies convertible, and the converse was never
-- claimed. It is checked before reducing at every recursive step, which is
-- what keeps conversion of two large identical terms from reducing both.
convert
  :: GlobalEnv -> Context -> Int -> Core -> Core
  -> (Maybe ConversionFailure, [Obligation], Int)
convert env = related Same env

-- | Is @actual@ usable where @expected@ is wanted? Cumulativity's relation
-- (MS3 phase 32).
--
-- **This is where the direction lives, and 'convert' keeps none.** Conversion
-- is an equality — its own header says there is no left and no right — and
-- cumulativity is not: @Type₀@ is usable where @Type₁@ is wanted and not the
-- other way about. Making @convert@ directional would have made every caller
-- that wants an equality state a direction it does not have.
--
-- @subsumes expected actual@, in that order, matching
-- 'Thena.Core.Typing.check''s own argument order.
--
-- **A Π's codomain is the only position that varies. Everything else — its
-- domain, a λ's body, and every argument of an application, a saturated former
-- or an elimination — is compared at 'Same'** (MS4 phase 41h).
--
-- **The domain is invariant, and the reason is not the one this comment used
-- to give.** It said /"a function expecting @Type₁@ arguments cannot stand in
-- for one expecting @Type₀@ arguments, because it would be handed something
-- too small"/ — which is backwards. Being handed something smaller is exactly
-- what is fine: @Type₀ ⊑ Type₁@ means every @Type₀@ /is/ a @Type₁@, so
-- @Type₁ -> Nat@ genuinely is usable where @Type₀ -> Nat@ is wanted. Ordinary
-- subtyping is **contravariant** in the domain, and that would be sound here.
--
-- We decline it anyway, which is Coq's choice too: invariance is strictly more
-- conservative — it can only reject — and a dependent Π's codomain binds a
-- variable whose type is the thing being varied, so a contravariant domain
-- means comparing two codomains in two different contexts.
--
-- **An argument of an application is a different question and has no variance
-- at all.** The head is opaque, so nothing whatever relates @F Type₀@ to
-- @F Type₁@; they are equal or they are unrelated. Inheriting the direction
-- there was **unsound**, and it is what @ms4/CLOSEOUT.md@ 12 recorded:
-- @x : F Type₀@ was accepted at a goal of @F Type₁@ and @:revalidate@ called
-- it valid.
--
-- **The third component is what it could not decide** (phase 33): a subsumption
-- between levels one of which is still a meta is neither true nor false yet, so
-- it comes back as an 'Obligation' and the answer is still a success. Who
-- collects them is stated once, in "Thena.Core.Typing" — during a proof they
-- are dropped, and the pass that re-checks the finished development is where
-- they are discharged.
subsumes
  :: GlobalEnv -> Context -> Int -> Core -> Core
  -> (Maybe ConversionFailure, [Obligation], Int)
subsumes = related Cumulative

-- | Which relation the universe case and the Π codomain are read at.
--
-- **Exported, and "Thena.Core.Unify" uses this one rather than declaring its
-- own** (MS4 phase 41g). It is the same question there — a directed
-- unification differs from a symmetric one at exactly these two places — and
-- two types with one name and one meaning is the confusion the standing rule
-- is about.
data Direction = Same | Cumulative
  deriving (Eq, Show)

related
  :: Direction -> GlobalEnv -> Context -> Int -> Core -> Core
  -> (Maybe ConversionFailure, [Obligation], Int)
related dir env = go
  where
    go ctx n s t
      | s == t    = ok n
      | otherwise = heads ctx n (whnf env ctx s) (whnf env ctx t)

    -- Both sides are in whnf here. A 'Let' cannot appear: 'whnf' substitutes
    -- every one it meets away, which is recorded as a property of that function
    -- and is why there is no @Let@ case below.
    heads ctx n s t = case (s, t) of
      (Universe k, Universe l) -> case dir of
        -- An **equality** between levels, which a meta makes undecided in both
        -- directions at once. It is owed as two obligations rather than
        -- refused: a Π's domain is invariant (see 'subsumes'), and a bare
        -- @Type@ written in a domain is ordinary, so failing here would make
        -- the commonest thing a user writes unusable.
        --
        -- **With no meta on either side this is exactly what it always was** —
        -- 'Eq' 'Level' up to the normal form — which is why the suite did not
        -- move when this arrived.
        Same
          | k == l     -> ok n
          | undecided  -> (Nothing, [AtMost k l, AtMost l k], n)
          | otherwise  -> bad n [] (LevelsDiffer k l)
          where undecided = not (null (metasIn k) && null (metasIn l))
        -- @k@ is what was expected and @l@ is what was found, so cumulativity
        -- asks @l <= k@.
        --
        -- **@Nothing@ is no longer a failure** (phase 33). Only a meta produces
        -- it, and refusing there would make @Type@ a term nothing can be
        -- checked against; the relation is handed back for the collector
        -- instead. @Just False@ still fails on the spot — an inequality that is
        -- false for every instantiation is a mistake in the term, and reporting
        -- it here is what puts the error on the line that caused it.
        Cumulative -> case levelLeq l k of
          Just True  -> ok n
          Just False -> bad n [] (LevelsDiffer k l)
          Nothing    -> (Nothing, [AtMost l k], n)

      (Free x, Free y)
        | x == y    -> ok n
        | otherwise -> bad n [] (VariablesDiffer x y)

      -- **A reference's level arguments are part of what it is.** @Eq {0}@ and
      -- @Eq {1}@ are two different types, and this case used to compare the
      -- names alone and call them convertible — which made conversion agree
      -- terms whose /own/ types it then refused to convert. Found reviewing
      -- MS3; it is the same omission phase 29 left in @Eq Core@ and the
      -- @Canonical@ and @Eliminate@ cases below, and unlike those it was
      -- reachable in one line at the REPL.
      (Global f ks, Global g ls)
        | f /= g                 -> bad n [] (NamesDiffer f g)
        | length ks /= length ls -> bad n [] (CountsDiffer (length ks) (length ls))
        | otherwise              -> levels n ks ls

      (Bound i, Bound j)
        | i == j    -> ok n
        | otherwise -> bad n [] (HeadsDiffer ctx s t)

      -- **A Π's codomain is the one covariant position in the language.**
      (Pi i dom sc, Pi _ dom' sc') -> binder dir ctx n i dom sc dom' sc'
      -- A λ is not a type, so a direction has nothing to mean under one.
      (Lam i dom sc, Lam _ dom' sc') -> binder Same ctx n i dom sc dom' sc'

      -- A neutral spine. Comparing the function and the argument separately is
      -- what makes two stuck applications of the same head agree.
      (App f a, App g b) ->
        both ctx n (TheFunction, f, g) (TheArgument, a, b)

      (Canonical f ks as, Canonical g ls bs)
        | f /= g              -> bad n [] (NamesDiffer f g)
        | length ks /= length ls -> bad n [] (CountsDiffer (length ks) (length ls))
        | length as /= length bs -> bad n [] (CountsDiffer (length as) (length bs))
        | otherwise -> levels n ks ls `andThen` \n1 -> list ctx n1 (TheArgumentOf f) as bs

      (Eliminate d ks ps m ms is tgt, Eliminate d' ls ps' m' ms' is' tgt')
        | d /= d'                   -> bad n [] (NamesDiffer d d')
        | length ks /= length ls    -> bad n [] (CountsDiffer (length ks) (length ls))
        | length ps /= length ps'   -> bad n [] (CountsDiffer (length ps) (length ps'))
        | length ms /= length ms'   -> bad n [] (CountsDiffer (length ms) (length ms'))
        | length is /= length is'   -> bad n [] (CountsDiffer (length is) (length is'))
        | otherwise ->
            levels n ks ls `andThen` \n0' -> chain ctx n0'
              [ (TheParameter k, p, p') | (k, p, p') <- zip3 [0 ..] ps ps' ]
              `andThen` \n1 -> at ctx n1 TheMotive m m'
              `andThen` \n2 -> chain ctx n2
                 [ (TheMethod k, x, y) | (k, x, y) <- zip3 [0 ..] ms ms' ]
              `andThen` \n3 -> chain ctx n3
                 [ (TheIndex k, x, y) | (k, x, y) <- zip3 [0 ..] is is' ]
              `andThen` \n4 -> at ctx n4 TheTarget tgt tgt'

      -- η, and the reason 'convert' recurses through 'go' rather than
      -- comparing here: the opened body and the applied spine must both be
      -- whnf'd again before they are compared. That is what discharges phase
      -- 7's obligation. @cons A@ is a legal whnf (δ waits for a former wrapper
      -- to saturate, §5.1), and against @λ n a as -> ‹cons A n a as›@ this rule
      -- fires once per remaining binder, growing the spine by one argument each
      -- time, until the fourth application saturates the wrapper — at which
      -- point δ fires, β follows, and the two sides meet at the 'Canonical'.
      -- It terminates because each step removes one 'Lam' from a finite term.
      (Lam i dom sc, _) -> eta ctx n i dom sc t False
      (_, Lam i dom sc) -> eta ctx n i dom sc s True

      _ -> bad n [] (HeadsDiffer ctx s t)

    -- **The domain is compared at 'Same' whatever @dir@ is** — see 'subsumes'.
    -- 'related Same' rather than 'go' is what makes that true for the whole
    -- subtree, not just the head. @below@ is what the /body/ is compared at,
    -- and it is @dir@ only for a Π.
    binder below ctx n i dom sc dom' sc' =
      at ctx n (TheDomain i) dom dom' `andThen` \n1 ->
        let (x, n2) = fresh n1
            ctx'    = ctx ++ [Hypothesis x i dom]
         in beneath (TheBody i) (related below env ctx' n2 (open x sc) (open x sc'))

    -- One η step: open the λ with a fresh variable and apply the other side to
    -- it. @flipped@ only keeps the two sides in the order the caller passed
    -- them, so a reported clash is not silently mirrored.
    eta ctx n i dom sc other flipped =
      let (x, n1) = fresh n
          ctx'    = ctx ++ [Hypothesis x i dom]
          body    = open x sc
          applied = App other (Free x)
          -- At 'Same': η relates a λ with a spine, and a λ is not a type, so
          -- there is no direction for this to be read at.
          same a b = related Same env ctx' n1 a b
       in beneath (TheBody i) (if flipped then same applied body else same body applied)

    -- **Every site that reaches this is invariant**, so the direction stops
    -- here rather than being carried down (MS4 phase 41h). It was @go@, which
    -- inherits @dir@, and that made an application's arguments, a saturated
    -- former's arguments and an elimination's fields all cumulative — the
    -- unsoundness of @ms4/CLOSEOUT.md@ 12.
    --
    -- This is what @atSame@ was, under another name, for the Π domain's use.
    -- The two are one function now, because every caller wants the same thing.
    at ctx n site s t = beneath site (related Same env ctx n s t)

    both ctx n (s1, a, b) (s2, c, d) =
      at ctx n s1 a b `andThen` \n1 -> at ctx n1 s2 c d

    list ctx n site as bs =
      chain ctx n [ (site k, a, b) | (k, a, b) <- zip3 [0 ..] as bs ]

    chain _   n []                 = ok n
    chain ctx n ((site, a, b) : r) =
      at ctx n site a b `andThen` \n1 -> chain ctx n1 r

    -- One reading of a level relation, used by all four sites that have one:
    -- the universe case above and the three reference forms. **Undecided is an
    -- obligation, not a refusal** — the same three answers, said once.
    levels n ks ls = case levelsAgree ks ls of
      Left (a, b) -> bad n [] (LevelsDiffer a b)
      Right owed  -> (Nothing, owed, n)

    ok n = (Nothing, [], n)
    bad n site clash = (Just (ConversionFailure site clash), [], n)

-- | Push one step onto a failure's route. A success passes through untouched,
-- which is why the site list is built on the way /out/ and comes out
-- outermost-first without a reverse.
beneath
  :: Site
  -> (Maybe ConversionFailure, [Obligation], Int)
  -> (Maybe ConversionFailure, [Obligation], Int)
beneath site (Just f, o, n) = (Just f { conversionSite = site : conversionSite f }, o, n)
beneath _    (Nothing, o, n) = (Nothing, o, n)

-- | Continue only if convertible so far, carrying the counter and the
-- obligations owed so far across either branch.
--
-- Written out rather than reached for as a monad: the counter is an 'Int' in
-- the outer state and there is deliberately no supply type (§3.5).
andThen
  :: (Maybe ConversionFailure, [Obligation], Int)
  -> (Int -> (Maybe ConversionFailure, [Obligation], Int))
  -> (Maybe ConversionFailure, [Obligation], Int)
andThen (Just f,  o, n) _ = (Just f, o, n)
andThen (Nothing, o, n) k = let (r, o', n') = k n in (r, o ++ o', n')
infixl 1 `andThen`

-- | Do two uses of the same reference agree on their level arguments?
--
-- Compared **up to the level algebra**, since that is what @Eq Level@ is —
-- @Type (max 0 1)@ and @Type 1@ are one level. Two uses of the same name at
-- different levels are different terms, so a disagreement is a clash and not a
-- sub-problem: a level is not a 'Core' and cannot be converted further.
--
-- **An undecided pair is owed, exactly as the universe case owes one.** A level
-- argument is an /equality/, so a meta on either side is owed both ways round —
-- the same two obligations, for the same reason, and this is the whole of why
-- the four sites that read a level relation now read it the same way.
levelsAgree :: [Level] -> [Level] -> Either (Level, Level) [Obligation]
levelsAgree ks ls = concat <$> traverse one (zip ks ls)
  where
    one (a, b)
      | a == b                                = Right []
      | null (metasIn a) && null (metasIn b)  = Left (a, b)
      | otherwise                             = Right [AtMost a b, AtMost b a]
