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
-- **A Π's domain stays invariant and only its codomain varies**, which is
-- Coq's rule and the sound one: a function expecting @Type₁@ arguments cannot
-- stand in for one expecting @Type₀@ arguments, because it would be handed
-- something too small. Everything that is not a universe or a Π is compared
-- exactly as 'convert' compares it.
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
data Direction = Same | Cumulative
  deriving (Eq)

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

      (Global f _, Global g _)
        | f == g    -> ok n
        | otherwise -> bad n [] (NamesDiffer f g)

      (Bound i, Bound j)
        | i == j    -> ok n
        | otherwise -> bad n [] (HeadsDiffer ctx s t)

      (Pi i dom sc, Pi _ dom' sc') -> binder ctx n i dom sc dom' sc'
      (Lam i dom sc, Lam _ dom' sc') -> binder ctx n i dom sc dom' sc'

      -- A neutral spine. Comparing the function and the argument separately is
      -- what makes two stuck applications of the same head agree.
      (App f a, App g b) ->
        both ctx n (TheFunction, f, g) (TheArgument, a, b)

      (Canonical f ks as, Canonical g ls bs)
        | f /= g              -> bad n [] (NamesDiffer f g)
        | length ks /= length ls -> bad n [] (CountsDiffer (length ks) (length ls))
        | Just (a, b) <- levelsDiffer ks ls -> bad n [] (LevelsDiffer a b)
        | length as /= length bs -> bad n [] (CountsDiffer (length as) (length bs))
        | otherwise -> list ctx n (TheArgumentOf f) as bs

      (Eliminate d ks ps m ms is tgt, Eliminate d' ls ps' m' ms' is' tgt')
        | d /= d'                   -> bad n [] (NamesDiffer d d')
        | length ks /= length ls    -> bad n [] (CountsDiffer (length ks) (length ls))
        | Just (a, b) <- levelsDiffer ks ls -> bad n [] (LevelsDiffer a b)
        | length ps /= length ps'   -> bad n [] (CountsDiffer (length ps) (length ps'))
        | length ms /= length ms'   -> bad n [] (CountsDiffer (length ms) (length ms'))
        | length is /= length is'   -> bad n [] (CountsDiffer (length is) (length is'))
        | otherwise ->
            chain ctx n
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
    -- subtree, not just the head.
    binder ctx n i dom sc dom' sc' =
      atSame ctx n (TheDomain i) dom dom' `andThen` \n1 ->
        let (x, n2) = fresh n1
            ctx'    = ctx ++ [Hypothesis x i dom]
         in beneath (TheBody i) (go ctx' n2 (open x sc) (open x sc'))

    atSame ctx n site a b = beneath site (related Same env ctx n a b)

    -- One η step: open the λ with a fresh variable and apply the other side to
    -- it. @flipped@ only keeps the two sides in the order the caller passed
    -- them, so a reported clash is not silently mirrored.
    eta ctx n i dom sc other flipped =
      let (x, n1) = fresh n
          ctx'    = ctx ++ [Hypothesis x i dom]
          body    = open x sc
          applied = App other (Free x)
       in beneath (TheBody i)
            (if flipped then go ctx' n1 applied body else go ctx' n1 body applied)

    at ctx n site s t = beneath site (go ctx n s t)

    both ctx n (s1, a, b) (s2, c, d) =
      at ctx n s1 a b `andThen` \n1 -> at ctx n1 s2 c d

    list ctx n site as bs =
      chain ctx n [ (site k, a, b) | (k, a, b) <- zip3 [0 ..] as bs ]

    chain _   n []                 = ok n
    chain ctx n ((site, a, b) : r) =
      at ctx n site a b `andThen` \n1 -> chain ctx n1 r

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

-- | Continue only if convertible so far, carrying the counter across either
-- branch. Written out rather than reached for as a monad: the counter is an
-- 'Int' in the outer state and there is deliberately no supply type (§3.5).
-- | Continue only if convertible so far, carrying the counter and the
-- obligations owed so far across either branch.
andThen
  :: (Maybe ConversionFailure, [Obligation], Int)
  -> (Int -> (Maybe ConversionFailure, [Obligation], Int))
  -> (Maybe ConversionFailure, [Obligation], Int)
andThen (Just f,  o, n) _ = (Just f, o, n)
andThen (Nothing, o, n) k = let (r, o', n') = k n in (r, o ++ o', n')
infixl 1 `andThen`

-- | The first pair of level arguments that are not the same level, if any.
--
-- Compared **up to the level algebra**, since that is what @Eq Level@ is —
-- @Type (max 0 1)@ and @Type 1@ are one level. Two uses of the same former or
-- eliminator at different levels are different terms, so this is a clash and
-- not a sub-problem: a level is not a 'Core' and cannot be converted further.
levelsDiffer :: [Level] -> [Level] -> Maybe (Level, Level)
levelsDiffer ks ls = case [(a, b) | (a, b) <- zip ks ls, a /= b] of
  (p : _) -> Just p
  []      -> Nothing
