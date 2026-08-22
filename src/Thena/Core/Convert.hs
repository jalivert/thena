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
  ) where

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
  -> (Maybe ConversionFailure, Int)
convert env = go
  where
    go ctx n s t
      | s == t    = (Nothing, n)
      | otherwise = heads ctx n (whnf env ctx s) (whnf env ctx t)

    -- Both sides are in whnf here. A 'Let' cannot appear: 'whnf' substitutes
    -- every one it meets away, which is recorded as a property of that function
    -- and is why there is no @Let@ case below.
    heads ctx n s t = case (s, t) of
      (Universe k, Universe l)
        | k == l    -> ok n
        | otherwise -> bad n [] (LevelsDiffer k l)

      (Free x, Free y)
        | x == y    -> ok n
        | otherwise -> bad n [] (VariablesDiffer x y)

      (Global f, Global g)
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

      (Canonical f as, Canonical g bs)
        | f /= g              -> bad n [] (NamesDiffer f g)
        | length as /= length bs -> bad n [] (CountsDiffer (length as) (length bs))
        | otherwise -> list ctx n (TheArgumentOf f) as bs

      (Eliminate d ps m ms is tgt, Eliminate d' ps' m' ms' is' tgt')
        | d /= d'                   -> bad n [] (NamesDiffer d d')
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

    binder ctx n i dom sc dom' sc' =
      at ctx n (TheDomain i) dom dom' `andThen` \n1 ->
        let (x, n2) = fresh n1
            ctx'    = ctx ++ [Hypothesis x i dom]
         in beneath (TheBody i) (go ctx' n2 (open x sc) (open x sc'))

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

    ok n = (Nothing, n)
    bad n site clash = (Just (ConversionFailure site clash), n)

-- | Push one step onto a failure's route. A success passes through untouched,
-- which is why the site list is built on the way /out/ and comes out
-- outermost-first without a reverse.
beneath :: Site -> (Maybe ConversionFailure, Int) -> (Maybe ConversionFailure, Int)
beneath site (Just f, n) = (Just f { conversionSite = site : conversionSite f }, n)
beneath _    (Nothing, n) = (Nothing, n)

-- | Continue only if convertible so far, carrying the counter across either
-- branch. Written out rather than reached for as a monad: the counter is an
-- 'Int' in the outer state and there is deliberately no supply type (§3.5).
andThen :: (Maybe ConversionFailure, Int) -> (Int -> (Maybe ConversionFailure, Int)) -> (Maybe ConversionFailure, Int)
andThen (Just f, n)  _ = (Just f, n)
andThen (Nothing, n) k = k n
infixl 1 `andThen`
