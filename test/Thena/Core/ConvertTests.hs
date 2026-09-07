-- | Conversion (§5.2): whnf-driven, η for functions, no η for datatypes, no
-- cumulativity — and the structured reason when it says no.
module Thena.Core.ConvertTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

import Thena.Core.Level (Level (..), LevelVar (..), Obligation (..), levelOfNat)
import Thena.Core.Context (Context, Entry (..))
import Thena.Core.Convert (convert, subsumes)
import Thena.Core.Term (Core (..), GlobalName (..), Ident (..), close, fresh)
import Thena.Declared (natVec, natVecCounter)
import Thena.Driver (parseCore)
import Thena.Errors (Clash (..), ConversionFailure (..), Site (..))

tests :: TestTree
tests =
  testGroup
    "Thena.Core.Convert"
    [ testGroup "syntactic and computational" basicTests
    , testGroup "eta for functions" etaTests
    , testGroup "eta meets an under-applied former wrapper" wrapperEtaTests
    , testGroup "no eta for datatypes, no cumulativity" refusalTests
    , testGroup "the reason says where" siteTests
    , testGroup "the counter comes back, and only ever goes up" counterTests
    , testGroup "an undecided level is owed, not refused" obligationTests
    , testGroup "only a Pi's codomain varies" varianceTests
    ]

-- --------------------------------------------------------------------------
-- Fixtures
-- --------------------------------------------------------------------------

term :: Context -> String -> Core
term = termAt natVecCounter

-- | Read a term with an explicit counter. Every test that builds a context by
-- hand must pass the counter that context ended at, never 'natVecCounter':
-- resolving a lambda mints variables too, and starting both from the same
-- number makes the binder and the hypothesis the SAME variable. That is not
-- hypothetical — the first draft of the eta tests below did it, and conversion
-- correctly reported two different variables where the test meant one.
termAt :: Int -> Context -> String -> Core
termAt n ctx src = case parseCore natVec ctx n src of
  Left e       -> error ("fixture term does not resolve: " ++ show e)
  Right (t, _) -> t

-- | 'convert' returns its level obligations as well (MS3 phase 33). Nothing in
-- this module builds a level meta, so the list is always empty; these two say
-- so once rather than at every call.
verdict :: (a, b, c) -> a
verdict (r, _, _) = r

counter :: (a, b, Int) -> Int
counter (_, _, n) = n

-- | Convertible? Reported as the reason itself, so a failing test prints why.
same :: Context -> String -> String -> Maybe ConversionFailure
same ctx a b = verdict (convert natVec ctx natVecCounter (term ctx a) (term ctx b))

yes :: Context -> String -> String -> IO ()
yes ctx a b = same ctx a b @?= Nothing

no :: Context -> String -> String -> IO ()
no ctx a b = (same ctx a b == Nothing) @?= False

named :: String -> GlobalName
named = GlobalName

-- | Convert two terms in a context built from @(name, type)@ pairs, with the
-- counter threaded through the context, then both terms, in that order.
convertIn :: [(String, String)] -> String -> String -> Maybe ConversionFailure
convertIn binders a b =
  verdict (convert natVec ctx n (termAt n ctx a) (termAt n ctx b))
  where
    (ctx, n) = foldl add ([], natVecCounter) binders
    add (c, k) (name, ty) =
      let (v, k1) = fresh k
       in (c ++ [Hypothesis v (Ident name) (termAt k c ty)], k1)

-- --------------------------------------------------------------------------

basicTests :: [TestTree]
basicTests =
  [ testCase "a term is convertible with itself, without reducing" $
      yes [] "succ zero" "succ zero"
  , testCase "beta: an applied identity meets its argument" $
      yes [] "(\\ (x : Nat) -> x) zero" "zero"
  , testCase "delta: a saturated wrapper meets its Canonical" $
      -- The right-hand side is written as the wrapper too, because §3.6's
      -- resolver never builds a 'Canonical'. What makes this a delta test is
      -- that the left is a redex and reaches the same value.
      yes [] "(\\ (x : Nat) -> succ x) zero" "succ zero"
  , testCase "iota: an elimination meets the value it computes to" $
      yes []
        "elim Nat () (\\ (_ : Nat) -> Nat) \
        \(zero (\\ (x : Nat) (ih : Nat) -> succ ih)) () (succ zero)"
        "succ zero"
  , testCase "under a binder: bodies are compared, and reduced there" $
      yes [] "\\ (x : Nat) -> (\\ (y : Nat) -> y) x" "\\ (x : Nat) -> x"
  , testCase "a let is never met at the head" $
      yes [] "let x = zero : Nat in succ x" "succ zero"
  , testCase "two different values do not meet" $
      no [] "zero" "succ zero"
  ]

etaTests :: [TestTree]
etaTests =
  [ testCase "f and \\x -> f x, lambda on the right" $
      convertIn oneFun "f" "\\ (x : Nat) -> f x" @?= Nothing
  , testCase "f and \\x -> f x, lambda on the left" $
      convertIn oneFun "\\ (x : Nat) -> f x" "f" @?= Nothing
  , testCase "eta is not blind: f and \\x -> g x differ" $
      (convertIn twoFuns "f" "\\ (x : Nat) -> g x" == Nothing) @?= False
  ]
  where
    oneFun  = [("f", "Nat -> Nat")]
    twoFuns = [("f", "Nat -> Nat"), ("g", "Nat -> Nat")]

-- | **Phase 7's explicit proof obligation, discharged** (`PLAN-semantics.md`
-- §5.1). δ waits for a former wrapper to saturate, so @cons A@ is a legal
-- whnf that is not a λ; η is what must still make it meet the λ-form.
--
-- The first case is §5.1's own example, verbatim. It is the whole obligation:
-- η fires once per remaining binder, growing the spine by one argument each
-- time, and on the fourth application the wrapper saturates, δ fires, β
-- follows, and both sides arrive at the same 'Canonical'.
wrapperEtaTests :: [TestTree]
wrapperEtaTests =
  [ testCase "cons A meets its full eta-expansion (three binders)" $
      yes []
        "cons Nat"
        "\\ (n : Nat) (a : Nat) (as : Vec Nat n) -> cons Nat n a as"
  , testCase "the partially applied wrapper is genuinely stuck, so this is not trivial" $
      -- If delta did not wait, the left side would already be a lambda and the
      -- eta rule would never be reached. Recorded as a term-level fact so the
      -- test above cannot quietly stop testing eta.
      no [] "cons Nat" "\\ (n : Nat) (a : Nat) (as : Vec Nat n) -> nil Nat"
  , testCase "one binder short still meets, by eta once more" $
      yes []
        "cons Nat zero"
        "\\ (a : Nat) (as : Vec Nat zero) -> cons Nat zero a as"
  , testCase "a wrong argument inside the expansion is caught" $
      no []
        "cons Nat"
        "\\ (n : Nat) (a : Nat) (as : Vec Nat n) -> cons Nat n a (nil Nat)"
  , testCase "the type former's wrapper too: Vec meets its expansion" $
      yes [] "Vec" "\\ (A : Type\8320) (n : Nat) -> Vec A n"
  ]

refusalTests :: [TestTree]
refusalTests =
  [ testCase "no eta for datatypes: a variable does not meet a constructor" $
      -- Were there eta for a single-constructor type this would have to
      -- succeed. §5.2 says there is not, and this pins it.
      (convertIn [("v", "Vec Nat zero")] "v" "nil Nat" == Nothing) @?= False
  , testCase "no cumulativity: Type0 does not meet Type1" $
      no [] "Type\8320" "Type\8321"
  , testCase "no cumulativity: it does not hold in the other direction either" $
      no [] "Type\8321" "Type\8320"
  ]

-- | Exact reasons, not just "no". A round trip through @== Nothing@ would pass
-- for a conversion that always failed; these are the cases that say the route
-- and the clash are the real ones.
siteTests :: [TestTree]
siteTests =
  [ testCase "two universes, at the top" $
      same [] "Type\8320" "Type\8321"
        @?= Just (ConversionFailure [] (LevelsDiffer (LZero) (levelOfNat 1)))
  , testCase "two formers, at the top" $
      same [] "zero" "nil Nat"
        @?= Just (ConversionFailure [] (NamesDiffer (named "zero") (named "nil")))
  , testCase "inside a former's argument" $
      same [] "succ zero" "succ (succ zero)"
        @?= Just
              (ConversionFailure
                 [TheArgumentOf (named "succ") 0]
                 (NamesDiffer (named "zero") (named "succ")))
  , testCase "under a binder, then in the domain" $
      routeOf (same [] "\\ (x : Nat) -> Vec Nat zero -> Nat"
                     "\\ (x : Nat) -> Vec Nat (succ zero) -> Nat")
        @?= [TheBody (Ident "x"), TheDomain (Ident "_"), TheArgumentOf (named "Vec") 1]
  , testCase "in an elimination's motive — with a target that keeps it stuck" $
      -- The target must be a variable. With a value there, iota fires on both
      -- sides before the motives are ever compared and the two are convertible
      -- for a perfectly good reason; the first draft of this case had @zero@
      -- there and was testing nothing.
      routeOf (convertIn [("m", "Nat")]
                 "elim Nat () (\\ (_ : Nat) -> Nat) (zero succ) () m"
                 "elim Nat () (\\ (_ : Nat) -> Vec Nat zero) (zero succ) () m")
        @?= [TheMotive, TheBody (Ident "_")]
  ]
  where
    routeOf = maybe [] conversionSite

-- | The counter is threaded in and out and never rewinds — decided by the user
-- 2026-08-22. Checked on the failing branch too, because that is the branch
-- that hands a freshly minted variable to the user inside a 'HeadsDiffer'.
counterTests :: [TestTree]
counterTests =
  [ testCase "opening a binder advances it" $
      (counter (convert natVec [] 100
              (term [] "\\ (x : Nat) -> x") (term [] "\\ (x : Nat) -> x")) > 100)
        @?= False
      -- Syntactically equal: the fast path returns before any binder is opened,
      -- so nothing is minted. That is the point of the fast path.
  , testCase "a binder that IS opened advances it" $
      (counter (convert natVec [] 100
              (term [] "\\ (x : Nat) -> (\\ (y : Nat) -> y) x")
              (term [] "\\ (x : Nat) -> x")) > 100)
        @?= True
  , testCase "it advances on the failing branch too" $
      (counter (convert natVec [] 100
              (term [] "\\ (x : Nat) -> zero") (term [] "\\ (x : Nat) -> succ zero")) > 100)
        @?= True
  ]

-- | Where cumulativity is allowed to look, and where it must not (MS4 phase
-- 41h).
--
-- **This group exists because the whole suite passed while 'subsumes' was
-- unsound.** The direction was carried into every sub-problem, so an
-- application's arguments, a saturated former's arguments and an elimination's
-- fields were all compared cumulatively — and nothing here asked.
--
-- @subsumes expected actual@, matching 'Thena.Core.Typing.check'.
varianceTests :: [TestTree]
varianceTests =
  [ -- The Π codomain is the one covariant position, and it still is.
    testCase "a codomain may be smaller than the one wanted" $
      subsumesIn [] "Nat -> Type\8321" "Nat -> Type\8320" @?= Nothing

    -- Invariant, and deliberately more conservative than ordinary subtyping:
    -- contravariance would be sound here and is declined (see 'subsumes').
  , testCase "but a domain may not" $
      (subsumesIn [] "Type\8321 -> Nat" "Type\8320 -> Nat" == Nothing) @?= False
  , testCase "in either direction" $
      (subsumesIn [] "Type\8320 -> Nat" "Type\8321 -> Nat" == Nothing) @?= False

    -- **The unsoundness that was shipped.** @F@ is opaque, so nothing relates
    -- @F Type₀@ to @F Type₁@. This was accepted, and @:revalidate@ called the
    -- development valid — @ms4/CLOSEOUT.md@ 12.
  , testCase "a neutral spine's argument is invariant" $
      (subsumesIn [("F", "Type\8322 -> Type\8320")] "F Type\8321" "F Type\8320" == Nothing)
        @?= False
  , testCase "and so is its head" $
      (subsumesIn [("F", "Type\8322 -> Type\8320"), ("G", "Type\8322 -> Type\8320")]
         "F Type\8320" "G Type\8320" == Nothing)
        @?= False
  ]

-- | 'subsumes' over 'convertIn'\'s context builder.
subsumesIn :: [(String, String)] -> String -> String -> Maybe ConversionFailure
subsumesIn binders a b =
  verdict (subsumes natVec ctx n (termAt n ctx a) (termAt n ctx b))
  where
    (ctx, n) = foldl add ([], natVecCounter) binders
    add (c, k) (name, ty) =
      let (v, k1) = fresh k
       in (c ++ [Hypothesis v (Ident name) (termAt k c ty)], k1)

-- --------------------------------------------------------------------------
-- Level obligations (MS3 phase 33)
-- --------------------------------------------------------------------------

-- | **The invariant this group is really about**: with no meta on either side,
-- nothing is owed and the answer is exactly what it was before phase 33. That
-- is why the rest of the suite did not move, and it is checked here rather than
-- left to be inferred from the suite passing.
obligationTests :: [TestTree]
obligationTests =
  [ testCase "closed universes owe nothing, whichever way they subsume" $
      owed (subsumes natVec [] natVecCounter (universe 1) (universe 0)) @?= []

  , testCase "nor does an equality between closed universes" $
      owed (convert natVec [] natVecCounter (universe 1) (universe 1)) @?= []

  , -- @subsumes expected actual@, so this asks whether a term at @Type ?m@ is
    -- usable where @Type1@ is wanted: @?m <= 1@.
    testCase "a meta on the right of the relation is owed" $
      subsumes natVec [] natVecCounter (universe 1) (Universe (LVar meta))
        @?= (Nothing, [AtMost (LVar meta) (levelOfNat 1)], natVecCounter)

  , testCase "and it is a success, not a failure" $
      verdict (subsumes natVec [] natVecCounter (universe 1) (Universe (LVar meta)))
        @?= Nothing

  , -- An **equality** is undecided in both directions at once, and both are
    -- owed: a Π's domain is invariant, so a bare @Type@ written in a domain
    -- reaches this case and must not be refused.
    testCase "an equality with a meta owes the relation both ways" $
      owed (convert natVec [] natVecCounter (Universe (LVar meta)) (universe 0))
        @?= [AtMost (LVar meta) (levelOfNat 0), AtMost (levelOfNat 0) (LVar meta)]

  , -- False for every instantiation, so it is reported here rather than
    -- postponed — the error lands on the line that caused it.
    testCase "a relation that no level could satisfy still fails on the spot" $
      (verdict (subsumes natVec [] natVecCounter (universe 0) (universe 1)) == Nothing)
        @?= False

  , -- Reached through a Π rather than at the head, so the obligation has to
    -- survive the recursion that 'andThen' threads it through.
    testCase "obligations come back from under a binder" $
      owed (convert natVec [] natVecCounter
              (arrow (Universe (LVar meta)) (universe 0))
              (arrow (universe 0) (universe 0)))
        @?= [AtMost (LVar meta) (levelOfNat 0), AtMost (levelOfNat 0) (LVar meta)]
  ]
  where
    universe = Universe . levelOfNat
    meta     = LMeta 900

    owed (_, o, _) = o

    -- A non-dependent function type, built by hand: the concrete syntax cannot
    -- write a meta down, which is the point — only a bare @Type@ mints one, and
    -- this module reads no source.
    arrow dom cod = Pi (Ident "_") dom (close (fst (fresh 990)) cod)
