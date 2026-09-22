-- **'genDevelopment' is exported** (2026-09-12) so that @CursorTests@ can walk
-- the same corpus. A second copy of a generator drifts, exactly as a second copy
-- of a word table does.
module Thena.DevelopmentTests (tests, genDevelopment) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))
import Test.Tasty.QuickCheck
  ( Gen, counterexample, elements, forAll, frequency, oneof, property, testProperty
  , withNumTests )

import Thena.Core.Level (Level (..), levelOfNat)
import Thena.Core.Context (Entry (..))
import Thena.Core.Term (Core (..), Ident (..), close, fresh)
import Thena.Development.Component (Component (..), forget)
import Thena.Development.Partial (Partial (..))
import Thena.Driver (parseDevelopment)
import Thena.Global.Env (emptyGlobals)
import Thena.Fixtures
  ( allFour
  , guessShadowing
  , idMidway
  , shadowedBinders
  , trailingLam
  , withConstraint
  )
import Thena.Repl (renderPartial)

tests :: TestTree
tests =
  testGroup
    "Thena.Development"
    [ testGroup "forget" forgetTests
    , testGroup "rendering" renderTests
    , testGroup "longest prefix" prefixTests
    , testGroup "scope" scopeTests
    , testGroup "round trip" roundTripTests
    , generatedRoundTrip
    ]

-- --------------------------------------------------------------------------
-- The printer and the reader, over generated developments (2026-09-12)
-- --------------------------------------------------------------------------

-- | **Everything the printer writes must read back as what it printed.**
--
-- 'roundTripTests' above says this on six hand-built developments. What a
-- fixture corpus cannot say is that it holds for every /combination/ of link,
-- and the printer and the reader are different code in different modules:
-- 'renderPartial' decides where a newline, a parenthesis and a freshened name
-- go, and @Syntax.Parser@ plus @Syntax.Resolve@ decide what those mean. The
-- surface printer had exactly this shape of defect and a fixed corpus did not
-- see it (@ms5\/CLOSEOUT.md@ 26).
--
-- **Generated as SOURCE and not as a 'Partial'**, which is what makes it cheap:
-- a generated development is well scoped by construction — a name is written
-- only where it is bound — and needs no var supply threaded through the
-- generator. It also checks something the value-level version could not, that
-- everything the /grammar/ admits is something the printer can print.
--
-- The property is the printer's own: @render . parse@ is idempotent. It cannot
-- be @parse . render == id@ because 'Partial'\'s 'Eq' compares 'Var's literally
-- and re-reading mints fresh ones — 'reprint' says so.
generatedRoundTrip :: TestTree
generatedRoundTrip =
  testGroup
    "any development the grammar admits"
    [ testProperty "parses, and printing it is idempotent" $
        withNumTests 1000 $ forAll (genDevelopment [] 5) $ \src ->
          case parseDevelopment [] emptyGlobals [] 500 src of
            Left e -> counterexample (src ++ "\n  did not parse: " ++ show e) False
            -- **Rendered with the counter the parse handed back**, not with
            -- the one it started from: the vars in @p@ were minted from 500
            -- upward, so rendering at 500 lets the printer mint a display name
            -- that collides with one already there — §13e, and 'reprint' is
            -- safe from it only because its fixtures mint from zero.
            Right (p, n) ->
              let once = renderPartial [] n [] p
                  twice = case parseDevelopment [] emptyGlobals [] n once of
                    Left e            -> "PARSE FAILED: " ++ show e
                    Right (p', n')    -> renderPartial [] n' [] p'
               in counterexample
                    (src ++ "\n  printed:\n" ++ once ++ "\n  reprinted:\n" ++ twice)
                    (property (twice == once))
    ]

-- | A written development, well scoped by construction.
--
-- @scope@ is the names a term here may mention. A guess's body is generated in
-- the scope /outside/ the hole, because a guess body does not see the hole's
-- name — which is what @guessShadowing@ above is about.
genDevelopment :: [String] -> Int -> Gen String
genDevelopment scope n
  | n <= 0 = genTerm' scope 2
  | otherwise =
      frequency
        [ (2, genTerm' scope 2)
        , (3, do
              x  <- genName
              ty <- genTerm' scope 1
              k  <- elements ["λ", "∀"]
              r  <- genDevelopment (x : scope) (n - 1)
              pure (k ++ " (" ++ x ++ " : " ++ ty ++ ") ->\n" ++ r))
        , (2, do
              x  <- genName
              v  <- genTerm' scope 1
              ty <- genTerm' scope 1
              r  <- genDevelopment (x : scope) (n - 1)
              pure ("let " ++ x ++ " = " ++ v ++ " : " ++ ty ++ " in\n" ++ r))
        , (2, do
              x  <- genName
              ty <- genTerm' scope 1
              r  <- genDevelopment (x : scope) (n - 1)
              pure ("let ? " ++ x ++ " : " ++ ty ++ " in\n" ++ r))
        , (2, do
              x  <- genName
              ty <- genTerm' scope 1
              g  <- genDevelopment scope (n - 2)
              r  <- genDevelopment (x : scope) (n - 1)
              pure ("let ? " ++ x ++ " : " ++ ty ++ " ≐ (\n" ++ g ++ "\n) in\n" ++ r))
          -- A constraint binds nothing, so the scope does not grow — but Ξ's
          -- own binders scope over the equation and nowhere else (§3.3).
        , (1, do
              y     <- genName
              yty   <- genTerm' scope 1
              inner <- elements [True, False]
              let below = if inner then y : scope else scope
              a  <- genTerm' below 1
              b  <- genTerm' below 1
              ty <- genTerm' below 1
              r  <- genDevelopment scope (n - 1)
              let xi = if inner then "(" ++ y ++ " : " ++ yty ++ ") " else ""
              pure (xi ++ "⊢ " ++ a ++ " ≟ " ++ b ++ " : " ++ ty ++ " ▸\n" ++ r))
        ]

-- | A written core term over @scope@.
--
-- **Every compound form is parenthesised**, so that a generated term can stand
-- as a development's trailing term without a leading @λ@ being read as one more
-- link — which is a real reading of the grammar and not something to generate
-- around by accident.
genTerm' :: [String] -> Int -> Gen String
genTerm' scope n
  | n <= 0 = atom
  | otherwise =
      oneof
        [ atom
        , do { a <- half; b <- half; pure ("(" ++ a ++ " -> " ++ b ++ ")") }
        , do { f <- half; a <- half; pure ("(" ++ f ++ " " ++ a ++ ")") }
        , do
            x <- genName
            t <- half
            b <- genTerm' (x : scope) (n - 1)
            k <- elements ["λ", "∀"]
            pure ("(" ++ k ++ " (" ++ x ++ " : " ++ t ++ ") -> " ++ b ++ ")")
        , do
            x <- genName
            v <- half
            t <- half
            b <- genTerm' (x : scope) (n - 1)
            pure ("(let " ++ x ++ " = " ++ v ++ " : " ++ t ++ " in " ++ b ++ ")")
        ]
  where
    half = genTerm' scope (n - 1)
    atom
      | null scope = universe
      | otherwise  = oneof [universe, elements scope]
    universe = elements ["Type₀", "Type₁"]

-- | Four names, so that shadowing happens often rather than never.
genName :: Gen String
genName = elements ["x", "y", "A", "h"]

-- --------------------------------------------------------------------------
-- forget — §3.2's table, as four cases
-- --------------------------------------------------------------------------

forgetTests :: [TestTree]
forgetTests =
  [ testCase "an assumption keeps its type" $
      forget (Assume v (Ident "x") ty) @?= Hypothesis v (Ident "x") ty
  , testCase "a definition keeps its value and its type" $
      forget (Define v (Ident "x") val ty) @?= Definition v (Ident "x") val ty
  , testCase "a hole forgets to a hypothesis" $
      forget (Claim v (Ident "x") ty) @?= Hypothesis v (Ident "x") ty
  , testCase "a guess drops its body — guesses are invisible to the core" $
      forget (Guess v (Ident "x") (Trailing val) ty) @?= Hypothesis v (Ident "x") ty
  ]
  where
    (v, _) = fresh 0
    ty     = Universe (LZero)
    val    = Universe (LZero)

-- --------------------------------------------------------------------------
-- Rendering, as exact strings. These are what pin the printer down (§7).
-- --------------------------------------------------------------------------

renderTests :: [TestTree]
renderTests =
  [ testCase "the running example" $
      renderPartial [] 500 [] idMidway
        @?= unlines'
          [ "λ (A : Type₀) ->"
          , "let ? id' : A -> A ≐ ("
          , "  λ (a : A) ->"
          , "  let ? h : A in"
          , "  h"
          , ") in"
          , "id'"
          ]
  , testCase "a constraint, with a non-empty Ξ" $
      renderPartial [] 500 [] withConstraint
        @?= unlines'
          [ "λ (A : Type₀) ->"
          , "λ (a : A) ->"
          , "let ? h : A in"
          , "(x : A) ⊢ h ≟ x : A ▸"
          , "h"
          ]
  , testCase "one link of each kind" $
      renderPartial [] 500 [] allFour
        @?= unlines'
          [ "λ (A : Type₀) ->"
          , "let d = A : Type₀ in"
          , "let ? h : A in"
          , "let ? g : A ≐ ("
          , "  h"
          , ") in"
          , "g"
          ]
  , testCase "a shadowed chain binder is freshened" $
      renderPartial [] 500 [] shadowedBinders
        @?= unlines' [ "λ (x : Type₀) ->", "λ (x1 : Type₀) ->", "x" ]
  , testCase "a guess body does not see the hole's name, so nothing is freshened" $
      renderPartial [] 500 [] guessShadowing
        @?= unlines'
          [ "let ? x : Type₀ ≐ ("
          , "  λ (x : Type₀) ->"
          , "  x"
          , ") in"
          , "x"
          ]
  , testCase "a trailing binder is quoted, or it would re-read as a link" $
      renderPartial [] 500 [] trailingLam @?= "⌜ λ (A : Type₀) -> A ⌝"
  ]

-- | 'unlines' appends a trailing newline; 'renderPartial' does not emit one.
unlines' :: [String] -> String
unlines' = foldr1 (\a b -> a ++ "\n" ++ b)

-- --------------------------------------------------------------------------
-- Longest prefix, pinned against hand-built values (§7.2 — the round trip
-- cannot see any of these).
-- --------------------------------------------------------------------------

prefixTests :: [TestTree]
prefixTests =
  [ testCase "a leading λ becomes a chain link, not a trailing Lam" $
      fmap fst (parseDevelopment [] emptyGlobals [] 0 "λ (A : Type₀) -> A")
        @?= Right (Under (Assume vA (Ident "A") type0) (Trailing (Free vA)))
  , testCase "corners stop the spine" $
      fmap fst (parseDevelopment [] emptyGlobals [] 0 "[| λ (A : Type₀) -> A |]")
        @?= Right (Trailing (Lam (Ident "A") type0 (close vA (Free vA))))
  , testCase "and those two are genuinely different developments" $
      assertBool "chain link and trailing Lam must differ" $
        fmap fst (parseDevelopment [] emptyGlobals [] 0 "λ (A : Type₀) -> A")
          /= fmap fst (parseDevelopment [] emptyGlobals [] 0 "[| λ (A : Type₀) -> A |]")
  , testCase "a leading let becomes a Define link" $
      fmap fst (parseDevelopment [] emptyGlobals [] 0 "let d = Type₀ : Type₁ in d")
        @?= Right (Under (Define vA (Ident "d") type0 (Universe (levelOfNat 1)))
                     (Trailing (Free vA)))
  , testCase "several binder groups become several links" $
      fmap fst (parseDevelopment [] emptyGlobals [] 0 "λ (A : Type₀) (B : Type₀) -> B")
        @?= Right
              (Under (Assume vA (Ident "A") type0)
                (Under (Assume vB (Ident "B") type0)
                  (Trailing (Free vB))))
    -- **A leading @∀@ run is links, exactly as a leading @λ@ run is** (MS4
    -- phase 41f). This asserted the opposite until then, when the development
    -- calculus had no ∀-binder to read one as.
  , testCase "a leading ∀ becomes a Quantify link" $
      fmap fst (parseDevelopment [] emptyGlobals [] 0 "∀ (A : Type₀) -> A")
        @?= Right (Under (Quantify vA (Ident "A") type0) (Trailing (Free vA)))
    -- And the same escape the λ case has: corners stop the spine, so a
    -- trailing Π is still writable.
  , testCase "corners keep a ∀ in the trailing term" $
      fmap fst (parseDevelopment [] emptyGlobals [] 0 "[| ∀ (A : Type₀) -> A |]")
        @?= Right (Trailing (Pi (Ident "A") type0 (close vA (Free vA))))
  ]
  where
    type0    = Universe (LZero)
    (vA, n1) = fresh 0
    (vB, _)  = fresh n1

-- --------------------------------------------------------------------------
-- Scope. Γ_(?x ≐ P : S . p) = Γ_P — a guess body cannot see its own hole.
-- --------------------------------------------------------------------------

scopeTests :: [TestTree]
scopeTests =
  [ testCase "a guess body does not see the hole it fills" $
      fmap fst (parseDevelopment [] emptyGlobals [] 0 "λ (h : Type₀) -> let ? h : Type₀ ≐ (h) in h")
        @?= Right
              (Under (Assume vOuter (Ident "h") type0)
                (Under (Guess vHole (Ident "h")
                          (Trailing (Free vOuter))   -- the λ's h, not the hole
                          type0)
                  (Trailing (Free vHole))))
  , testCase "so a guess naming only its own hole is a scope error" $
      isLeft (parseDevelopment [] emptyGlobals [] 0 "let ? h : Type₀ ≐ (h) in h") @?= True
  , testCase "a definition's value does not see its own name" $
      isLeft (parseDevelopment [] emptyGlobals [] 0 "let d = d : Type₀ in d") @?= True
  , testCase "a hole's type does not see its own name" $
      isLeft (parseDevelopment [] emptyGlobals [] 0 "let ? h : h in h") @?= True
  , testCase "Ξ's binders scope over the equation" $
      isLeft (parseDevelopment [] emptyGlobals [] 0
                "let ? h : Type₀ in (x : Type₀) |- h ?= x : Type₀ |> h") @?= False
  , testCase "but not over the rest of the chain" $
      isLeft (parseDevelopment [] emptyGlobals [] 0
                "let ? h : Type₀ in (x : Type₀) |- h ?= x : Type₀ |> x") @?= True
  ]
  where
    type0        = Universe (LZero)
    (vOuter, n1) = fresh 0
    (vHole, _)   = fresh n1

-- --------------------------------------------------------------------------

roundTripTests :: [TestTree]
roundTripTests =
  [ testCase (name ++ " survives print then read") $
      reprint p @?= renderPartial [] 500 [] p
  | (name, p) <-
      [ ("the running example", idMidway)
      , ("a constraint", withConstraint)
      , ("one of each", allFour)
      , ("shadowed binders", shadowedBinders)
      , ("a guess shadowing its hole", guessShadowing)
      , ("a trailing binder", trailingLam)
      ]
  ]

-- | Print, read, print again.
--
-- NOT @parse . render == id@: 'Eq' on 'Partial' is derived, so it compares
-- 'Var's literally and re-reading mints fresh ones. Comparing the two renders
-- is the property that holds, and a failure shows the difference.
--
-- **The second render uses the counter the parse handed back**, not the one it
-- started with. Rendering with the earlier counter lets the printer mint a
-- 'Var' that collides with one already in the term — which is not
-- hypothetical: it silently turned @A -> A@ into @∀ (_ : A) -> _@ while this
-- suite was being written (§13e).
reprint :: Partial -> String
reprint p = case parseDevelopment [] emptyGlobals [] 500 (renderPartial [] 500 [] p) of
  Right (p', n) -> renderPartial [] n [] p'
  Left e        -> "PARSE FAILED: " ++ show e

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _        = False
