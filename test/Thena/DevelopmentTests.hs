module Thena.DevelopmentTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))

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
    ]

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
      renderPartial 500 [] idMidway
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
      renderPartial 500 [] withConstraint
        @?= unlines'
          [ "λ (A : Type₀) ->"
          , "λ (a : A) ->"
          , "let ? h : A in"
          , "(x : A) ⊢ h ≟ x : A ▸"
          , "h"
          ]
  , testCase "one link of each kind" $
      renderPartial 500 [] allFour
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
      renderPartial 500 [] shadowedBinders
        @?= unlines' [ "λ (x : Type₀) ->", "λ (x1 : Type₀) ->", "x" ]
  , testCase "a guess body does not see the hole's name, so nothing is freshened" $
      renderPartial 500 [] guessShadowing
        @?= unlines'
          [ "let ? x : Type₀ ≐ ("
          , "  λ (x : Type₀) ->"
          , "  x"
          , ") in"
          , "x"
          ]
  , testCase "a trailing binder is quoted, or it would re-read as a link" $
      renderPartial 500 [] trailingLam @?= "⌜ λ (A : Type₀) -> A ⌝"
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
      fmap fst (parseDevelopment emptyGlobals [] 0 "λ (A : Type₀) -> A")
        @?= Right (Under (Assume vA (Ident "A") type0) (Trailing (Free vA)))
  , testCase "corners stop the spine" $
      fmap fst (parseDevelopment emptyGlobals [] 0 "[| λ (A : Type₀) -> A |]")
        @?= Right (Trailing (Lam (Ident "A") type0 (close vA (Free vA))))
  , testCase "and those two are genuinely different developments" $
      assertBool "chain link and trailing Lam must differ" $
        fmap fst (parseDevelopment emptyGlobals [] 0 "λ (A : Type₀) -> A")
          /= fmap fst (parseDevelopment emptyGlobals [] 0 "[| λ (A : Type₀) -> A |]")
  , testCase "a leading let becomes a Define link" $
      fmap fst (parseDevelopment emptyGlobals [] 0 "let d = Type₀ : Type₁ in d")
        @?= Right (Under (Define vA (Ident "d") type0 (Universe (levelOfNat 1)))
                     (Trailing (Free vA)))
  , testCase "several binder groups become several links" $
      fmap fst (parseDevelopment emptyGlobals [] 0 "λ (A : Type₀) (B : Type₀) -> B")
        @?= Right
              (Under (Assume vA (Ident "A") type0)
                (Under (Assume vB (Ident "B") type0)
                  (Trailing (Free vB))))
    -- **A leading @∀@ run is links, exactly as a leading @λ@ run is** (MS4
    -- phase 41f). This asserted the opposite until then, when the development
    -- calculus had no ∀-binder to read one as.
  , testCase "a leading ∀ becomes a Quantify link" $
      fmap fst (parseDevelopment emptyGlobals [] 0 "∀ (A : Type₀) -> A")
        @?= Right (Under (Quantify vA (Ident "A") type0) (Trailing (Free vA)))
    -- And the same escape the λ case has: corners stop the spine, so a
    -- trailing Π is still writable.
  , testCase "corners keep a ∀ in the trailing term" $
      fmap fst (parseDevelopment emptyGlobals [] 0 "[| ∀ (A : Type₀) -> A |]")
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
      fmap fst (parseDevelopment emptyGlobals [] 0 "λ (h : Type₀) -> let ? h : Type₀ ≐ (h) in h")
        @?= Right
              (Under (Assume vOuter (Ident "h") type0)
                (Under (Guess vHole (Ident "h")
                          (Trailing (Free vOuter))   -- the λ's h, not the hole
                          type0)
                  (Trailing (Free vHole))))
  , testCase "so a guess naming only its own hole is a scope error" $
      isLeft (parseDevelopment emptyGlobals [] 0 "let ? h : Type₀ ≐ (h) in h") @?= True
  , testCase "a definition's value does not see its own name" $
      isLeft (parseDevelopment emptyGlobals [] 0 "let d = d : Type₀ in d") @?= True
  , testCase "a hole's type does not see its own name" $
      isLeft (parseDevelopment emptyGlobals [] 0 "let ? h : h in h") @?= True
  , testCase "Ξ's binders scope over the equation" $
      isLeft (parseDevelopment emptyGlobals [] 0
                "let ? h : Type₀ in (x : Type₀) |- h ?= x : Type₀ |> h") @?= False
  , testCase "but not over the rest of the chain" $
      isLeft (parseDevelopment emptyGlobals [] 0
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
      reprint p @?= renderPartial 500 [] p
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
reprint p = case parseDevelopment emptyGlobals [] 500 (renderPartial 500 [] p) of
  Right (p', n) -> renderPartial n [] p'
  Left e        -> "PARSE FAILED: " ++ show e

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _        = False
