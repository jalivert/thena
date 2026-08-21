module Thena.SyntaxTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))
import Test.Tasty.QuickCheck
  ( Gen
  , elements
  , forAll
  , oneof
  , resize
  , sized
  , testProperty
  )

import Thena.Core.Term
  ( Core (..)
  , Ident (..)
  , Level (..)
  , close
  , fresh
  )
import Thena.Driver (parseCore)
import Thena.Repl (renderCore)
import Thena.Syntax.Concrete (Raw (..), RawBinder (..))
import Thena.Syntax.Resolve (resolve)

-- | Resolve, render, re-resolve. The property everything else supports.
roundTrips :: Core -> Int -> Bool
roundTrips t n = case parseCore n (renderCore n t) of
  Right (t', _) -> t' == t
  Left _        -> False

-- --------------------------------------------------------------------------
-- Generating closed terms
-- --------------------------------------------------------------------------

-- | A small pool, so that shadowing happens often rather than rarely.
namePool :: [String]
namePool = ["x", "y", "f"]

-- | Raw trees that are closed by construction: a name is only ever generated
-- when it is in scope. Phase 2's subset only — no 'Canonical', no 'Eliminate',
-- which have no concrete syntax yet (§2.6).
genRaw :: [String] -> Gen Raw
genRaw = sized . go
  where
    go scope n
      | n <= 1    = leaf scope
      | otherwise = oneof [leaf scope, node scope n]

    leaf scope =
      oneof $
        (RawUniverse <$> elements [0, 1])
          : [RawName <$> elements scope | not (null scope)]

    node scope n =
      oneof
        [ RawApp <$> half <*> half
        , RawArrow <$> half <*> half
        , binder RawLam
        , binder RawPi
        , do
            x <- elements namePool
            v <- half
            ty <- half
            b <- resize (n `div` 2) (genRaw (x : scope))
            pure (RawLet x v ty b)
        ]
      where
        half = resize (n `div` 2) (genRaw scope)
        binder con = do
          x <- elements namePool
          ty <- half
          b <- resize (n `div` 2) (genRaw (x : scope))
          pure (con [RawBinder x ty] b)

-- | 'genRaw' only ever names something in scope, so resolution cannot fail; if
-- it ever does, the generator is wrong and the test should say so loudly.
genClosed :: Gen Core
genClosed = do
  raw <- genRaw []
  case resolve [] 0 raw of
    Right (t, _) -> pure t
    Left e       -> error ("generator produced an unresolvable term: " ++ show e)

-- --------------------------------------------------------------------------

tests :: TestTree
tests =
  testGroup
    "Thena.Syntax"
    [ testGroup "round trip" roundTripTests
    , testGroup "rendering" renderTests
    , testGroup "input spellings" inputTests
    , testGroup "errors" errorTests
    , testGroup "shadowing" shadowTests
    , testGroup "resolution" resolveTests
    ]

roundTripTests :: [TestTree]
roundTripTests =
  [ testProperty "parse . render is the identity on closed terms" $
      forAll genClosed $ \t -> roundTrips t 500
  ]

-- Rendering, as exact strings. These, not the round trip, are what pin the
-- printer down — see §7.
renderTests :: [TestTree]
renderTests =
  [ testCase "identity function" $
      render "λ (x : Type₀) -> x" @?= "λ (x : Type₀) -> x"
  , testCase "dependent function type keeps its ∀" $
      render "∀ (A : Type₀) -> A -> A" @?= "∀ (A : Type₀) -> A -> A"
  , testCase "a non-dependent Pi prints as an arrow" $
      render "∀ (A : Type₀) -> Type₀" @?= "Type₀ -> Type₀"
  , testCase "binder groups collapse when both are dependent" $
      render "∀ (A : Type₀) -> ∀ (x : A) -> x" @?= "∀ (A : Type₀) (x : A) -> x"
  , testCase "a non-dependent binder ends the run" $
      render "∀ (A : Type₀) -> ∀ (x : A) -> A" @?= "∀ (A : Type₀) -> A -> A"
  , testCase "λ groups collapse too" $
      render "λ (A : Type₀) -> λ (x : A) -> x" @?= "λ (A : Type₀) (x : A) -> x"
  , testCase "arrows are right associative" $
      render "(Type₀ -> Type₀) -> Type₀" @?= "(Type₀ -> Type₀) -> Type₀"
  , testCase "application is left associative" $
      render "λ (f : Type₀) (x : Type₀) (y : Type₀) -> f x y"
        @?= "λ (f : Type₀) (x : Type₀) (y : Type₀) -> f x y"
  , testCase "an argument that is an application is parenthesised" $
      render "λ (f : Type₀) (x : Type₀) -> f (f x)"
        @?= "λ (f : Type₀) (x : Type₀) -> f (f x)"
  , testCase "let" $
      render "let x = Type₀ : Type₁ in x" @?= "let x = Type₀ : Type₁ in x"
  , testCase "a higher universe" $
      render "Type₁₀" @?= "Type₁₀"
  ]

-- Both spellings parse; only one is printed (§2.6).
inputTests :: [TestTree]
inputTests =
  [ testCase "backslash prints as λ" $
      render "\\ (x : Type₀) -> x" @?= "λ (x : Type₀) -> x"
  , testCase "forall prints as ∀" $
      render "forall (A : Type₀) -> A -> A" @?= "∀ (A : Type₀) -> A -> A"
  , testCase "Type0 prints as Type₀" $
      render "Type0" @?= "Type₀"
  , testCase "ASCII and unicode agree" $
      parseCore 0 "\\ (x : Type0) -> x" @?= parseCore 0 "λ (x : Type₀) -> x"
  ]

errorTests :: [TestTree]
errorTests =
  [ testCase "an unbound name is a scope error" $
      isLeft (parseCore 0 "y") @?= True
  , testCase "a λ with no body is a parse error" $
      isLeft (parseCore 0 "λ (x : Type₀)") @?= True
  , testCase "a stray character is a lex error" $
      isLeft (parseCore 0 "x # y") @?= True
  ]

-- | The case that cannot be written in concrete syntax and must still print
-- correctly: two nested binders with the same identifier, where the body refers
-- to the /outer/ one. Without freshening this prints as
-- @λ (x : _) (x : _) -> x@ and re-parses to the inner binder — a different term.
shadowTests :: [TestTree]
shadowTests =
  [ testCase "the inner binder is renamed, so the body still reparses" $
      assertBool (renderCore 500 shadowed) (roundTrips shadowed 500)
  , testCase "and the two binders really do print differently" $
      renderCore 500 shadowed @?= "λ (x : Type₀) (x1 : Type₀) -> x"
  ]

shadowed :: Core
shadowed =
  let (v1, n1) = fresh 0
      (v2, _)  = fresh n1
      ty       = Universe (Level 0)
   in Lam (Ident "x") ty (close v1 (Lam (Ident "x") ty (close v2 (Free v1))))

-- | Pinned against hand-built terms, because the round trip cannot see these:
-- it resolves twice with the same rule, so a wrong rule agrees with itself.
resolveTests :: [TestTree]
resolveTests =
  [ testCase "an inner binder shadows an outer one of the same name" $
      fmap fst (parseCore 0 "λ (x : Type₀) -> λ (x : Type₁) -> x")
        @?= Right (nestedLam Inner)
  , testCase "and that is not the same term as referring to the outer" $
      assertBool "inner and outer must differ" (nestedLam Inner /= nestedLam Outer)
  ]

data Which = Inner | Outer

-- | @λ (x : Type₀) -> λ (x : Type₁) -> x@, with the body referring to whichever
-- binder is asked for.
nestedLam :: Which -> Core
nestedLam which =
  let (v1, n1) = fresh 0
      (v2, _)  = fresh n1
      body     = Free (case which of Inner -> v2; Outer -> v1)
   in Lam (Ident "x") (Universe (Level 0))
        (close v1 (Lam (Ident "x") (Universe (Level 1)) (close v2 body)))

render :: String -> String
render src = case parseCore 0 src of
  Right (t, n) -> renderCore n t
  Left e       -> "ERROR: " ++ show e

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _        = False
