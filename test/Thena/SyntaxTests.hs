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

import Thena.Core.Level (Level (..), LevelVar (..), levelOfNat)
import Thena.Core.Term
  ( Core (..)
  , Ident (..)
  , close
  , fresh
  )
import Thena.Driver (parseCore, parseDeclaration)
import Thena.Global.Declare (declare)
import Thena.Global.Env (GlobalEnv, emptyGlobals)
import Thena.Repl (renderCore)
import Thena.Syntax.Concrete (Raw (..), RawBinder (..))
import Thena.Syntax.Resolve (resolve)

-- | The environment the generator resolves against.
--
-- @Nat@ is declared so that 'genRaw' can build @elim@ nodes (§2.6, phase 7):
-- an @elim@\'s head must name a real datatype and its parameter, method and
-- index counts are checked against that datatype's record, so there is no way
-- to generate one against an empty environment. Nothing else changes — the
-- generator's own names are 'namePool', which shares nothing with @Nat@'s.
natEnv :: GlobalEnv
natEnv = case parseDeclaration emptyGlobals 0 decl of
  Left e -> error ("generator fixture does not parse: " ++ show e)
  Right (d, n) -> case declare emptyGlobals n d of
    Left e            -> error ("generator fixture refused: " ++ show e)
    Right (env, _, _) -> env
  where
    decl = "Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"

-- | Resolve, render, re-resolve. The property everything else supports.
roundTrips :: Core -> Int -> Bool
roundTrips t n = case parseCore natEnv [] n (renderCore n [] t) of
  Right (t', _) -> t' == t
  Left _        -> False

-- --------------------------------------------------------------------------
-- Generating closed terms
-- --------------------------------------------------------------------------

-- | A small pool, so that shadowing happens often rather than rarely.
namePool :: [String]
namePool = ["x", "y", "f"]

-- | Raw trees that are closed by construction: a name is only ever generated
-- when it is in scope.
--
-- Covers phase 2's subset **and** phase 7's @elim@. It still never generates a
-- 'Canonical' — the user cannot write one and the resolver never builds one
-- (§3.6), so no raw tree corresponds to it.
--
-- The @elim@ case is what pins the printer's parenthesisation of a form whose
-- fields are grammar @atom@s rather than @term@s: a 'RawLam' motive has to come
-- back parenthesised or the methods group after it is swallowed, and only a
-- generator that puts arbitrary terms in those positions will keep finding
-- that. Added 2026-08-22 — the phase-7 plan claimed this coverage before it
-- existed.
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
        , -- Nat has no parameters, no indices, and two constructors, so the
          -- shape is fixed: () motive (mz ms) ().
          RawElim "Nat" [] [] <$> half <*> ((\a b -> [a, b]) <$> half <*> half)
                              <*> pure [] <*> half
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
  case resolve natEnv [] 0 raw of
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
    , testGroup "a bare Type mints a level meta" openUniverseTests
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
      parseCore emptyGlobals [] 0 "\\ (x : Type0) -> x" @?= parseCore emptyGlobals [] 0 "λ (x : Type₀) -> x"
  ]

errorTests :: [TestTree]
errorTests =
  [ testCase "an unbound name is a scope error" $
      isLeft (parseCore emptyGlobals [] 0 "y") @?= True
  , testCase "a λ with no body is a parse error" $
      isLeft (parseCore emptyGlobals [] 0 "λ (x : Type₀)") @?= True
  , testCase "a stray character is a lex error" $
      isLeft (parseCore emptyGlobals [] 0 "x # y") @?= True
  ]

-- | The case that cannot be written in concrete syntax and must still print
-- correctly: two nested binders with the same identifier, where the body refers
-- to the /outer/ one. Without freshening this prints as
-- @λ (x : _) (x : _) -> x@ and re-parses to the inner binder — a different term.
shadowTests :: [TestTree]
shadowTests =
  [ testCase "the inner binder is renamed, so the body still reparses" $
      assertBool (renderCore 500 [] shadowed) (roundTrips shadowed 500)
  , testCase "and the two binders really do print differently" $
      renderCore 500 [] shadowed @?= "λ (x : Type₀) (x1 : Type₀) -> x"
  ]

shadowed :: Core
shadowed =
  let (v1, n1) = fresh 0
      (v2, _)  = fresh n1
      ty       = Universe (LZero)
   in Lam (Ident "x") ty (close v1 (Lam (Ident "x") ty (close v2 (Free v1))))

-- | Pinned against hand-built terms, because the round trip cannot see these:
-- it resolves twice with the same rule, so a wrong rule agrees with itself.
resolveTests :: [TestTree]
resolveTests =
  [ testCase "an inner binder shadows an outer one of the same name" $
      fmap fst (parseCore emptyGlobals [] 0 "λ (x : Type₀) -> λ (x : Type₁) -> x")
        @?= Right (nestedLam Inner)
  , testCase "and that is not the same term as referring to the outer" $
      assertBool "inner and outer must differ" (nestedLam Inner /= nestedLam Outer)

  -- @elim@'s head is a name like any other (decided 2026-08-22). As first
  -- written it went straight to the inductive table, so a binder shadowing a
  -- datatype's name was silently ignored — and because the head always
  -- resolved globally, the term still round-tripped, which is why no test
  -- could see it. Pinned here rather than left to the round trip for exactly
  -- that reason.
  , testCase "a binder shadowing a datatype's name shadows it for elim too" $
      isLeft (parseCore natEnv [] 0
                "λ (Nat : Type₀) -> elim Nat () zero (zero zero) () zero")
        @?= True
  , testCase "and unshadowed, the same elim resolves" $
      isLeft (parseCore natEnv [] 0 "elim Nat () zero (zero zero) () zero")
        @?= False
  ]

-- --------------------------------------------------------------------------
-- Bare @Type@ (MS3 phase 33)
-- --------------------------------------------------------------------------

-- | @Type@ with no braces is a universe whose level is worked out rather than
-- written. It was a **parse error** before this phase, which is why nothing
-- that already existed can have changed meaning.
openUniverseTests :: [TestTree]
openUniverseTests =
  [ testCase "it resolves to a meta drawn from the counter it was given" $
      parseCore emptyGlobals [] 40 "Type"
        @?= Right (Universe (LVar (LMeta 40)), 41)

  , -- Two universes written in one term are two unknowns, not one. Writing them
    -- equal is what the *checker* may conclude, never what the reader wrote.
    testCase "each one written is its own meta" $
      fmap fst (parseCore emptyGlobals [] 40 "Type -> Type")
        @?= Right (arrowOf (Universe (LVar (LMeta 40))) (Universe (LVar (LMeta 41))))

  , testCase "and Typeₙ is still exactly the level written" $
      fmap fst (parseCore emptyGlobals [] 40 "Type\8321")
        @?= Right (Universe (levelOfNat 1))

  , -- A datatype's levels are stored and instantiated at every use, so a meta in
    -- one would be shared rather than solved. Phase 33c makes them inferred;
    -- until then a declaration says its level.
    testCase "a declaration may not write one" $
      isLeft (parseDeclaration emptyGlobals 0 "data Box : Type where { }") @?= True

  , testCase "not even in a parameter it never mentions again" $
      isLeft (parseDeclaration emptyGlobals 0
                "data Box (A : Type) : Type\8320 where { }") @?= True
  ]
  where
    -- The counter that 'parseCore' spends on the arrow's own binder is why this
    -- reads @fmap fst@: what is under test is which metas were minted.
    arrowOf dom cod = Pi (Ident "_") dom (close (fst (fresh 42)) cod)

data Which = Inner | Outer

-- | @λ (x : Type₀) -> λ (x : Type₁) -> x@, with the body referring to whichever
-- binder is asked for.
nestedLam :: Which -> Core
nestedLam which =
  let (v1, n1) = fresh 0
      (v2, _)  = fresh n1
      body     = Free (case which of Inner -> v2; Outer -> v1)
   in Lam (Ident "x") (Universe (LZero))
        (close v1 (Lam (Ident "x") (Universe (levelOfNat 1)) (close v2 body)))

render :: String -> String
render src = case parseCore emptyGlobals [] 0 src of
  Right (t, n) -> renderCore n [] t
  Left e       -> "ERROR: " ++ show e

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _        = False
