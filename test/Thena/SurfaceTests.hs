{-# LANGUAGE OverloadedLists #-}

-- | The surface language's tree and its parser (MS4 phase 39).
--
-- **Exact trees, not round trips.** The standing lesson from phases 2–5 is that
-- @parse . render == id@ can pass while a real bug hides, because a
-- self-consistent error agrees with itself. So every case here either builds
-- the tree by hand and compares, or pins an exact string — and the round trip
-- is a third check on top, over a fixed corpus, never the only one.
module Thena.SurfaceTests (tests) where

import Data.List.NonEmpty (NonEmpty (..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertFailure, testCase, (@?=))

import Thena.Repl (renderSurface)
import Thena.Surface.Concrete
  ( Plicity (..)
  , Surface (..)
  , SurfaceArg (..)
  , SurfaceBinder (..)
  )
import Thena.Surface.Parser (parseSurface)
import Thena.Syntax.Lexer (lexTokens)

tests :: TestTree
tests =
  testGroup
    "the surface language (MS4)"
    [ testGroup "application is a spine" spineTests
    , testGroup "placeholders and holes" holeTests
    , testGroup "binders" binderTests
    , testGroup "precedence" precedenceTests
    , testGroup "it prints as it was written" renderTests
    ]

-- --------------------------------------------------------------------------
-- The spine
-- --------------------------------------------------------------------------

spineTests :: [TestTree]
spineTests =
  [ -- **One node, two arguments — not two nested nodes.** This is the decision
    -- the whole AST turns on: phase 44's @EXPAND@ needs the argument list whole
    -- to know where the implicit positions fall.
    parses "f a b"
      (SurfaceApp (SurfaceName "f")
         (SurfaceArg Explicit (SurfaceName "a") :| [SurfaceArg Explicit (SurfaceName "b")]))

    -- **Parentheses are not represented**, so these are the same term and the
    -- tree says so. Two application constructors would have made them two
    -- forms of one thing.
  , testCase "and (f a) b is the same tree as f a b" $
      tree "(f a) b" >>= \a -> tree "f a b" >>= \b -> a @?= b

    -- **An empty argument list is not constructible**, which is his ruling:
    -- a head with no arguments is the head.
  , parses "f" (SurfaceName "f")

  , parses "f (g a)"
      (SurfaceApp (SurfaceName "f")
         [SurfaceArg Explicit
            (SurfaceApp (SurfaceName "g") [SurfaceArg Explicit (SurfaceName "a")])])

    -- The head may be anything, which is why one constructor is enough.
  , parses "(\\ x -> x) a"
      (SurfaceApp (SurfaceLam [SurfaceBinder Explicit "x" Nothing] (SurfaceName "x"))
         [SurfaceArg Explicit (SurfaceName "a")])

  , parses "f {A} a"
      (SurfaceApp (SurfaceName "f")
         (SurfaceArg Implicit (SurfaceName "A") :| [SurfaceArg Explicit (SurfaceName "a")]))
  ]

-- --------------------------------------------------------------------------
-- _ and ?foo
-- --------------------------------------------------------------------------

holeTests :: [TestTree]
holeTests =
  [ parses "_" SurfacePlaceholder
  , parses "?goal" (SurfaceHole "goal")

    -- **Neither is a lexer rule**, and this is what that buys: a name may still
    -- contain both characters. @_@ alone is the placeholder and @_foo@ is a
    -- name, exactly as @PLAN-interface.md@ §2.6 says a name may start with @_@.
  , parses "_foo" (SurfaceName "_foo")
  , parses "foo?" (SurfaceName "foo?")

    -- @?@ cannot start an identifier, so this really is two tokens and the
    -- grammar puts them together. Spaced, it means the same thing.
  , testCase "?goal and ? goal are the same tree" $
      tree "?goal" >>= \a -> tree "? goal" >>= \b -> a @?= b

  , refuses "?"
  ]

-- --------------------------------------------------------------------------
-- Binders
-- --------------------------------------------------------------------------

binderTests :: [TestTree]
binderTests =
  [ -- **The main thing the surface has that the development calculus does
    -- not.** His ruling: lambdas only — @let@, @∀@ and a signature keep theirs.
    parses "\\ x -> x"
      (SurfaceLam [SurfaceBinder Explicit "x" Nothing] (SurfaceName "x"))
  , refuses "∀ x -> x"

  , parses "\\ (x : A) -> x"
      (SurfaceLam [SurfaceBinder Explicit "x" (Just (SurfaceName "A"))] (SurfaceName "x"))

    -- A group is a spelling, not a structure: it expands, **in order**.
  , parses "∀ (x y : A) -> x"
      (SurfacePi (SurfaceBinder Explicit "x" (Just (SurfaceName "A"))
                    :| [SurfaceBinder Explicit "y" (Just (SurfaceName "A"))])
         (SurfaceName "x"))

  , parses "\\ {A} x -> x"
      (SurfaceLam (SurfaceBinder Implicit "A" Nothing
                     :| [SurfaceBinder Explicit "x" Nothing])
         (SurfaceName "x"))
  , parses "∀ {A : Type} -> A"
      (SurfacePi [SurfaceBinder Implicit "A" (Just SurfaceUniverseOpen)] (SurfaceName "A"))

    -- @let@ keeps its annotation optional here and required in the development
    -- calculus, where there is nothing to infer it with.
  , parses "let x = a in x"
      (SurfaceLet "x" Nothing (SurfaceName "a") (SurfaceName "x"))
  , parses "let x : A = a in x"
      (SurfaceLet "x" (Just (SurfaceName "A")) (SurfaceName "a") (SurfaceName "x"))
  ]

-- --------------------------------------------------------------------------
-- Precedence
-- --------------------------------------------------------------------------

precedenceTests :: [TestTree]
precedenceTests =
  [ -- **Ascription binds loosest**, which is the reading Agda and Haskell both
    -- give it: the lambda is ascribed, not its body.
    parses "\\ x -> x : A"
      (SurfaceAnnot (SurfaceLam [SurfaceBinder Explicit "x" Nothing] (SurfaceName "x"))
         (SurfaceName "A"))

  , parses "A -> B -> C"
      (SurfaceArrow (SurfaceName "A")
         (SurfaceArrow (SurfaceName "B") (SurfaceName "C")))

  , parses "f a -> b"
      (SurfaceArrow
         (SurfaceApp (SurfaceName "f") [SurfaceArg Explicit (SurfaceName "a")])
         (SurfaceName "b"))

  , parses "Type₀ -> Type"
      (SurfaceArrow (SurfaceUniverse 0) SurfaceUniverseOpen)
  ]

-- --------------------------------------------------------------------------
-- Rendering
-- --------------------------------------------------------------------------

-- | Exact strings, and then the round trip on the same corpus.
--
-- The round trip is the weaker of the two and is here as a second opinion: it
-- would pass on a printer and parser that agreed with each other and with
-- nothing else, which the exact strings above rule out.
renderTests :: [TestTree]
renderTests =
  concatMap
    (\src -> [ testCase ("renders: " ++ src) (rendered src src)
             , testCase ("round trips: " ++ src) (roundTrips src)
             ])
    corpus

corpus :: [String]
corpus =
  [ "f a b"
  , "f (g a)"
  , "f {A} a"
  , "λ x (y : A) -> x"
  , "λ {A} (x : A) -> x"
  , "∀ (A : Type) (B : Type) -> A -> B"
  , "∀ {A : Type₀} -> A -> A"
  , "let x = a in x"
  , "let x : A = a in x"
  , "x : A -> A"
  , "(λ x -> x) a"
  , "f _ ?goal"
  , "elim Nat () (λ (z : Nat) -> Nat) (zero (λ k ih -> ih)) () n"
  ]

-- --------------------------------------------------------------------------
-- Helpers
-- --------------------------------------------------------------------------

tree :: String -> IO Surface
tree src = case lexTokens src of
  Left e   -> assertFailure (src ++ ": " ++ show e)
  Right ts -> case parseSurface ts of
    Left e  -> assertFailure (src ++ ": " ++ show e)
    Right t -> pure t

parses :: String -> Surface -> TestTree
parses src expected = testCase src (tree src >>= (@?= expected))

refuses :: String -> TestTree
refuses src = testCase ("refused: " ++ src) $
  case lexTokens src of
    Left _   -> pure ()
    Right ts -> case parseSurface ts of
      Left _  -> pure ()
      Right t -> assertFailure ("accepted it: " ++ show t)

rendered :: String -> String -> Assertion
rendered src expected = tree src >>= \t -> renderSurface t @?= expected

roundTrips :: String -> Assertion
roundTrips src = do
  t  <- tree src
  t' <- tree (renderSurface t)
  t' @?= t
