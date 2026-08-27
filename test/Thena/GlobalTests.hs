-- | The global environment, and @data@ (§3.3.1, §3.7).
--
-- The two tests that do the work are 'agreesWithTheResolver' and
-- 'roundTripTests', and both are shaped by the standing lesson from phases 2–5:
-- look for the invariant that is checked by different code from the code that
-- maintains it.
--
--   * A former's stored type is built by "Thena.Global.Env" from a record whose
--     telescopes "Thena.Syntax.Resolve" split apart. Written out in full and
--     resolved as an ordinary term, it must come back identical. Nothing in the
--     splitting path is shared with the ordinary path, so a lost binder, a
--     reordered telescope or a parameter dropped from a target all show up.
--   * A declaration printed and read back must mean the same thing — compared
--     as /terms/, not as text, because two declarations can legally print the
--     same way and still differ in what they bind.
module Thena.GlobalTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertFailure, testCase, (@?=))

import Thena.Core.Level (Level (..), levelOfNat)
import Thena.Core.Term
  ( Core (..)
  , GlobalName (..)
  , Ident (..)
  , close
  , fresh
  , open
  )
import Thena.Driver (parseCore, parseDeclaration)
import Thena.Errors (TypeError (..))
import Thena.Global.Declare (DeclareError (..), declare)
import Thena.Global.Env
  ( Definition (..)
  , GlobalEnv
  , InductiveDefinition (..)
  , constructorArguments
  , constructorName
  , constructorType
  , emptyGlobals
  , formerType
  , inductiveConstructors
  , inductiveIndices
  , inductiveName
  , inductiveParameters
  , inductives
  , isDeclared
  , lookupConstant
  , lookupDefinition
  , lookupInductive
  )
import Thena.Repl (renderInductive)

tests :: TestTree
tests =
  testGroup
    "Thena.Global"
    [ testGroup "what a declaration writes" tablesTests
    , testGroup "the generated wrappers" wrapperTests
    , testGroup "generation agrees with the ordinary resolver" agreesWithTheResolver
    , testGroup "strict positivity" positivityTests
    , testGroup "universes (thesis §4.1.1, back-filled at phase 8)" universeTests
    , testGroup "names" nameTests
    , testGroup "printed and read back" roundTripTests
    ]

-- --------------------------------------------------------------------------
-- Fixtures
-- --------------------------------------------------------------------------

-- What is typed after the command word: the driver splits @data@ off the line
-- before the lexer sees anything (§2.4).
natDecl, vecDecl, emptyDecl :: String
natDecl   = "Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
vecDecl   =
  "Vec (A : Type\8320) : Nat -> Type\8320 \
  \where { nil : Vec A zero \
  \; cons : forall (n : Nat) (a : A) (as : Vec A n) -> Vec A (succ n) }"
emptyDecl = "Empty : Type\8320 where { }"

-- | Declare in order, against the empty environment, threading the counter.
-- Either the reason it was refused, or the environment and the counter.
declareAll :: [String] -> Either String (GlobalEnv, Int)
declareAll = foldl one (Right (emptyGlobals, 0))
  where
    one acc src = do
      (env, n)  <- acc
      (d, n1)      <- shown (parseDeclaration env n src)
      (env', n2, _) <- shown (declare env n1 d)
      Right (env', n2)

    shown :: Show e => Either e a -> Either String a
    shown = either (Left . show) Right

-- | The environment after a run of declarations that must all be admitted,
-- and the counter it left behind.
--
-- The counter matters: rendering mints display variables, and a printer given a
-- counter below the term's highest 'Thena.Core.Term.Var' makes a colliding name
-- (phase 3's §7). Every fixture below carries its counter for that reason.
after :: [String] -> (GlobalEnv, Int)
after srcs = case declareAll srcs of
  Left e  -> error ("fixture refused: " ++ e)
  Right r -> r

nat, natVec :: GlobalEnv
nat    = fst (after [natDecl])
natVec = fst (after [natDecl, vecDecl])

natVecCounter :: Int
natVecCounter = snd (after [natDecl, vecDecl])

named :: String -> GlobalName
named = GlobalName

-- --------------------------------------------------------------------------
-- What a declaration writes
-- --------------------------------------------------------------------------

tablesTests :: [TestTree]
tablesTests =
  [ testCase "the datatype has a record" $
      fmap inductiveName (lookupInductive (named "Nat") nat) @?= Just (named "Nat")
  , testCase "the type former is a constant at its declared universe" $
      lookupConstant (named "Nat") nat @?= Just (Universe (LZero))
  , testCase "a former is in two tables under one name (§3.3.1)" $
      sequence_
        [ lookupConstant (named g) natVec
            @?= fmap definitionType (lookupDefinition (named g) natVec)
        | g <- ["Nat", "zero", "succ", "Vec", "nil", "cons"]
        ]
  , testCase "a datatype with no constructors is a datatype" $
      fmap (length . inductiveConstructors)
           (lookupInductive (named "Empty") (fst (after [emptyDecl])))
        @?= Just 0
  , testCase "the parameters and the indices are told apart" $
      fmap (\d -> (length (inductiveParameters d), length (inductiveIndices d)))
           (lookupInductive (named "Vec") natVec)
        @?= Just (1, 1)
  , testCase "an index is not a parameter of the record it is declared with" $
      fmap (\d -> (length (inductiveParameters d), length (inductiveIndices d)))
           (lookupInductive (named "Nat") natVec)
        @?= Just (0, 0)
  ]

-- --------------------------------------------------------------------------
-- The generated wrappers (§3.7 item 2)
-- --------------------------------------------------------------------------

wrapperTests :: [TestTree]
wrapperTests =
  [ testCase "a nullary former's wrapper is the bare Canonical" $
      fmap definitionBody (lookupDefinition (named "zero") nat)
        @?= Just (Canonical (named "zero") [])
  , testCase "a unary former's wrapper abstracts and applies" $
      fmap definitionBody (lookupDefinition (named "succ") nat)
        @?= Just (Lam (Ident "n") natTy (close v (Canonical (named "succ") [Free v])))
  , testCase "the type former gets a wrapper too" $
      fmap definitionBody (lookupDefinition (named "Nat") nat)
        @?= Just (Canonical (named "Nat") [])
  , testCase "every wrapper body is a saturated Canonical (§12 invariant 6)" $
      sequence_ (map saturated (formerNames natVec))
  ]
  where
    natTy   = Global (named "Nat")
    (v, _)  = fresh 0

    -- Peel the wrapper's λs, counting them, and check the body applies the
    -- former to exactly that many arguments. Under-application is what
    -- invariant 6 forbids, and it is the one thing generation could get wrong
    -- without any type error.
    saturated :: (GlobalName, Int) -> Assertion
    saturated (g, arity) = case fmap definitionBody (lookupDefinition g natVec) of
      Just b  -> peel 0 b
      Nothing -> assertFailure (show g ++ " has no wrapper")
      where
        peel k t = case t of
          Lam _ _ sc -> peel (k + 1) (open v sc)
          Canonical f as
            | f == g && length as == k && k == arity -> pure ()
          _ -> assertFailure (show g ++ ": wrapper body is " ++ show t)

-- | Every former the fixtures declare, with the number of arguments its
-- 'Canonical' must carry: the parameters plus its own.
formerNames :: GlobalEnv -> [(GlobalName, Int)]
formerNames env =
  concat
    [ (inductiveName d, length (inductiveParameters d) + length (inductiveIndices d))
        : [ ( constructorName c
            , length (inductiveParameters d) + length (constructorArguments c)
            )
          | c <- inductiveConstructors d
          ]
    | (_, d) <- inductives env
    ]

-- --------------------------------------------------------------------------
-- Generation agrees with the ordinary resolver
-- --------------------------------------------------------------------------

-- | The stored type of every former, against the same type written out and
-- read as an ordinary term.
--
-- The two are built by disjoint code. The left-hand side went through
-- 'Thena.Syntax.Resolve.resolveData', which splits a constructor's type into a
-- telescope and a target and throws the parameters away, and then through
-- 'Thena.Global.Env.constructorType', which puts them back. The right-hand side
-- is one call to the term resolver on a Π-chain.
agreesWithTheResolver :: [TestTree]
agreesWithTheResolver =
  [ testCase name $ case parseCore natVec [] 0 written of
      Left e  -> assertFailure (show e)
      Right (t, _) -> lookupConstant (named name) natVec @?= Just t
  | (name, written) <-
      [ ("Nat",  "Type\8320")
      , ("zero", "Nat")
      , ("succ", "Nat -> Nat")
      , ("Vec",  "Type\8320 -> Nat -> Type\8320")
      , ("nil",  "forall (A : Type\8320) -> Vec A zero")
      , ("cons", "forall (A : Type\8320) (n : Nat) (a : A) (as : Vec A n) \
                 \-> Vec A (succ n)")
      ]
  ]

-- --------------------------------------------------------------------------
-- Strict positivity, and MS1's two further limits (§3.7)
-- --------------------------------------------------------------------------

positivityTests :: [TestTree]
positivityTests =
  [ accepted "a non-recursive argument" "T : Type\8320 where { c : Nat -> T }"
  , accepted "a recursive argument" "T : Type\8320 where { c : T -> T }"
  , accepted "a function argument that does not mention the datatype"
      "T : Type\8320 where { c : (Nat -> Nat) -> T }"
  , accepted "several recursive arguments" "T : Type\8320 where { c : T -> T -> T }"
  , refused "the datatype left of an arrow"
      "T : Type\8320 where { c : (T -> T) -> T }"
      (NotStrictlyPositive (named "c") (Ident "x"))
  , refused "a higher-order recursive argument (thesis §4.1.3)"
      "T : Type\8320 where { c : (Nat -> T) -> T }"
      (HigherOrderRecursion (named "c") (Ident "x"))
  , refused "the datatype under another former"
      "T : Type\8320 where { c : Vec T zero -> T }"
      (NestedRecursion (named "c") (Ident "x"))
  , refused "the argument is named in the message when it has a name"
      "T : Type\8320 where { c : forall (f : T -> T) -> T }"
      (NotStrictlyPositive (named "c") (Ident "f"))
  ]

-- --------------------------------------------------------------------------
-- Universes (thesis §4.1.1)
-- --------------------------------------------------------------------------
--
-- The check needs 'Thena.Core.Typing.infer', so it could only land once phase 8
-- existed. Two things it must get right beyond the inequality itself: the type
-- former has to be in scope while its own constructors are checked, or no
-- recursive argument types at all; and each argument is checked in a context of
-- the parameters plus the arguments before it, or a telescope that refers back
-- to itself does not type either.

universeTests :: [TestTree]
universeTests =
  [ accepted "a small argument in a large datatype"
      "T : Type\8321 where { c : Type\8320 -> T }"
  , refused "a large argument in a small datatype"
      "T : Type\8320 where { c : Type\8320 -> T }"
      (ArgumentTooLarge (named "c") (Ident "x") (levelOfNat 1) (LZero))
  , accepted "a recursive argument, which needs the former in scope already"
      "T : Type\8320 where { c : T -> T }"
  , accepted "a parameter used as an argument's type"
      "Box (A : Type\8320) : Type\8320 where { box : A -> Box A }"
  , refused "a parameter from a larger universe than the datatype"
      "Box (A : Type\8321) : Type\8320 where { box : A -> Box A }"
      (ArgumentTooLarge (named "box") (Ident "x") (levelOfNat 1) (LZero))
  , accepted "an argument whose type mentions an earlier argument"
      "T : Type\8320 where { c : forall (n : Nat) (v : Vec Nat n) -> T }"
  , refused "an argument whose type is not a type at all"
      "T : Type\8320 where { c : zero -> T }"
      (ArgumentNotAType (named "c") (Ident "x")
         (NotAType [] (Global (named "zero")) (Canonical (named "Nat") [])))
  ]

-- --------------------------------------------------------------------------
-- Names (§3.6: one namespace)
-- --------------------------------------------------------------------------

nameTests :: [TestTree]
nameTests =
  [ refused "a datatype that is already declared"
      "Nat : Type\8320 where { z : Nat }"
      (AlreadyDeclared (named "Nat"))
  , refused "a constructor whose name is taken"
      "T : Type\8320 where { zero : T }"
      (AlreadyDeclared (named "zero"))
  , refused "a declaration that uses one name twice"
      "T : Type\8320 where { c : T ; c : T }"
      (RepeatedName (named "c"))
  , testCase "everything a declaration introduces is declared afterwards" $
      sequence_
        [ isDeclared (named g) natVec @?= True
        | g <- ["Nat", "zero", "succ", "Vec", "nil", "cons"]
        ]
  , testCase "and nothing else is" $
      isDeclared (named "pred") natVec @?= False
  ]

-- --------------------------------------------------------------------------
-- Printed and read back
-- --------------------------------------------------------------------------

-- | Compared as terms, not as text. Two declarations that differ only in a
-- binder's name print the same and are the same; one that lost an index does
-- not, and would slip past a string comparison of the header alone.
roundTripTests :: [TestTree]
roundTripTests =
  [ testCase name $ case lookupInductive (named name) natVec of
      Nothing -> assertFailure (name ++ " was not declared")
      Just d  -> case reread (renderInductive natVecCounter d) of
        Left e   -> assertFailure e
        Right d' -> do
          formerType d' @?= formerType d
          map (constructorType d') (inductiveConstructors d')
            @?= map (constructorType d) (inductiveConstructors d)
          map constructorName (inductiveConstructors d')
            @?= map constructorName (inductiveConstructors d)
  | name <- ["Nat", "Vec"]
  ]
  where
    -- The printer emits the whole command; the parser is handed what follows
    -- the command word, and the grammar does not care about the line breaks.
    reread ls = case parseDeclaration natVec natVecCounter (drop 5 (unwords ls)) of
      Left e       -> Left (show e)
      Right (d, _) -> Right d

-- --------------------------------------------------------------------------
-- Little helpers
-- --------------------------------------------------------------------------

accepted :: String -> String -> TestTree
accepted name src = testCase name $ case declareAll [natDecl, vecDecl, src] of
  Left e  -> assertFailure e
  Right _ -> pure ()

refused :: String -> String -> DeclareError -> TestTree
refused name src expect = testCase name $ case afterFixtures src of
  Left e   -> e @?= expect
  Right _  -> assertFailure "admitted, and it should not have been"

-- | Run one declaration against the fixtures' environment, keeping the
-- 'DeclareError' rather than rendering it.
afterFixtures :: String -> Either DeclareError ()
afterFixtures src = case parseDeclaration natVec 0 src of
  Left e       -> error ("fixture does not parse: " ++ show e)
  Right (d, n) -> () <$ declare natVec n d
