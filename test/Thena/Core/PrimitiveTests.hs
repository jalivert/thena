-- | The three primitive types and their literals (MS6 phase 97a).
--
-- **The load-bearing test is the round trip** — 'printsAndReadsBack' — and it
-- is what crosses the printer with something that is not itself: the reader.
-- A printer tested against a printer agrees with itself, which is the failure
-- @CLAUDE.md@ names; here 'Thena.Repl.renderCore' is checked against
-- 'Thena.Driver.parseCore', which was written by a different phase and does
-- not share a line of code with it.
--
-- The escaping cases are the reason it matters. Haskell's @show@ renders a tab
-- inside a string as @\\t@, and @Thena.Syntax.Lexer@\'s @\@escape@ reads back
-- exactly three escapes, of which @\\t@ is not one — so a literal holding a tab
-- would print in a spelling the reader refuses. 'escapeString' exists for that
-- and this is the test that keeps it honest.
module Thena.Core.PrimitiveTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import Test.Tasty.QuickCheck (forAll, testProperty, (===))

import Data.Maybe (isJust)

import Thena.Core.Context (Context)
import Thena.Core.Convert (convert)
import Thena.Core.Level (levelOfNat)
import Thena.Core.Reduce (whnf)
import Thena.Core.Term (Core (..), GlobalName (..), Literal (..), primitiveType)
import Thena.Core.Typing (infer)
import Thena.Driver (parseCore)
import Thena.Global.Env (Constant (..), GlobalEnv, emptyGlobals, lookupConstant)
import Thena.Repl (renderCore)

import Thena.Core.TermTests (genLiteral)

env :: GlobalEnv
env = emptyGlobals

ctx :: Context
ctx = []

tests :: TestTree
tests =
  testGroup
    "primitive types and their literals"
    [ testGroup "the three types are seeded into every environment" seeded
    , testGroup "a literal has the type its kind fixes" typed
    , testGroup "a literal is already a value" values
    , testGroup "equality is by the literal, and across the three types" equality
    , testGroup "conversion tells two literals apart" conversion
    , testGroup "printing and reading are inverse" roundTrip
    ]

-- --------------------------------------------------------------------------
-- The environment
-- --------------------------------------------------------------------------

-- An empty environment is not empty of these: they are 'constants' of
-- 'emptyGlobals', so 'isDeclared' protects the names before a user has loaded
-- anything at all.
seeded :: [TestTree]
seeded =
  [ testCase name $ case lookupConstant (GlobalName name) env of
      Nothing -> assertFailure (name ++ " is not in an empty environment")
      Just c  -> constantType c @?= Universe (levelOfNat 0)
  | name <- ["String", "Char", "Int"]
  ]

-- --------------------------------------------------------------------------
-- Typing, reduction, equality
-- --------------------------------------------------------------------------

typed :: [TestTree]
typed =
  [ testCase (show l) $ case infer env ctx 0 (Primitive l) of
      (Right ty, _, _) -> ty @?= Global (primitiveType l) []
      (Left e, _, _)   -> assertFailure (show e)
  | l <- [LString "ab", LChar 'c', LInt 7]
  ]

values :: [TestTree]
values =
  [ testProperty "whnf leaves it alone" $
      forAll genLiteral $ \l -> whnf env ctx (Primitive l) === Primitive l
  ]

equality :: [TestTree]
equality =
  [ testCase "the same literal" $ (Primitive (LInt 3) == Primitive (LInt 3)) @?= True
  , testCase "two of a kind that differ" $
      (Primitive (LString "a") == Primitive (LString "b")) @?= False
  -- A 'Char' and a one-character 'String' are different terms, which is the
  -- case a single untyped literal constructor would have got wrong.
  , testCase "a Char is not the String of one character" $
      (Primitive (LChar 'a') == Primitive (LString "a")) @?= False
  , testCase "a literal is not a global of the same spelling" $
      (Primitive (LString "Nat") == Global (GlobalName "Nat") []) @?= False
  ]

-- --------------------------------------------------------------------------
-- Conversion
-- --------------------------------------------------------------------------

-- 'Thena.Core.Convert' has no case for a literal: equal ones are taken by the
-- @s == t@ fast path, and unequal ones fall to the catch-all. **That is only
-- correct if the catch-all really refuses**, which nothing else in this phase
-- would notice, so it is checked here rather than assumed — a literal that
-- converted with another would let @"a"@ prove a theorem about @"b"@.
conversion :: [TestTree]
conversion =
  [ testCase "the same literal converts" $
      failureOf (Primitive (LInt 3)) (Primitive (LInt 3)) @?= Nothing
  , testCase "two that differ do not" $
      isJust (failureOf (Primitive (LString "a")) (Primitive (LString "b"))) @?= True
  , testCase "nor a Char and the String of one character" $
      isJust (failureOf (Primitive (LChar 'a')) (Primitive (LString "a"))) @?= True
  , testCase "nor a literal and a universe" $
      isJust (failureOf (Primitive (LInt 0)) (Universe (levelOfNat 0))) @?= True
  ]
  where
    failureOf s t = let (why, _, _) = convert env ctx 0 s t in why

-- --------------------------------------------------------------------------
-- The round trip
-- --------------------------------------------------------------------------

roundTrip :: [TestTree]
roundTrip =
  [ testProperty "a generated literal" $
      forAll genLiteral (printsAndReadsBack . Primitive)
  ]
    ++ [ testCase (show l) (printsAndReadsBack (Primitive l) @?= True)
       | l <- awkward
       ]

-- | Every literal whose spelling the lexer and the printer could disagree
-- about. The tab is the one @show@ gets wrong; the quotes and the backslash are
-- the three escapes; the empty string is the empty case.
awkward :: [Literal]
awkward =
  [ LString ""
  , LString "a b"
  , LString "quote \" inside"
  , LString "back \\ slash"
  , LString "tab \t inside"
  , LString "newline \n inside"
  , LChar '\''
  , LChar '\\'
  , LChar '\n'
  , LChar ' '
  , LInt 0
  , LInt 1234567890123456789012345678901234567890  -- wider than a machine word
  ]

printsAndReadsBack :: Core -> Bool
printsAndReadsBack t =
  case parseCore env ctx 0 (renderCore 0 ctx t) of
    Right (t', _) -> t' == t
    Left _        -> False
