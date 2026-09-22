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
import Thena.Core.Level (Level (..), levelOfNat)
import Thena.Core.Reduce (whnf)
import Thena.Core.Term
  ( Core (..)
  , GlobalName (..)
  , Ident (..)
  , Literal (..)
  , close
  , fresh
  )
import Thena.Core.Typing (check, infer)
import Thena.Driver (checkedPrimitive, parseCore)
import Thena.Global.Env
  ( Constant (..)
  , Definition (..)
  , GlobalEnv
  , addDefinition
  , addPrimitive
  , emptyGlobals
  , lookupConstant
  )
import Thena.Repl (renderCore)

import Thena.Core.TermTests (genLiteral)
import Thena.Declared (declared)

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
    , testGroup "a declared primitive computes on literals" computing
    , testGroup "a primitive declaration the system cannot keep is refused" refusals
    , testGroup "a deciding primitive answers with its evidence (phase 109a)" deciding
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
      (Right ty, _, _) -> ty @?= expected
      (Left e, _, _)   -> assertFailure (show e)
  | (l, expected) <-
      [ (LString "ab", named "String")
      , (LChar 'c', named "Char")
      , (LInt 7, named "Int")
      ]
  ]
  where
    named g = Global (GlobalName g) []

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
  -- **Found in phase 105**: the two sides were compared syntactically first,
  -- so "a" against "a" converted, but "a" against a definition of "a" reduced
  -- to two literals and fell through to a clash. @refl String "a"@ was refused
  -- at @Eq String "a" "a"@ because of it.
  , testCase "a literal and a definition of that literal convert" $
      failureInA (Primitive (LString "a")) named @?= Nothing
  , testCase "and of a different one do not" $
      isJust (failureInA (Primitive (LString "b")) named) @?= True
  ]
  where
    failureOf s t = let (why, _, _) = convert env ctx 0 s t in why
    failureInA s t = let (why, _, _) = convert withA ctx 0 s t in why
    named = Global (GlobalName "a") []
    withA = addDefinition (GlobalName "a")
              (MkDefinition [] [] (Global (GlobalName "String") []) (Primitive (LString "a"))) env

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

-- --------------------------------------------------------------------------
-- The primitives' rule (MS6 phase 97b)
-- --------------------------------------------------------------------------

-- | An environment with a two-constructor answer type and @eqString@ declared
-- to answer with it.
--
-- **The answer type is deliberately not the prelude's** @Comparison@: the rule
-- is supposed to read the declared type and use /its/ two constructors, never
-- a name written in the reducer. If the rule ever hard-codes one, these tests
-- are what notices, because @yes@ and @no@ appear nowhere in @src/@.
answering :: GlobalEnv
answering = addPrimitive (GlobalName "eqString") eqTy withAnswer
  where
    withAnswer = fst (declared ["Answer : Type₀ where { yes : Answer ; no : Answer }"])
    eqTy = arrow str (arrow str (Global (GlobalName "Answer") []))
    str = Global (GlobalName "String") []
    arrow a b = Pi (Ident "_") a (close (fst (fresh 900)) b)

answer :: String -> Core
answer c = Canonical (GlobalName c) [] []

computing :: [TestTree]
computing =
  [ testCase "two literals that agree take the first constructor" $
      reduced (apply [str "a", str "a"]) @?= answer "yes"
  , testCase "two that differ take the second" $
      reduced (apply [str "a", str "b"]) @?= answer "no"
  -- A comparison of anything but two literals has no rule and must stay as it
  -- is: reduction that guessed here would decide equality of open terms.
  , testCase "a variable is not compared" $
      reduced (apply [Free v, str "a"]) @?= apply [Free v, str "a"]
  , testCase "nor is one argument alone enough" $
      reduced (apply [str "a"]) @?= apply [str "a"]
  -- **An argument is reduced before it is read** (phase 100, closeout item 7).
  -- These were stuck: the rule matched a literal as the argument stood, so a
  -- closed comparison of something that /is/ a literal did not compute.
  , testCase "a definition of a literal is compared, in either place" $
      map reduced [apply [named "a", str "a"], apply [str "b", named "a"]]
        @?= [answer "yes", answer "no"]
  , testCase "so is a redex that reduces to one" $
      reduced (apply [App identity (str "a"), str "a"]) @?= answer "yes"
  -- appendString (MS6 phase 105): the one way a String is built.
  , testCase "appendString puts two literals together" $
      reduced (append [str "x", str "'"]) @?= str "x'"
  , testCase "and reads a definition of one, as a comparison does" $
      reduced (append [named "a", str "b"]) @?= str "ab"
  , testCase "and leaves a variable where it is" $
      reduced (append [Free v, str "'"]) @?= append [Free v, str "'"]
  ]
  where
    v = fst (fresh 500)
    str s = Primitive (LString s)
    named g = Global (GlobalName g) []
    apply = foldl App (Global (GlobalName "eqString") [])
    append = foldl App (Global (GlobalName "appendString") [])
    reduced = whnf withA ctx
    withA = addDefinition (GlobalName "a") (MkDefinition [] [] stringTy (str "a")) answering
    stringTy = Global (GlobalName "String") []
    identity = Lam (Ident "x") stringTy (close x (Free x))
    x = fst (fresh 501)

-- | What @declare-primitive@ does with a declaration it cannot honour.
--
-- **This is the whole of why @primitive@ is not a postulate**, so each case is
-- one way of trying to smuggle an axiom in.
refusals :: [TestTree]
refusals =
  [ refusedCase "a name with no rule" (GlobalName "myAxiom") (twoOf "String")
  , refusedCase "the wrong argument type" (GlobalName "eqString") (twoOf "Int")
  , refusedCase "too few arguments" (GlobalName "eqString") oneArgument
  , refusedCase "an answer that is not a datatype" (GlobalName "eqString") intoAUniverse
  , refusedCase "an answer with the wrong constructors" (GlobalName "eqInt") intoAnswerOfOne
  , testCase "and the declaration this phase ships is accepted" $
      isRight (checkedPrimitive answering (GlobalName "eqString") (twoOf "String")) @?= True
  -- appendString's rule reads no declared type: it is String -> String ->
  -- String exactly, and a comparison's shape is not that.
  , refusedCase "appendString answering with a datatype" (GlobalName "appendString") (twoOf "String")
  , refusedCase "appendString over Int" (GlobalName "appendString")
      (arrow (named "Int") (arrow (named "Int") (named "Int")))
  , testCase "appendString at its own type is accepted" $
      isRight (checkedPrimitive answering (GlobalName "appendString")
                 (arrow (named "String") (arrow (named "String") (named "String")))) @?= True
  ]
  where
    refusedCase what nm ty =
      testCase what (isRight (checkedPrimitive answering nm ty) @?= False)
    twoOf p = arrow (named p) (arrow (named p) (named "Answer"))
    oneArgument = arrow (named "String") (named "Answer")
    intoAUniverse = arrow (named "String") (arrow (named "String") (Universe (levelOfNat 0)))
    intoAnswerOfOne = arrow (named "Int") (arrow (named "Int") (named "One"))
    named n = Global (GlobalName n) []
    arrow a b = Pi (Ident "_") a (close (fst (fresh 900)) b)
    isRight = either (const False) (const True)

printsAndReadsBack :: Core -> Bool
printsAndReadsBack t =
  case parseCore env ctx 0 (renderCore 0 ctx t) of
    Right (t', _) -> t' == t
    Left _        -> False

-- --------------------------------------------------------------------------
-- Deciding, with evidence (MS6 phase 109a, ms6/CLOSEOUT.md 32)
-- --------------------------------------------------------------------------

-- | @decString@, @decInt@ and @decChar@ declared over an equality and a
-- decision type **that are not the prelude's**: @Same@ and @Verdict@, with
-- @Void@ for what a refutation reaches. The rule reads every one of those names
-- off the declared type; if it ever writes @Eq@, @Dec@, @yes@ or @Empty@
-- itself, these are what notice.
decidingEnv :: GlobalEnv
decidingEnv = foldr declareOne base ["String", "Int", "Char"]
  where
    base = fst (declared
      [ "Same (A : Type) : A -> A -> Type where { itself : \8704 (a : A) -> Same A a a }"
      , "Void : Type where { }"
      , "Verdict (A : Type) : Type where { proved : \8704 (p : A) -> Verdict A ; refuted : \8704 (n : A -> Void {0}) -> Verdict A }" ])
    declareOne p = addPrimitive (GlobalName ("dec" ++ p)) (decType p)

-- | @(a b : P) -> Verdict {0} (Same {0} P a b)@.
decType :: String -> Core
decType p =
  Pi (Ident "a") (prim p) $ close va $
  Pi (Ident "b") (prim p) $ close vb $
  App (Global (GlobalName "Verdict") [LZero]) (same p (Free va) (Free vb))
  where
    va = fst (fresh 700)
    vb = fst (fresh 701)

prim :: String -> Core
prim p = Global (GlobalName p) []

same :: String -> Core -> Core -> Core
same p x y = App (App (App (Global (GlobalName "Same") [LZero]) (prim p)) x) y

deciding :: [TestTree]
deciding =
  [ testCase "two literals that agree are proved, by the equality's own constructor" $
      reduced (decide "String" [str "a", str "a"])
        @?= Canonical (GlobalName "proved") [LZero]
              [same "String" (str "a") (str "a"), Canonical (GlobalName "itself") [LZero] [prim "String", str "a"]]
  , testCase "two that differ are refuted" $
      case reduced (decide "String" [str "a", str "b"]) of
        Canonical (GlobalName "refuted") _ [_, _] -> pure ()
        other -> assertFailure (show other)
    -- **The load-bearing one.** The refutation is a term the reducer wrote;
    -- the kernel checks it, at exactly the type the constructor wants.
  , testCase "and the refutation the reducer writes is a proof the kernel accepts" $
      case reduced (decide "String" [str "a", str "b"]) of
        Canonical _ _ [_, refutation] ->
          fst3 (check decidingEnv ctx 0 refutation
                  (Pi (Ident "_") (same "String" (str "a") (str "b"))
                      (close (fst (fresh 702)) (Global (GlobalName "Void") [LZero]))))
            @?= Right ()
        other -> assertFailure (show other)
  , testCase "so is the whole answer, at the primitive's own result type" $
      mapM_ (\(p, a, b) ->
               fst3 (check decidingEnv ctx 0 (reduced (decide p [a, b]))
                       (App (Global (GlobalName "Verdict") [LZero]) (same p a b)))
                 @?= Right ())
        [ ("String", str "a", str "a"), ("String", str "a", str "b")
        , ("Int", Primitive (LInt 1), Primitive (LInt 2)), ("Char", Primitive (LChar 'x'), Primitive (LChar 'x')) ]
  , testCase "a variable is not decided" $
      reduced (decide "String" [Free v, str "a"]) @?= decide "String" [Free v, str "a"]
  , testCase "the declaration the prelude makes is accepted" $
      isRight (checkedPrimitive decidingEnv (GlobalName "decString") (decType "String")) @?= True
  , testCase "a comparison's type is not a decision's" $
      isRight (checkedPrimitive answering (GlobalName "decString")
                 (arrow (prim "String") (arrow (prim "String") (prim "Answer")))) @?= False
  , testCase "nor is a decision over the wrong primitive type" $
      isRight (checkedPrimitive decidingEnv (GlobalName "decString") (decType "Int")) @?= False
  , testCase "nor one whose answer has the wrong number of constructors" $
      isRight (checkedPrimitive threeWay (GlobalName "decString") (decType "String")) @?= False
  ]
  where
    v = fst (fresh 703)
    str s = Primitive (LString s)
    decide p = foldl App (Global (GlobalName ("dec" ++ p)) [])
    reduced = whnf decidingEnv ctx
    fst3 (a, _, _) = a
    arrow a b = Pi (Ident "_") a (close (fst (fresh 900)) b)
    isRight = either (const False) (const True)
    threeWay = fst (declared
      [ "Same (A : Type) : A -> A -> Type where { itself : \8704 (a : A) -> Same A a a }"
      , "Void : Type where { }"
      , "Verdict (A : Type) : Type where { proved : \8704 (p : A) -> Verdict A ; refuted : \8704 (n : A -> Void {0}) -> Verdict A ; unsure : \8704 (p : A) -> Verdict A }" ])

