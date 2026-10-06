-- | The three primitive types and their literals (MS6 phase 97a).
--
-- **The load-bearing test is the round trip** — 'printsAndReadsBack' — and it
-- is what crosses the printer with something that is not itself: the reader.
-- A printer tested against a printer agrees with itself, which is the failure
-- @CLAUDE.md@ names; here 'Thena.Render.renderCore' is checked against
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
import Thena.Driver
  ( checkedPrimitive
  , parseCore
  )
import Thena.Global.Env
  ( Constant (..)
  , Definition (..)
  , GlobalEnv
  , addDefinition
  , addPrimitive
  , emptyGlobals
  , lookupConstant
  )
import Thena.Render ( Rendering (..)
  ,renderCore)

import Thena.Engine (Machine (..))
import Thena.Driver (machineOf)
import Thena.Files (startingSession)

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
    , testGroup "deciding is a prelude definition now (MS8 phase 152)" deciding
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
  case parseCore [] env ctx 0 (renderCore (Rendering [] 0) ctx t) of
    Right (t', _) -> t' == t
    Left _        -> False

-- --------------------------------------------------------------------------
-- Deciding, retired into the prelude (MS8 phase 152)
-- --------------------------------------------------------------------------

-- | @decString@, @decChar@ and @decInt@ used to be reduction rules in Haskell:
-- a 'Thena.Core.Reduce.PrimitiveRule' that read the declared type back and
-- /wrote/ a @yes@ carrying a @refl@, or a @no@ carrying a refutation it built
-- itself. **They are definitions in @prelude\/prelude.thena@ now**, each
-- eliminating its comparison primitive with a motive that keeps the answer, and
-- each resting on exactly two @trusted@ claims about that primitive — so the
-- escape hatch is a core term whose claim @:trust@ can name, instead of sixty
-- lines of term-building nobody outside the implementation could see.
--
-- **These tests run against the real prelude**, because that is now where the
-- behaviour lives. What they check is what the rule used to guarantee: two
-- literals that agree decide @yes@ with the equality's own constructor, two
-- that differ decide @no@ with a refutation the kernel accepts, and a name
-- nobody knows decides nothing.
--
-- **Convertibility, not reduction on the nose.** 'Thena.Core.Reduce.whnf' is
-- weak-head, so the evidence inside the answer is still a spine of prelude
-- definitions once the head is @yes@; the old rule handed back a finished
-- @refl@ because it had built one. What survived the change is that the answer
-- /is/ that finished one, and 'Thena.Core.Convert.convert' is the question.
deciding :: [TestTree]
deciding =
  [ testCase "two literals that agree decide yes, by the equality's own constructor" $ do
      gs <- preludeGlobals
      convertibleIn gs
        (decide "String" [str "a", str "a"])
        (Canonical (GlobalName "yes") [LZero, LZero]
          [ eqOf "String" (str "a") (str "a")
          , Canonical (GlobalName "refl") [LZero] [prim "String", str "a"] ])
  , testCase "two that differ decide no" $ do
      gs <- preludeGlobals
      case whnf gs ctx (decide "String" [str "a", str "b"]) of
        Canonical (GlobalName "no") _ [_, _] -> pure ()
        other -> assertFailure (show other)
    -- **The load-bearing one.** The refutation is no longer written by the
    -- reducer; it is derived in the prelude from @eqStringRefl@ and
    -- @transport@, and the kernel still has to accept it at exactly the type
    -- the constructor wants.
  , testCase "and the derived refutation is a proof the kernel accepts" $ do
      gs <- preludeGlobals
      case whnf gs ctx (decide "String" [str "a", str "b"]) of
        Canonical _ _ [_, refutation] ->
          fst3 (check gs ctx 0 refutation
                  (Pi (Ident "_") (eqOf "String" (str "a") (str "b"))
                      (close (fst (fresh 702)) (Global (GlobalName "Empty") [LZero]))))
            @?= Right ()
        other -> assertFailure (show other)
  , testCase "so is the whole answer, at the definition's own result type" $ do
      gs <- preludeGlobals
      mapM_ (\(p, a, b) ->
               fst3 (check gs ctx 0 (whnf gs ctx (decide p [a, b])) (decOf p a b))
                 @?= Right ())
        [ ("String", str "a", str "a"), ("String", str "a", str "b")
        , ("Int", Primitive (LInt 1), Primitive (LInt 2))
        , ("Char", Primitive (LChar 'x'), Primitive (LChar 'x')) ]
  , testCase "a name nobody knows is not decided" $ do
      gs <- preludeGlobals
      case whnf gs ctx (decide "String" [Free v, str "a"]) of
        Canonical (GlobalName g) _ _ ->
          assertFailure ("decided " ++ g ++ " about a variable")
        _ -> pure ()
    -- **The retirement is complete, and this is what says so.** @primitive@
    -- accepts only the names 'Thena.Core.Reduce.primitiveNames' has a rule
    -- for, so with the rule gone the declaration the prelude used to make is
    -- refused outright at every type — nobody can put @decString@ back as a
    -- constant with no body.
  , testCase "declare-primitive no longer knows the name at all" $
      mapM_ (\p -> isRight' (checkedPrimitive emptyGlobals (GlobalName ("dec" ++ p))
                               (Universe LZero)) @?= False)
        ["String", "Char", "Int"]
  ]
  where
    v = fst (fresh 703)
    str s = Primitive (LString s)
    decide p = foldl App (Global (GlobalName ("dec" ++ p)) [])
    fst3 (a, _, _) = a
    isRight' = either (const False) (const True)
    prim p = Global (GlobalName p) []
    eqOf p x y = App (App (App (Global (GlobalName "Eq") [LZero]) (prim p)) x) y
    decOf p x y = App (Global (GlobalName "Dec") [LZero, LZero]) (eqOf p x y)
    convertibleIn gs a b = case convert gs ctx 0 a b of
      (Nothing, [], _) -> pure ()
      (why, obs, _)    -> assertFailure (show (why, length obs))

-- | The environment a fresh session starts in — the rule base and the shipped
-- prelude, which is where @decString@ lives now.
preludeGlobals :: IO GlobalEnv
preludeGlobals = globals . machineOf . fst <$> startingSession
