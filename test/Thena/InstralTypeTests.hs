-- | @instral@'s type language and the signature table (MS5 phase 66b).
--
-- **What is checked here is the readable half**: that a type spells the way a
-- rule author would write it, and that a representative op says what it takes.
-- The two structural properties — a signature's arity agreeing with
-- 'Thena.Ops.operandsOf', and 'Thena.Ops.produces' agreeing with the result
-- column — are not tested, because neither can fail: both are derived from one
-- case split (see 'Thena.Ops.operandTypes'). What the table's result column
-- /is/ checked against is the engine, in @RulesTests@' @produces agrees with
-- the engine@ group, which now also asserts the value's shape.
module Thena.InstralTypeTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?), (@?=))

import Thena.Core.Term (GlobalName (..))
import Thena.Instral.Type
  ( Signature (..)
  , fits
  , Ty (..)
  , renderSignature
  , renderTy
  , typeVarsIn
  )
import Thena.Ops (AnswerKind (..), Op (..), Operand (..), Value (..), signatureOf)
import qualified Thena.Ops as Op
import Thena.Ops (Test (..))
import Thena.Rules (testTypes)

tests :: TestTree
tests =
  testGroup
    "Thena.Instral.Type"
    [ renderTests
    , signatureTests
    , headTests
    , fitting
    ]

-- | The relation @:accepts@ and @:produces@ ask (MS5 phase 71).
--
-- **One-way**: a scheme's variable may move, the asked type's may not.
fitting :: TestTree
fitting =
  testGroup
    "fits"
    [ testCase "a type fits itself" $ fits TCore TCore @?= True
    , testCase "and not another" $ fits TCore TSurface @?= False
      -- **The point of the relation.** @:accepts Core@ must list a rule whose
      -- parameter is @a@, because such a rule does accept a Core.
    , testCase "a scheme variable fits anything" $ fits (TVar 0) TCore @?= True
      -- …and the other way round it does not: asking about @a@ is asking about a
      -- variable, which only a variable answers.
    , testCase "but not the other way round" $ fits TCore (TVar 0) @?= False
      -- **Repeated variables must agree**, so @a -> a@ fits @Core -> Core@ and
      -- not @Core -> Surface@.
    , testCase "a repeated variable must agree" $
        fits (TFun [TVar 0] (TVar 0)) (TFun [TCore] TCore) @?= True
    , testCase "and disagreeing is a miss" $
        fits (TFun [TVar 0] (TVar 0)) (TFun [TCore] TSurface) @?= False
    , testCase "it goes under a constructor" $
        fits (TList (TVar 0)) (TList TInt) @?= True
    , testCase "and the constructor has to match" $
        fits (TList (TVar 0)) (TOption TInt) @?= False
      -- Arity is part of a function type (MS5 phase 68b).
    , testCase "a function of one does not fit a function of two" $
        fits (TFun [TVar 0] (TVar 1)) (TFun [TCore, TCore] TCore) @?= False
    ]

-- | Exact strings, not a round trip. Phase 2's standing lesson: a round-trip
-- property passes while a self-consistent error agrees with itself.
renderTests :: TestTree
renderTests =
  testGroup
    "rendering"
    [ testCase "the ground set" $
        map renderTy [TString, TName, TInt, TChar, TBool]
          @?= ["String", "Name", "Int", "Char", "Bool"]
    , testCase "the abstract four" $
        map renderTy [TSurface, TCore, TDevelopment]
          @?= ["Surface", "Core", "Development"]
      -- **@Name@ is not @String@ and prints as itself** — his ruling,
      -- 2026-09-12. If these two ever render the same the distinction is
      -- invisible in every message the type system will produce.
    , testCase "a name does not print as a string" $
        (renderTy TName /= renderTy TString) @?= True
    , testCase "a scheme variable is a letter" $
        map (renderTy . TVar) [0, 1, 25, 26] @?= ["a", "b", "z", "a1"]
    , testCase "a list and an option" $
        map renderTy [TList TInt, TOption TCore] @?= ["List Int", "Option Core"]
      -- A one-parameter constructor is the only place a type nests without a
      -- bracket of its own, so it is the only place parentheses are needed.
    , testCase "nesting takes parentheses" $
        renderTy (TList (TOption TInt)) @?= "List (Option Int)"
    , testCase "and a pair brings its own" $
        renderTy (TList (TPair TName TCore)) @?= "List (Name, Core)"
    , testCase "a pair needs none inside a pair" $
        renderTy (TPair (TList TInt) TBool) @?= "(List Int, Bool)"
      -- **An op that produces nothing ends in @()@**, so that the absence is
      -- something you can see rather than a word that seems to be missing.
    , testCase "no result prints as unit" $
        renderSignature (Signature [TCore] Nothing) @?= "Core -> ()"
    , testCase "and no arguments either" $
        renderSignature (Signature [] (Just TCore)) @?= "Core"
      -- **A function-typed parameter takes parentheses** (MS5 phase 73). Without
      -- them this prints as a signature of three arguments rather than two, and
      -- arity is the one thing a reader takes from a listing.
    , testCase "a function-typed parameter is parenthesised" $
        renderSignature (Signature [TFun [TString] TString, TString] (Just TString))
          @?= "(String -> String) -> String -> String"
      -- **…and so does a function-typed RESULT** (2026-09-12). Bare, the two
      -- signatures below print the same text while being different callables:
      -- one takes a @String@ and gives a function, the other takes two.
    , testCase "a function-typed result is parenthesised too" $
        renderSignature (Signature [TString] (Just (TFun [TString] TString)))
          @?= "String -> (String -> String)"
    , testCase "so the two do not print alike" $
        renderSignature (Signature [TString] (Just (TFun [TString] TString)))
          /= renderSignature (Signature [TString, TString] (Just TString))
          @? "a function result and one more argument print the same"
    , testCase "the variables a type mentions, in order" $
        typeVarsIn (TPair (TList (TVar 3)) (TOption (TVar 1))) @?= [3, 1]
    ]

-- | One op per interesting shape, pinned as the string a reader would write.
--
-- Not all 79: the table is total and @-Wall@ makes a new op answer it, so what
-- is worth pinning is the /kinds/ of answer, and the ones a later phase is most
-- likely to disturb.
signatureTests :: TestTree
signatureTests =
  testGroup
    "signatures"
    [ sig "claim"        (Claim r r)                    "Name -> Core -> Core"
    , sig "assume"       (Assume r r)                   "Name -> Core -> Core"
    , sig "quantify"     (Op.Quantify r r)              "Name -> Core -> ()"
      -- **The two halves of what was one op** (this phase). One took either a
      -- variable or a name and so had no signature at all; these are why the
      -- word was split.
    , sig "goto"         (Goto r)                       "Core -> ()"
    , sig "goto-named"   (Op.GotoNamed r)               "Name -> ()"
      -- **The coercion the shipped base needs** — @ask … name@ gives a Name and
      -- @concat@ wants a String.
    , sig "name-text"    (Op.NameText r)                "Name -> String"
    , sig "concat"       (Concat r r)                   "String -> String -> String"
    , sig "say"          (Say r)                        "String -> ()"
      -- **The kind decides what @ask@ hands back**, which is the one place a
      -- field and not an operand changes a signature.
    , sig "ask … text"   (Ask r AText)                  "String -> String"
    , sig "ask … name"   (Ask r AName)                  "String -> Name"
      -- **Core in, Core out** — his ruling: the type system does not tell an
      -- unresolved written term from a resolved one.
    , sig "resolve-core" (Op.ResolveCore r)             "Core -> Core"
    , sig "surface-name" (Op.SurfaceNameOf r)           "Surface -> Name"
    , sig "lambda-tail"  (Op.LambdaTail r)              "Surface -> Surface"
    , sig "resolve-name" (Op.ResolveName r)             "Name -> Core"
    , sig "apply-next"   (Op.ApplyNext r r)             "Core -> Name -> Core"
    , sig "here"         Here                           "Core"
    , sig "goal"         Goal                           "Core"
    , sig "prim-attack"  Attack                         "()"
      -- The data structures are where the scheme variables are.
      -- Its arity is the table's even though its types are inference's.
      --
      -- **The parentheses say it takes nothing and gives a function**
      -- (2026-09-12). Bare, this printed as @b -> a@ — the spelling of an op
      -- that takes a @b@ and gives an @a@, which is a different signature.
    , sig "lambda, one parameter"
                         (Op.Lambda ["x"] [])           "(b -> a)"
    , sig "some"         (Op.Some r)                    "a -> Option a"
    , sig "none"         Op.None                        "Option a"
    , sig "list-head"    (Op.ListHead r)                "List a -> Option a"
    , sig "list-tail"    (Op.ListTail r)                "List a -> List a"
    , sig "pair-first"   (Op.PairFirst r)               "(a, b) -> a"
    , sig "pair-second"  (Op.PairSecond r)              "(a, b) -> b"
    , sig "option-value" (Op.OptionValue r)             "Option a -> a"
      -- **A call says nothing**, and cannot: which clauses a name has is not
      -- known when a body is read, so every argument and the result are their
      -- own variable until phase 66c takes them from the rule.
    , sig "call, two arguments"
                         (Call (GlobalName "f") [r, r]) "a -> b -> c"
      -- **A variadic op is not a special shape**, because the table takes the
      -- 'Op' and not a tag: an @intro@ with a name and one without are two
      -- values, so they simply have two signatures.
    , sig "prim-lambda, named"   (IntroPi (Just r))     "Name -> ()"
    , sig "prim-lambda, unnamed" (IntroPi Nothing)      "()"
    ]
  where
    r = Lit (VText "x")
    sig label o expected =
      testCase label (renderSignature (signatureOf o) @?= expected)

-- | A head test's operands (MS5 phase 66b) — where a rule's parameters get
-- their types, and the reason this table exists before inference does.
headTests :: TestTree
headTests =
  testGroup
    "head tests"
    [ testCase "a focus question asks about nothing" $
        map snd (testTypes FocusIsHole) @?= []
    , testCase "a surface question wants a surface term" $
        map snd (testTypes (SurfaceIsLambda r)) @?= [TSurface]
    , testCase "and so does every other one" $
        map snd (testTypes (AppHeadIsName r)) @?= [TSurface]
      -- The four data questions are the only head tests that ask about
      -- something @instral@ owns rather than about a surface node.
    , testCase "a list question wants a list" $
        map snd (testTypes (ListIsCons r)) @?= [TList (TVar 0)]
    , testCase "an option question wants an option" $
        map snd (testTypes (OptionIsNone r)) @?= [TOption (TVar 0)]
    ]
  where
    r = Lit (VText "x")
