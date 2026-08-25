-- | The rule language's concrete syntax (§8, phase 21).
--
-- The load-bearing test is 'againstTheBase': every rule in
-- 'Thena.Rules.standardRules' is written out by hand here, and reading that
-- text back must give the very 'Rule' the Haskell literal gives. A fixture and
-- not a round trip — @parse . render == id@ would pass while both halves
-- shared a mistake, which is the standing lesson from phases 2–5.
--
-- The op and test vocabularies get the same treatment from the other side:
-- 'Thena.Ops.opKeyword' and 'Thena.Rules.testWord' are total case splits, so
-- @-Wall@ makes a new op or test say how it is spelled, and 'everyOp' below
-- checks that what they say is a word the parser and resolver actually accept.
module Thena.RuleSyntaxTests (tests) where

import Data.Maybe (listToMaybe)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Term (GlobalName (..))
import Thena.Development.Cursor (Part (..))
import Thena.Ops
  ( AnswerKind (..)
  , Instr (..)
  , Op (..)
  , Operand (..)
  , Rule (..)
  , Test (..)
  , Value (..)
  , opKeyword
  )
import qualified Thena.Ops as Op
import Thena.Rules
  ( RuleBase (..)
  , RuleError (..)
  , allRules
  , resolveRule
  , testWord
  , validate
  )
import Thena.Standard (expectedStandard, standardBases)
import Thena.Syntax.Lexer (lexTokens)
import Thena.Syntax.Parser (parseRule)

tests :: TestTree
tests =
  testGroup
    "rule syntax (§8)"
    [ againstTheBase
    , vocabulary
    , shapes
    , mistakes
    ]

-- --------------------------------------------------------------------------
-- Reading a rule
-- --------------------------------------------------------------------------

-- | Lex, parse, resolve. Phase 21 has no driver entry point that does this —
-- there is nowhere to type a rule (rules come from the rule base and nowhere
-- else, DECIDED by the user 2026-08-25) and no file to load one from until
-- phase 22, so the composition lives here and moves to the loader when there
-- is one.
readRule :: [Rule] -> String -> Either String Rule
readRule visible src = case lexTokens src of
  Left e -> Left ("lex: " ++ show e)
  Right ts -> case parseRule ts of
    Left e -> Left ("parse: " ++ show e)
    Right raw -> case resolveRule visible raw of
      Left es -> Left ("resolve: " ++ show es)
      Right r -> Right r

expectRule :: [Rule] -> String -> IO Rule
expectRule visible src =
  either (assertFailure . ((src ++ " — ") ++)) pure (readRule visible src)

-- | A rule whose body is the one instruction under test.
bodyOf :: String -> IO [Instr]
bodyOf src = ruleBody <$> expectRule expectedStandard ("rule r :- when focus-is-hole then " ++ src)

-- --------------------------------------------------------------------------
-- The base, written out
-- --------------------------------------------------------------------------

-- | The **shipped file** against the Haskell literals.
--
-- Phase 21 compared nine hand-written lines with 'Thena.Rules.standardRules';
-- phase 22 deleted that value, so the comparison would have become the file
-- against itself. The literals moved to "Thena.Standard" instead and this now
-- pins @rules/standard.thena.rules@ — a stronger target, because it is the file
-- the REPL actually reads at startup.
againstTheBase :: TestTree
againstTheBase =
  testGroup
    "the shipped base, read off disk"
    [ testCase "it is one base, named, with a description and a path" $ do
        bs <- standardBases
        map baseName bs @?= ["standard"]
        map baseDescription bs @?= [Just "the rules the engine starts with"]
        map (null . basePath) bs @?= [False]

    , testCase "its rules are exactly the nine, in order" $ do
        rs <- allRules <$> standardBases
        map ruleName rs @?= map ruleName expectedStandard
        rs @?= expectedStandard

    , testCase "and every one of them validates" $ do
        rs <- allRules <$> standardBases
        concatMap validate rs @?= []
    ]

-- --------------------------------------------------------------------------
-- The vocabularies
-- --------------------------------------------------------------------------

-- | Every op that has a written form, with the text that writes it.
--
-- 'Thena.Ops.opKeyword' is the total case split @-Wall@ guards; this is the
-- list the parser is checked against, and the two are crossed below — the word
-- the table gives must be the word the text starts with, and the text must
-- resolve to the op the table was asked about.
--
-- @data@ is absent and is checked separately: it has a keyword and no written
-- form (§3.7).
everyOp :: [(String, Op)]
everyOp =
  [ ("assume x y",   Assume (Ref "x") (Ref "y"))
  , ("claim x y",    Claim (Ref "x") (Ref "y"))
  , ("ask x text",   Ask (Ref "x") AText)
  , ("ask x name",   Ask (Ref "x") AName)
  , ("ask x term",   Ask (Ref "x") ATerm)
  , ("ask x rule-name", Ask (Ref "x") ARule)
  , ("say x",        Say (Ref "x"))
  , ("concat x y",   Concat (Ref "x") (Ref "y"))
  , ("along",        Along)
  , ("into",         Into)
  , ("cross type",   CrossType)
  , ("cross val",    CrossValue)
  , ("fun",          Down Fun)
  , ("arg",          Down Arg)
  , ("arg 2",        Down (CanonArg 2))
  , ("dom",          Down Dom)
  , ("cod",          Down Cod)
  , ("val",          Down Val)
  , ("type",         Down Type)
  , ("body",         Down Body)
  , ("motive",       Down Motive)
  , ("target",       Down Target)
  , ("param 0",      Down (Param 0))
  , ("method 1",     Down (Method 1))
  , ("index 2",      Down (Index 2))
  , ("back",         Back)
  , ("reduce",       Reduce)
  , ("unify x y",    Unify (Ref "x") (Ref "y"))
  , ("attack",       Attack)
  , ("intro",        Intro)
  , ("try x",        Try (Ref "x"))
  , ("regret",       Regret)
  , ("solve",        Solve)
  , ("abandon",      Abandon)
  , ("prove",        Prove Nothing)
  , ("prove x",      Prove (Just (Ref "x")))
  , ("parse x",      Parse (Ref "x"))
  , ("resolve x",    Op.Resolve (Ref "x"))
  , ("certify x",    Certify (Ref "x"))
  , ("eliminate x",  Op.Eliminate (Ref "x"))
  ]

vocabulary :: TestTree
vocabulary =
  testGroup
    "vocabulary"
    [ testGroup "every op reads back" (map opCase everyOp)
    , testGroup "every op's keyword is the word it is written with"
        (map keywordCase everyOp)
    , testGroup "every test reads back" (map testCase' allTests)
    , testCase "call names a rule in the base" $ do
        b <- bodyOf "call try x"
        callee <- case expectedStandard of
          _ : t : _ -> pure t
          _         -> assertFailure "the base has no second rule"
        b @?= [Do (Call (Lit (VRule callee)) [Ref "x"])]
    ]
  where
    opCase (src, expected) =
      testCase src $ do
        b <- bodyOf src
        b @?= [Do expected]

    keywordCase (src, expected) =
      testCase src $ Just (opKeyword expected) @?= listToMaybe (words src)

    allTests = [FocusIsHole, FocusIsGuess, GoalTypeIsPi, GoalTypeIsLet, HintIsName]

    testCase' t =
      testCase (testWord t) $ do
        r <- expectRule expectedStandard
               ("rule r :- when " ++ testWord t ++ " then solve")
        ruleHead r @?= [t]

-- --------------------------------------------------------------------------
-- The shape of a rule
-- --------------------------------------------------------------------------

shapes :: TestTree
shapes =
  testGroup
    "shape"
    [ testCase "no parameters, no parentheses" $ do
        r <- expectRule expectedStandard "rule r :- when focus-is-hole then solve"
        ruleParams r @?= []
    , testCase "parameters need no space before the parenthesis" $ do
        r <- expectRule expectedStandard "rule r(a b c) :- when focus-is-hole then solve"
        ruleParams r @?= ["a", "b", "c"]
    , testCase "and a space is allowed" $ do
        r <- expectRule expectedStandard "rule r (a) :- when focus-is-hole then solve"
        ruleParams r @?= ["a"]
    , -- A rule may apply everywhere, so 'when' is optional; a rule with no body
      -- does nothing, so 'then' is not.
      testCase "when is optional" $ do
        r <- expectRule expectedStandard "rule r :- then solve"
        ruleHead r @?= []
    , testCase "several instructions, separated by semicolons" $ do
        b <- bodyOf "attack; along; solve"
        b @?= [Do Attack, Do Along, Do Solve]
    , testCase "a binding instruction" $ do
        b <- bodyOf "x = resolve hint"
        b @?= [Bind "x" (Op.Resolve (Ref "hint"))]
    , -- The hyphens are the reason the lexer was widened this phase: §8 and
      -- OBJECTIVE.md have always written rule and test names this way.
      testCase "a hyphenated name is one identifier" $ do
        r <- expectRule expectedStandard "rule elab-app :- when focus-is-hole then solve"
        ruleName r @?= GlobalName "elab-app"
    ]

-- --------------------------------------------------------------------------
-- Mistakes
-- --------------------------------------------------------------------------

mistakes :: TestTree
mistakes =
  testGroup
    "mistakes"
    [ refused "an unknown test word"
        "rule r :- when focus-is-purple then solve"
        [NoSuchTest (GlobalName "r") "focus-is-purple"]
    , refused "an unknown op word"
        "rule r :- when focus-is-hole then frobnicate"
        [NoSuchOp (GlobalName "r") 0 "frobnicate"]
    , refused "too many arguments"
        "rule r :- when focus-is-hole then solve x"
        [BadOperands (GlobalName "r") 0 "solve"]
    , refused "too few arguments"
        "rule r :- when focus-is-hole then unify x"
        [BadOperands (GlobalName "r") 0 "unify"]
    , refused "a position where a name was wanted"
        "rule r :- when focus-is-hole then try 3"
        [BadOperands (GlobalName "r") 0 "try"]
    , refused "calling a rule that is not in the base"
        "rule r :- when focus-is-hole then call nonesuch x"
        [NoSuchRuleCalled (GlobalName "r") 0 "nonesuch"]
    , -- §3.7: a declaration is a command, never a rule-body operation. It is
      -- refused in resolution now, one step before 'validate' would have —
      -- which is why 'validate''s own check stays reachable only for a rule
      -- built in Haskell.
      refused "a declaration in a body"
        "rule r :- when focus-is-hole then data"
        [DeclarationInBody (GlobalName "r") 0]
    , refused "every mistake, not the first"
        "rule r :- when focus-is-purple then frobnicate; solve x"
        [ NoSuchTest (GlobalName "r") "focus-is-purple"
        , NoSuchOp (GlobalName "r") 0 "frobnicate"
        , BadOperands (GlobalName "r") 1 "solve"
        ]
    , testCase "a body is required" $
        case readRule expectedStandard "rule r :- when focus-is-hole" of
          Left _  -> pure ()
          Right r -> assertFailure ("parsed: " ++ show r)
    ]
  where
    refused what src expected =
      testCase what $ case readRuleErrors src of
        Just es -> es @?= expected
        Nothing -> assertFailure ("was accepted: " ++ src)

    readRuleErrors src = case lexTokens src of
      Left _ -> Nothing
      Right ts -> case parseRule ts of
        Left _ -> Nothing
        Right raw -> case resolveRule expectedStandard raw of
          Left es -> Just es
          Right _ -> Nothing
