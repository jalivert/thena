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
  , Test (..)
  , Instr (..)
  , Op (..)
  , Operand (..)
  , Rule (..)
  , Value (..)
  , opKeyword
  )
import qualified Thena.Ops as Op
import Thena.Rules
  ( RuleBase (..)
  , RuleError (..)
  , allRules
  , resolveRule
  , everyTest
  , testOperands
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
    , text
    , headOperands
    , regions
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
readRule :: String -> Either String Rule
readRule src = case lexTokens src of
  Left e -> Left ("lex: " ++ show e)
  Right ts -> case parseRule ts of
    Left e -> Left ("parse: " ++ show e)
    Right raw -> case resolveRule raw of
      Left es -> Left ("resolve: " ++ show es)
      Right r -> Right r

expectRule :: String -> IO Rule
expectRule src = either (assertFailure . ((src ++ " — ") ++)) pure (readRule src)

-- | A rule whose body is the one instruction under test.
bodyOf :: String -> IO [Instr]
bodyOf src = ruleBody <$> expectRule ("rule r :- when focus-is-hole then " ++ src)

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

    , testCase "its rules are exactly the expected ones, in order" $ do
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
  , ("resolve-core r", Op.ResolveCore (Ref "r"))
  , ("elim-spine t", Op.ElimSpine (Ref "t"))
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
  , ("prim-attack",  Attack)
  , ("prim-lambda",   IntroPi Nothing)
  , ("prim-lambda x", IntroPi (Just (Ref "x")))
  , ("prim-let",      IntroLet Nothing)
  , ("prim-let x",    IntroLet (Just (Ref "x")))
  , ("prim-try x",   Try (Ref "x"))
  , ("prim-regret",  Regret)
  , ("prim-solve",   Solve)
  , ("prim-abandon", Abandon)
  , ("prim-prove",   Prove)
  , ("expand-implicits t", Op.ExpandImplicits (Ref "t"))
  , ("app-head t", Op.AppHead (Ref "t"))
  , ("app-first-argument t", Op.AppFirstArgument (Ref "t"))
  , ("app-tail t", Op.AppTail (Ref "t"))
  , ("apply-next f n", Op.ApplyNext (Ref "f") (Ref "n"))
  , ("certify x",    Certify (Ref "x"))
  , ("prim-eliminate x", Op.Eliminate (Ref "x"))
  , ("prim-apply x",  Op.Apply (Ref "x"))
  , ("goal",          Goal)
  , ("here",          Here)
  , ("arrow x y",     Arrow (Ref "x") (Ref "y"))
  , ("apply-to x y",  ApplyTo (Ref "x") (Ref "y"))
  , ("fresh-name x",  FreshName (Ref "x"))
  , ("typeof x",      Typing (Ref "x"))
  , ("define x y",    Define (Ref "x") (Ref "y"))
  , ("fresh-universe", Op.FreshUniverse)
  , ("resolve-name x", Op.ResolveName (Ref "x"))
  ]

vocabulary :: TestTree
vocabulary =
  testGroup
    "vocabulary"
    [ testGroup "every op reads back" (map opCase everyOp)
    , testGroup "every op's keyword is the word it is written with"
        (map keywordCase everyOp)
    , testGroup "every test reads back" (map testCase' allTests)
    , -- **The name is recorded and nothing is looked up** (phase 23), which is
      -- what lets a rule call itself and call rules written after it.
      testCase "call records a name, and resolves nothing" $ do
        b <- bodyOf "call try x"
        b @?= [Do (Call (GlobalName "try") [Ref "x"])]

    , testCase "including a name no rule bears" $ do
        b <- bodyOf "call nonesuch x"
        b @?= [Do (Call (GlobalName "nonesuch") [Ref "x"])]
    ]
  where
    opCase (src, expected) =
      testCase src $ do
        b <- bodyOf src
        b @?= [Do expected]

    keywordCase (src, expected) =
      testCase src $ Just (opKeyword expected) @?= listToMaybe (words src)

    -- **'everyTest', not a copy of it.** This was a hand-written list until MS4
    -- phase 47, and it silently did not grow when that phase added a test —
    -- the same hazard that still stands for 'everyOp' below, arriving one type
    -- over. The list is exported precisely so this cannot happen again.
    allTests = everyTest

    -- A test taking operands is written in parentheses, so the parameters it
    -- names have to exist. The assertion is on the word and on what was
    -- written after it rather than on the 'Test' itself, because 'everyTest'
    -- carries a placeholder operand and this rule writes real ones.
    testCase' t =
      testCase (testWord t) $ do
        r <- expectRule
               ("rule r " ++ unwords params ++ " :- when " ++ written
                  ++ " then prim-solve")
        map testWord (ruleHead r) @?= [testWord t]
        map testOperands (ruleHead r) @?= [map Ref params]
      where
        params = [ "p" ++ show i | i <- [1 .. length (testOperands t)] ]
        written = case params of
          [] -> testWord t
          _  -> "(" ++ unwords (testWord t : params) ++ ")"

-- --------------------------------------------------------------------------
-- A test written with operands (MS4 phase 47)
-- --------------------------------------------------------------------------

-- | **A head is a run of tests with nothing between them**, so a test taking
-- operands is parenthesised and a bare word is a test of none. The ambiguity
-- the brackets answer is the one the REPL's argument runs have, and it is
-- answered the same way: without them @when focus-is-hole goal-type-is-pi@
-- reads as one test applied to another word.
--
-- **The existing spellings do not move**, which is why this shape and not
-- semicolons between tests — every rule already written, and every golden,
-- stays as it is.
headOperands :: TestTree
headOperands =
  testGroup
    "a test may take operands"
    [ testCase "parenthesised, it takes a parameter" $ do
        r <- expectRule "rule r s :- when (surface-is-name s) then prim-solve"
        ruleHead r @?= [SurfaceIsName (Ref "s")]

    , testCase "beside bare ones, in either order" $ do
        r <- expectRule
               "rule r s :- when focus-is-hole (surface-is-name s) goal-type-is-pi \
               \then prim-solve"
        ruleHead r @?= [FocusIsHole, SurfaceIsName (Ref "s"), GoalTypeIsPi]

    , testCase "a literal is accepted where a name is" $ do
        r <- expectRule "rule r :- when (surface-is-name \"x\") then prim-solve"
        ruleHead r @?= [SurfaceIsName (Lit (VText "x"))]

    , -- Every operand of a head must be one of the rule's own parameters: a
      -- head runs before the body, so there is no earlier binding it could
      -- have come from.
      testCase "a head naming something that is not a parameter is refused" $ do
        r <- expectRule "rule r s :- when (surface-is-name q) then prim-solve"
        validate r @?= [UnboundInHead (GlobalName "r") "q"]

    , testCase "and a parameter it does name is fine" $ do
        r <- expectRule "rule r s :- when (surface-is-name s) then prim-solve"
        validate r @?= []

    , testCase "the wrong number of operands is refused" $
        case readRule "rule r s :- when (surface-is-name s s) then prim-solve" of
          Left _  -> pure ()
          Right _ -> assertFailure "two operands should not resolve"

    , testCase "and so is a bare word that wanted one" $
        case readRule "rule r s :- when surface-is-name then prim-solve" of
          Left _  -> pure ()
          Right _ -> assertFailure "no operands should not resolve"

    , -- 'Down' is the only op that takes a position, so a head has no use for
      -- one and says so rather than resolving it to something odd.
      testCase "a position is not a head operand" $
        case readRule "rule r s :- when (surface-is-name 2) then prim-solve" of
          Left _  -> pure ()
          Right _ -> assertFailure "a position should not resolve"
    ]

-- --------------------------------------------------------------------------
-- The shape of a rule
-- --------------------------------------------------------------------------

shapes :: TestTree
shapes =
  testGroup
    "shape"
    [ testCase "no parameters, no parentheses" $ do
        r <- expectRule "rule r :- when focus-is-hole then prim-solve"
        ruleParams r @?= []
    , -- **No parentheses and no commas** — corrected by the user 2026-08-25,
      -- so that a definition and a call site write their arguments alike.
      testCase "parameters are a bare run of names" $ do
        r <- expectRule "rule r a b c :- when focus-is-hole then prim-solve"
        ruleParams r @?= ["a", "b", "c"]
    , -- A rule may apply everywhere, so 'when' is optional; a rule with no body
      -- does nothing, so 'then' is not.
      testCase "when is optional" $ do
        r <- expectRule "rule r :- then prim-solve"
        ruleHead r @?= []
    , testCase "several instructions, separated by semicolons" $ do
        b <- bodyOf "prim-attack; along; prim-solve"
        b @?= [Do Attack, Do Along, Do Solve]
    , testCase "a binding instruction" $ do
        b <- bodyOf "x = typeof y"
        b @?= [Bind "x" (Typing (Ref "y"))]
    , -- The hyphens are the reason the lexer was widened this phase: §8 and
      -- OBJECTIVE.md have always written rule and test names this way.
      testCase "a hyphenated name is one identifier" $ do
        r <- expectRule "rule elab-app :- when focus-is-hole then prim-solve"
        ruleName r @?= GlobalName "elab-app"
    ]

-- --------------------------------------------------------------------------
-- Text literals (phase 22b)
-- --------------------------------------------------------------------------

-- | @"…"@, at the user's instruction: *"Rules absolutely need a string
-- literal."* Without one @say@, @ask@ and @concat@ had keywords that resolved
-- and nothing they could be given.
text :: TestTree
text =
  testGroup
    "text literals"
    [ testCase "say" $ do
        b <- bodyOf "say \"attacking\""
        b @?= [Do (Say (Lit (VText "attacking")))]

    , testCase "concat, both sides" $ do
        b <- bodyOf "m = concat \"no rule for \" g"
        b @?= [Bind "m" (Concat (Lit (VText "no rule for ")) (Ref "g"))]

    , -- The op this was really missing: a rule can now interrogate the user.
      testCase "ask" $ do
        b <- bodyOf "x = ask \"which one?\" name"
        b @?= [Bind "x" (Ask (Lit (VText "which one?")) AName)]

    , testCase "the empty string" $ do
        b <- bodyOf "say \"\""
        b @?= [Do (Say (Lit (VText "")))]

    , testCase "the three escapes" $ do
        b <- bodyOf "say \"a \\\"q\\\" b\\\\c\\nd\""
        b @?= [Do (Say (Lit (VText "a \"q\" b\\c\nd")))]

    , -- Reserved characters are ordinary inside a string: it is one token, and
      -- the lexer never looks inside it.
      testCase "reserved characters are ordinary inside a string" $ do
        b <- bodyOf "say \"( ) { } ; , :- -> λ\""
        b @?= [Do (Say (Lit (VText "( ) { } ; , :- -> λ")))]

    , -- §7.2's bargain: an op given the wrong kind of value fails at run time,
      -- not in the grammar. So this resolves and would fail when run.
      testCase "text is accepted wherever an operand is" $ do
        b <- bodyOf "prim-try \"not a term\""
        b @?= [Do (Try (Lit (VText "not a term")))]

    , testCase "an unterminated string does not lex" $
        case readRule "rule r :- when focus-is-hole then say \"oops" of
          Left _  -> pure ()
          Right r -> assertFailure ("read: " ++ show r)

    , testCase "a rule name is still a name, not text" $
        case readRule "rule r :- when focus-is-hole then call \"try\" x" of
          Left _  -> pure ()
          Right r -> assertFailure ("read: " ++ show r)
    ]

-- --------------------------------------------------------------------------
-- Mistakes
-- --------------------------------------------------------------------------

-- | Tagged regions in a rule body (MS5 phase 61b).
--
-- The fence never appears literally in a test's source: 'tagged' builds it, so
-- that this module stays readable and so that a stray backtick in a string
-- literal cannot quietly change what a case is testing.
regions :: TestTree
regions =
  testGroup
    "tagged regions (MS5 phase 61b)"
    [ testCase "a surface region resolves, and is finished at load" $ do
        -- @elaborate@ names no op, so it is a call to the rule of that name
        -- (phase 25e). What this checks is that the region reached it at all.
        b <- bodyOf ("elaborate " ++ tagged "surface" "f x")
        map opWord b @?= ["call"]
    , testCase "a core region resolves to the instruction that will resolve it" $ do
        b <- bodyOf ("t = resolve-core " ++ tagged "core" "Type\8320")
        map opWord b @?= ["resolve-core"]
    , testCase "an empty region parses as a region, and its contents still must" $
        -- The fence is Thena's and the contents are the embedded language's.
        -- Emptiness is legal to *delimit* and is not a surface term, so this
        -- fails inside the region rather than at it.
        case errs ("say " ++ tagged "surface" "") of
          Just [BadRegion (GlobalName "r") 0 "surface" _] -> pure ()
          other -> assertFailure ("expected a BadRegion, got " ++ show other)
    , testCase "corners are the other spelling of a core region" $ do
        b <- bodyOf "t = resolve-core \8988 Type\8320 \8989"
        map opWord b @?= ["resolve-core"]
    , testCase "and the ASCII corners are too" $ do
        b <- bodyOf "t = resolve-core [| Type\8320 |]"
        map opWord b @?= ["resolve-core"]
    , testCase "angle brackets are the other spelling of a surface region" $ do
        b <- bodyOf "elaborate \10216f x\10217"
        map opWord b @?= ["call"]
    , testCase "a tag no language answers to is refused at load" $
        errs ("elaborate " ++ tagged "agda" "f x")
          @?= Just [NoSuchTag (GlobalName "r") 0 "agda"]
    , testCase "contents that do not parse in the tag's language are refused" $
        case errs ("elaborate " ++ tagged "surface" "(") of
          Just [BadRegion (GlobalName "r") 0 "surface" _] -> pure ()
          other -> assertFailure ("expected a BadRegion, got " ++ show other)
    , testCase "a region may not appear in a head" $
        -- Parenthesised because a test with operands is (phase 47).
        case headErrs ("(surface-is-name " ++ tagged "surface" "x" ++ ")") of
          Just [BadTestOperands (GlobalName "r") "surface-is-name"] -> pure ()
          other -> assertFailure ("expected the head to refuse it, got " ++ show other)
    ]
  where
    tick = toEnum 96 :: Char

    tagged tag src = tag ++ [tick] ++ src ++ [tick]

    opWord i = case i of
      Bind _ o -> opKeyword o
      Do o     -> opKeyword o

    errs src = readErrors ("rule r :- when focus-is-hole then " ++ src)

    headErrs src = readErrors ("rule r :- when " ++ src ++ " then prim-solve")

    readErrors src = case lexTokens src of
      Left _ -> Nothing
      Right ts -> case parseRule ts of
        Left _ -> Nothing
        Right raw -> case resolveRule raw of
          Left es -> Just es
          Right _ -> Nothing

mistakes :: TestTree
mistakes =
  testGroup
    "mistakes"
    [ refused "an unknown test word"
        "rule r :- when focus-is-purple then prim-solve"
        [NoSuchTest (GlobalName "r") "focus-is-purple"]
    , -- **A word that names no op is a call** (phase 25e), so this is no
      -- longer a load-time refusal: it resolves, and finds no clause when it
      -- runs. The same trade phase 23 took for explicit @call@.
      testCase "an unknown op word is a rule call" $
        bodyOf "frobnicate x"
          >>= (@?= [Do (Call (GlobalName "frobnicate") [Ref "x"])])
    , -- **An op word at an arity the op does not have is a CALL** (MS5 phase
      -- 62b, the user's decision). It was 'BadOperands' until then, so that
      -- @claim x@ was caught when the base loaded; his design for the asking
      -- half of the component tactics needs the other reading — @claim ty@ is
      -- the one-argument rule of that name, and @claim n ty@ is the op.
      testCase "an op word at another arity is a call" $
        bodyOf "prim-solve x y"
          >>= (@?= [Do (Call (GlobalName "prim-solve") [Ref "x", Ref "y"])])
    , testCase "one argument too many is a call too" $
        bodyOf "prim-solve x"
          >>= (@?= [Do (Call (GlobalName "prim-solve") [Ref "x"])])
    , testCase "and one too few" $
        bodyOf "unify x" >>= (@?= [Do (Call (GlobalName "unify") [Ref "x"])])
    , -- The arity the op /does/ have is still the op, which is what stops the
      -- reading above from swallowing every word.
      testCase "the arity the op has is still the op" $
        bodyOf "unify x y" >>= (@?= [Do (Unify (Ref "x") (Ref "y"))])
    , -- A wrong /operand/ is still a mistake about the op: this is an arity the
      -- op has, so nothing falls through.
      refused "a position where a name was wanted"
        "rule r :- when focus-is-hole then prim-try 3"
        [BadOperands (GlobalName "r") 0 "prim-try"]
    , -- §3.7: a declaration is a command, never a rule-body operation.
      --
      -- **Refused one step earlier again as of MS4 phase 42b**: @data@ is a
      -- keyword now, so a rule body carrying it does not lex into a body word
      -- at all and the parser stops it. It used to reach resolution and come
      -- back as @DeclarationInBody@, which is why 'validate''s own check has
      -- been reachable only for a rule built in Haskell since before that.
      testCase "a declaration in a body" $
        case lexTokens "rule r :- when focus-is-hole then data" of
          Left _  -> pure ()
          Right ts -> case parseRule ts of
            Left _  -> pure ()
            Right r -> assertFailure ("parsed: " ++ show r)
    , refused "every mistake, not the first"
        "rule r :- when focus-is-purple then frobnicate; prim-try 3"
        [ NoSuchTest (GlobalName "r") "focus-is-purple"
        , BadOperands (GlobalName "r") 1 "prim-try"
        ]
    , testCase "a body is required" $
        case readRule "rule r :- when focus-is-hole" of
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
        Right raw -> case resolveRule raw of
          Left es -> Just es
          Right _ -> Nothing
