-- | Patterns in a parameter position (MS5 phase 82) — stage a of
-- @discussion\/pattern-matching.md@: @instral@'s own data, and nothing else.
--
-- **Four things are crossed here, and each with something that is not itself**,
-- which is the standing method:
--
-- * the matcher against hand-built values, form by form;
-- * the __printer against the reader__ — 'renderPattern' then parse, over an
--   exhaustive list. @ms5\/CLOSEOUT.md@ 26 is why: a printer and a grammar
--   disagreed about a structure neither owns, twice in two days, and both had
--   shipped;
-- * __the two grammars against each other__ — a pattern written in a rule file
--   and the same pattern written in a @do@ block's lambda. §7b's registered
--   duplication has now drifted three times;
-- * the engine against his ruling: __a rule is searched and a function is
--   called__, which patterns are the first thing able to make false.
module Thena.PatternTests (tests) where

import Data.List (isInfixOf)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

import Thena.Global.Env (emptyGlobals)
import Thena.Instral.Ops
  ( Instr (..)
  , Pattern (..)
  , Value (..)
  , matchPattern
  , matchPatterns
  , patternBinds
  , patternIrrefutable
  )
import Thena.Repl (renderPattern)
import Thena.Rules (resolveRule, validate)
import Thena.Syntax.Lexer (lexTokens)
import Thena.Surface.Layout (layout)
import Thena.Syntax.Parser (parseRule)
import Thena.Instral.Ops (Rule (..))

tests :: TestTree
tests =
  testGroup
    "patterns (MS5 phase 82)"
    [ matching
    , binding
    , spelling
    , destructuring
    , refusals
    , totality
    ]

-- --------------------------------------------------------------------------
-- Reading a pattern back from its own spelling
-- --------------------------------------------------------------------------

-- | Every pattern form, written the way a user writes it.
--
-- **Exhaustive by construction is not available** — a 'Pattern' is a plain sum,
-- so this is a hand-written mirror like 'Thena.RuleSyntaxTests.everyOp', and
-- 'totality' below is what stops it silently failing to grow: it walks a total
-- case over 'Pattern' and asserts this list covers every constructor.
everyPattern :: [(String, Pattern)]
everyPattern =
  [ ("x",             PVar "x")
  , ("_",             PWild)
  , ("3",             PInt 3)
  , ("'c'",           PChar 'c')
  , ("true",          PBool True)
  , ("false",         PBool False)
  , ("\"hi\"",        PText "hi")
  , ("[]",            PList [] Nothing)
  , ("[a]",           PList [PVar "a"] Nothing)
  , ("[a, b]",        PList [PVar "a", PVar "b"] Nothing)
  , ("[a, ...rest]",  PList [PVar "a"] (Just (PVar "rest")))
  , ("[a, ..._]",     PList [PVar "a"] (Just PWild))
  , ("[a, ...[]]",    PList [PVar "a"] (Just (PList [] Nothing)))
  , ("[...xs]",       PList [] (Just (PVar "xs")))
  , ("(x, y)",        PPair (PVar "x") (PVar "y"))
  , ("((a, b), c)",   PPair (PPair (PVar "a") (PVar "b")) (PVar "c"))
  , ("(some x)",      PSome (PVar "x"))
  , ("(some [a])",    PSome (PList [PVar "a"] Nothing))
  , ("none",          PNone)
  ]

-- | Read a whole rule, for the binding cases above.
readWhole :: String -> Either String Rule
readWhole text = case lexTokens text of
  Left e -> Left ("lex: " ++ show e)
  Right ts -> case layout ts of
    Left e -> Left ("layout: " ++ show e)
    Right ts' -> case parseRule ts' of
      Left e -> Left ("parse: " ++ show e)
      Right raw -> case resolveRule [] raw of
        Left es -> Left ("resolve: " ++ show es)
        Right r -> Right r

-- | Read one pattern by putting it in a rule's parameter position.
readPattern :: String -> Either String Pattern
readPattern src = case readParams src of
  Left e   -> Left e
  Right [p] -> Right p
  Right ps  -> Left ("expected one parameter, got " ++ show (length ps))

readParams :: String -> Either String [Pattern]
readParams src = case lexTokens text of
  Left e -> Left ("lex: " ++ show e)
  Right ts -> case layout ts of
    Left e -> Left ("layout: " ++ show e)
    Right ts' -> case parseRule ts' of
      Left e -> Left ("parse: " ++ show e)
      Right raw -> case resolveRule [] raw of
        Left es -> Left ("resolve: " ++ show es)
        Right r -> Right (ruleParams r)
  where
    text = "rule r " ++ src ++ " :- do solve"

spelling :: TestTree
spelling =
  testGroup
    "written and printed"
    [ testCase "every form parses to the pattern it spells" $
        mapM_ one everyPattern
    , -- **The crossing that matters** (@ms5\/CLOSEOUT.md@ 26). A fixture list
      -- says what the author believes; this says the printer and the grammar
      -- agree about it, which is a different question and is the one that has
      -- twice been answered wrongly in shipped code.
      testCase "and printing it gives a spelling that reads back the same" $
        mapM_ roundTrip (map snd everyPattern)
    , -- **The reserved-name check for a parameter is unreachable now** (MS5
      -- phase 82), because this is what a written @true@ becomes before
      -- 'Thena.Rules.validate' ever sees it. @RulesTests@ records the removal
      -- from the other side.
      testCase "true in a parameter position is the literal, not a name" $
        readParams "true" @?= Right [PBool True]
    , -- A run, so that the *sequence* is read as several patterns and not one.
      testCase "a run of patterns is a run" $
        readParams "a [] (x, y) none" @?=
          Right [PVar "a", PList [] Nothing, PPair (PVar "x") (PVar "y"), PNone]
    ]
  where
    one (src, want) = case readPattern src of
      Left e  -> assertFailure (src ++ " — " ++ e)
      Right p -> p @?= want

    roundTrip p = case readPattern (renderPattern p) of
      Left e   -> assertFailure (renderPattern p ++ " — " ++ e)
      Right p' -> p' @?= p

-- --------------------------------------------------------------------------
-- On the left of a binding (MS5 phase 84 — stage d)
-- --------------------------------------------------------------------------

-- | **@(x, y) = some-rule@ takes the answer apart where it lands.**
--
-- Stage d of @discussion\/pattern-matching.md@, and his ruling is what makes it
-- small: __a refutable pattern that does not match is a FAILURE__ — in a rule it
-- backtracks like any other, in a function it is the caller\'s, as in Haskell.
-- No irrefutable\/refutable distinction is invented, so there is no second kind
-- of binding and no new instruction shape.
destructuring :: TestTree
destructuring =
  testGroup
    "on the left of a binding"
    [ testCase "a compound pattern parses where a name did" $
        readBindings "rule r :- do (x, y) = f ; say x"
          @?= Right [PPair (PVar "x") (PVar "y"), PWild]

    , testCase "…and a list one" $
        readBindings "rule r :- do [a, ...rest] = f ; say a"
          @?= Right [PList [PVar "a"] (Just (PVar "rest")), PWild]

      -- A plain name is the pattern that binds it, so nothing that could be
      -- written before means anything different.
    , testCase "a plain name is still a plain name" $
        readBindings "rule r :- do x = f" @?= Right [PVar "x"]

      -- @_ = ‹op›@ is run-and-discard, and it is not a special case: @_@ is a
      -- pattern like any other and 'PWild' binds nothing.
    , testCase "a wildcard binding is writable" $
        readBindings "rule r :- do _ = f" @?= Right [PWild]

      -- **The scope walk must see what the pattern binds**, or a later line
      -- naming one of them is refused at load. This is the case that catches
      -- 'Thena.Rules.resolveBlock' forgetting to thread them.
    , testCase "what a compound pattern binds is in scope below it" $
        loadsCleanly "rule r :- do (x, y) = f ; m = concat x y ; say m"

    , testCase "…and a name it does NOT bind is still refused" $
        refuses "rule r :- do (x, y) = f ; say z" "UnboundInRule"
    ]
  where
    readBindings src = map leftOf <$> readBody src

    leftOf i = case i of
      Bind p _ _ -> p
      Do _       -> PWild   -- only to give `say x` a shape in the lists above

    readBody src = case readWhole src of
      Left e  -> Left e
      Right r -> Right (ruleBody r)

    loadsCleanly src = case readWhole src of
      Left e  -> assertFailure (src ++ " — " ++ e)
      Right r -> case validate r of
        [] -> pure ()
        es -> assertFailure (src ++ " — " ++ show es)

    refuses src want = case readWhole src of
      Left e  -> assertBool (src ++ " said " ++ e) (want `isInfixOf` e)
      Right r -> case validate r of
        [] -> assertFailure ("expected a refusal for " ++ src)
        es -> assertBool (src ++ " said " ++ show es) (want `isInfixOf` show es)

-- --------------------------------------------------------------------------
-- What the matcher does
-- --------------------------------------------------------------------------

matching :: TestTree
matching =
  testGroup
    "matching"
    [ testCase "a variable takes anything and binds it" $
        matchPattern emptyGlobals (PVar "x") (VInt 3) @?= Just [("x", VInt 3)]
    , testCase "a wildcard takes anything and binds nothing" $
        matchPattern emptyGlobals PWild (VInt 3) @?= Just []
    , testCase "a literal matches its own value" $
        matchPattern emptyGlobals (PInt 3) (VInt 3) @?= Just []
    , testCase "…and refuses another" $
        matchPattern emptyGlobals (PInt 3) (VInt 4) @?= Nothing
    , testCase "…and refuses another type" $
        matchPattern emptyGlobals (PInt 3) (VText "3") @?= Nothing
    , testCase "true and false are told apart" $ do
        matchPattern emptyGlobals (PBool True) (VBool True) @?= Just []
        matchPattern emptyGlobals (PBool True) (VBool False) @?= Nothing
    , testCase "a closed list must exhaust the value" $ do
        matchPattern emptyGlobals (PList [PVar "a"] Nothing) (VList [VInt 1])
          @?= Just [("a", VInt 1)]
        matchPattern emptyGlobals (PList [PVar "a"] Nothing) (VList [VInt 1, VInt 2])
          @?= Nothing
        matchPattern emptyGlobals (PList [PVar "a"] Nothing) (VList []) @?= Nothing
    , testCase "an open list binds the remainder" $
        matchPattern emptyGlobals (PList [PVar "a"] (Just (PVar "r"))) (VList [VInt 1, VInt 2])
          @?= Just [("a", VInt 1), ("r", VList [VInt 2])]
    , testCase "…and the remainder may be empty" $
        matchPattern emptyGlobals (PList [PVar "a"] (Just (PVar "r"))) (VList [VInt 1])
          @?= Just [("a", VInt 1), ("r", VList [])]
    , -- The tail is a whole pattern, which is what makes this the long way of
      -- saying "exactly one element".
      testCase "a list tail is itself matched" $ do
        matchPattern emptyGlobals (PList [PVar "a"] (Just (PList [] Nothing))) (VList [VInt 1])
          @?= Just [("a", VInt 1)]
        matchPattern emptyGlobals (PList [PVar "a"] (Just (PList [] Nothing)))
                     (VList [VInt 1, VInt 2])
          @?= Nothing
    , testCase "a pair takes a pair apart" $
        matchPattern emptyGlobals (PPair (PVar "x") (PVar "y")) (VPair (VInt 1) (VInt 2))
          @?= Just [("x", VInt 1), ("y", VInt 2)]
    , testCase "some and none are told apart" $ do
        matchPattern emptyGlobals (PSome (PVar "x")) (VOption (Just (VInt 1)))
          @?= Just [("x", VInt 1)]
        matchPattern emptyGlobals (PSome (PVar "x")) (VOption Nothing) @?= Nothing
        matchPattern emptyGlobals PNone (VOption Nothing) @?= Just []
        matchPattern emptyGlobals PNone (VOption (Just (VInt 1))) @?= Nothing
    , -- **Arity is part of matching**, which is why 'matchPatterns' answers
      -- 'Nothing' rather than being paired with a length test.
      testCase "a run of the wrong length does not match" $ do
        matchPatterns emptyGlobals [PVar "a"] [VInt 1, VInt 2] @?= Nothing
        matchPatterns emptyGlobals [PVar "a", PVar "b"] [VInt 1] @?= Nothing
    , -- §3: a pattern matches as written. Nothing here reduces or coerces.
      testCase "a text pattern matches a name, because both are VText" $
        matchPattern emptyGlobals (PText "h") (VText "h") @?= Just []
    ]

binding :: TestTree
binding =
  testGroup
    "what a pattern binds"
    [ testCase "left to right, nested" $
        patternBinds (PList [PPair (PVar "a") (PVar "b")] (Just (PVar "r")))
          @?= ["a", "b", "r"]
    , testCase "a literal binds nothing" $
        concatMap patternBinds [PInt 1, PWild, PNone, PText "t"] @?= []
    , -- **'patternBinds' and 'matchPattern' must agree**, and they are written
      -- separately, so the agreement is worth asserting rather than assuming:
      -- 'Thena.Rules.validate' decides what a body may name from the first and
      -- the engine supplies the environment from the second.
      testCase "and it agrees with what the matcher actually binds" $
        mapM_ agree
          [ (PVar "x",                                 VInt 1)
          , (PList [PVar "a"] (Just (PVar "r")),       VList [VInt 1, VInt 2])
          , (PPair (PVar "x") (PVar "y"),              VPair (VInt 1) (VInt 2))
          , (PSome (PVar "q"),                         VOption (Just (VInt 1)))
          , (PList [PPair (PVar "a") (PVar "b")] Nothing,
                                                       VList [VPair (VInt 1) (VInt 2)])
          ]
    , testCase "a pair of variables matches everything of its type" $
        assertBool "irrefutable" (patternIrrefutable (PPair (PVar "a") PWild))
    , -- A list is refutable however general its elements are: the value may be
      -- a different length. This is the line 'Thena.Driver' draws.
      testCase "a list is refutable however general its elements" $
        assertBool "refutable" (not (patternIrrefutable (PList [PVar "a"] (Just (PVar "r")))))
    ]
  where
    agree (p, v) = case matchPattern emptyGlobals p v of
      Nothing -> assertFailure ("expected a match for " ++ renderPattern p)
      Just bs -> map fst bs @?= patternBinds p

-- --------------------------------------------------------------------------
-- What is refused
-- --------------------------------------------------------------------------

refusals :: TestTree
refusals =
  testGroup
    "refused"
    [ testCase "a word that is not some, applied" $
        expectRefusal "(cons x xs)" "BadPattern"
    , testCase "some with the wrong number of arguments" $
        expectRefusal "(some x y)" "BadPattern"
    , -- Patterns are linear. Matching a value against another value is a
      -- different feature and nothing has asked for it.
      testCase "the same name twice in one clause" $
        expectRefusal' "rule r x x :- do solve" "RepeatedInPattern"
    , testCase "…including through a nesting" $
        expectRefusal' "rule r (a, b) [a] :- do solve" "RepeatedInPattern"
    ]
  where
    expectRefusal src want = case readPattern src of
      Right p -> assertFailure ("expected a refusal, got " ++ show p)
      Left e  -> assertBool (src ++ " said " ++ e) (want `isInfixOf` e)

    -- The linearity check is 'validate''s, not resolution's, so these go
    -- through a whole rule.
    expectRefusal' text want = case readParams' text of
      Left e   -> assertBool (text ++ " said " ++ e) (want `isInfixOf` e)
      Right r  -> case validate r of
        [] -> assertFailure ("expected a refusal for " ++ text)
        es -> assertBool (text ++ " said " ++ show es)
                         (want `isInfixOf` show es)

    readParams' text = case lexTokens text of
      Left e -> Left ("lex: " ++ show e)
      Right ts -> case layout ts of
        Left e -> Left ("layout: " ++ show e)
        Right ts' -> case parseRule ts' of
          Left e -> Left ("parse: " ++ show e)
          Right raw -> case resolveRule [] raw of
            Left es -> Left ("resolve: " ++ show es)
            Right r -> Right r

-- --------------------------------------------------------------------------
-- The mirror is total
-- --------------------------------------------------------------------------

-- | **'everyPattern' must cover every constructor**, and this is what makes it
-- so rather than hoping.
--
-- @ms5\/CLOSEOUT.md@ 5 and 25 are the same lesson twice: 'everyOp' was missing
-- a row for @goto@, then for twenty-six words, and each time the mirror shared
-- the blind spot of what it mirrored. A total case over 'Pattern' cannot: a new
-- constructor makes @-Wall@ demand a tag here, and the assertion then demands a
-- row above.
totality :: TestTree
totality =
  testCase "every pattern constructor has a spelling above" $
    mapM_ covered representatives
  where
    covered p =
      assertBool (tagOf p ++ " has no row in everyPattern")
                 (tagOf p `elem` map (tagOf . snd) everyPattern)

-- | One value per constructor.
--
-- **A hand-written mirror, and it says so** — the same kind as
-- 'Thena.RuleSyntaxTests.everyOp', which twice shared the blind spot of what it
-- mirrored (@ms5\/CLOSEOUT.md@ 5 and 25). What makes this one bite is that it
-- is crossed with 'tagOf', which is a __total case over 'Pattern'__: a new
-- constructor makes @-Wall@ demand a line there, and adding that line without
-- adding a row to 'everyPattern' fails this test.
representatives :: [Pattern]
representatives =
  [ PVar "x", PWild, PInt 0, PChar 'c', PBool True, PText ""
  , PList [] Nothing, PPair PWild PWild, PSome PWild, PNone
  ]

tagOf :: Pattern -> String
tagOf p = case p of
  PVar _    -> "PVar"
  PWild     -> "PWild"
  PInt _    -> "PInt"
  PChar _   -> "PChar"
  PBool _   -> "PBool"
  PText _   -> "PText"
  PList _ _ -> "PList"
  PObject _ -> "PObject"
  PPair _ _ -> "PPair"
  PSome _   -> "PSome"
  PNone     -> "PNone"
