-- | Rule-base files: the header, the ordered list, and what a load refuses.
--
-- All of it is pure — 'Thena.Driver.loadRuleBases' takes file /contents/, not
-- paths (§12 invariant 4) — so the paths here are made up and nothing is read.
-- The one test that touches the real file is "Thena.RuleSyntaxTests"; the one
-- that drives the real REPL is "Thena.GoldenTests".
--
-- Deliberately not a golden transcript: @:bases@ prints the path a base came
-- from, and for the shipped base that is an absolute path that differs on every
-- machine.
module Thena.RuleFileTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Term (GlobalName (..))
import Thena.Driver
  ( CommandError (..)
  , Response (..)
  , RuleFileError (..)
  , Session (..)
  , command
  , loadRuleBases
  , newSession
  , baseHead
  )
import Thena.Engine (Machine (rules))
import Thena.Ops (Rule (..))
import Thena.Rules (RuleBase (..), RuleError (..))

tests :: TestTree
tests = testGroup "rule files (§8)" [headers, loading, ordering, refusals, commands]

-- --------------------------------------------------------------------------
-- The header
-- --------------------------------------------------------------------------

-- | An optional @\"\"\"…\"\"\"@ description, then @rule base ‹name› where@ — read
-- textually before the lexer sees anything, which is what lets a description
-- hold characters the lexer reserves.
--
-- **The description moved above the header at phase 25e** (his change). The
-- third component of the result is how many lines the head took, which is what
-- the caller blanks so later positions still name the right line.
headers :: TestTree
headers =
  testGroup
    "header"
    [ testCase "name only" $
        baseHead ["rule base standard where"] @?= Just ("standard", Nothing, 1)
    , testCase "a description above it" $
        baseHead ["\"\"\"the ones we start with\"\"\"", "", "rule base standard where"]
          @?= Just ("standard", Just "the ones we start with", 3)
    , -- The characters the lexer reserves. They never reach it, which is the
      -- whole reason the head is read this way.
      testCase "a description may contain reserved characters" $
        baseHead ["\"\"\"(things; quoted, bracketed)\"\"\"", "rule base tidy where"]
          @?= Just ("tidy", Just "(things; quoted, bracketed)", 2)
    , -- What the one-line form could never do: the delimiter is a delimiter,
      -- so @where@ is just a word.
      testCase "a description may contain the word where" $
        baseHead ["\"\"\"where it all begins\"\"\"", "rule base start where"]
          @?= Just ("start", Just "where it all begins", 2)
    , testCase "several lines" $
        baseHead ["\"\"\"", "one", "two", "\"\"\"", "rule base long where"]
          @?= Just ("long", Just "one\ntwo", 5)
    , testCase "blank lines before and between are skipped" $
        baseHead ["", "\"\"\"d\"\"\"", "", "", "rule base b where"]
          @?= Just ("b", Just "d", 5)
    , -- Consume nothing rather than swallow the file: it then fails on the
      -- header, which is the true complaint.
      testCase "an unterminated description is no header" $
        baseHead ["\"\"\"never closed", "rule base b where"] @?= Nothing
    , testCase "no name is no header" $
        baseHead ["rule base where"] @?= Nothing
    , testCase "no trailing where is no header" $
        baseHead ["rule base standard"] @?= Nothing
    , -- The description is no longer part of the line, so extra words are not
      -- a description any more — they are a malformed header.
      testCase "words between the name and where are no header" $
        baseHead ["rule base standard and more where"] @?= Nothing
    , testCase "something else entirely" $
        baseHead ["rule attack :- then prim-attack"] @?= Nothing
    , testCase "an empty file is no header" $
        baseHead [] @?= Nothing
    ]

-- --------------------------------------------------------------------------
-- Loading
-- --------------------------------------------------------------------------

oneRule :: String
oneRule = "rule base tiny where\nrule solve :- when focus-is-guess then prim-solve\n"

load1 :: [(FilePath, String)] -> (Session, Response)
load1 = loadRuleBases newSession

basesOf :: Session -> [RuleBase]
basesOf = rules . sessionMachine

ruleNames :: RuleBase -> [String]
ruleNames b = [ n | Rule (GlobalName n) _ _ _ <- baseRules b ]

loading :: TestTree
loading =
  testGroup
    "loading"
    [ testCase "one base, named from its header" $ do
        let (s, resp) = load1 [("tiny.thena.rules", oneRule)]
        map baseName (basesOf s) @?= ["tiny"]
        map basePath (basesOf s) @?= ["tiny.thena.rules"]
        map ruleNames (basesOf s) @?= [["solve"]]
        case resp of
          BasesLoaded bs -> map baseName bs @?= ["tiny"]
          other          -> assertFailure (show other)

    , -- Rules may span lines — DECIDED by the user 2026-08-25 — and what ends
      -- one is the next 'rule' keyword.
      testCase "a rule may span lines" $ do
        let src = "rule base multi where\n\
                  \rule long :- when focus-is-hole\n\
                  \  then prim-attack\n\
                  \     ; along\n\
                  \     ; prim-solve\n\
                  \\n\
                  \rule short :- when focus-is-guess then prim-solve\n"
        case basesOf (fst (load1 [("m.thena.rules", src)])) of
          [b] -> do
            ruleNames b @?= ["long", "short"]
            map (length . ruleBody) (baseRules b) @?= [3, 1]
          bs  -> assertFailure (show (map baseName bs))

    , testCase "a file with no rules is still a base" $
        map ruleNames (basesOf (fst (load1 [("e.thena.rules", "rule base empty where\n")])))
          @?= [[]]

    , testCase "no header is refused" $
        refusal [("x.thena.rules", "rule solve :- when focus-is-guess then prim-solve")]
          @?= Just ("x.thena.rules", NoRuleHeader)

    , -- @frobnicate@ is a rule call as of phase 25e, so the only mistake left
      -- here is the arity one.
      testCase "a rule that does not resolve is refused, naming every mistake" $
        refusal [("x.thena.rules", "rule base b where\nrule r :- when focus-is-hole then frobnicate; prim-solve x")]
          @?= Just
                ( "x.thena.rules"
                , RuleIllFormed [BadOperands (GlobalName "r") 1 "prim-solve"]
                )

    , -- The load-time pass §2.4 asked for, now running at load rather than in
      -- a test.
      testCase "a rule that does not validate is refused" $
        refusal [("x.thena.rules", "rule base b where\nrule r :- when focus-is-hole then prim-try nothing")]
          @?= Just
                ( "x.thena.rules"
                , RuleIllFormed [UnboundInRule (GlobalName "r") 0 "nothing"] )
    ]
  where
    refusal fs = case snd (load1 fs) of
      RuleFileRefused p e -> Just (p, e)
      _                   -> Nothing

-- --------------------------------------------------------------------------
-- Several bases, in order
-- --------------------------------------------------------------------------

ordering :: TestTree
ordering =
  testGroup
    "several bases"
    [ testCase "search order is the order written" $
        map baseName (basesOf (fst (load1 [a, b]))) @?= ["a", "b"]

    , testCase "and the other way round" $
        map baseName (basesOf (fst (load1 [b, a]))) @?= ["b", "a"]

    , -- **Phase 23 made a call a run-time search**, so loading no longer has an
      -- opinion about who calls whom. Both orders load; which clause a call
      -- finds is decided when it runs, and a call that finds nothing fails
      -- with 'Thena.Errors.NoClauseMatched'.
      testCase "a call is not resolved at load time, either way round" $ do
        map baseName (basesOf (fst (load1 [a, caller]))) @?= ["a", "calls"]
        map baseName (basesOf (fst (load1 [caller, a]))) @?= ["calls", "a"]

    , testCase "and calling a name nothing defines still loads" $
        map baseName (basesOf (fst (load1 [caller]))) @?= ["calls"]

    , -- All or nothing: a bad second file leaves the first uninstalled, so a
      -- session never searches half of what was asked for.
      testCase "a refused file installs none of them" $
        basesOf (fst (load1 [a, ("bad.thena.rules", "no header here")])) @?= []

    , testCase "a load replaces the whole list" $
        let s1 = fst (load1 [a, b])
            s2 = fst (loadRuleBases s1 [b])
         in map baseName (basesOf s2) @?= ["b"]
    ]
  where
    a = ("a.thena.rules", "rule base a where\nrule helper t :- when focus-is-hole then prim-try t")
    b = ("b.thena.rules", "rule base b where\nrule solve :- when focus-is-guess then prim-solve")
    caller =
      ( "calls.thena.rules"
      , "rule base calls where\n\
        \rule c t :- when focus-is-hole then call helper t"
      )

-- --------------------------------------------------------------------------
-- What a load refuses
-- --------------------------------------------------------------------------

-- | The base may not change under a half-built development (the user, 2026-08-25).
refusals :: TestTree
refusals =
  testGroup
    "the base may not change under a proof"
    [ testCase "while one is being proved" $
        rejected (proving ":load extra.thena.rules")
          @?= Just (ProofUnderway (GlobalName "t"))

    , testCase "or while one is suspended" $
        rejected (suspended ":load extra.thena.rules")
          @?= Just (ProofsSuspended [GlobalName "t"])

    , testCase "but between theorems it is allowed" $
        case snd (command newSession ":load extra.thena.rules") of
          RulesRequested ps -> ps @?= ["extra.thena.rules"]
          other             -> assertFailure (show other)

    , -- A script and a rule base are two different operations.
      testCase "a script and a base in one load is refused" $
        rejected (command newSession ":load prelude.thena extra.thena.rules")
          @?= Just (MixedLoad ":load")

    , testCase "an ordinary script still loads" $
        case snd (command newSession ":load prelude.thena") of
          LoadRequested p -> p @?= "prelude.thena"
          other           -> assertFailure (show other)

    , -- "comma or space separated (or both)" — the user, 2026-08-25.
      testCase "several paths, commas and spaces" $
        case snd (command newSession ":load a.thena.rules, b.thena.rules c.thena.rules") of
          RulesRequested ps -> ps @?= ["a.thena.rules", "b.thena.rules", "c.thena.rules"]
          other             -> assertFailure (show other)
    ]
  where
    rejected (_, resp) = case resp of
      Rejected e -> Just e
      _          -> Nothing

    proving line =
      let (s, _) = command newSession ":theorem t : Type\8320"
       in command s line

    suspended line =
      let (s0, _) = command newSession ":theorem t : Type\8320"
          (s1, _) = command s0 ":suspend"
       in command s1 line

-- --------------------------------------------------------------------------
-- Listing
-- --------------------------------------------------------------------------

commands :: TestTree
commands =
  testGroup
    "listing"
    [ testCase ":bases with none loaded" $
        listed ":bases" newSession @?= Just []

    , testCase ":bases after a load" $ do
        let s = fst (load1 [("tiny.thena.rules", oneRule)])
        fmap (map baseName) (listed ":bases" s) @?= Just ["tiny"]

    , testCase ":rules lists the rules of every base, in order" $ do
        let s = fst (load1 [ ("tiny.thena.rules", oneRule)
                           , ("b.thena.rules", "rule base b where\nrule attack :- when focus-is-hole then prim-attack")
                           ])
        fmap (concatMap ruleNames) (ruled s) @?= Just ["solve", "attack"]
    ]
  where
    listed w s = case snd (command s w) of
      BasesListed bs -> Just bs
      _              -> Nothing
    ruled s = case snd (command s ":rules") of
      RulesListed bs -> Just bs
      _              -> Nothing
