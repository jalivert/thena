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
  , Stop (..)
  , Response (..)
  , RuleFileError (..)
  , Session (..)
  , command
  , loadRuleBases
  , newSession
  , baseHead
  )
import Thena.Engine (Machine (rules))
import qualified Thena.Engine as Engine
import Thena.Instral.Ops (Value (..))
import Thena.Errors (FailReason (..))
import Thena.Instral.Ops (Rule (..), Pattern (..))
import Thena.Rules (RuleBase (..), RuleError (..))

tests :: TestTree
tests =
  testGroup
    "rule files (§8)"
    [headers, loading, ordering, refusals, commands, argumentHeads, returning, primitives, walking]

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
      -- **And so are comment lines** (MS4 phase 43). The header is read
      -- textually, before the lexer, so it is the one place a comment has to be
      -- recognised a second time — and a rule base you could not comment above
      -- its own header would make the uniformity his ruling asked for a
      -- fiction.
    , testCase "comment lines before and between are skipped too" $
        baseHead ["-- what this is", "\"\"\"d\"\"\"", "-- and why", "rule base b where"]
          @?= Just ("b", Just "d", 4)
    , testCase "and -- without a space is not one, so the header is not found" $
        baseHead ["--nope", "rule base b where"] @?= Nothing
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
        baseHead ["rule attack :- do prim-attack"] @?= Nothing
    , testCase "an empty file is no header" $
        baseHead [] @?= Nothing
    ]

-- --------------------------------------------------------------------------
-- Loading
-- --------------------------------------------------------------------------

oneRule :: String
oneRule = "rule base tiny where\nrule solve :- when focus-is-guess do prim-solve\n"

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
                  \  do prim-attack\n\
                  \     ; along\n\
                  \     ; prim-solve\n\
                  \\n\
                  \rule short :- when focus-is-guess do prim-solve\n"
        case basesOf (fst (load1 [("m.thena.rules", src)])) of
          [b] -> do
            ruleNames b @?= ["long", "short"]
            map (length . ruleBody) (baseRules b) @?= [3, 1]
          bs  -> assertFailure (show (map baseName bs))

    , testCase "a file with no rules is still a base" $
        map ruleNames (basesOf (fst (load1 [("e.thena.rules", "rule base empty where\n")])))
          @?= [[]]

    , testCase "no header is refused" $
        refusal [("x.thena.rules", "rule solve :- when focus-is-guess do prim-solve")]
          @?= Just ("x.thena.rules", NoRuleHeader)

    , -- @frobnicate@ is a rule call as of phase 25e, and @prim-solve x@ is one
      -- too as of MS5 phase 62b — an op word at an arity the op does not have
      -- is a call. So the mistake left here is the scope one: @x@ is bound by
      -- nothing, which 'validate' catches when the file loads.
      testCase "a rule that does not resolve [] is refused, naming every mistake" $
        refusal [("x.thena.rules", "rule base b where\nrule r :- when focus-is-hole do frobnicate; prim-solve x")]
          @?= Just
                ( "x.thena.rules"
                , RuleIllFormed [UnboundInRule (GlobalName "r") 1 "x"]
                )

    , -- The load-time pass §2.4 asked for, now running at load rather than in
      -- a test.
      testCase "a rule that does not validate is refused" $
        refusal [("x.thena.rules", "rule base b where\nrule r :- when focus-is-hole do prim-try nothing")]
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

    , -- **But a name no loaded base defines is refused** — his ruling,
      -- 2026-09-15 (MS5 phase 92). The bases loaded together are the program,
      -- in either order; a call outside all of them is a type error.
      testCase "and calling a name nothing defines is refused" $
        map baseName (basesOf (fst (load1 [caller]))) @?= []

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
    a = ("a.thena.rules", "rule base a where\nrule helper t :- when focus-is-hole do prim-try t")
    b = ("b.thena.rules", "rule base b where\nrule solve :- when focus-is-guess do prim-solve")
    caller =
      ( "calls.thena.rules"
      , "rule base calls where\n\
        \rule c t :- when focus-is-hole do call helper t"
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
        rejected (command newSession ":load prelude.thena.script extra.thena.rules")
          @?= Just (MixedLoad ":load")

    , testCase "an ordinary script still loads" $
        case snd (command newSession ":load prelude.thena.script") of
          LoadRequested p -> p @?= "prelude.thena.script"
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

-- --------------------------------------------------------------------------
-- A head that asks about an argument, from the REPL (MS4 phase 47)
-- --------------------------------------------------------------------------

-- | **The phase working the way a user meets it.** Two clauses of one name,
-- one of which asks what it was called with, loaded from a written file and
-- called by typing the rule's name.
--
-- "Thena.CallTests" asks the same question of the engine; this asks it of the
-- driver, which is where a bare REPL argument becomes a
-- 'Thena.Instral.Ops.VSurface' in the first place.
argumentHeads :: TestTree
argumentHeads =
  testGroup
    "a loaded head may ask about its argument"
    [ testCase "a name takes the clause that asks for one" $
        said "pick \10216 foo \10217" @?= Just "that is a name"
    , testCase "and anything else falls through to the other" $
        said "pick \10216 Type\8320 -> Type\8320 \10217" @?= Just "that is not a name"
    ]
  where
    picking =
      "rule base pick where\n\
      \rule pick s :- when focus-is-hole (surface-is-name s) \
      \do say \"that is a name\"\n\
      \rule pick s :- when focus-is-hole do say \"that is not a name\"\n"

    -- A claim to stand in, then the call. The last thing said is the answer.
    said line =
      let (s0, _) = load1 [("pick.thena.rules", picking)]
          run s l = fst (command s l)
          s1 = foldl run s0 [":theorem t : Type\8321"]
       in case snd (command s1 line) of
            Ran msgs _ _ -> lastOf msgs
            other      -> error ("expected Ran, got " ++ show other)

    lastOf ms = case reverse ms of
      m : _ -> Just m
      []    -> Nothing

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
                           , ("b.thena.rules", "rule base b where\nrule attack :- when focus-is-hole do prim-attack")
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

-- --------------------------------------------------------------------------
-- A rule that returns, and a call written as an operand (MS5 phase 63)
-- --------------------------------------------------------------------------

-- | **The phase working the way a user meets it**, like 'argumentHeads' above:
-- written in a file, loaded, and called by typing a name.
--
-- @twice@ returns; @shout@ binds a call and passes another call as an operand,
-- which is what was unwritable before — it had to be split into
-- @a = twice t ; b = twice a@. "Thena.RulesTests" asks the engine the same
-- questions against a base built in Haskell.
returning :: TestTree
returning =
  testGroup
    "a loaded rule may return a value"
    [ testCase "a bound call is filled by the callee's return" $
        said "shout \"a\"" @?= Just "aaaa"
    , -- The nested operand really is evaluated: without it the inner @twice@
      -- would not run and the answer would be @aa@.
      testCase "and a nested call in an operand is one of the steps" $
        said "once \"a\"" @?= Just "aa"
    , -- **A callable some of whose clauses return and some do not.** That is
      -- the case inference cannot rule out — the clause that runs is chosen at
      -- run time — so 'Thena.Errors.NothingReturned' is still reachable and
      -- still names the binding it could not fill. A callable NO clause of
      -- which returns is refused when the file loads now; see 'illTyped'.
      testCase "a clause that does not return fails where the value was wanted" $
        stuck "half" @?= Just (NothingReturned (PVar "x"))
    ]
  where
    base =
      "rule base give where\n\
      \rule twice t :- do s = concat t t ; return s\n\
      \rule shout t :- do m = twice (twice t) ; say m\n\
      \rule once t :- do m = twice t ; say m\n\
      \rule sometimes t :- when focus-is-guess do return t\n\
      \rule sometimes t :- do say \"nothing to give\"\n\
      \rule half t :- do x = sometimes t ; say x\n"

    said line = case snd (command (loaded ()) line) of
      Ran msgs _ _ -> lastOf msgs
      other      -> error ("expected Ran, got " ++ show other)

    stuck word = case snd (command (loaded ()) (word ++ " \"a\"")) of
      Ran _ _ (Halted r) -> Just r
      other            -> error ("expected a halt, got " ++ show other)

    loaded () = fst (load1 [("give.thena.rules", base)])

    lastOf ms = case reverse ms of
      m : _ -> Just m
      []    -> Nothing

-- --------------------------------------------------------------------------
-- The primitives, end to end (MS5 phase 64)
-- --------------------------------------------------------------------------

-- | **Nothing calls these yet**, which is the milestone's doctrine rather than
-- an oversight — so the whole path is exercised here instead: written in a file,
-- lexed, parsed, resolved, returned by a rule, and read back out of the
-- machine's environment.
primitives :: TestTree
primitives =
  testGroup
    "instral's primitives"
    [ testCase "a number" $ bound "a" "do { a = pick }" @?= Just (VInt 42)
    , testCase "a character" $ bound "b" "do { b = glyph }" @?= Just (VChar 'x')
    , testCase "true" $ bound "c" "do { c = yes }" @?= Just (VBool True)
    , testCase "false" $ bound "d" "do { d = no }" @?= Just (VBool False)
    , testCase "and a string, which was always here" $
        bound "e" "do { e = word }" @?= Just (VText "hello")
    ]
  where
    base =
      "rule base prim where\n\
      \rule pick :- do return 42\n\
      \rule glyph :- do return 'x'\n\
      \rule yes :- do return true\n\
      \rule no :- do return false\n\
      \rule word :- do return \"hello\"\n"

    bound n line =
      let s0 = fst (load1 [("prim.thena.rules", base)])
       in lookup n (Engine.env (Engine.exec (sessionMachine (fst (command s0 line)))))

-- --------------------------------------------------------------------------
-- Walking a list with two clauses (MS5 phase 65)
-- --------------------------------------------------------------------------

-- | **The phase's point, in one rule.** A list is usable without @if@ and
-- without a second control structure, because a rule branches on its head — so
-- a fold is two clauses, one per shape, exactly as @intro-binders@ is two
-- clauses over a surface term.
--
-- **Rewritten in patterns at MS5 phase 86**, which is the phase's own
-- demonstration: it used to exercise two head tests and three ops that no
-- longer exist — @list-is-empty@, @list-is-cons@, @list-head@, @list-tail@,
-- @option-value@ — and says exactly the same thing with a parameter pattern per
-- clause and a destructuring binding. **The assertions did not move.**
walking :: TestTree
walking =
  testGroup
    "a rule walks a list"
    [ testCase "an empty list" $ said "shout []" @?= Just ""
    , testCase "and a list with elements" $
        said "shout [\"a\", \"b\", \"c\"]" @?= Just "abc"
    , -- The elements are operands, so a reference among them is read where the
      -- list is built.
      testCase "a pair, taken apart" $
        said "both (\"a\", \"b\")" @?= Just "ab"

      -- **The two ops that needed a FUNCTION and not a pattern** (MS5 phase
      -- 86). @list-head@ was **total** — it answered @none@ on the empty list,
      -- which its own comment called deliberate, /"so that the empty list needs
      -- no second answer and no caller has to ask before asking"/ — and a bare
      -- pattern is partial. Two clauses restore the totality, and these four
      -- cases are the ones that used to test the ops.
    , testCase "head' of the empty list is none" $
        said "peek []" @?= Just "none"
    , testCase "…and of a non-empty one is some" $
        said "peek [\"a\", \"b\"]" @?= Just "a"
    , testCase "tail' drops one" $
        said "rest [\"a\", \"b\"]" @?= Just "b"
    , testCase "…and the empty list has an empty tail" $
        said "rest []" @?= Just "none"
    ]
  where
    base =
      "rule base walk where\n\
      \rule join [] :- do return \"\"\n\
      \rule join [c, ...t] :- do r = join t\n\
      \     ; s = concat c r\n\
      \     ; return s\n\
      \rule shout xs :- do m = join xs ; say m\n\
      \rule both p :- do (a, b) = p\n\
      \     ; s = concat a b\n\
      \     ; say s\n\
      \head\x27 [] = none\n\
      \head\x27 [a, ..._] = some a\n\
      \tail\x27 [] = do { return [] }\n\
      \tail\x27 [_, ...r] = do { return r }\n\
      \rule peek xs :- do h = head\x27 xs ; say-option h\n\
      \rule rest xs :- do t = tail\x27 xs ; h = head\x27 t ; say-option h\n\
      \rule say-option none :- do say \"none\"\n\
      \rule say-option (some v) :- do say v\n"

    said line =
      let s0 = fst (load1 [("walk.thena.rules", base)])
       in case snd (command s0 line) of
            Ran msgs _ _ -> case reverse msgs of
              m : _ -> Just m
              []    -> Nothing
            other -> error ("expected Ran, got " ++ show other)
