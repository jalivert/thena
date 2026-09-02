-- | Loading a file, and the prelude (§9, phase 11).
--
-- **A file is a script of command lines** — decided by the user 2026-08-22. So
-- most of this suite is about 'loadSource', which is pure and takes contents
-- rather than a path (§12 invariant 4 keeps IO in "Thena.Repl"). The two cases
-- that must touch the disk are the shipped prelude ones, and they go through
-- 'loadPrelude' — the same function @repl@ calls at startup, so they fail if
-- the @data-files@ wiring is wrong rather than only if the parser is.
--
-- **The golden transcripts do not load the prelude and this suite does.**
-- 'Thena.Repl.transcript' starts from a bare 'newSession' on purpose: it is the
-- harness for the loop, the existing scripts declare their own @Nat@ and
-- @Empty@, and the prelude's own @Empty@ would collide with phase 10's. That
-- divergence from the real @repl@ is covered here instead — see
-- 'preludeIsInTheWay'.
module Thena.LoadTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

import Thena.Core.Level (Level (..), instantiateLevels)
import Thena.Core.Term (GlobalName (..))
import Thena.Driver
  ( LoadError (..)
  , Loaded (..)
  , LoadKind (..)
  , Response (..)
  , Session (..)
  , command
  , kindOf
  , loadProofSource
  , loadSource
  , newSession
  )
import Thena.Engine (Machine (..))
import Thena.Core.Term (Core, substLevelsIn)
import Thena.Global.Env
  ( Definition (..)
  , lookupDefinition
  , InductiveDefinition
  , eliminatorType
  , inductiveLevels
  , isDeclared
  , lookupInductive
  )
import Thena.Repl (startingSession, loadProofFile, renderCore, renderEliminator)
import Thena.Core.Convert (convert)
import Thena.Core.Context ()
import Data.ByteString.Builder (stringUtf8, toLazyByteString)
import Test.Tasty.Golden (goldenVsString)

tests :: TestTree
tests =
  testGroup
    "loading a file (§9, phase 11)"
    [ testGroup "the shipped prelude" preludeTests
    , testGroup "a file is a script of command lines" scriptTests
    , testGroup "a load stops, and says where" failureTests
    , testGroup "three kinds behind one word (phase 43)" kindTests
    , testGroup "a proof module (phase 43)" moduleTests
    , testGroup "MS4 tier 0 (phase 43)" tierTests
    ]

-- --------------------------------------------------------------------------
-- The prelude
-- --------------------------------------------------------------------------

preludeTests :: [TestTree]
preludeTests =
  [ testCase "it is found where cabal put it, and loads clean" $ do
      (_, problems) <- startingSession
      problems @?= []

  , testCase "and declares exactly Eq, refl, Unit, unit and Empty" $ do
      (s, _) <- startingSession
      let env = globals (sessionMachine s)
      sequence_
        [ assertBool (n ++ " is not declared") (isDeclared (GlobalName n) env)
        | n <- ["Eq", "refl", "Unit", "unit", "Empty"]
        ]

    -- §9's phase-11 deliverable, in full: "Eq's generated eliminator is J and
    -- can be used". Pinned as a string, for 'Thena.EliminatorTests'' reason.
  , testCase "Eq's generated eliminator is J" $ do
      (s, _) <- startingSession
      let env = globals (sessionMachine s)
          n0  = names (sessionMachine s)
      case lookupInductive (GlobalName "Eq") env of
        Nothing -> assertFailure "Eq is not declared"
        Just d  ->
          -- **At @Eq {0}@**, not at its bare parameter (MS3 phase 31d): the
          -- eliminator is a scheme now, and what a use site sees is the
          -- instantiation. Rendering it uninstantiated would pin @ℓ@'s number,
          -- which is a counter value and no business of this assertion.
          renderEliminator n0 (GlobalName "Eq") (atZero d (fst (eliminatorType d LZero n0)))
            @?= [ "elim Eq : ∀ (A : Type₀) (P : ∀ (x : A) (x1 : A) -> Eq {0} A x x1 -> Type₀) \
                  \-> (∀ (a : A) -> P a a (refl {0} A a)) \
                  \-> ∀ (x : A) (x1 : A) (target : Eq {0} A x x1) -> P x x1 target"
                ]

    -- "and can be used": eliminating a 'refl' must actually fire. The motive is
    -- constant so the reduct is the method applied to the one index.
  , testCase "and J computes on refl" $ do
      (s, _) <- startingSession
      afterLines s
        [ ":whnf elim Eq {0} (Unit {0}) \
          \(\\ (x : Unit {0}) (y : Unit {0}) (p : Eq {0} (Unit {0}) x y) -> Unit {0}) \
          \((\\ (a : Unit {0}) -> a)) (unit {0} unit {0}) (refl {0} (Unit {0}) (unit {0}))"
        ]
        (\l -> do
            loadedError l @?= Nothing
            renderedLast l @?= Just "unit {0}")

    -- The real @repl@ has the prelude in scope and 'transcript' does not; this
    -- is the difference, made visible.
  , testCase "preludeIsInTheWay: Empty cannot be redeclared over the prelude" $ do
      (s, _) <- startingSession
      afterLines s ["data Empty : Type₀ where { }"] $ \l ->
        loadedError l @?= Just (LoadStopped 1)
  ]

-- --------------------------------------------------------------------------
-- A file is a script
-- --------------------------------------------------------------------------

scriptTests :: [TestTree]
scriptTests =
  [ testCase "every line runs, in order" $
      let l = source ["data A0 : Type₀ where { a0 : A0 }", "data B0 : Type₀ where { b0 : B0 }"]
       in do
            loadedError l @?= Nothing
            length (loadedResponses l) @?= 2
            mapM_ (\n -> assertBool (n ++ " missing") (declared n l)) ["A0", "B0"]

  , testCase "a blank line is a line, and is counted" $
      let l = source ["data A0 : Type₀ where { a0 : A0 }", "", "data B0 : Type₀ where { b0 : B0 }"]
       in do
            loadedError l @?= Nothing
            loadedResponses l !! 1 @?= Blank

    -- The whole reason to reuse 'oneLine' rather than call 'command' directly:
    -- an op that asks is answered by the next line of the file, exactly as it
    -- would be by the next line typed (§7.5).
  , testCase "a question is answered by the next line" $
      let l = source ["assume : Type₀", "A"]
       in do
            loadedError l @?= Nothing
            length (loadedResponses l) @?= 2

  , testCase ":quit ends the load and is not a failure" $
      let l = source ["data A0 : Type₀ where { a0 : A0 }", ":quit", "data B0 : Type₀ where { b0 : B0 }"]
       in do
            loadedError l @?= Nothing
            declared "A0" l @?= True
            declared "B0" l @?= False
  ]

-- --------------------------------------------------------------------------
-- Failing
-- --------------------------------------------------------------------------

failureTests :: [TestTree]
failureTests =
  [ testCase "it stops at the first failure, and names the line" $
      let l = source
                [ "data A0 : Type₀ where { a0 : A0 }"
                , "data B0 : Type₀ where { b0 : (B0 -> A0) -> B0 }"
                , "data C0 : Type₀ where { c0 : C0 }"
                ]
       in do
            loadedError l @?= Just (LoadStopped 2)
            declared "A0" l @?= True
            declared "C0" l @?= False

    -- The reason is the last response, not a second copy inside 'LoadError'.
  , testCase "and the reason is the last response, not carried twice" $
      let l = source ["data A0 : Type₀ where { a0 : A0 }", ":no-such-command-here"]
       in case reverse (loadedResponses l) of
            Rejected _ : _ -> pure ()
            other          -> assertFailure ("not a rejection: " ++ show (take 1 other))

  , testCase "a syntax error stops it too" $
      (loadedError (source ["data ohno"]) @?= Just (LoadStopped 1))

  , testCase "nested :load is refused, not followed" $
      let l = source ["data A0 : Type₀ where { a0 : A0 }", ":load somewhere.thena.script"]
       in do
            loadedError l @?= Just (NestedLoad 2)
            -- what ran before it still ran
            declared "A0" l @?= True

  , testCase "a file that ends while something is asking says so" $
      loadedError (source ["assume : Type₀"]) @?= Just (UnansweredQuestion 1)
  ]

-- --------------------------------------------------------------------------
-- Helpers
-- --------------------------------------------------------------------------

-- | Run lines against an empty session.
source :: [String] -> Loaded
source = loadSource newSession . unlines

-- | Run lines against a session that already has something in it.
afterLines :: Session -> [String] -> (Loaded -> IO ()) -> IO ()
afterLines s ls k = k (loadSource s (unlines ls))

declared :: String -> Loaded -> Bool
declared n l = isDeclared (GlobalName n) (globals (sessionMachine (loadedSession l)))

-- | The last line's rendered term, printed as the REPL would print it.
--
-- A string rather than the 'Core': @unit@ could come back as the wrapper's
-- 'Thena.Core.Term.Global' or as the saturated 'Thena.Core.Term.Canonical', and
-- both are correct reducts of this elimination (§5.1). What the deliverable
-- claims is that J computes, and the printed answer is the honest witness.
renderedLast :: Loaded -> Maybe String
renderedLast l = case reverse (loadedResponses l) of
  Rendered t : _ -> Just (renderCore (names (sessionMachine (loadedSession l))) [] t)
  _              -> Nothing

-- | A datatype's own level parameters, all instantiated at zero.
atZero :: InductiveDefinition -> Core -> Core
atZero d t = case instantiateLevels (inductiveLevels d) (map (const LZero) (inductiveLevels d)) of
  Just sub -> substLevelsIn sub t
  Nothing  -> t

-- --------------------------------------------------------------------------
-- The three kinds (MS4 phase 43)
-- --------------------------------------------------------------------------

-- | @:load@ answers one question — which kind is this — and the extension
-- answers it, with the keywords saying the same thing out loud.
--
-- **The three suffixes are disjoint**, which is the property worth a test of
-- its own: a path has exactly one reading, and @.thena.rules@ is not a
-- @.thena@ that happens to end in something.
kindTests :: [TestTree]
kindTests =
  [ testCase "a bare .thena is a proof module" $
      kindOf "examples/arith.thena" @?= LoadProof
  , testCase ".thena.rules is a rule base, not a proof module" $
      kindOf "rules/standard.thena.rules" @?= LoadRules
  , testCase ".thena.script is a script, not a proof module" $
      kindOf "prelude/prelude.thena.script" @?= LoadScript

  , testCase "the keyword says which, and overrides nothing else" $
      case snd (command newSession ":load proof somewhere.thena") of
        ProofRequested p -> p @?= "somewhere.thena"
        other            -> assertFailure (show other)

  , -- The keyword is read before the path, so a script *named* like a proof
    -- module still loads as a script when it is asked for.
    testCase "a keyword beats the extension" $
      case snd (command newSession ":load script odd.thena") of
        LoadRequested p -> p @?= "odd.thena"
        other           -> assertFailure (show other)

  , testCase "and without one the extension decides" $
      case snd (command newSession ":load odd.thena") of
        ProofRequested p -> p @?= "odd.thena"
        other            -> assertFailure (show other)

  , testCase "mixing kinds in one load is refused" $
      case snd (command newSession ":load a.thena b.thena.rules") of
        Rejected _ -> pure ()
        other      -> assertFailure (show other)
  ]

-- --------------------------------------------------------------------------
-- Proof modules (MS4 phase 43)
-- --------------------------------------------------------------------------

-- | A whole file of surface declarations, elaborated.
--
-- These go through 'loadProofSource', which is pure and takes the contents,
-- for the same reason 'loadSource' does: §12 invariant 4 keeps IO in
-- "Thena.Repl".
moduleTests :: [TestTree]
moduleTests =
  [ testCase "a module declares what it says it declares" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 natModule of
        (_, ProofLoaded nm ds) -> (nm, ds) @?= ("M", ["Nat", "one"])
        (_, other)             -> assertFailure (show other)

  , testCase "and the globals are really there afterwards" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource s0 natModule
          g = globals (sessionMachine s1)
      map (\n -> isDeclared (GlobalName n) g) ["Nat", "zero", "succ", "one"]
        @?= [True, True, True, True]

  , -- **Quiet on success, loud on failure** — his call, 2026-09-02. The success
    -- case above carries no op messages at all; this one keeps them, because
    -- that is where the reason is.
    testCase "a module that does not elaborate reports why" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 badModule of
        (_, ProofLoaded _ _) -> assertFailure "admitted, and it should not have been"
        (_, _)               -> pure ()

  , -- **Comments, in the other two kinds** (MS4 phase 43). The surface cases
    -- are in "Thena.SurfaceTests"; these are the two that do not go through the
    -- lexer first — a script splits its command word off before lexing, and a
    -- rule base reads its header textually.
    testCase "a comment line in a proof module is skipped" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 commentedModule of
        (_, ProofLoaded nm ds) -> (nm, ds) @?= ("M", ["Nat", "one"])
        (_, other)             -> assertFailure (show other)

  , testCase "a comment line in a script is a blank line" $
      loadedError (loadSource newSession
        "-- a heading\ndata Nat : Type\8320 where { zero : Nat }  -- trailing\n")
        @?= Nothing

  , testCase "and -- without a space is still not one" $
      loadedError (loadSource newSession "--nope\n") @?= Just (LoadStopped 1)

  , testCase "a file that is not a module at all is a syntax error" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 "data Nat : Type\8320 where { zero : Nat }" of
        (_, Failed _) -> pure ()
        (_, other)    -> assertFailure (show other)
  ]
  where
    natModule =
      "module M where\n\
      \data Nat : Type\8320 where\n\
      \  zero : Nat\n\
      \  succ : Nat -> Nat\n\
      \\n\
      \one : Nat\n\
      \one = succ zero\n"

    commentedModule =
      "-- a module about numbers\n\
      \module M where\n\
      \\n\
      \-- the numbers themselves\n\
      \data Nat : Type\8320 where\n\
      \  zero : Nat\n\
      \  succ : Nat -> Nat      -- successor\n\
      \\n\
      \one : Nat\n\
      \one = succ zero\n"

    badModule =
      "module M where\n\
      \data Nat : Type\8320 where\n\
      \  zero : Nat\n\
      \\n\
      \one : Nat\n\
      \one = nosuchthing\n"

-- --------------------------------------------------------------------------
-- MS4 tier 0 (phase 43)
-- --------------------------------------------------------------------------

-- | **The checkpoint MS4\'s done-when calls tier 0**: a surface file that
-- declares a datatype, defines a function by elimination, uses one declaration
-- from another, and proves a theorem about it — elaborated from a file, with
-- every term argument written out.
--
-- @examples\/tier0.thena@ is the deliverable and the golden is what it
-- produced. His reason for wanting the explicit form first, 2026-09-01:
-- /"Couldn\'t we have a demo that uses all explicit arguments in case we want
-- to test out that we are doing well and all is according the plan?"/
tierTests :: [TestTree]
tierTests =
  [ goldenVsString "tier0" "test/golden/tier0.golden" $ do
      (s, problems) <- startingSession
      (s1, out) <- loadProofFile s "examples/tier0.thena"
      let shown = concatMap (renderResponse' s1) ["one", "two", "plusZeroLeft"]
      pure (toLazyByteString (stringUtf8 (unlines (problems ++ out ++ shown))))

  , -- **Implicit insertion is semantically transparent**, which is the property
    -- MS4\'s done-when asks for at phase 44 and not an approximation of it.
    -- The two spellings do **not** give the same term — they differ by one
    -- @=@-binding, because @fill@ parks a written argument and an inserted one
    -- is simply never elaborated into (@ms4\/CLOSEOUT.md@ 8, recorded at 44b).
    -- So the check is convertibility, which is the property; the syntactic gap
    -- is the finding, and it is already written down.
    testCase "a written implicit argument and an inserted one agree" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 bothSpellings of
        (_, ProofLoaded _ _) -> pure ()
        (_, other)           -> assertFailure (show other)

  , testCase "and they are convertible, not merely both admitted" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource s0 bothSpellings
          m = sessionMachine s1
      case ( lookupDefinition (GlobalName "oneExplicit") (globals m)
           , lookupDefinition (GlobalName "oneImplicit") (globals m)
           ) of
        (Just a, Just b) ->
          case convert (globals m) [] 0 (definitionBody a) (definitionBody b) of
            (Nothing, _, _) -> pure ()
            (Just why, _, _) -> assertFailure (show why)
        _ -> assertFailure "one of the two was not admitted"
  ]
  where
    renderResponse' s g = case lookupDefinition (GlobalName g) (globals (sessionMachine s)) of
      Just d  -> [g ++ " = " ++ renderCore 0 [] (definitionBody d)]
      Nothing -> [g ++ " is missing"]

    bothSpellings =
      "module Both where\n\
      \data Nat : Type\8320 where\n\
      \  zero : Nat\n\
      \  succ : Nat -> Nat\n\
      \\n\
      \idE : forall (A : Type\8320) -> A -> A\n\
      \idE = \\ A x -> x\n\
      \\n\
      \idI : forall {A : Type\8320} -> A -> A\n\
      \idI = \\ A x -> x\n\
      \\n\
      \oneExplicit : Nat\n\
      \oneExplicit = idE Nat (succ zero)\n\
      \\n\
      \oneImplicit : Nat\n\
      \oneImplicit = idI (succ zero)\n"
