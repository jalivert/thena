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

import Thena.Core.Term (GlobalName (..), Level (..))
import Thena.Driver
  ( LoadError (..)
  , Loaded (..)
  , Response (..)
  , Session (..)
  , Stop (..)
  , loadSource
  , newSession
  )
import Thena.Engine (Machine (..))
import Thena.Global.Env (eliminatorType, isDeclared, lookupInductive)
import Thena.Repl (loadPrelude, renderCore, renderEliminator)

tests :: TestTree
tests =
  testGroup
    "loading a file (§9, phase 11)"
    [ testGroup "the shipped prelude" preludeTests
    , testGroup "a file is a script of command lines" scriptTests
    , testGroup "a load stops, and says where" failureTests
    ]

-- --------------------------------------------------------------------------
-- The prelude
-- --------------------------------------------------------------------------

preludeTests :: [TestTree]
preludeTests =
  [ testCase "it is found where cabal put it, and loads clean" $ do
      (_, problems) <- loadPrelude newSession
      problems @?= []

  , testCase "and declares exactly Eq, refl, Unit, unit and Empty" $ do
      (s, _) <- loadPrelude newSession
      let env = globals (sessionMachine s)
      sequence_
        [ assertBool (n ++ " is not declared") (isDeclared (GlobalName n) env)
        | n <- ["Eq", "refl", "Unit", "unit", "Empty"]
        ]

    -- §9's phase-11 deliverable, in full: "Eq's generated eliminator is J and
    -- can be used". Pinned as a string, for 'Thena.EliminatorTests'' reason.
  , testCase "Eq's generated eliminator is J" $ do
      (s, _) <- loadPrelude newSession
      let env = globals (sessionMachine s)
          n0  = names (sessionMachine s)
      case lookupInductive (GlobalName "Eq") env of
        Nothing -> assertFailure "Eq is not declared"
        Just d  ->
          renderEliminator n0 (GlobalName "Eq") (fst (eliminatorType d (Level 0) n0))
            @?= [ "elim Eq : ∀ (A : Type₀) (P : ∀ (x : A) (x1 : A) -> Eq A x x1 -> Type₀) \
                  \-> (∀ (a : A) -> P a a (refl A a)) \
                  \-> ∀ (x : A) (x1 : A) (target : Eq A x x1) -> P x x1 target"
                ]

    -- "and can be used": eliminating a 'refl' must actually fire. The motive is
    -- constant so the reduct is the method applied to the one index.
  , testCase "and J computes on refl" $ do
      (s, _) <- loadPrelude newSession
      afterLines s
        [ ":whnf elim Eq (Unit) (\\ (x : Unit) (y : Unit) (p : Eq Unit x y) -> Unit) \
          \((\\ (a : Unit) -> a)) (unit unit) (refl Unit unit)"
        ]
        (\l -> do
            loadedError l @?= Nothing
            renderedLast l @?= Just "unit")

    -- The real @repl@ has the prelude in scope and 'transcript' does not; this
    -- is the difference, made visible.
  , testCase "preludeIsInTheWay: Empty cannot be redeclared over the prelude" $ do
      (s, _) <- loadPrelude newSession
      afterLines s ["data Empty : Type₀ { }"] $ \l ->
        loadedError l @?= Just (LoadStopped 1)
  ]

-- --------------------------------------------------------------------------
-- A file is a script
-- --------------------------------------------------------------------------

scriptTests :: [TestTree]
scriptTests =
  [ testCase "every line runs, in order" $
      let l = source ["data A0 : Type₀ { a0 : A0 }", "data B0 : Type₀ { b0 : B0 }"]
       in do
            loadedError l @?= Nothing
            length (loadedResponses l) @?= 2
            mapM_ (\n -> assertBool (n ++ " missing") (declared n l)) ["A0", "B0"]

  , testCase "a blank line is a line, and is counted" $
      let l = source ["data A0 : Type₀ { a0 : A0 }", "", "data B0 : Type₀ { b0 : B0 }"]
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
      let l = source ["data A0 : Type₀ { a0 : A0 }", ":quit", "data B0 : Type₀ { b0 : B0 }"]
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
                [ "data A0 : Type₀ { a0 : A0 }"
                , "data B0 : Type₀ { b0 : (B0 -> A0) -> B0 }"
                , "data C0 : Type₀ { c0 : C0 }"
                ]
       in do
            loadedError l @?= Just (LoadStopped 2)
            declared "A0" l @?= True
            declared "C0" l @?= False

    -- The reason is the last response, not a second copy inside 'LoadError'.
  , testCase "and the reason is the last response, not carried twice" $
      let l = source ["data A0 : Type₀ { a0 : A0 }", "no such command here"]
       in case reverse (loadedResponses l) of
            Rejected _ : _ -> pure ()
            other          -> assertFailure ("not a rejection: " ++ show (take 1 other))

  , testCase "a syntax error stops it too" $
      (loadedError (source ["data ohno"]) @?= Just (LoadStopped 1))

  , testCase "nested :load is refused, not followed" $
      let l = source ["data A0 : Type₀ { a0 : A0 }", ":load somewhere.thena"]
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
