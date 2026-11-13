-- | A module whose proofs are not all finished loads anyway (MS12 phase 315,
-- @~mgqwb@, his design of 2026-11-11).
--
-- **What this suite is about, in one line**: at the prompt a module loads as
-- far as it can, and what did not go through is written down rather than taking
-- the module with it.
--
-- Until this phase a module was one program for the whole file, so a
-- declaration that did not elaborate took every other declaration with it —
-- /"I can't debug them because they are written in a module together with
-- proofs that are not ok yet? That's dumb."/ The items are run one at a time
-- now, and the two things that decide everything are **which act was typed**
-- ('Lenient' at the prompt, 'Strict' for a batch run) and **nothing else**: no
-- analysis works out why anything failed, so the loader simply tries the next
-- one.
--
-- **The fixtures**: @test\/modules\/PartlyGood.thena@ declares three things with
-- the middle one unelaborable, @PartlyWorse.thena@ breaks two of four and
-- imports @Bit@, and @GetsPartly.thena@ imports @PartlyGood@ and is itself
-- fine — which is what the leniency-all-the-way-down test needs.
--
-- **Every test drives the real door.** @importModule@ is what @import ‹module›@
-- reaches, so nothing here is tested through a shortcut the prompt does not
-- take.
module Thena.PartialImportTests (tests) where

import Data.List (isInfixOf)
import Data.Maybe (isJust, isNothing)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

import Thena.Driver
  ( Leniency (..)
  , Partly (..)
  , Response (..)
  , Session
  , Unfinished (..)
  , declaredByModule
  , moduleImportsOf
  , moduleLoaded
  , moduleName
  , moduleText
  , modulePartly
  , moduleWhole
  , modulesPartly
  )
import Thena.Core.Term (nameDotted)
import Thena.Files (importModule, startingSession)
import Thena.Render (renderResponse)

-- | A session with the shipped base and prelude in it, and nothing else.
fresh :: IO Session
fresh = do
  (s, trouble) <- startingSession
  assertBool ("the shipped files would not load: " ++ show trouble) (null trouble)
  pure s

-- | Import a module through the door @import ‹module›@ reaches.
importing :: Leniency -> String -> IO (Session, [Response])
importing leniency what = do
  s <- fresh
  Just m <- pure (moduleName what)
  (s', out, trouble) <- importModule leniency s m
  assertBool ("nothing should be trouble here: " ++ show trouble) (null trouble)
  pure (s', out)

-- | The names a module declared, as words.
declared :: String -> Session -> [String]
declared what s = case moduleName what of
  Nothing -> []
  Just m  -> map nameDotted (declaredByModule m s)

-- | The one response that is about this module.
about :: String -> [Response] -> IO Response
about what out = case [ r | r <- out, names r == Just what ] of
  r : _ -> pure r
  []    -> assertFailure ("no response about " ++ what ++ ": " ++ show out)
  where
    names r = case r of
      ProofLoaded nm _ _ _         -> Just nm
      ProofLoadedPartly nm _ _ _ _ -> Just nm
      _                            -> Nothing

tests :: TestTree
tests = testGroup "a module that loads as far as it can (MS12 phase 315)"
  [ testCase "what elaborates lands, and what does not is left out" $ do
      (s, _) <- importing Lenient "test.modules.PartlyGood"
      Just m <- pure (moduleName "test.modules.PartlyGood")
      -- **The module is IN**, which is the whole of the feature: the theorem
      -- the user was after is reachable although a later one is not.
      assertBool "the module is in" (moduleLoaded m s)
      let ds = declared "test.modules.PartlyGood" s
      assertBool ("first should be declared: " ++ show ds)
                 ("test.modules.PartlyGood.first" `elem` ds)
      -- **AND THE LOADER CARRIED ON PAST THE FAILURE.** @after@ is written
      -- below @broken@ and has nothing to do with it, so it lands — his
      -- ruling, and the case his first proposal (park everything below the
      -- first failure) would have lost.
      assertBool ("after should be declared: " ++ show ds)
                 ("test.modules.PartlyGood.after" `elem` ds)
      assertBool ("broken should NOT be declared: " ++ show ds)
                 ("test.modules.PartlyGood.broken" `notElem` ds)

  , testCase "the response says what went in and what did not" $ do
      (_, out) <- importing Lenient "test.modules.PartlyGood"
      r <- about "test.modules.PartlyGood" out
      case r of
        ProofLoadedPartly _ ds _ _ unfin -> do
          assertBool ("what went in: " ++ show ds) ("first" `elem` ds)
          assertBool ("what went in: " ++ show ds) ("broken" `notElem` ds)
          map unfinishedDeclares unfin @?= [["broken"]]
        other -> assertFailure ("expected a partial load, got " ++ show other)

  , testCase "the first failure is the root and the rest are pending" $ do
      -- **One failure and N pending, not N+1 failures** — his ruling of
      -- 2026-11-11. The order of the list is the whole of how that is said.
      (_, out) <- importing Lenient "test.modules.PartlyWorse"
      r <- about "test.modules.PartlyWorse" out
      case r of
        ProofLoadedPartly _ _ _ _ unfin ->
          map unfinishedDeclares unfin @?= [["broken"], ["alsoBroken"]]
        other -> assertFailure ("expected a partial load, got " ++ show other)

  , testCase "and it is rendered as one reason and a list of the rest" $ do
      (s, out) <- importing Lenient "test.modules.PartlyWorse"
      r <- about "test.modules.PartlyWorse" out
      let text = unlines (renderResponse s r)
      assertBool ("the root's own reason: " ++ text)
                 ("broken did not go in:" `isInfixOf` text)
      assertBool ("the root's own reason: " ++ text)
                 ("not in scope: nonesuch" `isInfixOf` text)
      -- **The pending one is named and NOTHING IS SAID ABOUT WHY**, because
      -- nothing worked out why — his ruling of 2026-11-11. @neitherThis@ is
      -- what the second one could not resolve and it does not appear.
      assertBool ("the pending one: " ++ text)
                 ("and 1 more pending: alsoBroken" `isInfixOf` text)
      assertBool ("no reason for the pending one: " ++ text)
                 (not ("neitherThis" `isInfixOf` text))

  , testCase "the session says which modules are partly in" $ do
      (s, _) <- importing Lenient "test.modules.PartlyGood"
      Just m <- pure (moduleName "test.modules.PartlyGood")
      assertBool "it is in" (moduleLoaded m s)
      -- **Three-valued, which is what @~84j24@'s pane needs**: in,
      -- partly in, absent.
      assertBool "it is not whole" (not (moduleWhole m s))
      case modulePartly m s of
        Nothing -> assertFailure "there should be a record of what did not go in"
        Just p  -> do
          partlyModule p @?= Just m
          partlyText p @?= "test.modules.PartlyGood"
          map unfinishedDeclares (partlyUnfinished p) @?= [["broken"]]

  , testCase "a module that went in whole leaves no record" $ do
      (s, out) <- importing Lenient "test.modules.Bit"
      Just m <- pure (moduleName "test.modules.Bit")
      -- **Absence is the answer and not a missing record**, which is what
      -- keeps a whole load costing nothing.
      assertBool "it is whole" (moduleWhole m s)
      assertBool "nothing is written down" (isNothing (modulePartly m s))
      modulesPartly s @?= []
      r <- about "test.modules.Bit" out
      case r of
        ProofLoaded {} -> pure ()
        other -> assertFailure ("a whole load answers as it always did: " ++ show other)

  , testCase "STRICT is what it always was: the module declares nothing" $ do
      -- **His ruling of 2026-09-30 is untouched** — /"Atomic from now on"/ —
      -- and this is what a batch run still gets. Leniency belongs to the act.
      (s, _) <- importing Strict "test.modules.PartlyGood"
      Just m <- pure (moduleName "test.modules.PartlyGood")
      assertBool "the module is not in" (not (moduleLoaded m s))
      declared "test.modules.PartlyGood" s @?= []
      assertBool "and nothing is written down" (isNothing (modulePartly m s))

  , testCase "leniency reaches everything the act pulls in, however deep" $ do
      -- **The seam is WHERE THE ACT WAS TYPED and it gives no second seam one
      -- level down** — his ruling of 2026-11-11, /"I think leniency all the
      -- day down makes sense."/ @GetsPartly@ imports @PartlyGood@, which is
      -- the one with the broken declaration; the import the user typed is
      -- @GetsPartly@.
      (s, out) <- importing Lenient "test.modules.GetsPartly"
      Just outer <- pure (moduleName "test.modules.GetsPartly")
      Just inner <- pure (moduleName "test.modules.PartlyGood")
      assertBool "the outer module is in whole" (moduleWhole outer s)
      assertBool "the inner one is in" (moduleLoaded inner s)
      assertBool "and it is the partial one" (isJust (modulePartly inner s))
      r <- about "test.modules.GetsPartly" out
      case r of
        ProofLoaded {} -> pure ()
        other -> assertFailure ("the outer module went in whole: " ++ show other)

  , testCase "and under STRICT the whole closure still goes back" $ do
      -- **A refusal inside a module nobody named arrives as trouble about
      -- that file** (MS11 phase 275), which is why this does not go through
      -- 'importing': the point here is what the session holds afterwards.
      s0 <- fresh
      Just outer <- pure (moduleName "test.modules.GetsPartly")
      Just inner <- pure (moduleName "test.modules.PartlyGood")
      (s, _, trouble) <- importModule Strict s0 outer
      assertBool "the inner file is what is named" (not (null trouble))
      assertBool "the outer module is not in" (not (moduleLoaded outer s))
      assertBool "nor the inner one" (not (moduleLoaded inner s))

  , testCase "the import tree's edges are kept" $ do
      -- **Nothing else keeps them**: 'Thena.Files' flattens the closure into
      -- dependency order before the walk, so the shape the user wrote is gone
      -- by the time anything lands. @~84j24@'s pane is drawn from this.
      (s, _) <- importing Lenient "test.modules.GetsPartly"
      Just outer <- pure (moduleName "test.modules.GetsPartly")
      Just inner <- pure (moduleName "test.modules.PartlyGood")
      map moduleText (moduleImportsOf outer s) @?= ["test.modules.PartlyGood"]
      -- A leaf's edges are empty, and so are a module that is not in — the
      -- same answer, which 'moduleLoaded' is what tells apart.
      moduleImportsOf inner s @?= []

  , testCase "a partial module's own imports are edges too" $ do
      (s, _) <- importing Lenient "test.modules.PartlyWorse"
      Just m <- pure (moduleName "test.modules.PartlyWorse")
      map moduleText (moduleImportsOf m s) @?= ["test.modules.Bit"]
  ]
