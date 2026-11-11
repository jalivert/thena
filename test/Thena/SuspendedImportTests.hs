-- | A @yield@ out of a module being imported (MS12 phase 309, @~4qgxx@).
--
-- **What this suite is about, in one line**: an import is a program the machine
-- runs, so it can stop in the middle, and when it does the prompt gets the
-- wheel.
--
-- Until this phase the suspension was thrown away. The rule fired and its
-- message printed — so the user was told control had been handed over — and then
-- the session was rolled back, which is the one thing it must not do. The
-- fixtures are @test\/modules\/Pausing.thena.rules@, which yields where an author
-- wrote a placeholder, and @test\/modules\/Pauses.thena@, which writes one.
--
-- **Every test here drives the real doors.** @importModule@ is what
-- @import ‹module›@ reaches and @following@ is what notices a later line's
-- @yield@ finishing a load, so nothing is tested through a shortcut that the
-- REPL does not take.
module Thena.SuspendedImportTests (tests) where

import Data.Maybe (isJust, isNothing)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

import Thena.Core.Term (nameDotted)
import Thena.Driver
  ( CommandError (..)
  , Response (..)
  , Session
  , declaredByModule
  , importSuspended
  , moduleName
  , moduleText
  , modulesLoaded
  , oneLine
  , refuseSuspension
  )
import Thena.Files (consultRuleFiles, following, importModule, startingSession)

-- | The session with the pausing base pushed, which is what makes a placeholder
-- hand control over instead of being refused.
--
-- **A @:consult@ and not a @:load@**, because the shipped base has to stay
-- underneath: the yielding clause is reached first and the standard one is still
-- there for everything else.
pausing :: IO Session
pausing = do
  (s0, trouble) <- startingSession
  assertBool ("the shipped files would not load: " ++ show trouble) (null trouble)
  (s1, _, t1) <- consultRuleFiles s0 ["test/modules/Pausing.thena.rules"]
  assertBool ("the pausing base would not load: " ++ show t1) (null t1)
  pure s1

-- | Import @test.modules.Pauses@ and stop in its placeholder.
suspended :: IO (Session, [Response])
suspended = do
  s <- pausing
  Just m <- pure (moduleName "test.modules.Pauses")
  (s', out, trouble) <- importModule s m
  assertBool ("nothing should be trouble here: " ++ show trouble) (null trouble)
  pure (s', out)

-- | Submit a line the way the REPL does, **following it as the REPL does**.
--
-- The second half is the point: a @yield@ that finishes a load is noticed after
-- the line, so a test that called 'oneLine' alone would never see the module
-- land.
line :: Session -> String -> IO (Session, [Response])
line s l = case oneLine s l of
  (s', resp) -> case following s' resp of
    Nothing  -> pure (s', [resp])
    Just act -> do
      (s'', more, trouble) <- act
      assertBool ("unexpected trouble on " ++ show l ++ ": " ++ show trouble)
                 (null trouble)
      pure (s'', resp : more)

rejected :: [Response] -> [CommandError]
rejected out = [ e | Rejected e <- out ]

tests :: TestTree
tests = testGroup "a yield out of an imported module"
  [ testCase "the load suspends and says which module it is in" $ do
      (s, out) <- suspended
      assertBool "the session should be holding a suspended import"
                 (isJust (importSuspended s))
      [ nm | ImportSuspended nm _ _ _ <- out ] @?= ["test.modules.Pauses"]

  , testCase "nothing is declared while it stands, so atomicity holds" $ do
      (s, _) <- suspended
      -- **The module is not in** — his ruling of 2026-09-30 is untouched by this
      -- phase, and a suspended load is one command that has not come back
      -- rather than a module that half went in.
      assertBool "test.modules.Pauses must not be loaded yet"
                 ("test.modules.Pauses" `notElem` map moduleText (modulesLoaded s))

  , testCase "yield hands control back and the module lands" $ do
      (s, _) <- suspended
      (s1, _) <- line s "try-core core`this`"
      (s2, _) <- line s1 "solve"
      (s3, out) <- line s2 "yield"
      assertBool "nothing should be suspended once it finished"
                 (isNothing (importSuspended s3))
      assertBool ("test.modules.Pauses should be in: " ++ show (map moduleText (modulesLoaded s3)))
                 ("test.modules.Pauses" `elem` map moduleText (modulesLoaded s3))
      [ nm | ProofLoaded nm _ _ _ <- out ] @?= ["test.modules.Pauses"]

  , testCase "a line typed during the suspension runs in front of the yield" $ do
      (s, _) <- suspended
      (s1, out) <- line s "declare mine : Type\8320 ; mine = Two"
      assertBool "the import should still be standing after an ordinary line"
                 (isJust (importSuspended s1))
      assertBool ("the line should have gone through: " ++ show out)
                 (null (rejected out))

  , testCase "a second import is refused while one is in flight" $ do
      (s, _) <- suspended
      (_, out) <- line s "import test.modules.Bit"
      rejected out @?= [ImportInFlight "test.modules.Pauses"]

  , testCase ":theorem is refused rather than destroying the elaboration" $ do
      -- **The defect this refusal replaces** (@~s6tbx@): the four proof
      -- boundaries empty the machine's program, so opening a theorem here used
      -- to admit the theorem and silently lose the suspended load.
      (s, _) <- suspended
      (s1, out) <- line s ":theorem t : Type\8320"
      rejected out @?= [ProvingWhileYielding]
      assertBool "the import must still be standing after the refusal"
                 (isJust (importSuspended s1))

  , testCase ":abandon takes the whole import, and the user's own work with it" $ do
      -- His ruling of 2026-11-11: /"I want the abandoning of the import to take
      -- everything. The honest way."/
      (s, _) <- suspended
      (s1, _) <- line s "declare mine : Type\8320 ; mine = Two"
      (s2, out) <- line s1 ":abandon"
      assertBool "nothing should be suspended after an abandon"
                 (isNothing (importSuspended s2))
      -- **It names the user's own, and counts the module's** — a closure
      -- generates hundreds of names and the list was unreadable; that your
      -- lemma goes is the half worth printing in full.
      [ map nameDotted mine | ImportAbandoned _ _ mine <- out ] @?= [["mine"]]
      assertBool "the module must not be loaded after an abandon"
                 ("test.modules.Pauses" `notElem` map moduleText (modulesLoaded s2))

  , testCase "a name the user typed is NOT the module's declaration" $ do
      -- @~3c2db@, his ruling of 2026-11-11. 'moduleDeclared' works a module's
      -- declarations out as a set difference of the environment, which cannot
      -- tell a name the file wrote from a lemma proved at the prompt to get
      -- unstuck — and a module with no @exporting@ clause publishes what it
      -- declared, so without the subtraction one file would offer different
      -- names depending on how a session went.
      (s, _) <- suspended
      (s1, _) <- line s "declare mine : Type\8320 ; mine = Two"
      (s2, _) <- line s1 "try-core core`this`"
      (s3, _) <- line s2 "solve"
      (s4, _) <- line s3 "yield"
      Just m <- pure (moduleName "test.modules.Pauses")
      let theirs = map nameDotted (declaredByModule m s4)
      assertBool ("the module's own declarations should be there: " ++ show theirs)
                 ("picked" `elem` theirs)
      assertBool ("a name typed at the prompt is not the module's: " ++ show theirs)
                 ("mine" `notElem` theirs)

  , testCase "a module that imports the suspended one waits for it" $ do
      -- The suspension lands in the middle of a fold over the closure, so the
      -- rest of the walk has to be carried or the importing module is lost.
      s <- pausing
      Just m <- pure (moduleName "test.modules.ImportsPauses")
      (s1, out, trouble) <- importModule s m
      assertBool ("no trouble expected: " ++ show trouble) (null trouble)
      [ nm | ImportSuspended nm _ _ _ <- out ] @?= ["test.modules.Pauses"]
      (s2, _) <- line s1 "try-core core`this`"
      (s3, _) <- line s2 "solve"
      (s4, landed) <- line s3 "yield"
      assertBool "nothing should be suspended once the closure finished"
                 (isNothing (importSuspended s4))
      -- **Both modules, in dependency order**, from one @yield@: finishing the
      -- suspended one let the walk carry on to the module that imported it.
      [ nm | ProofLoaded nm _ _ _ <- landed ]
        @?= ["test.modules.Pauses", "test.modules.ImportsPauses"]

  , testCase "a caller with no prompt refuses it and keeps nothing" $ do
      -- What @thena-check@ does: a batch checker has nobody to hand the wheel
      -- to, and the refusal is the caller's rather than the load's.
      (s, _) <- suspended
      case refuseSuspension s of
        (s', Rejected (NobodyToYieldTo nm)) -> do
          nm @?= "test.modules.Pauses"
          assertBool "nothing should be suspended after the refusal"
                     (isNothing (importSuspended s'))
          assertBool "and the module must not be in"
                     ("test.modules.Pauses" `notElem` map moduleText (modulesLoaded s'))
        (_, other) -> assertFailure ("expected a refusal, got " ++ show other)

  , testCase "the suspended load keeps the module's own scope" $ do
      -- His ruling of 2026-11-11: /"what is in scope for the prompt, is what was
      -- in scope for the elaboration."/ @Two@ is the module's own datatype and
      -- it is reachable unqualified at the prompt because the module wrote
      -- @open Two@ above the placeholder.
      (s, _) <- suspended
      (_, out) <- line s "declare mine : Type\8320 ; mine = Two"
      assertBool ("the module's own names should be reachable: " ++ show out)
                 (null (rejected out))
  ]
