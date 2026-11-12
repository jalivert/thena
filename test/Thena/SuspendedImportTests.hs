-- | A @yield@ out of a module being imported (MS12 phase 309).
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

import Thena.Core.Term (nameDotted, rootName)
import Thena.Driver
  ( CommandError (..)
  , Parked (..)
  , Quest (..)
  , Response (..)
  , Session
  , currentQuest
  , declaredByModule
  , importSuspended
  , moduleName
  , moduleText
  , modulesLoaded
  , oneLine
  , parked
  , parkedWord
  , refuseSuspension
  )
import Thena.Files (consultRuleFiles, following, importModule, startingSession)
import Thena.View (Budget (..), proofsView)
import Thena.View.Proofs (ProofsView (..), QuestClaim (..), QuestView (..))

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
      -- **And the refusal names the park** (MS12 phase 310): the first step of
      -- his five is @:suspend@, so the message that refuses the proof is where
      -- it has to be said.
      rejected out @?= [ProvingWhileYielding (Just "test.modules.Pauses")]
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
      -- **Under the module's own namespace** (MS12 phase 313): the prompt
      -- stands inside the suspended module's namespace, so a lemma typed to get
      -- unstuck is declared there — and @~3c2db@'s rule is about who PUBLISHES
      -- it, which the test below asserts.
      [ map nameDotted mine | ImportAbandoned _ _ mine <- out ]
        @?= [["test.modules.Pauses.mine"]]
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
                 ("test.modules.Pauses.picked" `elem` theirs)
      assertBool ("a name typed at the prompt is not the module's: " ++ show theirs)
                 ("test.modules.Pauses.mine" `notElem` theirs)

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
  , parking
  ]

-- | __Parking the import so that a lemma can be proved__ (MS12 phase 310, his
-- rulings of 2026-11-11).
--
-- **The sequence is his and it is five steps**: yielded at the prompt → park
-- the quest → @:theorem@ the lemma → @qed@, which lands it as a name → pick the
-- quest back up → @yield@. The first test here is that sequence end to end, and
-- the rest are the edges it has.
--
-- **Nothing is automatic, which is the ruling the whole group rests on** —
-- /"There is a step to park the current 'quest' and that is done manually, so I
-- think the opposite should be manual also."/ So @qed@ does not pick the import
-- back up and there is nothing here that asserts it does.
parking :: TestTree
parking = testGroup "parking it, so that a lemma can be proved"
  [ testCase "his five steps, end to end" $ do
      (s, _) <- suspended
      (s1, out1) <- line s ":suspend"
      [ nm | ImportParked nm <- out1 ] @?= ["test.modules.Pauses"]
      assertBool "the import should be off the wheel once it is parked"
                 (isNothing (importSuspended s1))
      -- **The lemma is proved in the module's scope**, which is what parking
      -- leaving the pool and the concealment in force buys: @this@ is the
      -- module's own constructor and the module had opened it.
      (s2, out2) <- line s1 ":theorem helper : Two"
      assertBool ("the theorem should be accepted in limbo: " ++ show out2)
                 (null (rejected out2))
      (s3, _) <- line s2 "elaborate surface`this`"
      (s4, out4) <- line s3 "qed"
      assertBool ("qed should land it: " ++ show out4) (null (rejected out4))
      (s5, out5) <- line s4 ":resume test.modules.Pauses"
      [ nm | ImportPickedUp nm <- out5 ] @?= ["test.modules.Pauses"]
      assertBool "the import should be back on the wheel"
                 (isJust (importSuspended s5))
      -- **And the lemma fills the module's hole** — the whole point of the
      -- feature, not a side effect of it.
      (s6, _) <- line s5 "try-core core`helper`"
      (s7, _) <- line s6 "solve"
      (s8, landed) <- line s7 "yield"
      [ nm | ProofLoaded nm _ _ _ <- landed ] @?= ["test.modules.Pauses"]
      assertBool "the module should be in once it finished"
                 ("test.modules.Pauses" `elem` map moduleText (modulesLoaded s8))
      -- @~3c2db@ again, on the parked path: the lemma was typed at the prompt,
      -- so the module does not publish it.
      Just m <- pure (moduleName "test.modules.Pauses")
      let theirs = map nameDotted (declaredByModule m s8)
      assertBool ("the module's own should be there: " ++ show theirs)
                 ("test.modules.Pauses.picked" `elem` theirs)
      assertBool ("the user's lemma is not the module's: " ++ show theirs)
                 ("test.modules.Pauses.helper" `notElem` theirs)

  , testCase "it parks under its module name, in the one list" $ do
      -- **His words are /\"one list one word\"/**: @:proofs@ is the list and
      -- the module's name is the word, so nothing in the machinery tells a
      -- parked import from a parked proof.
      (s, _) <- suspended
      (s1, _) <- line s ":suspend"
      map parkedWord (parked s1) @?= ["test.modules.Pauses"]
      case map parkedQuest (parked s1) of
        [AnImport _] -> pure ()
        other -> assertFailure ("expected one parked import, got " ++ show other)

  , testCase "and the pane's view carries it beside the proofs" $ do
      -- His ruling of 2026-11-11: /"I will want TUI to have a pane for them to
      -- show them at all times."/ A row has the word @:resume@ takes and what
      -- the quest is; an import has no statement and says so.
      (s, _) <- suspended
      (s1, _) <- line s ":suspend"
      case proofsViewParked (proofsView (Budget 100) s1) of
        [QuestView w (AnImportStanding nm)] -> do
          w @?= "test.modules.Pauses"
          nm @?= "test.modules.Pauses"
        other -> assertFailure ("expected one import row, got " ++ show other)
      assertBool "nothing should be marked as current in limbo"
                 (isNothing (proofsViewOn (proofsView (Budget 100) s1)))

  , testCase "a standing import is what the session is ON, before it is parked" $ do
      -- 'Thena.Driver.currentQuest' is innermost-first and it is what
      -- @:suspend@, @:abandon@ and @:proofs@ all read, so they cannot come to
      -- disagree about which thing a bare word acts on.
      (s, _) <- suspended
      case currentQuest s of
        Just (AnImport _) -> pure ()
        other -> assertFailure ("expected the import to be current, got " ++ show other)
      case proofsViewOn (proofsView (Budget 100) s) of
        Just (QuestView w (AnImportStanding _)) -> w @?= "test.modules.Pauses"
        other -> assertFailure ("expected the import as the live row, got " ++ show other)

  , testCase ":theorem's refusal names the park, which is step two" $ do
      -- Phase 309 could not name it because there was nothing to park.
      (s, _) <- suspended
      (_, out) <- line s ":theorem t : Type\8320"
      rejected out @?= [ProvingWhileYielding (Just "test.modules.Pauses")]

  , testCase "a second import is refused while one is parked" $ do
      -- **Parking does not make room for another one**: the parked import's
      -- pool, held bases and concealment are still in force, so a second load
      -- would displace what it expects to find when it is picked up.
      (s, _) <- suspended
      (s1, _) <- line s ":suspend"
      (_, out) <- line s1 "import test.modules.Bit"
      rejected out @?= [ImportIsParked "test.modules.Pauses"]

  , testCase ":resume is refused while the lemma is still open" $ do
      -- **Nothing is stacked implicitly, which is the ruling parking rests
      -- on.** Picking a quest up installs a program and a development, so there
      -- has to be nowhere for the one you are on to go.
      (s, _) <- suspended
      (s1, _) <- line s ":suspend"
      (s2, _) <- line s1 ":theorem helper : Two"
      (_, out) <- line s2 ":resume test.modules.Pauses"
      map show (rejected out) @?= [show (AlreadyProving (rootName "helper"))]

  , testCase "and refused while a standing import holds the wheel" $ do
      -- A parked PROOF and a standing import, which is reachable because only
      -- an import refuses a second import: the refusal names the thing the user
      -- has to deal with, and its message says to park it.
      s <- pausing
      (s1, _) <- line s ":theorem spare : Type\8320"
      (s2, _) <- line s1 ":suspend"
      Just m <- pure (moduleName "test.modules.Pauses")
      (s3, _, trouble) <- importModule s2 m
      assertBool ("no trouble expected: " ++ show trouble) (null trouble)
      (_, out) <- line s3 ":resume spare"
      rejected out @?= [ImportInFlight "test.modules.Pauses"]

  , testCase ":resume naming nothing parked is refused" $ do
      (s, _) <- suspended
      (s1, _) <- line s ":suspend"
      (_, out) <- line s1 ":resume test.modules.Bit"
      rejected out @?= [NoSuchProof "test.modules.Bit"]

  , testCase "qed does not pick it up, because unparking is a step" $ do
      -- **His ruling, and the alternative was refused**: a boundary that
      -- unstacked implicitly would be a second driver underneath the first.
      (s, _) <- suspended
      (s1, _) <- line s ":suspend"
      (s2, _) <- line s1 ":theorem helper : Two"
      (s3, _) <- line s2 "elaborate surface`this`"
      (s4, _) <- line s3 "qed"
      assertBool "the import must still be parked after a qed"
                 (isNothing (importSuspended s4))
      map parkedWord (parked s4) @?= ["test.modules.Pauses"]

  , testCase "and a bare yield in limbo says nothing has yielded" $ do
      -- **@yield@ is program-local, not session-wide** — measured, and his
      -- inference: parking moves the program into the parked quest, so there is
      -- nothing standing at the prompt until it is picked up again.
      (s, _) <- suspended
      (s1, _) <- line s ":suspend"
      (_, out) <- line s1 "yield"
      rejected out @?= [NotYielding]
  ]
