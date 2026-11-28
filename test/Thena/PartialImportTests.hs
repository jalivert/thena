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
  , Pos (..)
  , Response (..)
  , Session
  , Unfinished (..)
  , declaredByModule
  , loadProofItems
  , loadProofSource
  , moduleImportsOf
  , moduleLoaded
  , moduleName
  , moduleText
  , modulePartly
  , moduleWhole
  , modulesPartly
  , parseSurfaceModule
  )
import Thena.Core.Term (nameDotted)
import Thena.Files (importModule, startingSession)
import Thena.Render (renderResponse)
import Thena.View (Budget (..), failureView)
import Thena.View.Failure
  ( Block (..)
  , FaultKind (..)
  , FaultView (..)
  , Nature (..)
  , PartView (..)
  , Piece (..)
  , Role (..)
  , Side (..)
  , Stage (..)
  , StopView (..)
  , Why (..)
  )

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


-- | The view of one unfinished item, from the response that reported it.
--
-- **The first unfinished item is the root** — the one whose reason a pane
-- shows — so every test below asks about that one.
viewOf :: Session -> Response -> IO StopView
viewOf s r = case r of
  ProofLoadedPartly _ _ _ _ (root : _) ->
    pure (failureView (Budget 200) s root)
  other -> assertFailure ("expected a partial load with an unfinished item, got " ++ show other)

-- | The one fault a 'Broken' item carries.
faultOf :: StopView -> IO FaultView
faultOf sv = case stopViewWhy sv of
  Faulty [one] -> pure one
  other -> assertFailure ("expected exactly one fault, got " ++ show other)

-- | What a fault says is playing this role.
playing :: Role -> FaultView -> [Piece]
playing r f = [ partViewPiece p | p <- faultViewParts f, partViewRole p == r ]

viewTests :: TestTree
viewTests = testGroup "the view of an unfinished item (MS12 phase 325)"
  [ -- **The row the tui track measured**, which is what the view exists for:
    -- @broken did not go in: stuck: not in scope: nonesuch@, drawn from parts
    -- rather than from text.
    testCase "a name that resolves to nothing is NotInScope, and the name is a part" $ do
      (s, out) <- importing Lenient "test.modules.PartlyGood"
      r <- about "test.modules.PartlyGood" out
      sv <- viewOf s r
      stopViewNature sv @?= Broken
      f <- faultOf sv
      faultViewKind f @?= NotInScope
      playing TheWord f @?= [AName "nonesuch"]
      -- **A leaf, so there is nothing indented under it.**
      faultViewInside f @?= Nothing

  , -- **The crossing against the text door.** The convention for every view:
    -- the pane and the prompt must not disagree about what the failure is
    -- about, and a name is the one part both of them say out loud.
    testCase "the name in the part is the name the prompt prints" $ do
      (s, out) <- importing Lenient "test.modules.PartlyGood"
      r <- about "test.modules.PartlyGood" out
      sv <- viewOf s r
      f <- faultOf sv
      let text = unlines (renderResponse s r)
      case playing TheWord f of
        [AName n] -> assertBool ("the prompt says " ++ n ++ ": " ++ text)
                                (("not in scope: " ++ n) `isInfixOf` text)
        other -> assertFailure ("expected one name, got " ++ show other)

  , -- **Two terms and neither is /found/**: @Mismatch@ is symmetric, so the
    -- second one is 'TheOther' and not 'TheFound'. A pane drawing a
    -- side-by-side has to know which of those it has.
    testCase "two types that cannot be made equal are two typed term parts" $ do
      (s, out) <- importing Lenient "test.modules.PartlyMistyped"
      r <- about "test.modules.PartlyMistyped" out
      sv <- viewOf s r
      stopViewNature sv @?= Broken
      f <- faultOf sv
      faultViewKind f @?= TypesDiffer
      assertBool ("the term: " ++ show f) (length (playing TheTerm f) == 1)
      assertBool ("the other: " ++ show f) (length (playing TheOther f) == 1)
      assertBool ("both are terms: " ++ show f)
                 (all isTerm (playing TheTerm f ++ playing TheOther f))

  , -- **The item that fails is the only one that gets a view**, and the two
    -- that landed are not in the list at all. Said here because a pane draws
    -- the fold from this list.
    testCase "only the unfinished item has a view" $ do
      (s, out) <- importing Lenient "test.modules.PartlyMistyped"
      r <- about "test.modules.PartlyMistyped" out
      case r of
        ProofLoadedPartly _ ds _ _ unfin -> do
          map unfinishedDeclares unfin @?= [["mistyped"]]
          assertBool ("what went in: " ++ show ds) ("first" `elem` ds)
          assertBool ("what went in: " ++ show ds) ("after" `elem` ds)
          _ <- viewOf s r
          pure ()
        other -> assertFailure ("expected a partial load, got " ++ show other)

  , -- **Four natures and not three** — the tui track asked for /fault, halt,
    -- given up/, and @Untrusted@ is in none of them. The closed list is their
    -- one condition on the shape, so it is asserted rather than described.
    testCase "a pane can enumerate the natures, and there are four" $
      [minBound .. maxBound] @?= [Broken, Stopped, NotTrusted, GivenUp]

  , -- **Nothing in the parts is a sentence.** The whole of what separates this
    -- shape from the one he rejected on 2026-11-19 is that a part is a typed
    -- value, so a fault whose every part was text would be the rejected shape
    -- wearing this one's type.
    testCase "the parts of a real failure are not text" $ do
      (s, out) <- importing Lenient "test.modules.PartlyGood"
      r <- about "test.modules.PartlyGood" out
      sv <- viewOf s r
      f <- faultOf sv
      assertBool ("no part is loose text: " ++ show f)
                 (not (any isLooseText (map partViewPiece (faultViewParts f))))
  ]
  where
    isTerm pc = case pc of
      ATerm _ -> True
      _       -> False
    isLooseText pc = case pc of
      AText _ -> True
      _       -> False

-- | **A refused grammar block says what is wrong with it** (MS12 phase 338,
-- @~csndm@).
--
-- Phase 325 walked every other failure into a kind and typed parts and left
-- this one carrying only its location, so a pane could draw /the language block
-- LC was refused, in production app/ and not the half of the sentence that says
-- what to change. The four fixtures are one problem from each level of the
-- grammar's own failures — the top of the tree, a production, a context block's
-- shape, and a judgment's rule.
--
-- **What is asserted is the split**: the location is on the outer fault and
-- what is wrong is the fault inside it. That is the thing a pane is written
-- against, and it is why two problems that are the same kind — a context whose
-- production shapes are wrong and a production with no items are both
-- 'BlockShapeWrong' — are still told apart.
grammarTests :: TestTree
grammarTests = testGroup "a refused grammar block, walked (MS12 phase 338)"
  [ testCase "a production problem is the fault inside, and the production is outside" $ do
      (s, out) <- importing Lenient "test.modules.GrammarScopes"
      r <- about "test.modules.GrammarScopes" out
      sv <- viewOf s r
      stopViewNature sv @?= Broken
      f <- faultOf sv
      faultViewKind f @?= GrammarRefused
      playing TheBlock f @?= [ABlock ALanguage]
      playing TheName f @?= [AName "LC"]
      playing TheProduction f @?= [AName "app"]
      -- **The half that did not exist before this phase.**
      inner <- insideOf f
      faultViewKind inner @?= ScopesDiffer
      playing TheName inner @?= [AName "M"]

  , -- **The crossing against the text door**, the convention for every view:
    -- the pane and the prompt must not disagree about what the failure is
    -- about.
    testCase "the name in the inner part is the name the prompt prints" $ do
      (s, out) <- importing Lenient "test.modules.GrammarScopes"
      r <- about "test.modules.GrammarScopes" out
      sv <- viewOf s r
      f <- faultOf sv
      inner <- insideOf f
      let text = unlines (renderResponse s r)
      case playing TheName inner of
        [AName n] ->
          assertBool ("the prompt says " ++ n ++ ": " ++ text)
                     ((n ++ " is written with different binders") `isInfixOf` text)
        other -> assertFailure ("expected one name, got " ++ show other)

  , -- **A problem at the top of the tree has no production**, and the inner
    -- fault has no parts of its own: the name it is about is the block's, which
    -- is already outside. A pane reading the inner fault alone would draw
    -- nothing, which is why the split is the thing asserted.
    testCase "a problem about the block itself names nothing inside it" $ do
      (s, out) <- importing Lenient "test.modules.GrammarTaken"
      r <- about "test.modules.GrammarTaken" out
      sv <- viewOf s r
      f <- faultOf sv
      faultViewKind f @?= GrammarRefused
      playing TheName f @?= [AName "LC"]
      playing TheProduction f @?= []
      inner <- insideOf f
      faultViewKind inner @?= NameAlreadyDeclared
      faultViewParts inner @?= []

  , -- **The kind is shared with a production that has no items**, and only the
    -- absence of 'TheProduction' outside says which of the two this is.
    testCase "a context's shape is the block's shape, so no production is named" $ do
      (s, out) <- importing Lenient "test.modules.GrammarContext"
      r <- about "test.modules.GrammarContext" out
      sv <- viewOf s r
      f <- faultOf sv
      playing TheBlock f @?= [ABlock AContext]
      playing TheName f @?= [AName "Ctx"]
      playing TheProduction f @?= []
      inner <- insideOf f
      faultViewKind inner @?= BlockShapeWrong

  , -- **A rule, and the side of it.** 'Side' is the one part this phase added
    -- to the vocabulary: the author wrote premises above the line and a
    -- conclusion below it, and a pane that draws a rule draws them apart.
    testCase "a rule that does not read says which side of the line it is" $ do
      (s, out) <- importing Lenient "test.modules.GrammarRule"
      r <- about "test.modules.GrammarRule" out
      sv <- viewOf s r
      f <- faultOf sv
      playing TheBlock f @?= [ABlock AJudgment]
      playing TheName f @?= [AName "typing"]
      playing TheRule f @?= [AName "T-true"]
      inner <- insideOf f
      faultViewKind inner @?= CouldNotRead
      playing TheSide inner @?= [ASide TheConclusion]
      playing TheStage inner @?= [AStage Parsing]
      -- **The author's own text**, which is what 'AText' is for and the one
      -- place a sentence would be wrong.
      case playing TheText inner of
        [AText t] -> assertBool ("the conclusion as written: " ++ show t)
                                ("true" `isInfixOf` t)
        other -> assertFailure ("expected the text, got " ++ show other)
  ]

-- | The fault indented under this one, which every refused block now has.
insideOf :: FaultView -> IO FaultView
insideOf f = case faultViewInside f of
  Just inner -> pure inner
  Nothing -> assertFailure ("expected a fault inside: " ++ show f)

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

  , viewTests
  , grammarTests
  , positionTests
  , blockTests
  ]

-- | __One unfinished proof inside a group no longer throws the group away__
-- (MS12 phase 336, @~6g27s@, his ruling of 2026-11-22).
--
-- **A @namespace@, @import … where@, @consult … where@, @private@ or
-- @open … in@ block was ONE item to the loader** until this phase, so
-- @namespace lemmata where { a ; b ; c }@ whose @b@ did not elaborate threw @a@
-- and @c@ away with it and reported one unfinished item naming all three. The
-- loader walks into a block now: the ops that open it run as their own program,
-- its declarations are walked one at a time, and the block is closed at the end
-- — the three moves 'Thena.Driver.loadProofItemsConsultingAt' already made for
-- a module body.
--
-- **What is pinned here is both halves**: that a sibling lands, and that the
-- block still ends where it ended — his ruling @~ckmsk@, that an @open@ reaches
-- to the end of the block it is written in, is the one that a walk closing a
-- block by hand could silently lose.
blockTests :: TestTree
blockTests = testGroup "the loader walks into a block (MS12 phase 336)"
  [ testCase "a sibling of an unfinished declaration inside a namespace lands" $ do
      s <- fresh
      case snd (loadProofSource Lenient s grouped) of
        ProofLoadedPartly _ ds _ _ unfin -> do
          -- **The whole of the ruling**: two of the three go in, under the
          -- block's prefix, and the one that did not is named on its own.
          assertBool ("what went in: " ++ show ds) ("lemmata.good" `elem` ds)
          assertBool ("what went in: " ++ show ds) ("lemmata.alsogood" `elem` ds)
          assertBool ("what went in: " ++ show ds) ("lemmata.broken" `notElem` ds)
          map unfinishedDeclares unfin @?= [["lemmata.broken"]]
        other -> assertFailure ("expected a partial load, got " ++ show other)

  , testCase "and the block is left, so what follows it is not inside it" $ do
      -- The namespace is closed once, at the end: a declaration written under
      -- the block lands at the module's own level and not under the prefix.
      s <- fresh
      case snd (loadProofSource Lenient s grouped) of
        ProofLoadedPartly _ ds _ _ _ -> do
          assertBool ("what went in: " ++ show ds) ("after" `elem` ds)
          assertBool ("what went in: " ++ show ds) ("lemmata.after" `notElem` ds)
        other -> assertFailure ("expected a partial load, got " ++ show other)

  , testCase "an open written inside a block still comes off with it" $ do
      -- **@~ckmsk@, and it is what the close has to get right.** The pops were
      -- counted off the one program the whole block compiled to; the walk
      -- cannot count ahead, so it closes to the depth the block was entered at.
      -- @inside@ writes the constructor bare and lands; @outside@ writes it
      -- bare after the block and is refused.
      s <- fresh
      case snd (loadProofSource Lenient s opened) of
        ProofLoadedPartly _ ds _ _ unfin -> do
          assertBool ("what went in: " ++ show ds) ("A.inside" `elem` ds)
          map unfinishedDeclares unfin @?= [["outside"]]
        other -> assertFailure ("expected a partial load, got " ++ show other)

  , testCase "a declaration inside a nested block lands under both prefixes" $ do
      -- Nesting is a longer prefix and costs no mechanism, which is as true of
      -- the walk as it was of the one compiled program.
      s <- fresh
      case snd (loadProofSource Lenient s nested) of
        ProofLoadedPartly _ ds _ _ unfin -> do
          assertBool ("what went in: " ++ show ds) ("A.B.good" `elem` ds)
          map unfinishedDeclares unfin @?= [["A.B.broken"]]
        other -> assertFailure ("expected a partial load, got " ++ show other)

  , testCase "a declaration inside an import's block lands, and the names still come off" $ do
      -- The other close: a 'Reveal' and its 'LeaveReveal'. @good@ writes a name
      -- the block reveals and lands; @outside@ writes it after the block and is
      -- refused, which is what @import … where@ means. **Through the IO door**,
      -- because the block names a module that has to be read off the disc.
      (_, out) <- importing Lenient "test.modules.PartlyInBlock"
      r <- about "test.modules.PartlyInBlock" out
      case r of
        ProofLoadedPartly _ ds _ _ unfin -> do
          assertBool ("what went in: " ++ show ds) ("good" `elem` ds)
          map unfinishedDeclares unfin @?= [["broken"], ["outside"]]
        other -> assertFailure ("expected a partial load, got " ++ show other)
  ]
  where
    grouped = unlines
      [ "module test.Grouped where"
      , ""
      , "namespace lemmata where"
      , "  good : Type\8321"
      , "  good = Type\8320"
      , ""
      , "  broken : Flag.Flag"
      , "  broken = nonesuch"
      , ""
      , "  alsogood : Type\8321"
      , "  alsogood = Type\8320"
      , ""
      , "after : Type\8321"
      , "after = Type\8320"
      ]
    opened = unlines
      [ "module test.Opened where"
      , ""
      , "data Pair : Type\8320 where"
      , "  only : Pair"
      , ""
      , "namespace A where"
      , "  open Pair"
      , "  inside : Pair"
      , "  inside = only"
      , ""
      , "outside : Pair"
      , "outside = only"
      ]
    nested = unlines
      [ "module test.Nested where"
      , ""
      , "namespace A where"
      , "  namespace B where"
      , "    good : Type\8321"
      , "    good = Type\8320"
      , ""
      , "    broken : Flag.Flag"
      , "    broken = nonesuch"
      ]

-- | __Where a declaration that did not go in was written__ (MS12 phase 334,
-- @~hcr2d@).
--
-- **His ask of 2026-11-20 was a line and a column**, so that a row in a pane's
-- fold under a module is a place to go rather than a sentence. Nothing in the
-- engine knew one before this phase: the lexer had a position on every token
-- and the parser dropped it.
--
-- **The fixture's line numbers are the assertion.** @PartlyGood.thena@ writes
-- @broken : Flag.Flag@ on line 12 at column 1 and @PartlyWorse.thena@ writes
-- @broken@ on line 12 and @alsoBroken@ on line 15; a signature and its equation
-- are one item, so the line is the signature's.
positionTests :: TestTree
positionTests = testGroup "where an unfinished declaration was written (MS12 phase 334)"
  [ testCase "the line and column reach the unfinished item" $ do
      (_, out) <- importing Lenient "test.modules.PartlyGood"
      r <- about "test.modules.PartlyGood" out
      case r of
        ProofLoadedPartly _ _ _ _ [u] -> do
          unfinishedDeclares u @?= ["broken"]
          unfinishedAt u @?= Just (Pos 12 1)
        other -> assertFailure ("expected one unfinished item, got " ++ show other)

  , testCase "and reach the view a pane draws" $ do
      -- **The one that matters**: a pane never sees an 'Unfinished', it sees
      -- this view, so a position that stopped here would have gone nowhere.
      (s, out) <- importing Lenient "test.modules.PartlyGood"
      r  <- about "test.modules.PartlyGood" out
      sv <- viewOf s r
      stopViewAt sv @?= Just (Pos 12 1)

  , testCase "each unfinished item carries its own line" $ do
      -- Two failures in one file, in file order — so the positions are not one
      -- position repeated, and not the module's.
      (_, out) <- importing Lenient "test.modules.PartlyWorse"
      r <- about "test.modules.PartlyWorse" out
      case r of
        ProofLoadedPartly _ _ _ _ us ->
          map unfinishedAt us @?= [Just (Pos 12 1), Just (Pos 15 1)]
        other -> assertFailure ("expected a partial load, got " ++ show other)

  , testCase "the column is the declaration's own, not column 1" $ do
      -- **What makes the column a measurement rather than a constant.** The
      -- layout pass opens the module's block at the column of its first
      -- declaration, so a file written indented reports that column.
      s <- fresh
      let src = unlines
            [ "module test.Indented where"
            , ""
            , "  broken : Flag.Flag"
            , "  broken = nonesuch"
            ]
      case snd (loadProofSource Lenient s src) of
        ProofLoadedPartly _ _ _ _ [u] -> unfinishedAt u @?= Just (Pos 3 3)
        other -> assertFailure ("expected one unfinished item, got " ++ show other)

  , testCase "a declaration inside a group carries its own line, and its prefix" $ do
      -- **This was the other way round until MS12 phase 336** (@~6g27s@, his
      -- ruling of 2026-11-22): a @namespace@ block was one item to the loader,
      -- so the position a row could point at was the @namespace@ line and the
      -- whole group was thrown away. The loader walks into a block now, so the
      -- declaration that did not go in is the inner one, at the inner line, and
      -- it is named under the block's prefix.
      s <- fresh
      let src = unlines
            [ "module test.Grouped where"
            , ""
            , "namespace lemmata where"
            , "  broken : Flag.Flag"
            , "  broken = nonesuch"
            ]
      case snd (loadProofSource Lenient s src) of
        ProofLoadedPartly _ _ _ _ [u] -> do
          unfinishedDeclares u @?= ["lemmata.broken"]
          unfinishedAt u @?= Just (Pos 4 3)
        other -> assertFailure ("expected one unfinished item, got " ++ show other)

  , testCase "the first declaration of a block takes the opening brace's column" $ do
      -- **A block's first declaration has no @;@ in front of it**, so the brace
      -- that opened the block is what stands there — 'openingAt'. Written out
      -- with an explicit brace, which is the case where the two differ: under
      -- layout the brace is inserted at the first declaration's own column, as
      -- the test above shows, and written by hand it is wherever it is written.
      s <- fresh
      let src = unlines
            [ "module test.Oneline where"
            , ""
            , "namespace lemmata where { broken : Flag.Flag ; broken = nonesuch }"
            ]
      case snd (loadProofSource Lenient s src) of
        ProofLoadedPartly _ _ _ _ [u] -> unfinishedAt u @?= Just (Pos 3 25)
        other -> assertFailure ("expected one unfinished item, got " ++ show other)

  , testCase "an item a caller handed over has no position" $ do
      -- **'Nothing' is honest and is not a missing feature**: there is no file,
      -- so there is nowhere for a row to go. 'Thena.Driver.loadProofItems' is
      -- the door a caller that built the items itself takes.
      s <- fresh
      Just m <- pure (moduleName "test.ByHand")
      let src = unlines
            [ "module test.ByHand where"
            , ""
            , "broken : Flag.Flag"
            , "broken = nonesuch"
            ]
      case parseSurfaceModule src of
        Left e -> assertFailure ("the fixture should parse: " ++ show e)
        Right (_, items) -> case snd (loadProofItems Lenient s m items) of
          ProofLoadedPartly _ _ _ _ [u] -> unfinishedAt u @?= Nothing
          other -> assertFailure ("expected one unfinished item, got " ++ show other)
  ]
