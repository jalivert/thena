-- | A family with a dependent index telescope — proved and admitted at a
-- /friendly/ index (phase 19), and split at a /tied/ one (MS9 phase 214) —
-- and a constructor with a dependent /argument/ telescope, split through (MS9
-- phase 215).
--
-- @examples\/dependent-index.thena.script@ declares
-- @Below : ∀ (n : Nat) (i : Fin n) -> Type₀@ — two indices, the second typed by
-- the first — and proves a theorem about it by induction. Before phase 19 the
-- elimination was refused outright, on a condition that only a /tied/ index can
-- violate; both of @Below@'s indices are plain variables here, so the dependent
-- one is friendly and states no equation.
--
-- **This is the check that the motive's dependent telescope is right**, and it
-- is the one the unit suite cannot make: @Thena.EliminateTests@ pins the
-- motive as a string, which says it has the shape intended, while @qed@ runs
-- 'Thena.Kernel.certify' and says the kernel accepts the term built from it.
-- Same pattern as "Thena.DeterminacyTests", and for the same reason.
--
-- __And the tied case, which is the one that states an equation — MS9 phase
-- 214, @~7gmvr@ step three.__ @examples\/tied-index-chain.thena@ declares
-- @Q : ∀ (n : N) -> Fin n -> Type₀@ and splits a @Q (s m) (fz m)@. Both indices
-- are tied there, the second's type mentions the first, so the motive states the
-- second equation only after transporting its side along the first — and the
-- second equation is stated about the first one's __proof__. Solving the first
-- removes the binder that proof is, so the solution transition supplies @refl@
-- for it and the transports ι-contract.
--
-- __AND THE OTHER TELESCOPE, WHICH IS A DIFFERENT CHAIN IN A DIFFERENT PLACE —
-- MS9 phase 215.__ @examples\/dependent-argument-chain.thena@ declares
-- @Pack@, whose one constructor's /own/ arguments are dependent — @i : Fin n@
-- after @n : N@ — over a datatype with no indices at all. So the chain is in
-- @noConfusionPack@ rather than in the motive, and the transition that meets it
-- is injectivity rather than solution. Neither telescope is downstream of the
-- other.
--
-- __It is a module and not a tactic script__, because the thing being exercised
-- is the surface split: @case … of@ is what reaches
-- "Thena.Tactics.Specialise", and a hand-driven @eliminate-core@ never does.
-- The declaration is elaborated and then type-checked whole, which is the
-- independent judge here — "Thena.SpecialiseTests" asserts the specialised
-- method type, and this says the term built from it is accepted.
module Thena.DependentIndexTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=), assertBool)

import Thena.Core.Reduce (whnf)
import Thena.Core.Term (Core (Canonical), GlobalName (..))
import Thena.Driver
  ( machineOf
  )
import Thena.Engine (Machine (..))
import Thena.Global.Env (Definition (..), lookupDefinition)
import Thena.Files (loadFile, loadProofFile, startingSession)
import Thena.Render ( Rendering (..)
  ,renderCore)

-- | Relative to the package root, which is where the suite runs.
target :: FilePath
target = "examples/dependent-index.thena.script"

tiedTarget :: FilePath
tiedTarget = "examples/tied-index-chain.thena"

argumentTarget :: FilePath
argumentTarget = "examples/dependent-argument-chain.thena"

vectorTarget :: FilePath
vectorTarget = "examples/vector-families.thena"

tests :: TestTree
tests =
  testGroup
    "a dependent index telescope, end to end"
    [ testCase "the tied file runs to the end" $ do
        (s, _) <- startingSession
        (_, _, stopped) <- loadProofFile s tiedTarget
        assertBool (unlines (map show stopped)) (null stopped)

      -- The split discharged both equations, so the arm bound the
      -- constructor's two arguments and nothing else. Were either equation
      -- kept, the arm would have been handed a hypothesis it does not bind and
      -- the declaration would not be here at all.
    , testCase "and the split's definition is admitted at its written type" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadProofFile s tiedTarget
        case lookupDefinition (GlobalName "tied") (globals (machineOf s')) of
          Nothing -> assertFailure "tied was not admitted"
          Just d  ->
            renderCore (Rendering [] (names (machineOf s'))) [] (definitionType d)
              @?= "\8704 (m : N) -> Q (s m) (fz m) -> N"

      -- The split's one equation is between two @pack@ applications, so
      -- injectivity fires and has to read the lemma's chain apart. Both of the
      -- equations it yields are then discharged, so the arm binds the
      -- constructor's arguments alone.
    , testCase "the dependent-argument file runs to the end" $ do
        (s, _) <- startingSession
        (_, _, stopped) <- loadProofFile s argumentTarget
        assertBool (unlines (map show stopped)) (null stopped)

      -- __And the arm really binds them__: @depth@ answers with the
      -- constructor's own @n@, so it computes to @s (s z)@ where the ambient
      -- @m@ would have given the same number by a different route. Reducing is
      -- what tells the two apart — an arm that had been handed the ambient copy
      -- would still have this type.
    , testCase "and the split's arm computes from the arguments it bound" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadProofFile s argumentTarget
        let m = machineOf s'
        case lookupDefinition (GlobalName "depth") (globals m) of
          Nothing -> assertFailure "depth was not admitted"
          Just d  ->
            renderCore (Rendering [] (names m)) [] (definitionType d)
              @?= "\8704 (m : N) (j : Fin m) -> Holds (pack m j) -> N"

      -- __The @Vec@-style families, which the corpus had never had — MS9 phase
      -- 216.__ @examples\/vector-families.thena@ declares @Vec@ at a level
      -- parameter and @All@ over it, whose /index/ telescope is dependent and
      -- whose @allCons@ reaches back past an argument nothing mentions. That
      -- last shape is what the phase found: the chain's package holds an
      -- interior member, the rest of the package is transported along its
      -- equation, and a generator that predicted the pair from the telescope
      -- left that proof free.
    , testCase "the vector file runs to the end" $ do
        (s, _) <- startingSession
        (_, _, stopped) <- loadProofFile s vectorTarget
        assertBool (unlines (map show stopped)) (null stopped)

      -- __And the recursion really fires.__ @count@ is a recursion over a
      -- dependent index telescope, so its split generalises both indices and
      -- the induction hypothesis has to be found at the shorter vector;
      -- @one@ is it at a one-element vector, and reducing is what says the
      -- hypothesis was reached rather than merely bound.
    , testCase "and the recursion over it computes" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadProofFile s vectorTarget
        let m = machineOf s'
        case lookupDefinition (GlobalName "one") (globals m) of
          Nothing -> assertFailure "one was not admitted"
          Just d  -> case whnf (globals m) [] (definitionBody d) of
            Canonical (GlobalName "s") _ [inner] ->
              case whnf (globals m) [] inner of
                Canonical (GlobalName "z") _ [] -> pure ()
                other -> assertFailure ("s applied to " ++ show other)
            other -> assertFailure ("not a successor: " ++ show other)

      -- __Two indices reaching back to the same earlier one__ — both of
      -- @Pairwise@\'s vectors are @Vec A n@, which is the shape MS9 phase 226
      -- made declarable: two components come out of one package and each one\'s
      -- projection mentions the other\'s argument, so the chain\'s substitution
      -- is simultaneous and not a fold. @two@ counts a one-element pair, so
      -- reducing says the split discharged all three equations and the arm
      -- reached its own induction hypothesis.
    , testCase "and so does the recursion over two vectors of one length" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadProofFile s vectorTarget
        let m = machineOf s'
        case lookupDefinition (GlobalName "two") (globals m) of
          Nothing -> assertFailure "two was not admitted"
          Just d  -> case whnf (globals m) [] (definitionBody d) of
            Canonical (GlobalName "s") _ [inner] ->
              case whnf (globals m) [] inner of
                Canonical (GlobalName "z") _ [] -> pure ()
                other -> assertFailure ("s applied to " ++ show other)
            other -> assertFailure ("not a successor: " ++ show other)

    , testCase "the file runs to the end" $ do
        (s, _) <- startingSession
        (_, _, stopped) <- loadFile s target
        assertBool (unlines (map show stopped)) (null stopped)

    , testCase "and the theorem is a global with the statement it should have" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadFile s target
        case lookupDefinition (GlobalName "belowRefl") (globals (machineOf s')) of
          Nothing -> assertFailure "belowRefl was not admitted"
          Just d  ->
            renderCore (Rendering [] (names (machineOf s'))) [] (definitionType d)
              @?= "∀ (n : Nat) (i : Fin n) -> Below n i -> Eq {0} (Fin n) i i"
    ]
