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
import Test.Tasty.HUnit (Assertion, assertFailure, testCase, (@?=), assertBool)

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

chainedTarget :: FilePath
chainedTarget = "examples/chained-index-telescope.thena"

-- | One rung deeper, and __its own file because it is expensive__: the
-- generated term grows about fourfold per chained index, so this split alone is
-- most of a load. One test case reads it, where the shallow file has three.
deepTarget :: FilePath
deepTarget = "examples/chained-index-telescope-deep.thena"

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

      -- __AND THE SAME CHAIN CROSSED BY INJECTIVITY RATHER THAN BY SOLUTION —
      -- MS9, @~rqs39@.__ @isFz@'s target pins the first index to @s n@, so the
      -- first equation is between two applications of @s@ where @mk@'s was a
      -- variable against a term. Injectivity drops that equation's binder, and
      -- the second equation — stated about it — is restated along the proof
      -- rebuilt by @noConfusionNInv@, with @isLeftInvN@ carrying the method
      -- back. Refused by name until the backwards half was generated.
    , testCase "and the split injectivity crosses is admitted at its written type" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadProofFile s tiedTarget
        case lookupDefinition (GlobalName "tiedTwo") (globals (machineOf s')) of
          Nothing -> assertFailure "tiedTwo was not admitted"
          Just d  ->
            renderCore (Rendering [] (names (machineOf s'))) [] (definitionType d)
              @?= "\8704 (m : N) -> Small (s m) (fz m) -> N"

      -- __And the arm answers with its own binder.__ The ambient @m@ and the
      -- constructor's @n@ are the same number here, so the type says nothing
      -- about which one was bound and only reducing does.
    , testCase "and the arm injectivity crossed computes from its own binder" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadProofFile s tiedTarget
        let m = machineOf s'
        case lookupDefinition (GlobalName "twoFromArm") (globals m) of
          Nothing -> assertFailure "twoFromArm was not admitted"
          Just d  -> case whnf (globals m) [] (definitionBody d) of
            Canonical (GlobalName "s") _ [inner] ->
              case whnf (globals m) [] inner of
                Canonical (GlobalName "s") _ [innermost] ->
                  case whnf (globals m) [] innermost of
                    Canonical (GlobalName "z") _ [] -> pure ()
                    other -> assertFailure ("s (s " ++ show other ++ ")")
                other -> assertFailure ("s applied to " ++ show other)
            other -> assertFailure ("not a successor: " ++ show other)

      -- __AND THE SHAPE DELETION MATCHES FIRST — MS9 phase 234, @~pxgxw@.__
      -- @T@'s index pins @fs@'s first argument on both sides, so the chain's
      -- first equation is @Eq N (s z) (s z)@: the same term twice, which is
      -- deletion's shape, and deletion is the one transition that cannot carry
      -- a chain. Injectivity applies to that very equation and is offered it,
      -- the chain reads apart to @Eq N z z@ and then to @Unit@, and the proof
      -- is rebuilt from @unit@ where no argument is left. Refused by name,
      -- with UIP as the reason, until that fallthrough existed.
    , testCase "and a chain deletion matched first is crossed by injectivity" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadProofFile s tiedTarget
        case lookupDefinition (GlobalName "pinned") (globals (machineOf s')) of
          Nothing -> assertFailure "pinned was not admitted"
          Just d  ->
            renderCore (Rendering [] (names (machineOf s'))) [] (definitionType d)
              @?= "T (fs (s z) (fz z)) -> Fin (s z)"

      -- __And that arm binds the constructor's argument too.__ The type says
      -- nothing about it — @Fin (s z)@ has more than one inhabitant here — so
      -- reducing at a known argument is what says the arm answered with it.
    , testCase "and the arm it crossed answers with the argument it bound" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadProofFile s tiedTarget
        let m = machineOf s'
        case lookupDefinition (GlobalName "pinnedFromArm") (globals m) of
          Nothing -> assertFailure "pinnedFromArm was not admitted"
          Just d  -> case whnf (globals m) [] (definitionBody d) of
            Canonical (GlobalName "fz") _ [inner] ->
              case whnf (globals m) [] inner of
                Canonical (GlobalName "z") _ [] -> pure ()
                other -> assertFailure ("fz applied to " ++ show other)
            other -> assertFailure ("not fz: " ++ show other)

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

      -- __A PROJECTION AT A PINNED INDEX — MS9 phase 235, @~5hshj@.__ Not a
      -- recursion and not a variable index: @vcons A m a as@ pins @vcons@'s
      -- own arguments, so the chain states an equation about its length —
      -- @m@ against @m@, because @Vec A (s n)@ says the length is the index —
      -- which says nothing and which deletion over a chain cannot remove
      -- without UIP. Injectivity reads a pinned index apart by projection
      -- instead, so no such equation is stated at all. Refused by name until
      -- then.
    , testCase "and a projection at a pinned index is admitted" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadProofFile s vectorTarget
        case lookupDefinition (GlobalName "headAll") (globals (machineOf s')) of
          Nothing -> assertFailure "headAll was not admitted"
          Just d  ->
            renderCore (Rendering [] (names (machineOf s'))) [] (definitionType d)
              @?= "\8704 (A : Type\8320) (P : A -> Type\8320) (m : N) (a : A) (as : Vec {0} A m) -> All A P (s m) (vcons {0} A m a as) -> P a"

      -- __And the arm answers with the argument it bound__, which the type
      -- cannot say: @headTwo@ is the projection at a one-element @All@, and
      -- only reducing says the proof came out of the constructor rather than
      -- from anywhere else.
    , testCase "and the arm of that projection computes" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadProofFile s vectorTarget
        let m = machineOf s'
        case lookupDefinition (GlobalName "headTwo") (globals m) of
          Nothing -> assertFailure "headTwo was not admitted"
          Just d  -> case whnf (globals m) [] (definitionBody d) of
            Canonical (GlobalName "s") _ [inner] ->
              case whnf (globals m) [] inner of
                Canonical (GlobalName "s") _ [innermost] ->
                  case whnf (globals m) [] innermost of
                    Canonical (GlobalName "z") _ [] -> pure ()
                    other -> assertFailure ("s (s " ++ show other ++ ")")
                other -> assertFailure ("s applied to " ++ show other)
            other -> assertFailure ("not a successor: " ++ show other)

      -- __AND THE CHAINED TELESCOPE — MS9 phase 237, @~fq5gp@.__ @Chain@'s
      -- third index is tied and its type mentions BOTH earlier ones, while the
      -- second's type mentions the first, so transporting the first has to
      -- carry the second with it. The motive binds the position that moves and
      -- states the right-hand residue at it carried along the same proof; this
      -- was refused by position and name until the phase.
    , testCase "the chained file runs to the end" $ do
        (s, _) <- startingSession
        (_, _, stopped) <- loadProofFile s chainedTarget
        assertBool (unlines (map show stopped)) (null stopped)

    , testCase "and the chained split is admitted at its written type" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadProofFile s chainedTarget
        case lookupDefinition (GlobalName "chained") (globals (machineOf s')) of
          Nothing -> assertFailure "chained was not admitted"
          Just d  ->
            renderCore (Rendering [] (names (machineOf s'))) [] (definitionType d)
              @?= "\8704 (m : N) -> Chain (s m) (fz m) (bz m) -> N"

      -- __And the arm answers with the constructor's own payload__, which the
      -- type cannot say. A split that typechecked and refined nothing would
      -- still admit @chained@ at the type above; only reducing says the @w@ the
      -- arm bound is the @w@ @c0@ was applied to.
    , testCase "and the chained arm computes from the payload it bound" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadProofFile s chainedTarget
        numeral (machineOf s') "chainedPayload" 3

      -- __One rung deeper, which is what says the construction recurses.__
      -- @Deep@'s fourth index is typed by @Over n i b@, whose own telescope is
      -- chained, so carrying the first position has to carry @b@, and carrying
      -- @b@ has to carry @i@ first. Two levels of the recursion in one split.
      --
      -- __One case for the three assertions the shallow file gets separately__,
      -- because this load is about six seconds on its own and the three would
      -- be three of them. Running to the end, being admitted and computing are
      -- all said by the payload reducing: it cannot reduce if the file stopped
      -- or the definition was never admitted.
    , testCase "and a telescope one rung deeper again computes too" $ do
        (s, _) <- startingSession
        (s', _, stopped) <- loadProofFile s deepTarget
        assertBool (unlines (map show stopped)) (null stopped)
        numeral (machineOf s') "deepPayload" 2

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

-- | A global that must reduce to a specific @N@ numeral.
--
-- The payload assertions want /the arm bound this argument and not another/,
-- and a numeral is how a term says so: @z@ and @s@ are the only two things it
-- can be built from, so reducing to the right depth cannot happen by accident.
numeral :: Machine -> String -> Int -> Assertion
numeral m name expected =
  case lookupDefinition (GlobalName name) (globals m) of
    Nothing -> assertFailure (name ++ " was not admitted")
    Just d  -> go expected (whnf (globals m) [] (definitionBody d))
  where
    go 0 t = case t of
      Canonical (GlobalName "z") _ [] -> pure ()
      other -> assertFailure (name ++ ": expected z, got " ++ show other)
    go k t = case t of
      Canonical (GlobalName "s") _ [inner] ->
        go (k - 1) (whnf (globals m) [] inner)
      other ->
        assertFailure (name ++ ": expected a successor, got " ++ show other)
