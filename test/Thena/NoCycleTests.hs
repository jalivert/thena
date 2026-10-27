-- | The generated acyclicity equipment — @Below@, @NotEq@, @NotBelow@ and
-- @NotBelowEq@ (MS9 phase 219, "Thena.Global.NoCycle").
--
-- Four groups, and each asks the question by different code from the code that
-- built the answer — the standing lesson from phases 2–5:
--
--   * 'reduceTests' pins what the tuple /computes/. The generator only ever
--     typed what it built, through @check@; whether @Below P (succ n)@ is the
--     conjunction of the sub-tuple and the motive at @n@ is decided by ι in
--     "Thena.Core.Reduce" and by conversion, which share no code with it. A
--     generator that put @Unit@ everywhere would still typecheck.
--   * 'constructionTests' is the one that matters most: the appendix's @Step@
--     lemma, the diagonal and @noCycle@ itself, written in the surface language
--     over the __generated__ relations and carried all the way to the user's
--     correctly-omitted case. Phase 220 generates exactly these; this says they
--     can be built on what phase 219 emits.
--   * 'kernelTests' re-checks all four with 'Thena.Kernel.certify'.
--   * 'guardTests' pins the thing @.claude\/HAZARDS.md@ records: this bundle has
--     __its own__ precondition, so a missing @Unit@ costs the acyclicity
--     equipment and leaves the no-confusion lemma standing.
module Thena.NoCycleTests (tests) where

import Data.List (isInfixOf)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertFailure, testCase, (@?=))

import Thena.Core.Term (GlobalName (..))
import Thena.Declared
  ( andDecl
  , declared
  , dpairDecl
  , emptyDecl
  , eqDecl
  , eqNat
  , eqNatFin
  , eqNatVec
  , eqStep
  , eqTapl
  , finDecl
  , natDecl
  , preludeDecls
  )
import Thena.Driver (Response (..), loadProofSource)
import Thena.Files (startingSession)
import Thena.Global.Env (GlobalEnv, definitionBody, definitionType, lookupDefinition)
import Thena.Kernel (certify)
import Thena.Render (renderResponse)

tests :: TestTree
tests =
  testGroup
    "Thena.Global.NoCycle"
    [ testGroup "the tuple computes the right case" reduceTests
    , testGroup "the appendix's construction, over what was generated" constructionTests
    , testGroup "the kernel accepts what was generated" kernelTests
    , testGroup "its own precondition, and what each piece is for" guardTests
    ]

-- --------------------------------------------------------------------------
-- What it computes
-- --------------------------------------------------------------------------

-- | Each of these is a definition whose /body/ is the unreduced application and
-- whose /type/ is what it should reduce to, so the assertion is made by
-- conversion rather than by comparing text.
reduceTests :: [TestTree]
reduceTests =
  [ testCase "a constructor with no recursive argument — nothing is below it" $
      loads
        [ "module BelowZero where"
        , ""
        , "data N : Type\8320 where"
        , "  z : N"
        , "  s : N -> N"
        , ""
        , "belowZ : \8704 (P : N -> Type\8320) (h : BelowN P z) -> Unit"
        , "belowZ = \\ P h -> h"
        ]
  , testCase "and one with a recursive argument — the sub-tuple and the motive" $
      loads
        [ "module BelowSucc where"
        , ""
        , "data N : Type\8320 where"
        , "  z : N"
        , "  s : N -> N"
        , ""
        , "belowS : \8704 (P : N -> Type\8320) (n : N) (h : BelowN P (s n))"
        , "      -> And (BelowN P n) (P n)"
        , "belowS = \\ P n h -> h"
        ]
  , -- **The motive is applied to the ARGUMENT's indices, not the target's** —
    -- @evs@ lands at @s (s n)@ while its recursive argument sits at @n@, and a
    -- generator that read the target's indices would be ill-typed here rather
    -- than merely wrong.
    testCase "an indexed family: the motive is at the argument's own index" $
      loads
        [ "module BelowEv where"
        , ""
        , "data N : Type\8320 where"
        , "  z : N"
        , "  s : N -> N"
        , ""
        , "data Ev : N -> Type\8320 where"
        , "  evz : Ev z"
        , "  evs : \8704 (n : N) (e : Ev n) -> Ev (s (s n))"
        , ""
        , "evzBelow : \8704 (j : N) (y : Ev j) (h : NotBelowEv j y z evz) -> Unit"
        , "evzBelow = \\ j y h -> h"
        , ""
        , "evsBelow : \8704 (n : N) (e : Ev n) (j : N) (y : Ev j)"
        , "             (h : NotBelowEv j y (s (s n)) (evs n e))"
        , "        -> And (NotBelowEv j y n e) (NotEqEv j y n e)"
        , "evsBelow = \\ n e j y h -> h"
        ]
  , -- @≢@ over a telescope is the curried chain of §3.3 negated: the index
    -- equation, then the element equation stated after transporting along it.
    testCase "NotEq is the curried chain into Empty" $
      loads
        [ "module ApartEv where"
        , ""
        , "data N : Type\8320 where"
        , "  z : N"
        , "  s : N -> N"
        , ""
        , "data Ev : N -> Type\8320 where"
        , "  evz : Ev z"
        , "  evs : \8704 (n : N) (e : Ev n) -> Ev (s (s n))"
        , ""
        , "evApart : \8704 (n : N) (x : Ev n) (j : N) (y : Ev j)"
        , "            (ne : NotEqEv n x j y)"
        , "            (q : (Eq N n j : Type\8320))"
        , "            (r : (Eq (Ev j) (transport N (\\ w -> Ev w) n j q x) y"
        , "                    : Type\8320))"
        , "         -> Empty"
        , "evApart = \\ n x j y ne q r -> ne q r"
        ]
  ]

-- --------------------------------------------------------------------------
-- The construction
-- --------------------------------------------------------------------------

-- | The whole of @resources\/withoutK.pdf@'s appendix, from (65) to the user's
-- omitted case, over the four definitions phase 219 generates and nothing else
-- written by hand.
--
-- **@noSelf@ is what all of this is for.** @n ≃ s n@ is the equation a split
-- leaves behind when the user correctly omits an impossible case, and the last
-- line turns it into @Empty@ — which is what the cycle transition will do
-- without being asked (phase 221).
constructionTests :: [TestTree]
constructionTests =
  [ testCase "Step, the diagonal, noCycle, and the omitted case discharged" $
      loads
        [ "module Acyclic where"
        , ""
        , "data N : Type\8320 where"
        , "  z : N"
        , "  s : N -> N"
        , ""
        , "-- (65): if the recursive argument is neither below nor equal to b,"
        , "-- neither is the whole application."
        , "stepN : \8704 (m : N) (b : N) -> NotBelowN m b -> NotBelowEqN (s m) b"
        , "stepN = \\ m b ->"
        , "  elim N ()"
        , "    (\\ t -> NotBelowN m t -> NotBelowEqN (s m) t)"
        , "    ( (\\ nb -> both (NotBelowN (s m) z) (NotEqN (s m) z)"
        , "                 unit"
        , "                 (\\ e -> noConfusionN (s m) z e))"
        , "      (\\ k H nb ->"
        , "         both (NotBelowN (s m) (s k)) (NotEqN (s m) (s k))"
        , "           (H (andLeft (NotBelowN m k) (NotEqN m k) nb))"
        , "           (\\ e -> andRight (NotBelowN m k) (NotEqN m k) nb"
        , "                     (noConfusionN (s m) (s k) e))) )"
        , "    () b"
        , ""
        , "-- No term is structurally below itself."
        , "noCycleDiagN : \8704 (a : N) -> NotBelowN a a"
        , "noCycleDiagN = \\ a ->"
        , "  elim N () (\\ t -> NotBelowN t t)"
        , "    ((unit) (\\ m h -> stepN m m h))"
        , "    () a"
        , ""
        , "noCycleN : \8704 (x : N) (y : N) (e : (Eq N x y : Type\8320))"
        , "        -> NotBelowN x y"
        , "noCycleN = \\ x y e ->"
        , "  transport N (\\ w -> NotBelowN x w) x y e (noCycleDiagN x)"
        , ""
        , "noSelfN : \8704 (n : N) (e : (Eq N n (s n) : Type\8320)) -> Empty"
        , "noSelfN = \\ n e ->"
        , "  andRight (NotBelowN n n) (NotEqN n n) (noCycleN n (s n) e) (refl N n)"
        ]
  ]

-- | Load a surface module and insist it went in.
loads :: [String] -> Assertion
loads ls = do
  (s0, _) <- startingSession
  case loadProofSource s0 (unlines ls) of
    (_,  ProofLoaded {}) -> pure ()
    (s1, other)          -> assertFailure (unwords (renderResponse s1 other))

-- --------------------------------------------------------------------------
-- The kernel
-- --------------------------------------------------------------------------

kernelTests :: [TestTree]
kernelTests =
  [ testCase "Nat's tuple" (certified eqNat "BelowNat")
  , testCase "Nat's three relations" $ do
      certified eqNat "NotEqNat"
      certified eqNat "NotBelowNat"
      certified eqNat "NotBelowEqNat"
    -- Four constructors, three of them recursive, and @ifthen@ has three
    -- recursive arguments — so its method conjoins three pairs, which no other
    -- fixture does.
  , testCase "Term's tuple, where a constructor has three recursive arguments" $
      certified eqTapl "BelowTerm"
  , testCase "and its relations" $ certified eqTapl "NotBelowEqTerm"
    -- One index, and a dependent /constructor/ telescope.
  , testCase "Fin's tuple" (certified eqNatFin "BelowFin")
  , testCase "and its relations, whose chain is one index equation deep" $
      certified eqNatFin "NotBelowEqFin"
    -- A parameter as well as an index.
  , testCase "Vec's tuple, with a parameter" (certified eqNatVec "BelowVec")
  , testCase "and its relations" (certified eqNatVec "NotBelowEqVec")
    -- **Two indices, and a recursive argument at indices of its own**: @eIf@'s
    -- premise is a @Step t1 t1'@ while the conclusion is at
    -- @ifthen t1 t2 t3@, so the motive in the method is applied to the
    -- premise's indices and not the conclusion's.
  , testCase "Step's tuple, two indices and a recursive premise" $
      certified eqStep "BelowStep"
  , testCase "and its relations" (certified eqStep "NotBelowEqStep")
    -- A dependent /index/ telescope, which is what makes the chain want a
    -- @DPair@: @Below@'s second index has the first in its type.
  , testCase "a dependent index telescope" (certified preludeBelowEnv "BelowBelow")
  , testCase "and its relations, where the index travels with the element" $
      certified preludeBelowEnv "NotBelowEqBelow"
  ]

certified :: GlobalEnv -> String -> Assertion
certified env g = case lookupDefinition (GlobalName g) env of
  Nothing -> assertFailure (g ++ " was not generated")
  Just d  -> case certify env (definitionBody d) (definitionType d) of
    Right _ -> pure ()
    Left e  -> assertFailure ("the kernel refused " ++ g ++ ": " ++ show e)

-- --------------------------------------------------------------------------
-- The precondition
-- --------------------------------------------------------------------------

-- | A datatype with a dependent index telescope, with the whole prelude behind
-- it — @Below@'s second index is a @Fin@ of its first.
preludeBelowEnv :: GlobalEnv
preludeBelowEnv = fst (declared (preludeDecls ++ [natDecl, finDecl, belowDecl]))

belowDecl :: String
belowDecl =
  "Below : \8704 (n : Nat) (i : Fin n) -> Type\8320 \
  \where { bz : \8704 (m : Nat) -> Below (succ m) (fz m) }"

-- | Every constructor has an argument, so no-confusion wants no @Unit@; @leaf@
-- has no /recursive/ argument, so the tuple does.
treeDecl :: String
treeDecl =
  "Tree : Type\8320 \
  \where { leaf : Nat -> Tree ; node : Tree -> Tree -> Tree }"

-- | @Eq@, @DPair@, @Empty@ and @And@ — the prelude without @Unit@.
noUnitEnv :: GlobalEnv
noUnitEnv = fst (declared [eqDecl, dpairDecl, emptyDecl, andDecl, natDecl, treeDecl])

has :: GlobalEnv -> String -> Bool
has env g = lookupDefinition (GlobalName g) env /= Nothing

guardTests :: [TestTree]
guardTests =
  [ -- **This is the hazard, asserted.** A missing @Unit@ is a reason this
    -- bundle declines and not a reason the no-confusion lemma does, and the two
    -- preconditions are separate so that it stays that way. Folding them
    -- together is what made a fixture without @DPair@ report
    -- @NoConfusionBelow was not generated@ at MS9 phase 218.
    testCase "no Unit: the tuple is declined" $
      has noUnitEnv "BelowTree" @?= False
  , testCase "and the no-confusion lemma is still there" $
      has noUnitEnv "noConfusionTree" @?= True
  , testCase "with Unit, both are" $
      has (fst (declared (preludeDecls ++ [natDecl, treeDecl]))) "BelowTree" @?= True
  , -- @Eq@ stands first in the prelude, so nothing its tuple would be written
    -- out of is in scope yet. Silent, like every other missing-prelude case.
    testCase "Eq's own: declined, because nothing is declared before it" $
      has eqNat "BelowEq" @?= False
  , testCase "but its no-confusion lemma is generated" $
      has eqNat "noConfusionEq" @?= True
  , -- One namespace, shared with generated names (§3.6).
    testCase "a user definition of the tuple's name refuses the declaration" $
      refuses "BelowN"
        [ "module Clash where"
        , ""
        , "BelowN : Unit"
        , "BelowN = unit"
        , ""
        , "data N : Type\8320 where"
        , "  z : N"
        , "  s : N -> N"
        ]
  ]

-- | Load a surface module and insist it did /not/ go in, __naming the reason__:
-- a refusal that happened to come from somewhere else would otherwise pass.
refuses :: String -> [String] -> Assertion
refuses blamed ls = do
  (s0, _) <- startingSession
  case loadProofSource s0 (unlines ls) of
    (_, ProofLoaded {}) -> assertFailure "the module loaded, and it should not have"
    (s1, other)
      | any (blamed `isInfixOf`) (renderResponse s1 other) -> pure ()
      | otherwise -> assertFailure
          ("refused, but not over " ++ blamed ++ ": " ++ unwords (renderResponse s1 other))
