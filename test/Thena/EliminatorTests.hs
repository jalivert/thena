-- | The elimination rule, and @:elim@ (§3.7, thesis §4.1).
--
-- **Nothing here tests generation into the environment, because there is
-- none.** The user reversed the 2026-08-11 storage decision on 2026-08-22:
-- 'eliminatorType' is a derived function of the record, called by @infer@ at
-- the level it reads off the motive and by this command at the level it is
-- told. So what is left to check is that the derivation says what thesis §4.1
-- says, and these are exact-string pins against the thesis's own displayed
-- rules — the standing lesson's "pin a new rendering rule with exact-string
-- cases", applied to a rule nothing else in the suite reads back.
--
-- An exact string is the right shape of test *here* and would be the wrong one
-- for, say, a move: two eliminators that print identically /are/ the same rule,
-- because every binder that could differ is printed.
--
-- Well-formedness of the same types is checked in "Thena.Core.TypingTests" by
-- @infer@, and their computational behaviour in "Thena.Core.ReduceTests" by ι.
-- Three different pieces of code reading one record, which is what §3.7 buys
-- by not emitting a second encoding of it.
module Thena.EliminatorTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Level (Level (..), instantiateLevels, levelOfNat)
import Thena.Core.Term (Core, GlobalName (..), substLevelsIn)
import Thena.Declared (natFin, natFinCounter, natVec, natVecCounter)
import Thena.Global.Env
  ( GlobalEnv
  , InductiveDefinition
  , caseWrapper
  , eliminatorType
  , inductiveLevels
  , lookupInductive
  )
import Thena.Render ( Rendering (..)
  ,renderCore, renderEliminator)

tests :: TestTree
tests =
  testGroup
    "the elimination rule (§3.7, thesis §4.1)"
    [ testGroup "the generated rule, against the thesis" ruleTests
    , testGroup "the level comes from the motive" levelTests
    , testGroup "case analysis is the same rule minus the hypotheses" caseTests
    ]

-- | Each case is thesis §4.1's own displayed rule, in §2.6's concrete syntax.
--
-- The differences from the thesis's rendering are all §2.6's and none are the
-- generator's: @∀@ for the thesis's parenthesised binder, @Type₀@ for its
-- unlabelled @Type@, and the datatype's own spelling of its constructors.
ruleTests :: [TestTree]
ruleTests =
  [ -- §4.1.1's @NatElim@, its worked simple datatype.
    rule "Nat, a simple datatype (§4.1.1)" natVec natVecCounter "Nat" (LZero)
      "elim Nat : ∀ (P : Nat -> Type₀) -> P zero \
      \-> (∀ (x : Nat) -> P x -> P (succ x)) \
      \-> ∀ (target : Nat) -> P target"

    -- §4.1.2's @ListElim@ shape: the parameter is bound first and the motive
    -- mentions it without binding it. That is the whole content of "parameters
    -- are not abstracted in the scheme".
  , rule "Vec, a parameterised family (§4.1.2)" natVec natVecCounter "Vec" (LZero)
      "elim Vec : ∀ (A : Type₀) (P : ∀ (x : Nat) -> Vec A x -> Type₀) \
      \-> P zero (nil A) \
      \-> (∀ (n : Nat) (a : A) (as : Vec A n) -> P n as -> P (succ n) (cons A n a as)) \
      \-> ∀ (x : Nat) (target : Vec A x) -> P x target"

    -- §4.1.4's @FinElim@, printed there as
    --
    -- > FinElim : (P : (n : Nat) -> Fin n -> Type)
    -- >        -> ((n : Nat) -> P (S n) (fz n))
    -- >        -> ((n : Nat) -> (i : Fin n) -> P n i -> P (S n) (fs n i))
    -- >        -> (n : Nat) -> (i : Fin n) -> P n i
    --
    -- The case @Nat@ cannot catch: @fs@'s inductive hypothesis is @P n i@, at
    -- the recursive argument's /own/ index, while its conclusion is at
    -- @succ n@. An eliminator that reused the target's indices would print
    -- @P (succ n) i@ here and pass every @Nat@ test in the suite.
  , rule "Fin, an indexed family (§4.1.4)" natFin natFinCounter "Fin" (LZero)
      "elim Fin : ∀ (P : ∀ (x : Nat) -> Fin x -> Type₀) \
      \-> (∀ (n : Nat) -> P (succ n) (fz n)) \
      \-> (∀ (n : Nat) (i : Fin n) -> P n i -> P (succ n) (fs n i)) \
      \-> ∀ (x : Nat) (target : Fin x) -> P x target"

    -- No constructors, so no methods: the motive and the target and nothing
    -- between them. Every other fixture has at least one method, so this is
    -- the only case that shows the methods are a list and not a non-empty one.
  , rule "Empty, with no constructors" natFin natFinCounter "Empty" (LZero)
      "elim Empty : ∀ (P : Empty {0} -> Type₀) (target : Empty {0}) -> P target"
  ]

-- | §3.7's "universe polymorphism of the eliminator, without universe
-- polymorphism": the same datatype yields a different rule per level, and the
-- level appears in exactly one place — the motive's codomain.
levelTests :: [TestTree]
levelTests =
  [ rule "Nat at Type₁" natVec natVecCounter "Nat" (levelOfNat 1)
      "elim Nat : ∀ (P : Nat -> Type₁) -> P zero \
      \-> (∀ (x : Nat) -> P x -> P (succ x)) \
      \-> ∀ (target : Nat) -> P target"
  , rule "Vec at Type₂, and its parameter stays at Type₀" natVec natVecCounter "Vec" (levelOfNat 2)
      "elim Vec : ∀ (A : Type₀) (P : ∀ (x : Nat) -> Vec A x -> Type₂) \
      \-> P zero (nil A) \
      \-> (∀ (n : Nat) (a : A) (as : Vec A n) -> P n as -> P (succ n) (cons A n a as)) \
      \-> ∀ (x : Nat) (target : Vec A x) -> P x target"
  ]

-- | @caseD@, against the eliminator printed above it (MS9 phase 178).
--
-- __Each case here is the one above it with exactly the inductive hypotheses
-- removed__, so the two groups read as a pair: whatever else differs between a
-- method and its case method is this generator inventing something.
--
-- Nothing here checks that the body works. It is a definition, so
-- @GlobalTests@' /every definition checks against its own type/ already types it
-- over the adversarial corpus — and @test\/golden\/eliminators.golden@ computes
-- with it, which a type cannot show.
caseTests :: [TestTree]
caseTests =
  [ -- @succ@'s method loses @P x ->@ and keeps its conclusion.
    analysis "Nat: the succ method takes no hypothesis" natVec natVecCounter "Nat" LZero
      "\8704 (P : Nat -> Type\8320) -> P zero \
      \-> (\8704 (x : Nat) -> P (succ x)) \
      \-> \8704 (target : Nat) -> P target"

    -- The parameter is still bound first and the motive still mentions it.
  , analysis "Vec: the parameter and the indices are untouched" natVec natVecCounter "Vec" LZero
      "\8704 (A : Type\8320) (P : \8704 (x : Nat) -> Vec A x -> Type\8320) \
      \-> P zero (nil A) \
      \-> (\8704 (n : Nat) (a : A) (as : Vec A n) -> P (succ n) (cons A n a as)) \
      \-> \8704 (x : Nat) (target : Vec A x) -> P x target"

    -- **The case @Nat@ cannot catch, again.** @fs@'s hypothesis is at the
    -- recursive argument's own index and its conclusion is at @succ n@, so a
    -- generator that dropped the wrong binder — or dropped the conclusion's
    -- indices with it — would still pass every @Nat@ case above.
  , analysis "Fin: the hypothesis goes and the conclusion's indices stay" natFin natFinCounter "Fin" LZero
      "\8704 (P : \8704 (x : Nat) -> Fin x -> Type\8320) \
      \-> (\8704 (n : Nat) -> P (succ n) (fz n)) \
      \-> (\8704 (n : Nat) (i : Fin n) -> P (succ n) (fs n i)) \
      \-> \8704 (x : Nat) (target : Fin x) -> P x target"

    -- No constructors, so there was nothing to drop: @caseEmpty@ and
    -- @elim Empty@ are the same rule.
  , analysis "Empty: nothing to drop" natFin natFinCounter "Empty" LZero
      "\8704 (P : Empty {0} -> Type\8320) (target : Empty {0}) -> P target"
  ]

-- | Build @caseD@'s type and render it as an ordinary type, which is what
-- @:show@ prints.
analysis :: String -> GlobalEnv -> Int -> String -> Level -> String -> TestTree
analysis name env n0 d l expect = testCase name $
  case lookupInductive g env of
    Nothing  -> assertFailure (d ++ " is not declared")
    Just def ->
      let (ty, _, _) = caseWrapper def l n0
       in oneLine (renderCore (Rendering [] n0) [] (atZero def ty)) @?= expect
  where
    g = GlobalName d

-- | One line, so that an exact-string case reads as one line.
oneLine :: String -> String
oneLine = unwords . words

-- | Build the rule and render it exactly as @:elim@ does.
rule :: String -> GlobalEnv -> Int -> String -> Level -> String -> TestTree
rule name env n0 d l expect = testCase name $
  case lookupInductive g env of
    Nothing  -> assertFailure (d ++ " is not declared")
    -- **Instantiated at the datatype's own levels** (MS3 phase 31g), which is
    -- what a use site sees. Rendering it uninstantiated would pin @ℓ@'s number
    -- — a counter value, and no business of an assertion about the shape.
    Just def -> renderEliminator (Rendering [] n0) g (atZero def (fst (eliminatorType def l n0))) @?= [expect]
  where
    g = GlobalName d

-- | A datatype's own level parameters, all instantiated at zero.
atZero :: InductiveDefinition -> Core -> Core
atZero d t = case instantiateLevels (inductiveLevels d) (map (const LZero) (inductiveLevels d)) of
  Just sub -> substLevelsIn sub t
  Nothing  -> t
