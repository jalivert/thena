-- | The kernel, extraction, and state validity (§5.3, thesis §2.3).
--
-- Three things that only look alike:
--
--   * 'certify' takes a closed pure term and its stated type. It shares the
--     core's typechecker (decided 2026-08-22), so what is tested here is not
--     typing — 'Thena.Core.TypingTests' does that — but the two checks the
--     kernel adds on top: closedness, and that the /stated/ type is the one
--     checked against rather than the one inferred.
--   * 'extract' reads the closed term off a finished construction.
--   * 'revalidate' walks a whole development, holes and all.
--
-- **The invalid developments here are hand-built and cannot be typed at the
-- REPL**, which is the point: every command builds a valid state by
-- construction, so 'revalidate' can only be tested by breaking one on purpose.
-- That is the standing lesson's shape — the invariant is checked by different
-- code from the code that maintains it.
module Thena.KernelTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertFailure, testCase, (@?=))

import Thena.Core.Level (LevelVar (..), Level (..), Unmet (..), levelOfNat)
import Thena.Core.Term
  ( Core (..)
  , Ident (..)
  , close
  , fresh
  )
import Thena.Declared (natVec, natVecCounter)
import Thena.Driver (parseCore)
import Thena.Development.Component (Component (..))
import Thena.Development.Partial (Constraint (..), Impure (..), Partial (..), extract)
import Thena.Development.Validate (revalidate)
import Thena.Errors (KernelError (..), Position (..), TypeError (..))
import Thena.Fixtures (idMidway, withConstraint)
import Thena.Kernel (certify)

tests :: TestTree
tests =
  testGroup
    "the kernel and state validity (§5.3)"
    [ testGroup "certify" certifyTests
    , testGroup "extract — the term a finished construction stands for" extractTests
    , testGroup "revalidate — thesis §2.3" validTests
    ]

-- --------------------------------------------------------------------------
-- certify
-- --------------------------------------------------------------------------

certifyTests :: [TestTree]
certifyTests =
  [ testCase "a closed term at its type is accepted" $
      -- **@Right@ carries the level solutions the check forced and the residue
      -- it could not decide** (phases 33 and 33b), and nothing here writes a
      -- bare @Type@, so both are empty almost everywhere in this module.
      certify natVec (nat "succ zero") (nat "Nat") @?= Right ([], [])

  , testCase "and under binders too, where the context reappears" $
      certify natVec
        (nat "\\ (n : Nat) -> succ n")
        (nat "Nat -> Nat")
        @?= Right ([], [])

    -- The check §5.3's context-free signature earns. @infer@ would report this
    -- as an unknown variable, which is true and says nothing about whose
    -- mistake it is: the caller's, for not abstracting it.
  , testCase "an open term is refused before typing is attempted" $
      certify natVec (Free loose) (nat "Nat") @?= Left (NotClosed loose)

  , testCase "an open stated type is refused too" $
      certify natVec (nat "zero") (Free loose) @?= Left (NotClosed loose)

    -- What makes the stated type load-bearing: the term has *a* type, and it
    -- is not this one. A kernel that inferred instead of checking would pass.
  , testCase "a well-typed term at the wrong stated type is refused" $
      case certify natVec (nat "zero") (nat "Nat -> Nat") of
        Left (Ill TheTerm (NotOfType {})) -> pure ()
        other -> assertFailure ("expected a mismatch at the term: " ++ show other)

  , testCase "and an ill-typed term is refused, with the core's own reason" $
      case certify natVec (nat "zero zero") (nat "Nat") of
        Left (Ill TheTerm _) -> pure ()
        other -> assertFailure ("expected an ill-typed term: " ++ show other)

    -- ------------------------------------------------------------------
    -- Levels (MS3 phase 33)
    -- ------------------------------------------------------------------

    -- 'closed' one sort down. A definition is about to be stored under this
    -- term, and a meta in it says nothing about which universe it is in.
    -- Phase 33b generalises rather than refusing; until then the recovery is to
    -- write the level.
    -- Stated at exactly the type it has, so every relation the check meets is
    -- between the meta and itself and nothing is owed. **A term with an unknown
    -- level in it is accepted** — phase 33 refused it here, and 33b generalises
    -- it instead, which is the caller's job and not the kernel's.
  , testCase "a level nothing pinned down is accepted, for generalising" $
      certify natVec (Universe (LVar undetermined))
                     (Universe (LSuc (LVar undetermined)))
        @?= Right ([], [])

    -- The obligation @suc ?m <= 1@ leaves one value, so the kernel takes it and
    -- hands it back for the caller to write into the development.
  , testCase "and one the obligations leave no choice about is solved" $
      certify natVec (Universe (LVar undetermined)) (nat "Type\8321")
        @?= Right ([(undetermined, levelOfNat 0)], [])

    -- Reported as the false relation it is, rather than as an unknown level:
    -- the meta is the symptom and the inequality is the cause.
  , testCase "a relation no level satisfies is reported as that" $
      case certify natVec
             (App (Lam (Ident "x") (Universe (LVar undetermined))
                       (close bound (Free bound)))
                  (Universe (levelOfNat 0)))
             (nat "Type\8320") of
        Left (Levels (Refuted _ _)) -> pure ()
        other -> assertFailure ("expected a refuted level: " ++ show other)
  ]
  where
    (loose, n1)         = fresh natVecCounter
    (bound, _)          = fresh n1
    undetermined        = LMeta 900

-- --------------------------------------------------------------------------
-- extract
-- --------------------------------------------------------------------------

extractTests :: [TestTree]
extractTests =
  [ testCase "a trailing term is itself" $
      extract (Trailing (nat "zero")) @?= Right (nat "zero")

    -- Thesis §2.3: assume is a λ, and a local definition — what solve leaves
    -- behind — is a let.
  , testCase "an assumption becomes a lambda" $
      extract (Under (Assume x (Ident "x") (nat "Nat")) (Trailing (Free x)))
        @?= Right (Lam (Ident "x") (nat "Nat") (close x (Free x)))

  , testCase "a definition becomes a let" $
      extract (Under (Define x (Ident "x") (nat "zero") (nat "Nat")) (Trailing (Free x)))
        @?= Right (Let (Ident "x") (nat "zero") (nat "Nat") (close x (Free x)))

  , testCase "and they nest, outermost first" $
      extract
        (Under (Assume x (Ident "x") (nat "Nat"))
          (Under (Define y (Ident "y") (Free x) (nat "Nat"))
            (Trailing (Free y))))
        @?= Right
              (Lam (Ident "x") (nat "Nat")
                (close x (Let (Ident "y") (Free x) (nat "Nat") (close y (Free y)))))

    -- The purity check *is* this traversal, so each impure form has to stop it
    -- and say which one it was.
  , testCase "a hole stops it, and names itself" $
      extract (Under (Claim x (Ident "h") (nat "Nat")) (Trailing (Free x)))
        @?= Left (StillAHole x (Ident "h"))

  , testCase "a guess stops it: tried is not solved" $
      extract (Under (Guess x (Ident "g") (Trailing (nat "zero")) (nat "Nat")) (Trailing (Free x)))
        @?= Left (StillAGuess x (Ident "g"))

    -- Not 'withConstraint' from "Thena.Fixtures": that one has a hole above its
    -- constraint, so it stops on the hole first — which is right, and is why
    -- this case needs a chain whose only impurity is the constraint.
  , testCase "an undischarged constraint stops it" $
      case extract (Pending (Equate [] (nat "zero") (nat "zero") (nat "Nat"))
                     (Trailing (nat "zero"))) of
        Left (StillConstrained _) -> pure ()
        other -> assertFailure ("expected a parked constraint: " ++ show other)

    -- The result of a successful extraction need not be closed: saying so is
    -- 'certify''s job, and this is the seam between the two.
  , testCase "extraction does not close: a stray free variable survives it" $
      extract (Trailing (Free x)) @?= Right (Free x)
  ]
  where
    (x, n1) = fresh natVecCounter
    (y, _)  = fresh n1

-- --------------------------------------------------------------------------
-- revalidate
-- --------------------------------------------------------------------------

validTests :: [TestTree]
validTests =
  [ testCase "a development with holes is a valid state" $
      valid (Under (Claim x (Ident "h") (nat "Nat")) (Trailing (Free x)))

  , testCase "and one with a guess in it" $ valid idMidway

  , testCase "and one carrying an undischarged constraint" $ valid withConstraint

    -- Nothing written down says what the top-level trailing term should be, so
    -- nothing is claimed about it (phase 5's expectedType, restated).
  , testCase "the top-level trailing term is not checked against anything" $
      valid (Trailing (nat "zero"))

  , testCase "a component's type must be a type" $
      invalid
        (Under (Claim x (Ident "h") (nat "zero")) (Trailing (Free x)))
        (TypeOf x (Ident "h"))

  , testCase "a definition's value must have its stated type" $
      invalid
        (Under (Define x (Ident "d") (nat "zero") (nat "Nat -> Nat")) (Trailing (Free x)))
        (ValueOf x (Ident "d"))

    -- A guess's body is a development in its own right, and its trailing term
    -- must build the guess's type. Its failures nest rather than flatten.
  , testCase "a guess whose body does not build its type is caught, inside it" $
      invalid
        (Under (Guess x (Ident "g") (Trailing (nat "zero")) (nat "Nat -> Nat"))
          (Trailing (Free x)))
        (Inside x (Ident "g") TheTerm)

    -- Only an assumption consumes the guess's type (thesis §2.3), so the
    -- running example above is valid *because* its λ eats the A -> A. Abstract
    -- once more than the type allows and there is no binder left.
  , testCase "a guess body may not abstract more than its type allows" $
      case fst (revalidate natVec [] n2
                  (Under (Guess x (Ident "g")
                            (Under (Assume y (Ident "a") (nat "Nat")) (Trailing (nat "zero")))
                            (nat "Nat"))
                    (Trailing (Free x)))) of
        Left (Overabstracted v (Ident "a") _) -> v @?= y
        other -> assertFailure ("expected an overabstraction: " ++ show other)

    -- **A ∀-binder consumes the guess's type too, and it must be a universe**
    -- (MS4 phase 41f). Its 'peeled' case is the ∀ counterpart of the one
    -- above.
  , testCase "a ∀-binder needs a universe above it" $
      case fst (revalidate natVec [] n2
                  (Under (Guess x (Ident "g")
                            (Under (Quantify y (Ident "a") (nat "Nat")) (Trailing (nat "Nat")))
                            (nat "Nat"))
                    (Trailing (Free x)))) of
        Left (NotAUniverseAbove v (Ident "a") _) -> v @?= y
        other -> assertFailure ("expected a universe complaint: " ++ show other)

    -- **The domain is checked AT the expected universe, not merely as a type**
    -- — the line the phase's design turned on. @Π x : S . T@ inhabits
    -- @Type (ℓ_S ⊔ ℓ_T)@, so without it @∀ x : Type₁ . Type₀@ would validate
    -- at @Type₁@, which is a level too low.
  , testCase "and a domain too big for it is refused" $
      case fst (revalidate natVec [] n2
                  (Under (Guess x (Ident "g")
                            (Under (Quantify y (Ident "a") (Universe (levelOfNat 1)))
                              (Trailing (Universe (levelOfNat 0))))
                            (Universe (levelOfNat 1)))
                    (Trailing (Free x)))) of
        Left _  -> pure ()
        other -> assertFailure ("expected a refusal: " ++ show other)

  , testCase "while one that fits is valid" $
      valid (Under (Guess x (Ident "g")
                      (Under (Quantify y (Ident "a") (Universe (levelOfNat 0)))
                        (Trailing (Universe (levelOfNat 0))))
                      (Universe (levelOfNat 1)))
              (Trailing (Free x)))

  , testCase "and the running example's λ is exactly what makes it valid" $
      valid (Under (Guess x (Ident "g")
                      (Under (Assume y (Ident "a") (nat "Nat")) (Trailing (Free y)))
                      (nat "Nat -> Nat"))
              (Trailing (Free x)))

  , testCase "a constraint's two sides must have the type it is asked at" $
      invalid
        (Pending (Equate [] (nat "zero") (nat "zero") (nat "Nat -> Nat"))
          (Trailing (nat "zero")))
        (ConstraintAt 1)

    -- Γ is built as the walk goes, so a type mentioning something bound later
    -- is not in scope where it is written. This is the case a check that
    -- forgot the whole chain at once would miss.
  , testCase "a component may not mention what is bound after it" $
      case revalidate natVec [] n2 later of
        (Left (Ill (TypeOf v _) (UnknownVariable _ _)), _) -> v @?= x
        (other, _) -> assertFailure ("expected a scope error at x: " ++ show other)
  ]
  where
    (x, n1) = fresh natVecCounter
    (y, n2) = fresh n1

    -- @? x : y . λ y : Nat . x@ — x's type names y, which is bound below it.
    later =
      Under (Claim x (Ident "x") (Free y))
        (Under (Assume y (Ident "y") (nat "Nat"))
          (Trailing (Free x)))

    valid p = case fst (revalidate natVec [] n2 p) of
      Right () -> pure () :: Assertion
      Left e   -> assertFailure ("should be valid: " ++ show e)

    invalid p pos = case fst (revalidate natVec [] n2 p) of
      Left (Ill pos' _) -> pos' @?= pos
      other             -> assertFailure ("should be invalid at " ++ show pos ++ ": " ++ show other)

-- --------------------------------------------------------------------------
-- Helpers
-- --------------------------------------------------------------------------

-- | A core term over the shared @Nat@/@Vec@ environment.
nat :: String -> Core
nat src = case parse src of
  Left e       -> error ("fixture does not resolve: " ++ show e)
  Right (t, _) -> t
  where
    parse = parseCore natVec [] natVecCounter
