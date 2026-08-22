-- | The generated @NoConfusion@ family and @noConfusion@ lemma (§3.7 items 3
-- and 4, phase 14).
--
-- Three groups do the real work, and each is the standing lesson from phases
-- 2–5 — look for the invariant checked by different code from the code that
-- maintains it:
--
--   * 'caseTests' reduces the family and pins the result as an exact string.
--     "Thena.Global.NoConfusion" only ever /typed/ what it built, through
--     @check@; whether it computes the right case is decided by ι in
--     "Thena.Core.Reduce", which shares no code with the generator. A family
--     that put @Empty@ on the diagonal would still typecheck.
--   * 'useTests' does what phase 17's elimination tactic will do: apply the
--     lemma to a real equation and use what comes back. That runs the family,
--     the lemma, ι, β and conversion together, against a goal written by hand.
--   * 'kernelTests' re-checks both definitions with 'Thena.Kernel.certify' —
--     §9's deliverable, and the strongest available statement of §3.7's "these
--     are checked by the normal checker like anything else".
--
-- 'skipTests' pins the MS1 limits (decided by the user 2026-08-22): a datatype
-- whose constructor telescope is dependent, or that is not at @Type₀@, gets no
-- no-confusion at all rather than a lemma that says less than its name.
module Thena.NoConfusionTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertFailure, testCase, (@?=))

import Thena.Core.Context (Context, Entry (..))
import Thena.Core.Reduce (whnf)
import Thena.Core.Term (Core, GlobalName (..), Ident (..), Level (..), fresh)
import Thena.Core.Typing (check)
import Thena.Declared
  ( declared
  , eqDecl
  , eqNat
  , eqNatCounter
  , eqTapl
  , eqTaplCounter
  , finDecl
  , natDecl
  , vecDecl
  )
import Thena.Driver (parseCore, parseDeclaration)
import Thena.Global.Declare (DeclareError (..), declare)
import Thena.Global.Env (GlobalEnv, definitionBody, definitionType, lookupDefinition)
import Thena.Global.NoConfusion (Skipped (..))
import Thena.Kernel (certify)
import Thena.Repl (renderCore)

tests :: TestTree
tests =
  testGroup
    "Thena.Global.NoConfusion"
    [ testGroup "the family computes the right case" caseTests
    , testGroup "the lemma is usable, which is the point of it" useTests
    , testGroup "the kernel accepts what was generated" kernelTests
    , testGroup "what gets none, and why" skipTests
    , testGroup "one namespace, shared with generated names" clashTests
    ]

-- --------------------------------------------------------------------------
-- Fixtures
-- --------------------------------------------------------------------------

termIn :: GlobalEnv -> Int -> Context -> String -> Core
termIn env n ctx src = case parseCore env ctx n src of
  Left e       -> error ("fixture term does not resolve: " ++ show e)
  Right (t, _) -> t

-- | Reduce a term of the family to weak head normal form and render it.
reduces :: GlobalEnv -> Int -> String -> String -> Assertion
reduces env n src expect =
  renderCore n [] (whnf env [] (termIn env n [] src)) @?= expect

natReduces, taplReduces :: String -> String -> Assertion
natReduces  = reduces eqNat eqNatCounter
taplReduces = reduces eqTapl eqTaplCounter

-- --------------------------------------------------------------------------
-- The cases
-- --------------------------------------------------------------------------

-- | Exact strings, not a shape match: what is being pinned here is /which/
-- case came out, and the four cases of @Nat@ are four different Π-types that
-- no shape assertion would distinguish more clearly than the text does.
--
-- Every case is CPS, including the two that §3.7 wrote as @Unit@ and @Empty@.
-- With no cumulativity (§5.2) a @Type₀@ case cannot sit in a family whose
-- multi-argument case is @(C : Type₀) -> … -> C@, which is at @Type₁@.
caseTests :: [TestTree]
caseTests =
  [ testCase "same nullary former — no equations to give" $
      natReduces "NoConfusionNat zero zero" "∀ (C : Type₀) -> C -> C"
  , testCase "different formers — the Church-encoded empty type" $
      natReduces "NoConfusionNat zero (succ zero)" "∀ (C : Type₀) -> C"
  , testCase "and the other way round" $
      natReduces "NoConfusionNat (succ zero) zero" "∀ (C : Type₀) -> C"
  , testCase "same former, one argument — injectivity" $
      natReduces
        "NoConfusionNat (succ zero) (succ (succ zero))"
        "∀ (C : Type₀) -> (Eq Nat zero (succ zero) -> C) -> C"
  , -- The case §3.7 is written around, and the only one in any fixture with
    -- more than one equation to conjoin.
    testCase "three arguments — three equations, in argument order" $
      taplReduces
        "NoConfusionTerm (ifthen true zero (succ zero)) (ifthen false zero zero)"
        "∀ (C : Type₀) -> (Eq Term true false -> Eq Term zero zero \
        \-> Eq Term (succ zero) zero -> C) -> C"
  , testCase "the family's own type" $
      typeOfGlobal eqTapl eqTaplCounter "NoConfusionTerm"
        @?= Just "Term -> Term -> Type₁"
  , testCase "the lemma's own type" $
      typeOfGlobal eqTapl eqTaplCounter "noConfusionTerm"
        @?= Just "∀ (x : Term) (y : Term) -> Eq Term x y -> NoConfusionTerm x y"
  ]

typeOfGlobal :: GlobalEnv -> Int -> String -> Maybe String
typeOfGlobal env n g =
  renderCore n [] . definitionType <$> lookupDefinition (GlobalName g) env

-- --------------------------------------------------------------------------
-- Using it
-- --------------------------------------------------------------------------

-- | @x : Term, y : Term, e : Eq Term (succ x) (succ y)@ — a context shaped like
-- the one a method of an elimination at specific indices is handed.
withEquation :: String -> (Context, Int)
withEquation eq = ([Hypothesis vx (Ident "x") tm, Hypothesis vy (Ident "y") tm, hyp], n3)
  where
    (vx, n1) = fresh eqTaplCounter
    (vy, n2) = fresh n1
    (ve, n3) = fresh n2
    tm       = termIn eqTapl eqTaplCounter [] "Term"
    prefix   = [Hypothesis vx (Ident "x") tm, Hypothesis vy (Ident "y") tm]
    hyp      = Hypothesis ve (Ident "e") (termIn eqTapl n3 prefix eq)

-- | Does this term have this type, in that context?
provesIn :: String -> String -> String -> Assertion
provesIn eq src ty =
  case fst (check eqTapl ctx n (termIn eqTapl n ctx src) (termIn eqTapl n ctx ty)) of
    Right () -> pure ()
    Left e   -> assertFailure ("rejected: " ++ show e)
  where (ctx, n) = withEquation eq

useTests :: [TestTree]
useTests =
  [ -- Injectivity: from @succ x ≡ succ y@ get @x ≡ y@. This is what a matching
    -- branch needs, and the continuation is how it is taken.
    testCase "injectivity, taken through the continuation" $
      provesIn
        "Eq Term (succ x) (succ y)"
        "noConfusionTerm (succ x) (succ y) e (Eq Term x y) (\\ (q : Eq Term x y) -> q)"
        "Eq Term x y"
  , -- Discrimination: from @true ≡ succ x@ get anything. This is what an
    -- impossible branch needs, and it closes in one application because the
    -- case is already the Church-encoded empty type.
    testCase "discrimination closes an impossible branch" $
      provesIn
        "Eq Term true (succ x)"
        "noConfusionTerm true (succ x) e (Eq Term x y)"
        "Eq Term x y"
  , -- Three equations arrive in argument order and each is usable on its own.
    testCase "the second of three equations" $
      provesIn
        "Eq Term (ifthen true x zero) (ifthen false y zero)"
        "noConfusionTerm (ifthen true x zero) (ifthen false y zero) e (Eq Term x y) \
        \(\\ (q1 : Eq Term true false) (q2 : Eq Term x y) (q3 : Eq Term zero zero) -> q2)"
        "Eq Term x y"
  ]

-- --------------------------------------------------------------------------
-- The kernel
-- --------------------------------------------------------------------------

-- | §9's deliverable: @certify@ accepts what was generated.
--
-- Both definitions are closed, which is what lets the kernel take them at all
-- (§5.3) — and it is a fact about the generator, since a stray 'Free' left
-- unabstracted would be the natural mistake to make in a term this size.
kernelTests :: [TestTree]
kernelTests =
  [ testCase "Nat's family" (certified eqNat "NoConfusionNat")
  , testCase "Nat's lemma" (certified eqNat "noConfusionNat")
  , testCase "Term's family" (certified eqTapl "NoConfusionTerm")
  , testCase "Term's lemma" (certified eqTapl "noConfusionTerm")
  , testCase "Eq's own, which is an indexed family" (certified eqNat "noConfusionEq")
  ]

certified :: GlobalEnv -> String -> Assertion
certified env g = case lookupDefinition (GlobalName g) env of
  Nothing -> assertFailure (g ++ " was not generated")
  Just d  -> case certify env (definitionBody d) (definitionType d) of
    Right ()             -> pure ()
    Left e   -> assertFailure ("the kernel refused " ++ g ++ ": " ++ show e)

-- --------------------------------------------------------------------------
-- What gets none
-- --------------------------------------------------------------------------

-- | Declare one datatype into an environment and keep what no-confusion did.
skipped :: [String] -> String -> Either DeclareError (Maybe Skipped)
skipped before src = case parseDeclaration env n src of
  Left e       -> error ("fixture does not parse: " ++ show e)
  Right (d, n1) -> (\(_, _, s) -> s) <$> declare env n1 d
  where (env, n) = declared before

skipTests :: [TestTree]
skipTests =
  [ -- The MS1 limit. @cons@ wants @Eq (Vec A n) as as'@ while @as' : Vec A n'@,
    -- and a transported chain of equations is the way out — not MS1's.
    testCase "Vec: cons's telescope is dependent" $
      skipped [eqDecl, natDecl] vecDecl
        @?= Right (Just (DependentArguments (GlobalName "cons") (Ident "as")))
  , testCase "Fin: so is fs's" $
      skipped [eqDecl, natDecl] finDecl
        @?= Right (Just (DependentArguments (GlobalName "fs") (Ident "i")))
  , -- Eq relates only Type₀ types, so nothing above it can have an equation.
    testCase "a datatype above Type₀" $
      skipped [eqDecl] "Big : Type\8321 { wrap : Type\8320 -> Big }"
        @?= Right (Just (NotAtTypeZero (Level 1)))
  , -- Silent, and it has to be: this is the state every prelude-free golden
    -- transcript declares its datatypes in, and a note on every @data@ line
    -- would be noise about the environment rather than about the declaration.
    testCase "no Eq in scope at all — skipped, and quietly" $
      skipped [] natDecl @?= Right Nothing
  , testCase "and then nothing was generated" $
      lookupDefinition (GlobalName "NoConfusionNat") (fst (declared [natDecl]))
        `seq` (lookupDefinition (GlobalName "NoConfusionNat") (fst (declared [natDecl])) == Nothing)
        @?= True
  , testCase "but with Eq it was" $
      (lookupDefinition (GlobalName "NoConfusionNat") eqNat == Nothing) @?= False
  ]

-- --------------------------------------------------------------------------
-- Names
-- --------------------------------------------------------------------------

-- | §3.6: one namespace, shared with generated names. A user who takes the name
-- first loses the declaration that would generate it, rather than either of the
-- two being hidden.
clashTests :: [TestTree]
clashTests =
  [ testCase "the family's name taken" $
      skipped [eqDecl, "NoConfusionNat : Type\8320 { }"] natDecl
        @?= Left (AlreadyDeclared (GlobalName "NoConfusionNat"))
  , testCase "the lemma's name taken" $
      skipped [eqDecl, "noConfusionNat : Type\8320 { }"] natDecl
        @?= Left (AlreadyDeclared (GlobalName "noConfusionNat"))
  ]
