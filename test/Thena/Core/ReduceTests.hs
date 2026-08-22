-- | Reduction (§5.1): β, the three forms of δ, ν, and ι.
--
-- Fixtures are declared through 'parseDeclaration' and terms through
-- 'parseCore', exactly as a user would type them — including @elim@\'s new
-- syntax (§2.6, phase 7), so a mistake in its grammar or its resolver-side
-- arity check shows up here rather than only in a hand-built 'Eliminate'.
module Thena.Core.ReduceTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Context (Context, Entry (..))
import Thena.Core.Reduce (whnf)
import Thena.Core.Term (Core (..), GlobalName (..), Ident (..), Var, fresh)
import Thena.Driver (SyntaxError, parseCore, parseDeclaration)
import Thena.Global.Declare (declare)
import Thena.Global.Env (Definition (..), GlobalEnv, addDefinition, emptyGlobals)

tests :: TestTree
tests =
  testGroup
    "Thena.Core.Reduce"
    [ testGroup "beta and delta" betaDeltaTests
    , testGroup "delta waits for a former wrapper to saturate" delayedDeltaTests
    , testGroup "nu (waste disposal)" nuTests
    , testGroup "iota — Nat" iotaNatTests
    , testGroup "iota — an indexed family carries its OWN index" iotaVecTests
    , testGroup "iota refuses an unsaturated target" iotaSaturationTests
    , testGroup "whnf leaves neutral terms alone" neutralTests
    , testGroup "elim's arity is checked at resolve time" elimShapeTests
    ]

-- --------------------------------------------------------------------------
-- Fixtures
-- --------------------------------------------------------------------------

natDecl, vecDecl :: String
natDecl = "Nat : Type\8320 { zero : Nat ; succ : Nat -> Nat }"
vecDecl =
  "Vec (A : Type\8320) : Nat -> Type\8320 \
  \{ nil : Vec A zero \
  \; cons : forall (n : Nat) (a : A) (as : Vec A n) -> Vec A (succ n) }"

declareAll :: [String] -> Either String (GlobalEnv, Int)
declareAll = foldl one (Right (emptyGlobals, 0))
  where
    one acc src = do
      (env, n) <- acc
      (d, n1)  <- shown (parseDeclaration env n src)
      shown (declare env n1 d)
    shown :: Show e => Either e a -> Either String a
    shown = either (Left . show) Right

declared :: [String] -> (GlobalEnv, Int)
declared srcs = case declareAll srcs of
  Left e  -> error ("fixture refused: " ++ e)
  Right r -> r

nat, natVec :: GlobalEnv
nat    = fst (declared [natDecl])
natVec = fst (declared [natDecl, vecDecl])

natVecCounter :: Int
natVecCounter = snd (declared [natDecl, vecDecl])

named :: String -> GlobalName
named = GlobalName

-- | One 'Hypothesis' with a made-up type, and the counter after it. Reduction
-- never looks at a hypothesis's type — only "Thena.Core.Typing" will, from
-- phase 8 — so any closed type is fine; 'Nat' is picked only because it is
-- always in scope in this file.
--
-- Every call chain in this file starts from 'natVecCounter', never from 0 —
-- 'term' always resolves against 'natVec', whose declarations mint their OWN
-- formal variables internally (a constructor argument's telescope, an arrow's
-- unnamed domain), and those numbers are not reserved. A hand-built context
-- starting back at 0 can collide with one of them by pure coincidence and
-- silently substitute the wrong occurrence — which is exactly what the first
-- draft of the Vec test below did, and it took a hand-traced substitution to
-- see: the fold applied a correction to a use of @A@ that only looked like a
-- use of @n@.
hyp :: Int -> String -> (Var, Entry, Int)
hyp n name =
  let (v, n1) = fresh n
   in (v, Hypothesis v (Ident name) (Global (named "Nat")), n1)

-- | Read a term against 'natVec' and its counter, in the given context.
-- Failing to parse is a fixture bug, not a test result: it errors loudly
-- rather than quietly turning into an unrelated assertion failure.
term :: Context -> String -> Core
term ctx src = case parseCore natVec ctx natVecCounter src of
  Left e       -> error ("fixture term does not resolve: " ++ show e)
  Right (t, _) -> t

-- --------------------------------------------------------------------------
-- Beta and delta
-- --------------------------------------------------------------------------

betaDeltaTests :: [TestTree]
betaDeltaTests =
  [ testCase "beta then delta: applying identity to zero gives zero" $
      whnf nat [] (term [] "(\\ (x : Nat) -> x) zero")
        @?= Canonical (named "zero") []
  , testCase "delta on a Global former with no arguments" $
      whnf nat [] (term [] "Nat") @?= Canonical (named "Nat") []
  , testCase "delta on a Free variable bound to a Definition" $
      let (v, _) = fresh 0
          ctx    = [Definition v (Ident "x") (term [] "zero") (Global (named "Nat"))]
       in whnf nat ctx (Free v) @?= Canonical (named "zero") []
  , testCase "a Free variable bound to a Hypothesis is already neutral" $
      let (v, e, _) = hyp natVecCounter "h"
       in whnf nat [e] (Free v) @?= Free v
  , testCase "a global absent from the environment stays neutral" $
      whnf emptyGlobals [] (Global (named "nowhere")) @?= Global (named "nowhere")
  ]

-- --------------------------------------------------------------------------
-- delta waits for a former wrapper to saturate (decided 2026-08-22)
-- --------------------------------------------------------------------------

-- | Under-applied former wrappers stay put; saturated ones unfold as before.
--
-- The point is not cosmetic. Before this, @cons A@ whnf'd to a three-binder
-- lambda wrapping a 'Canonical' — strictly bigger, and exposing nothing: no ι
-- can fire on an under-applied former, because an ι target is a value of the
-- datatype and so is saturated by construction.
delayedDeltaTests :: [TestTree]
delayedDeltaTests =
  [ testCase "a constructor given none of its arguments is already whnf" $
      whnf natVec [] (term [] "cons") @?= Global (named "cons")
  , testCase "given some but not all, still whnf, and the spine is untouched" $
      whnf natVec [] (term [] "cons Nat")
        @?= App (Global (named "cons")) (Global (named "Nat"))
  , testCase "a type former is counted over parameters AND indices" $
      -- Vec has one of each, so `Vec Nat` is one short.
      whnf natVec [] (term [] "Vec Nat")
        @?= App (Global (named "Vec")) (Global (named "Nat"))
  , testCase "a nullary former is saturated at once and does unfold" $
      whnf natVec [] (term [] "Nat") @?= Canonical (named "Nat") []
  , testCase "saturated, it unfolds and the Canonical appears" $
      whnf natVec [] (term [] "succ zero")
        @?= Canonical (named "succ") [Global (named "zero")]
  , testCase "an ordinary definition is not a former and unfolds regardless" $
      -- The `Nothing` branch of 'formerArity'. Nothing in MS1 builds one of
      -- these yet — proved theorems arrive at phase 13, the prelude at 11 —
      -- so it is added by hand rather than left uncovered.
      let env = addDefinition (named "twice")
                  (MkDefinition (term [] "Nat -> Nat") (term [] "\\ (k : Nat) -> k"))
                  natVec
       in whnf env [] (Global (named "twice")) @?= term [] "\\ (k : Nat) -> k"
  ]

-- --------------------------------------------------------------------------
-- nu — waste disposal
-- --------------------------------------------------------------------------

nuTests :: [TestTree]
nuTests =
  [ testCase "a let whose bound name is used substitutes it" $
      whnf nat [] (term [] "let y = zero : Nat in y") @?= Canonical (named "zero") []
  , testCase "a let whose bound name is unused leaves no residue" $
      -- Same result with or without the (unused) let: nothing about @y@
      -- survives, so there is no leftover binding for ν to dispose of on its
      -- own — 'instantiate' already erased it.
      whnf nat [] (term [] "let y = zero : Nat in Nat") @?= whnf nat [] (term [] "Nat")
  ]

-- --------------------------------------------------------------------------
-- iota — Nat, the simple non-dependent case
-- --------------------------------------------------------------------------

iotaNatTests :: [TestTree]
iotaNatTests =
  [ testCase "eliminating zero gives the zero method" $
      elimNat "zero" @?= Free mz
  , testCase "eliminating (succ zero) gives the succ method, applied" $
      -- The recursive call's target is 'zero' AS WRITTEN, not reduced to a
      -- 'Canonical': whnf never reduces an argument position, only the head
      -- spine, and 'zero' sits inside 'succ'\'s one argument.
      elimNat "(succ zero)"
        @?= App (App (Free ms) (Global (named "zero")))
                (Eliminate (named "Nat") [] (Free p) [Free mz, Free ms] []
                  (Global (named "zero")))
  ]
  where
    (p, ep, n0)   = hyp natVecCounter "P"
    (mz, emz, n1) = hyp n0 "mz"
    (ms, ems, _)  = hyp n1 "ms"
    ctx           = [ep, emz, ems]

    elimNat target = whnf nat ctx (term ctx ("elim Nat () P (mz ms) () " ++ target))

-- --------------------------------------------------------------------------
-- iota — Vec, a dependent family
-- --------------------------------------------------------------------------

-- | The load-bearing case: eliminating @cons n0 a0 as0@ at the outer index
-- @succ n0@ must recurse on @as0@ at index @n0@ — its OWN index — not at the
-- outer elimination's @succ n0@. Getting 'Thena.Core.Reduce.recursiveCalls'\'
-- substitution wrong (using the outer index, or forgetting to substitute the
-- parameter at all) would still pass every 'Nat' test above.
iotaVecTests :: [TestTree]
iotaVecTests =
  [ testCase "the recursive call carries the recursive argument's own index" $
      whnf natVec ctx (term ctx elimCons)
        @?= App
              (App (App (App (Free ccons) (Free n0)) (Free a0)) (Free as0))
              (Eliminate (named "Vec") [Free vA] (Free pm) [Free cnil, Free ccons]
                [Free n0] (Free as0))
  ]
  where
    (vA, evA, n0c)   = hyp natVecCounter "A"
    (n0, en0, n1c)   = hyp n0c "n0"
    (a0, ea0, n2c)   = hyp n1c "a0"
    (as0, eas0, n3c) = hyp n2c "as0"
    (pm, epm, n4c)   = hyp n3c "Pm"
    (cnil, ecnil, n5c) = hyp n4c "cnil"
    (ccons, eccons, _) = hyp n5c "ccons"

    ctx = [evA, en0, ea0, eas0, epm, ecnil, eccons]

    elimCons = "elim Vec (A) Pm (cnil ccons) ((succ n0)) (cons A n0 a0 as0)"

-- --------------------------------------------------------------------------
-- iota refuses an unsaturated target
-- --------------------------------------------------------------------------

-- | §12 invariant 6 makes a saturated 'Canonical' an invariant, and nothing a
-- user can type breaks it — the resolver never builds one and every generated
-- wrapper is saturated. But 'iota' claims to be total on arbitrary input, and
-- without the check it does not fail to reduce, it returns a **wrong** reduct:
-- the method applied to whatever arguments happen to be present.
--
-- Built by hand for exactly that reason: this is the shape no parse can
-- produce, which is why it needs a test rather than a transcript. Phase 9's
-- unifier and phase 12's kernel both construct 'Core' programmatically.
iotaSaturationTests :: [TestTree]
iotaSaturationTests =
  [ testCase "too few arguments: stuck, not the method on its own" $
      whnf nat ctx (elimAt (Canonical (named "succ") [])) @?= elimAt (Canonical (named "succ") [])
  , testCase "too many arguments: stuck, not the method over-applied" $
      whnf nat ctx (elimAt (Canonical (named "zero") [Free mz, Free mz]))
        @?= elimAt (Canonical (named "zero") [Free mz, Free mz])
  , testCase "and the correctly saturated target still fires" $
      whnf nat ctx (elimAt (Canonical (named "zero") [])) @?= Free mz
  ]
  where
    (p, ep, n0)   = hyp natVecCounter "P"
    (mz, emz, n1) = hyp n0 "mz"
    (ms, ems, _)  = hyp n1 "ms"
    ctx           = [ep, emz, ems]

    elimAt = Eliminate (named "Nat") [] (Free p) [Free mz, Free ms] []

-- --------------------------------------------------------------------------
-- Neutral terms
-- --------------------------------------------------------------------------

neutralTests :: [TestTree]
neutralTests =
  [ testCase "a Pi is already whnf" $
      whnf nat [] (term [] "forall (x : Nat) -> Nat") @?= term [] "forall (x : Nat) -> Nat"
  , testCase "a lambda is already whnf" $
      whnf nat [] (term [] "\\ (x : Nat) -> x") @?= term [] "\\ (x : Nat) -> x"
  , testCase "an application whose function is stuck stays stuck" $
      let (f, ef, _) = hyp natVecCounter "f"
       in whnf nat [ef] (App (Free f) (term [] "zero")) @?= App (Free f) (term [] "zero")
  , testCase "eliminating a stuck target stays stuck, but the target is whnf'd" $
      let (h, eh, n0)     = hyp natVecCounter "h"
          (p, ep, n1)      = hyp n0 "P"
          (mz, emz, n2)    = hyp n1 "mz"
          (ms, ems, _)     = hyp n2 "ms"
          ctx              = [eh, ep, emz, ems]
       in whnf nat ctx (term ctx "elim Nat () P (mz ms) () h")
            @?= Eliminate (named "Nat") [] (Free p) [Free mz, Free ms] [] (Free h)
  ]

-- --------------------------------------------------------------------------
-- elim's arity is checked at resolve time
-- --------------------------------------------------------------------------

elimShapeTests :: [TestTree]
elimShapeTests =
  [ refused "wrong number of methods" "elim Nat () P (mz) () zero"
  , refused "wrong number of parameters"
      "elim Vec (A A) Pm (cnil ccons) ((succ n0)) (cons A n0 a0 as0)"
  , refused "wrong number of indices"
      "elim Vec (A) Pm (cnil ccons) (succ n0 n0) (cons A n0 a0 as0)"
  , refused "not a declared datatype at all" "elim NotADatatype () P () () zero"
  ]
  where
    (_, evA, n0c)     = hyp natVecCounter "A"
    (_, en0, n1c)     = hyp n0c "n0"
    (_, ea0, n2c)     = hyp n1c "a0"
    (_, eas0, n3c)    = hyp n2c "as0"
    (_, epm, n4c)     = hyp n3c "Pm"
    (_, ecnil, n5c)   = hyp n4c "cnil"
    (_, eccons, n6c)  = hyp n5c "ccons"
    (_, ep, n7c)      = hyp n6c "P"
    (_, emz, _)       = hyp n7c "mz"

    ctx = [evA, en0, ea0, eas0, epm, ecnil, eccons, ep, emz]

    refused :: String -> String -> TestTree
    refused label src = testCase label $
      case parseCore natVec ctx natVecCounter src of
        Left (_ :: SyntaxError) -> pure ()
        Right (r, _)            -> assertFailure ("resolved when it should not have: " ++ show r)
