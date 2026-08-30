-- | Typing (§5.2, §7.4): @infer@, @check@, and the elimination rule.
--
-- Two of these groups do the real work, and both are the standing lesson from
-- phases 2–5 — look for the invariant that is checked by different code from
-- the code that maintains it:
--
--   * 'eliminatorTypeTests' type-checks 'eliminatorType''s /output/. Nothing in
--     @infer@ knows how that type was built, so a dropped binder, a parameter
--     abstracted in the wrong place or an inductive hypothesis at the wrong
--     indices stops being a well-formed type and is caught here — where the
--     elimination tests would happily agree with the same mistake twice.
--   * 'subjectReductionTests' types a term, reduces it with ι, and types the
--     reduct. ι lives in "Thena.Core.Reduce" and computes recursive /calls/;
--     the method types live in "Thena.Global.Env" and compute inductive
--     /hypotheses/. If those two ever disagreed about which arguments are
--     recursive, a datatype would reduce by a rule its own eliminator is not
--     typed for, and only a test that runs both catches it.
module Thena.Core.TypingTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertFailure, testCase, (@?=))

import Thena.Core.Level
  ( Level (..)
  , LevelVar (..)
  , Obligation (..)
  , levelOfNat
  )
import Thena.Core.Context (Context, Entry (..))
import Thena.Core.Convert (convert)
import Thena.Core.Reduce (whnf)
import Thena.Core.Term (Core (..), GlobalName (..), Ident (..), close, fresh)
import Thena.Core.Typing (check, infer)
import Thena.Declared (natFin, natFinCounter, natVec, natVecCounter)
import Thena.Driver (parseCore)
import Thena.Errors (TypeError (..))
import Thena.Global.Env
  ( Definition (..)
  , addDefinition
  , eliminatorType
  , lookupInductive
  )

tests :: TestTree
tests =
  testGroup
    "Thena.Core.Typing"
    [ testGroup "the ordinary forms" formTests
    , testGroup "universes: max, and cumulativity" universeTests
    , testGroup "formers and their wrappers" formerTests
    , testGroup "elimination" elimTests
    , testGroup "the generated eliminator type is itself a type" eliminatorTypeTests
    , testGroup "typing and iota agree — subject reduction" subjectReductionTests
    , testGroup "an elimination may return a function" recursiveFunctionTests
    , testGroup "check is infer then convert" checkTests
    , testGroup "what goes wrong" errorTests
    , testGroup "the counter comes back" counterTests
    , testGroup "a use owes its definition's level constraints" schemeTests
    ]

-- | Addition, defined by recursion on the first argument — the motive is
-- valued in @Nat -> Nat@, so the elimination's own type is a Π.
--
-- **A phase-8 bug, found while planning phase 14.** @spine@ refused any walk
-- that ended on a Π, on the grounds that both 'Canonical' and 'Eliminate' are
-- saturated by construction (§12 invariant 6). That is right for a 'Canonical',
-- whose stored type ends at the datatype or a universe. For an 'Eliminate'
-- every field group /is/ supplied and the residue is @P indices target@, which
-- is whatever the motive says — so this, the ordinary way to define a function
-- by recursion, was rejected as "Nat is not given enough arguments".
--
-- Typed and then reduced, because the two are different code: a residue check
-- that let the term through while ι mishandled it would pass the first half.
recursiveFunctionTests :: [TestTree]
recursiveFunctionTests =
  [ testCase "add has a function type" $
      hasType add "Nat -> Nat"
  , testCase "applied, it has the element type" $
      hasType ("(" ++ add ++ ") (succ zero)") "Nat"
  , testCase "and it computes: 1 + 1 = 2" $
      case convert natVec [] natVecCounter
             (term ("(" ++ add ++ ") (succ zero)"))
             (term "succ (succ zero)") of
        (Nothing,  _, _) -> pure ()
        (Just why, _, _) -> assertFailure ("does not converge: " ++ show why)
  ]
  where
    add =
      "elim Nat () (\\ (t : Nat) -> Nat -> Nat) \
      \((\\ (m : Nat) -> m) (\\ (k : Nat) (ih : Nat -> Nat) (m : Nat) -> succ (ih m))) \
      \() (succ zero)"

-- --------------------------------------------------------------------------
-- Fixtures
-- --------------------------------------------------------------------------

termAt :: Int -> Context -> String -> Core
termAt n ctx src = case parseCore natVec ctx n src of
  Left e       -> error ("fixture term does not resolve: " ++ show e)
  Right (t, _) -> t

term :: String -> Core
term = termAt natVecCounter []

-- | The typing entry points return their level obligations as well (MS3 phase
-- 33). Nothing here builds a level meta, so the list is always empty and these
-- two say so once instead of at every call.
verdict :: (a, b, c) -> a
verdict (r, _, _) = r

counter :: (a, b, Int) -> Int
counter (_, _, n) = n

-- | The inferred type of a closed term.
typeOf :: String -> Either TypeError Core
typeOf src = verdict (infer natVec [] natVecCounter (term src))

-- | @t@ has a type convertible with @ty@. A shape match, not a rendered-string
-- one: two different types can legally print the same way, and an inferred type
-- is not reduced, so @(λ _ -> Nat) zero@ is the right answer where @Nat@ is the
-- one a string test would have demanded.
hasType :: String -> String -> Assertion
hasType src ty = case verdict (check natVec [] natVecCounter (term src) (term ty)) of
  Right () -> pure ()
  Left e   -> assertFailure (show e)

illTyped :: String -> Assertion
illTyped src = case typeOf src of
  Left _  -> pure ()
  Right t -> assertFailure ("expected a type error, got the type " ++ show t)

named :: String -> GlobalName
named = GlobalName

-- --------------------------------------------------------------------------

formTests :: [TestTree]
formTests =
  [ testCase "a universe is one universe up" $
      typeOf "Type\8320" @?= Right (Universe (levelOfNat 1))
  , testCase "a variable takes its type from the context" $
      let (v, n) = fresh natVecCounter
          ctx    = [Hypothesis v (Ident "x") (Global (named "Nat") [])]
       in verdict (infer natVec ctx n (Free v)) @?= Right (Global (named "Nat") [])
  , testCase "a lambda gets a Pi over its own domain" $
      hasType "\\ (x : Nat) -> x" "Nat -> Nat"
  , testCase "a dependent lambda too" $
      hasType "\\ (A : Type\8320) (x : A) -> x" "\8704 (A : Type\8320) -> A -> A"
  , testCase "an application instantiates the codomain" $
      hasType "(\\ (A : Type\8320) -> \\ (x : A) -> x) Nat" "Nat -> Nat"
  , testCase "a let substitutes its value back into the body's type" $
      -- The body's type mentions the bound name, so a checker that returned it
      -- unsubstituted would produce a type with a loose variable in it.
      hasType "let n = zero : Nat in nil Nat" "Vec Nat zero"
  , testCase "a let's value is checked against its stated type" $
      illTyped "let n = nil Nat : Nat in n"
  ]

universeTests :: [TestTree]
universeTests =
  [ testCase "a Pi lands at the larger of its two levels" $
      typeOf "\8704 (A : Type\8320) -> A" @?= Right (Universe (levelOfNat 1))
  , testCase "the domain can be the larger one" $
      typeOf "Type\8321 -> Type\8320" @?= Right (Universe (levelOfNat 2))
    -- **Cumulativity, from MS3 phase 32.** This case asserted the opposite
    -- until then — @Nat@ at @Type₁@ was the recorded proof that there was no
    -- subsumption. It is the one behaviour the phase changes.
  , testCase "cumulativity: a Type0 term checks at Type1" $
      hasType "Nat" "Type\8321"
  , testCase "and at Type2, and at its own level" $ do
      hasType "Nat" "Type\8322"
      hasType "Nat" "Type\8320"
    -- It lifts and never lowers.
  , testCase "but Type1 does not check at Type0" $
      illTyped' "Type\8320" "Type\8320"
  ]
  where
    illTyped' src ty = case verdict (check natVec [] natVecCounter (term src) (term ty)) of
      Left _   -> pure ()
      Right () -> assertFailure "expected the universes not to match"

formerTests :: [TestTree]
formerTests =
  [ testCase "a wrapper has the type its declaration gives it" $
      hasType "succ" "Nat -> Nat"
  , testCase "a parametrised constructor's wrapper abstracts the parameters" $
      hasType "cons" "\8704 (A : Type\8320) (n : Nat) -> A -> Vec A n -> Vec A (succ n)"
  , testCase "a type former's wrapper too" $
      hasType "Vec" "Type\8320 -> Nat -> Type\8320"
  , testCase "a partially applied wrapper is fine, and keeps the rest of the Pi" $
      hasType "cons Nat" "\8704 (n : Nat) -> Nat -> Vec Nat n -> Vec Nat (succ n)"
  , testCase "a saturated application lands in the family at the right index" $
      hasType "cons Nat zero zero (nil Nat)" "Vec Nat (succ zero)"
  , testCase "a constructor given the wrong argument type is rejected" $
      illTyped "cons Nat zero (nil Nat) (nil Nat)"
  ]

elimTests :: [TestTree]
elimTests =
  [ testCase "eliminating Nat into Nat" $
      hasType
        "elim Nat () (\\ (_ : Nat) -> Nat) \
        \(zero (\\ (x : Nat) (ih : Nat) -> succ ih)) () (succ zero)"
        "(\\ (_ : Nat) -> Nat) (succ zero)"
  , testCase "the successor method must take its inductive hypothesis" $
      illTyped
        "elim Nat () (\\ (_ : Nat) -> Nat) (zero succ) () (succ zero)"
  , testCase "eliminating an indexed family, parameters and indices in place" $
      hasType
        "elim Vec (Nat) (\\ (n : Nat) (v : Vec Nat n) -> Nat) \
        \(zero (\\ (n : Nat) (a : Nat) (as : Vec Nat n) (ih : Nat) -> succ ih)) \
        \(zero) (nil Nat)"
        "(\\ (n : Nat) (v : Vec Nat n) -> Nat) zero (nil Nat)"
  , testCase "the inductive hypothesis is at the argument's OWN index" $
      -- @ih@ must be @P n as@, never @P (succ n) (cons …)@. Giving it the
      -- family itself instead of the motive applied is the mistake this catches.
      illTyped
        "elim Vec (Nat) (\\ (n : Nat) (v : Vec Nat n) -> Nat) \
        \(zero (\\ (n : Nat) (a : Nat) (as : Vec Nat n) (ih : Vec Nat n) -> zero)) \
        \(zero) (nil Nat)"
  , testCase "large elimination: the level is read from the motive (§3.7)" $
      -- The motive is valued in Type0, so this elimination lives at Type1, and
      -- the system has no universe polymorphism to get there with.
      hasType
        "elim Nat () (\\ (_ : Nat) -> Type\8320) \
        \(Nat (\\ (x : Nat) (ih : Type\8320) -> ih)) () zero"
        "(\\ (_ : Nat) -> Type\8320) zero"
  , testCase "the indices must match the target's own — the field's first real use" $
      -- @Eliminate@\'s 'indices' field was carried, counted and printed by
      -- phases 6 and 7 and never read for its meaning (@AGENDA.md@ Part 3). It
      -- is read here: the trailing binders of the eliminator's type are
      -- @forall indices (t : D params indices)@, so supplying the indices is
      -- what fixes the type the target is checked against.
      illTyped
        "elim Vec (Nat) (\\ (n : Nat) (v : Vec Nat n) -> Nat) \
        \(zero (\\ (n : Nat) (a : Nat) (as : Vec Nat n) (ih : Nat) -> succ ih)) \
        \((succ zero)) (nil Nat)"
  , testCase "a motive that does not end in a universe is refused" $
      illTyped "elim Nat () zero (zero succ) () zero"
  , testCase "a motive of the wrong arity is refused" $
      illTyped
        "elim Vec (Nat) (\\ (v : Vec Nat zero) -> Nat) (zero zero) (zero) (nil Nat)"
  ]

-- | Type-check what 'eliminatorType' builds. See the module header: @infer@
-- knows nothing about how that type was constructed, so this is an independent
-- check on the construction.
eliminatorTypeTests :: [TestTree]
eliminatorTypeTests =
  [ testCase "Nat's eliminator type, at Type0" $ wellFormed natVec natVecCounter "Nat" (LZero)
  , testCase "Nat's eliminator type, at Type1" $ wellFormed natVec natVecCounter "Nat" (levelOfNat 1)
  , testCase "Vec's eliminator type, at Type0" $ wellFormed natVec natVecCounter "Vec" (LZero)
  , testCase "Vec's eliminator type, at Type2" $ wellFormed natVec natVecCounter "Vec" (levelOfNat 2)
    -- Phase 10's two: an indexed family with no parameter, whose method
    -- conclusions are at constructor-supplied indices, and a family with no
    -- methods at all.
  , testCase "Fin's eliminator type, at Type0" $ wellFormed natFin natFinCounter "Fin" (LZero)
  , testCase "Fin's eliminator type, at Type1" $ wellFormed natFin natFinCounter "Fin" (levelOfNat 1)
  , testCase "Empty's eliminator type, at Type0" $ wellFormed natFin natFinCounter "Empty" (LZero)
  ]
  where
    wellFormed env n0 d l = case lookupInductive (named d) env of
      Nothing  -> assertFailure (d ++ " is not declared")
      Just def ->
        let (ty, n) = eliminatorType def l n0
         in case verdict (infer env [] n ty) of
              Right (Universe _) -> pure ()
              Right other        -> assertFailure ("not a type: " ++ show other)
              Left e             -> assertFailure (show e)

-- | Type a term, reduce it, type the reduct, and require the two types to
-- agree. See the module header for why this is the test that would catch ι and
-- the method types drifting apart.
subjectReductionTests :: [TestTree]
subjectReductionTests =
  [ testCase "Nat, at the zero method" $ preserved
      "elim Nat () (\\ (_ : Nat) -> Nat) \
      \(zero (\\ (x : Nat) (ih : Nat) -> succ ih)) () zero"
  , testCase "Nat, at the successor method, so the recursive call is made" $ preserved
      "elim Nat () (\\ (_ : Nat) -> Nat) \
      \(zero (\\ (x : Nat) (ih : Nat) -> succ ih)) () (succ (succ zero))"
  , testCase "Vec, at nil" $ preserved
      "elim Vec (Nat) (\\ (n : Nat) (v : Vec Nat n) -> Nat) \
      \(zero (\\ (n : Nat) (a : Nat) (as : Vec Nat n) (ih : Nat) -> succ ih)) \
      \(zero) (nil Nat)"
  , testCase "Vec, at cons, where the recursive call carries its own index" $ preserved
      "elim Vec (Nat) (\\ (n : Nat) (v : Vec Nat n) -> Nat) \
      \(zero (\\ (n : Nat) (a : Nat) (as : Vec Nat n) (ih : Nat) -> succ ih)) \
      \((succ zero)) (cons Nat zero zero (nil Nat))"
  , testCase "a beta redex, for the same reason" $ preserved
      "(\\ (A : Type\8320) (x : A) -> x) Nat zero"
  ]
  where
    preserved src =
      let t = term src
       in case verdict (infer natVec [] natVecCounter t) of
            Left e   -> assertFailure ("the term does not type: " ++ show e)
            Right ty ->
              let u = whnf natVec [] t
               in case verdict (infer natVec [] natVecCounter u) of
                    Left e    -> assertFailure ("the reduct does not type: " ++ show e)
                    Right ty' -> case verdict (convert natVec [] natVecCounter ty ty') of
                      Nothing  -> pure ()
                      Just why -> assertFailure ("the types differ: " ++ show why)

checkTests :: [TestTree]
checkTests =
  [ testCase "check accepts a type only convertible with the inferred one" $
      -- @(λ _ -> Nat) zero@ is not the inferred type syntactically; it reduces
      -- to it. If @check@ were comparing with 'Eq' this would fail.
      hasType "zero" "(\\ (_ : Type\8320) -> Nat) Nat"
  , testCase "check reports the conversion's own reason" $
      case verdict (check natVec [] natVecCounter (term "zero") (term "Type\8320")) of
        Left (NotOfType _ _ _ _ _) -> pure ()
        other                      -> assertFailure (show other)
  ]

errorTests :: [TestTree]
errorTests =
  [ testCase "a variable that is not in the context" $
      let (v, n) = fresh natVecCounter
       in case verdict (infer natVec [] n (Free v)) of
            Left (UnknownVariable _ _) -> pure ()
            other                      -> assertFailure (show other)
  , testCase "a global that is not declared" $
      verdict (infer natVec [] natVecCounter (Global (named "nowhere") []))
        @?= Left (UnknownGlobal (named "nowhere"))
  , testCase "applying something that is not a function" $
      case typeOf "zero zero" of
        Left (NotAFunction _ _ _) -> pure ()
        other                     -> assertFailure (show other)
  , testCase "a binder whose domain is not a type" $
      case typeOf "\\ (x : zero) -> x" of
        Left (NotAType _ _ _) -> pure ()
        other                 -> assertFailure (show other)
  , testCase "an unsaturated Canonical, which only a hand-built term can be" $
      case verdict (infer natVec [] natVecCounter (Canonical (named "succ") [] [])) of
        Left (Unsaturated _ _) -> pure ()
        other                  -> assertFailure (show other)
  , testCase "an over-applied Canonical" $
      case verdict (infer natVec [] natVecCounter
                  (Canonical (named "zero") [] [Canonical (named "zero") [] []])) of
        Left (OverApplied _) -> pure ()
        other                -> assertFailure (show other)
  , testCase "a loose de Bruijn index reaching the checker" $
      verdict (infer natVec [] natVecCounter (Bound 0)) @?= Left (LooseIndex 0)
  ]

counterTests :: [TestTree]
counterTests =
  [ testCase "inferring under a binder advances it" $
      (counter (infer natVec [] 100 (termAt 100 [] "\\ (x : Nat) -> x")) > 100) @?= True
  , testCase "it advances on the failing branch too" $
      (counter (infer natVec [] 100 (termAt 100 [] "\\ (x : Nat) -> zero zero")) > 100) @?= True
  ]

-- --------------------------------------------------------------------------
-- Scheme constraints at a use site (MS3 phase 33b)
-- --------------------------------------------------------------------------

-- | @discussion\/level-binders-and-constraints.md@ §4's call site, in one
-- module: the level arguments are in the **term** and the constraint list is in
-- the **environment**, and @infer@ puts them together.
--
-- **This is the soundness argument, not a convenience.** A constraint arising
-- from a subsumption inside a body is invisible in that body's type —
-- @Type ℓ0 -> Type ℓ1@ is well formed for any pair — so a badly instantiated
-- call would check on its type alone. Nothing else can regenerate it, because
-- checking a @Global@ never looks at the body.
schemeTests :: [TestTree]
schemeTests =
  [ testCase "a use instantiates the constraint at the levels it wrote" $
      owed (infer withScheme [] 800 (lift [levelOfNat 1, levelOfNat 0]))
        @?= [AtMost (levelOfNat 1) (levelOfNat 0)]

  , -- The obligation is **owed**, not decided: @infer@ never refuses one, and
    -- the pass at @qed@ is what turns this into an error.
    testCase "and it is owed rather than refused" $
      verdict (infer withScheme [] 800 (lift [levelOfNat 1, levelOfNat 0]))
        @?= Right (arrow (levelOfNat 1) (levelOfNat 0))

  , testCase "a good instantiation owes one that discharges" $
      owed (infer withScheme [] 800 (lift [levelOfNat 0, levelOfNat 1]))
        @?= [AtMost (levelOfNat 0) (levelOfNat 1)]

  , testCase "a definition with no constraints owes nothing" $
      owed (infer natVec [] natVecCounter (Global (named "succ") [])) @?= []
  ]
  where
    owed (_, o, _) = o

    l0 = LVar (LRigid 700)
    l1 = LVar (LRigid 701)

    lift ls = Global (named "lift") ls

    -- @lift {ℓ0 ℓ1} : Type ℓ0 -> Type ℓ1@, with @ℓ0 ≤ ℓ1@ — the shape
    -- @∀ (A : Type) -> Type@ generalises to, built here rather than proved
    -- because this module has no REPL.
    withScheme =
      addDefinition (named "lift")
        (MkDefinition [LRigid 700, LRigid 701] [AtMost l0 l1]
           (arrow l0 l1)
           (Lam (Ident "A") (Universe l0) (close (fst (fresh 990)) (Universe l0))))
        natVec

    arrow a b = Pi (Ident "_") (Universe a) (close (fst (fresh 991)) (Universe b))
