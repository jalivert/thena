-- | The global environment, and @data@ (§3.3.1, §3.7).
--
-- The two tests that do the work are 'agreesWithTheResolver' and
-- 'roundTripTests', and both are shaped by the standing lesson from phases 2–5:
-- look for the invariant that is checked by different code from the code that
-- maintains it.
--
--   * A former's stored type is built by "Thena.Global.Env" from a record whose
--     telescopes "Thena.Syntax.Resolve" split apart. Written out in full and
--     resolved as an ordinary term, it must come back identical. Nothing in the
--     splitting path is shared with the ordinary path, so a lost binder, a
--     reordered telescope or a parameter dropped from a target all show up.
--   * A declaration printed and read back must mean the same thing — compared
--     as /terms/, not as text, because two declarations can legally print the
--     same way and still differ in what they bind.
module Thena.GlobalTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertFailure, testCase, (@?=))

import Thena.Core.Level
  ( Level (..)
  , LevelVar (..)
  , Obligation (..)
  , levelOfNat
  )
import Thena.Core.Term
  ( Core (..)
  , GlobalName (..)
  , Ident (..)
  , beyond
  , close
  , fresh
  , open
  )
import Data.List (isPrefixOf)

import Thena.Core.Typing (check, infer)
import Thena.Driver
  ( Response (..)
  , Stop (..)
  , Session (..)
  , command
  , parseCore
  , parseDeclaration
  )
import Thena.Engine (Machine (..))
import Thena.Errors (TypeError (..))
import Thena.Global.Declare (DeclareError (..), declare)
import Thena.Global.Env
  ( Definition (..)
  , GlobalEnv
  , InductiveDefinition (..)
  , constructorArguments
  , constructorName
  , constructorType
  , emptyGlobals
  , formerType
  , inductiveConstructors
  , inductiveIndices
  , inductiveLevels
  , inductiveName
  , inductiveParameters
  , inductives
  , constants
  , definitions
  , definitionType
  , definitionBody
  , eliminatorType
  , varsInEnv
  , isDeclared
  , constantType
  , lookupConstant
  , lookupDefinition
  , lookupInductive
  , generalised
  )
import Thena.Repl (renderEliminator, renderInductive, startingSession)

tests :: TestTree
tests =
  testGroup
    "Thena.Global"
    [ testGroup "what a declaration writes" tablesTests
    , testGroup "the generated wrappers" wrapperTests
    , testGroup "generation agrees with the ordinary resolver" agreesWithTheResolver
    , testGroup "strict positivity" positivityTests
    , testGroup "universes (thesis §4.1.1, back-filled at phase 8)" universeTests
    , testGroup "names" nameTests
    , testGroup "printed and read back" roundTripTests
    , testGroup "generalisation turns a proof into a scheme" generaliseTests
    , equipment
    ]

-- --------------------------------------------------------------------------
-- Everything a declaration generates is well typed (2026-09-13)
-- --------------------------------------------------------------------------

-- | **Type-check the whole global environment, over an adversarial corpus.**
--
-- @TypingTests@' @eliminatorTypeTests@ types 'eliminatorType''s output for two
-- fixtures, and its header says why that is the shape to want: nothing in
-- @infer@ knows how the type was built, so a dropped binder or a parameter
-- abstracted in the wrong place stops being a well-formed type. This does the
-- same for **everything** a declaration writes — the former, every constructor
-- wrapper, the eliminator's type and its wrapper, and both no-confusion
-- globals — over datatypes chosen to have the properties the fixtures do not
-- combine.
--
-- **Why an adversarial corpus and not the prelude's**: every historical
-- soundness bug in this project was in generated equipment, and each was found
-- by a datatype that combined two things no fixture combined — a
-- level-polymorphic /recursive/ datatype (MS3 phase 33c), parameters /and/
-- indices through the surface (MS4 phase 54), an eliminated datatype with level
-- parameters (MS4 phase 49e). Phase 54's lesson was the sharpest: every elim
-- test used a constant motive, so a real bug survived a
-- behaviour-preserved check.
--
-- The corpus is declared through the REPL, which is the path a user takes and
-- the one that assembles the record the generators read.
equipment :: TestTree
equipment =
  testGroup
    "everything a declaration generates type checks"
    [ testCase "the corpus declares" $ do
        (_, problems) <- corpus
        problems @?= []
    , testCase "every constant's type is a type" $ do
        (env, _) <- corpus
        badConstants env @?= []
    , testCase "every definition checks against its own type" $ do
        (env, _) <- corpus
        badDefinitions env @?= []
      -- The one @TypingTests@ already does for two fixtures, over the corpus.
    , testCase "every eliminator's generated type is a type" $ do
        (env, _) <- corpus
        badEliminators env @?= []

      -- **And the two printers with no reader finish on all of it.**
      -- @renderInductive@ and @renderEliminator@ are display forms — nothing
      -- reads one back — so what is checkable is totality, over datatypes
      -- awkward enough to reach a case a fixture would not.
    , testCase "every declaration and every eliminator prints" $ do
        (env, _) <- corpus
        let printed =
              [ length l
              | (_, d) <- inductives env
              , l <- renderInductive 0 d
              ]
                ++ [ length l
                   | (g, d) <- inductives env
                   , l <- renderEliminator 0 g (fst (eliminatorType d LZero (pastEverything env)))
                   ]
        (sum printed >= 0) @?= True
    ]
  where
    fst3 (a, _, _) = a

    badConstants env =
      [ (g, e)
      | (g, c) <- constants env
      , Left e <- [fst3 (infer env [] (pastEverything env) (constantType c))]
      ]

    badDefinitions env =
      [ (g, e)
      | (g, d) <- definitions env
      , Left e <- [fst3 (check env [] (pastEverything env) (definitionBody d) (definitionType d))]
      ]

    -- At two motive levels, because §3.7's universe trick is one rule per
    -- universe the motive is valued in and a level argument dropped from the
    -- datatype's own reference shows up at one and not the other (MS4 phase
    -- 49e's live defect was exactly that).
    badEliminators env =
      [ (g, l, e)
      | (g, d) <- inductives env
      , l <- [LZero, levelOfNat 1]
      , let (ty, _) = eliminatorType d l (pastEverything env)
      , Left e <- [fst3 (infer env [] (pastEverything env) ty)]
      ]

-- | Past every variable the environment holds.
--
-- **@certify@'s own lesson** (MS3): the global environment is inside the trust
-- boundary and holds 'Thena.Core.Term.Var's minted at declaration time, so a
-- checker started from zero captures one. @Thena.Kernel@ says
-- @beyond (varsInEnv env)@ for exactly this reason and so does this.
pastEverything :: GlobalEnv -> Int
pastEverything = beyond . varsInEnv

-- | The corpus, declared through the REPL, and whatever it complained about.
corpus :: IO (GlobalEnv, [String])
corpus = do
  (s0, problems) <- startingSession
  let (s, said) = foldl' one (s0, []) corpusLines
  pure (globals (sessionMachine s), problems ++ said)
  where
    one (s, acc) l = case command s l of
      (s', Ran out Completed) -> (s', acc ++ [ o | o <- out, not (expected o) ])
      (s', r)                 -> (s', acc ++ [l ++ " => " ++ show r])

    -- A skipped no-confusion table is a stated limitation, not a failure to
    -- declare: three of the corpus's datatypes have a dependent telescope on
    -- purpose, which is what @Skipped@ is for.
    expected o = "no noConfusion" `isPrefixOf` o || "declared " `isPrefixOf` o

corpusLines :: [String]
corpusLines =
  [ "data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
    -- Parameters AND two indices AND recursion AND a level parameter, in one
    -- datatype, with a constructor of five arguments. Nothing in the fixtures
    -- combines more than two of those.
  , "data Chain (A : Type) : A -> A -> Type where \
    \{ link : \8704 (x : A) -> Chain A x x \
    \; hop : \8704 (x : A) (y : A) (z : A) -> Chain A x y -> Chain A y z -> Chain A x z }"
    -- A parameterised datatype with NO constructors: the eliminator's method
    -- telescope is empty and the motive still has to be abstracted correctly.
  , "data Void2 (A : Type) : Type where { }"
    -- An index whose type is another datatype, applied to its level argument.
  , "data Wrap (A : Type) : Type where { wrap : A -> Wrap A }"
  , "data Uses : Wrap {0} Nat -> Type\8320 where \
    \{ uses : \8704 (w : Wrap {0} Nat) -> Uses w }"
    -- A family whose index telescope is dependent, which is where the
    -- eliminator's index generalisation is hardest.
  , "data Fin : Nat -> Type\8320 where \
    \{ fz : \8704 (n : Nat) -> Fin (succ n) \
    \; fs : \8704 (n : Nat) (i : Fin n) -> Fin (succ n) }"
    -- A datatype above Type\8320, whose constructor argument lives below it —
    -- cumulativity is what makes its equations conjoinable (MS3 §2 item 2).
  , "data Box1 : Type\8321 where { box1 : \8704 (A : Type\8320) -> A -> Box1 }"
  ]

-- --------------------------------------------------------------------------
-- Fixtures
-- --------------------------------------------------------------------------

-- What is typed after the command word: the driver splits @data@ off the line
-- before the lexer sees anything (§2.4).
natDecl, vecDecl, emptyDecl :: String
natDecl   = "Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
vecDecl   =
  "Vec (A : Type\8320) : Nat -> Type\8320 \
  \where { nil : Vec A zero \
  \; cons : forall (n : Nat) (a : A) (as : Vec A n) -> Vec A (succ n) }"
emptyDecl = "Empty : Type\8320 where { }"

-- | Phase 50 wants a level-polymorphic global in scope whose level arguments a
-- constructor argument can be written at — 'Nat' and 'Vec' have none.
eqDecl :: String
eqDecl = "Eq (A : Type) : A -> A -> Type where { refl : \8704 (a : A) -> Eq A a a }"

-- | Declare in order, against the empty environment, threading the counter.
-- Either the reason it was refused, or the environment and the counter.
declareAll :: [String] -> Either String (GlobalEnv, Int)
declareAll = foldl one (Right (emptyGlobals, 0))
  where
    one acc src = do
      (env, n)  <- acc
      (d, n1)      <- shown (parseDeclaration env n src)
      (env', n2, _) <- shown (declare env n1 d)
      Right (env', n2)

    shown :: Show e => Either e a -> Either String a
    shown = either (Left . show) Right

-- | The environment after a run of declarations that must all be admitted,
-- and the counter it left behind.
--
-- The counter matters: rendering mints display variables, and a printer given a
-- counter below the term's highest 'Thena.Core.Term.Var' makes a colliding name
-- (phase 3's §7). Every fixture below carries its counter for that reason.
after :: [String] -> (GlobalEnv, Int)
after srcs = case declareAll srcs of
  Left e  -> error ("fixture refused: " ++ e)
  Right r -> r

nat, natVec :: GlobalEnv
nat    = fst (after [natDecl])
natVec = fst (after [natDecl, vecDecl])

natVecCounter :: Int
natVecCounter = snd (after [natDecl, vecDecl])

named :: String -> GlobalName
named = GlobalName

-- --------------------------------------------------------------------------
-- What a declaration writes
-- --------------------------------------------------------------------------

tablesTests :: [TestTree]
tablesTests =
  [ testCase "the datatype has a record" $
      fmap inductiveName (lookupInductive (named "Nat") nat) @?= Just (named "Nat")
  , testCase "the type former is a constant at its declared universe" $
      fmap constantType (lookupConstant (named "Nat") nat) @?= Just (Universe LZero)
  , testCase "a former is in two tables under one name (§3.3.1)" $
      sequence_
        [ fmap constantType (lookupConstant (named g) natVec)
            @?= fmap definitionType (lookupDefinition (named g) natVec)
        | g <- ["Nat", "zero", "succ", "Vec", "nil", "cons"]
        ]
  , testCase "a datatype with no constructors is a datatype" $
      fmap (length . inductiveConstructors)
           (lookupInductive (named "Empty") (fst (after [emptyDecl])))
        @?= Just 0
  , testCase "the parameters and the indices are told apart" $
      fmap (\d -> (length (inductiveParameters d), length (inductiveIndices d)))
           (lookupInductive (named "Vec") natVec)
        @?= Just (1, 1)
  , testCase "an index is not a parameter of the record it is declared with" $
      fmap (\d -> (length (inductiveParameters d), length (inductiveIndices d)))
           (lookupInductive (named "Nat") natVec)
        @?= Just (0, 0)
  ]

-- --------------------------------------------------------------------------
-- The generated wrappers (§3.7 item 2)
-- --------------------------------------------------------------------------

wrapperTests :: [TestTree]
wrapperTests =
  [ testCase "a nullary former's wrapper is the bare Canonical" $
      fmap definitionBody (lookupDefinition (named "zero") nat)
        @?= Just (Canonical (named "zero") [] [])
  , testCase "a unary former's wrapper abstracts and applies" $
      fmap definitionBody (lookupDefinition (named "succ") nat)
        @?= Just (Lam (Ident "n") natTy (close v (Canonical (named "succ") [] [Free v])))
  , testCase "the type former gets a wrapper too" $
      fmap definitionBody (lookupDefinition (named "Nat") nat)
        @?= Just (Canonical (named "Nat") [] [])
  , testCase "every wrapper body is a saturated Canonical (§12 invariant 6)" $
      sequence_ (map saturated (formerNames natVec))
  ]
  where
    natTy   = Global (named "Nat") []
    (v, _)  = fresh 0

    -- Peel the wrapper's λs, counting them, and check the body applies the
    -- former to exactly that many arguments. Under-application is what
    -- invariant 6 forbids, and it is the one thing generation could get wrong
    -- without any type error.
    saturated :: (GlobalName, Int) -> Assertion
    saturated (g, arity) = case fmap definitionBody (lookupDefinition g natVec) of
      Just b  -> peel 0 b
      Nothing -> assertFailure (show g ++ " has no wrapper")
      where
        peel k t = case t of
          Lam _ _ sc -> peel (k + 1) (open v sc)
          Canonical f _ as
            | f == g && length as == k && k == arity -> pure ()
          _ -> assertFailure (show g ++ ": wrapper body is " ++ show t)

-- | Every former the fixtures declare, with the number of arguments its
-- 'Canonical' must carry: the parameters plus its own.
formerNames :: GlobalEnv -> [(GlobalName, Int)]
formerNames env =
  concat
    [ (inductiveName d, length (inductiveParameters d) + length (inductiveIndices d))
        : [ ( constructorName c
            , length (inductiveParameters d) + length (constructorArguments c)
            )
          | c <- inductiveConstructors d
          ]
    | (_, d) <- inductives env
    ]

-- --------------------------------------------------------------------------
-- Generation agrees with the ordinary resolver
-- --------------------------------------------------------------------------

-- | The stored type of every former, against the same type written out and
-- read as an ordinary term.
--
-- The two are built by disjoint code. The left-hand side went through
-- 'Thena.Syntax.Resolve.resolveData', which splits a constructor's type into a
-- telescope and a target and throws the parameters away, and then through
-- 'Thena.Global.Env.constructorType', which puts them back. The right-hand side
-- is one call to the term resolver on a Π-chain.
agreesWithTheResolver :: [TestTree]
agreesWithTheResolver =
  [ testCase name $ case parseCore natVec [] 0 written of
      Left e  -> assertFailure (show e)
      Right (t, _) -> fmap constantType (lookupConstant (named name) natVec) @?= Just t
  | (name, written) <-
      [ ("Nat",  "Type\8320")
      , ("zero", "Nat")
      , ("succ", "Nat -> Nat")
      , ("Vec",  "Type\8320 -> Nat -> Type\8320")
      , ("nil",  "forall (A : Type\8320) -> Vec A zero")
      , ("cons", "forall (A : Type\8320) (n : Nat) (a : A) (as : Vec A n) \
                 \-> Vec A (succ n)")
      ]
  ]

-- --------------------------------------------------------------------------
-- Strict positivity, and MS1's two further limits (§3.7)
-- --------------------------------------------------------------------------

positivityTests :: [TestTree]
positivityTests =
  [ accepted "a non-recursive argument" "T : Type\8320 where { c : Nat -> T }"
  , accepted "a recursive argument" "T : Type\8320 where { c : T -> T }"
  , accepted "a function argument that does not mention the datatype"
      "T : Type\8320 where { c : (Nat -> Nat) -> T }"
  , accepted "several recursive arguments" "T : Type\8320 where { c : T -> T -> T }"
  , refused "the datatype left of an arrow"
      "T : Type\8320 where { c : (T -> T) -> T }"
      (NotStrictlyPositive (named "c") (Ident "x"))
  , refused "a higher-order recursive argument (thesis §4.1.3)"
      "T : Type\8320 where { c : (Nat -> T) -> T }"
      (HigherOrderRecursion (named "c") (Ident "x"))
  , refused "the datatype under another former"
      "T : Type\8320 where { c : Vec T zero -> T }"
      (NestedRecursion (named "c") (Ident "x"))
  , refused "the argument is named in the message when it has a name"
      "T : Type\8320 where { c : forall (f : T -> T) -> T }"
      (NotStrictlyPositive (named "c") (Ident "f"))
  ]

-- --------------------------------------------------------------------------
-- Universes (thesis §4.1.1)
-- --------------------------------------------------------------------------
--
-- The check needs 'Thena.Core.Typing.infer', so it could only land once phase 8
-- existed. Two things it must get right beyond the inequality itself: the type
-- former has to be in scope while its own constructors are checked, or no
-- recursive argument types at all; and each argument is checked in a context of
-- the parameters plus the arguments before it, or a telescope that refers back
-- to itself does not type either.

universeTests :: [TestTree]
universeTests =
  [ accepted "a small argument in a large datatype"
      "T : Type\8321 where { c : Type\8320 -> T }"
  , refused "a large argument in a small datatype"
      "T : Type\8320 where { c : Type\8320 -> T }"
      (ArgumentTooLarge (named "c") (Ident "x") (levelOfNat 1) (LZero))
  , accepted "a recursive argument, which needs the former in scope already"
      "T : Type\8320 where { c : T -> T }"
  , accepted "a parameter used as an argument's type"
      "Box (A : Type\8320) : Type\8320 where { box : A -> Box A }"
  , refused "a parameter from a larger universe than the datatype"
      "Box (A : Type\8321) : Type\8320 where { box : A -> Box A }"
      (ArgumentTooLarge (named "box") (Ident "x") (levelOfNat 1) (LZero))
  , accepted "an argument whose type mentions an earlier argument"
      "T : Type\8320 where { c : forall (n : Nat) (v : Vec Nat n) -> T }"
  , refused "an argument whose type is not a type at all"
      "T : Type\8320 where { c : zero -> T }"
      (ArgumentNotAType (named "c") (Ident "x")
         (NotAType [] (Global (named "zero") []) (Canonical (named "Nat") [] [])))

  -- **A level a constructor argument's own typing determines** (phase 50).
  -- 'Thena.Global.Declare.argumentLevels' used to drop these obligations and
  -- 'universes' used to discard the solver's answer, so @?\8467@ reached
  -- 'generaliseInductive' undetermined and became a rigid that its own bound
  -- then refuted — which surfaced as the generated no-confusion family failing
  -- to typecheck, reported as a bug in Thena.
  --
  -- The assertion is on 'inductiveLevels' rather than on the stored argument
  -- type because that is the invariant: a level the declaration determines is
  -- not a parameter of it. Different code from the fix (phase 5's lesson).
  , testCase "a level the argument's typing determines is solved, not generalised" $
      case declareAll [natDecl, eqDecl, "E : Type where { k : Eq {1} Type Nat Nat -> E }"] of
        Left e         -> assertFailure e
        Right (env, _) ->
          fmap inductiveLevels (lookupInductive (named "E") env) @?= Just []
  , -- **And one the bounds only constrain is defaulted** (phase 51). @suc ?ℓ ≤ 2@
    -- leaves @?ℓ@ free below 1; phase 50 refused it, because a datatype has
    -- nowhere to carry a conditional constraint, and minimisation is what gives
    -- it a value instead — the least, so @Type\8320@.
    testCase "and one they merely bound is defaulted to its least value" $
      case declareAll [natDecl, eqDecl, "E : Type where { k : Eq {2} Type Nat Nat -> E }"] of
        Left e         -> assertFailure e
        Right (env, _) ->
          fmap inductiveLevels (lookupInductive (named "E") env) @?= Just []
  ]

-- --------------------------------------------------------------------------
-- Names (§3.6: one namespace)
-- --------------------------------------------------------------------------

nameTests :: [TestTree]
nameTests =
  [ refused "a datatype that is already declared"
      "Nat : Type\8320 where { z : Nat }"
      (AlreadyDeclared (named "Nat"))
  , refused "a constructor whose name is taken"
      "T : Type\8320 where { zero : T }"
      (AlreadyDeclared (named "zero"))
  , refused "a declaration that uses one name twice"
      "T : Type\8320 where { c : T ; c : T }"
      (RepeatedName (named "c"))
    -- **The eliminator\'s wrapper is one of the names introduced** (MS4 phase
    -- 49e): §3.7 item 2 generates a global for it the way it does for a former
    -- and a constructor, which is what lets @elim D …@ elaborate as an
    -- ordinary application.
  , testCase "everything a declaration introduces is declared afterwards" $
      sequence_
        [ isDeclared (named g) natVec @?= True
        | g <- [ "Nat", "zero", "succ", "elimNat"
               , "Vec", "nil", "cons", "elimVec"
               ]
        ]
  , testCase "and nothing else is" $
      isDeclared (named "pred") natVec @?= False
  ]

-- --------------------------------------------------------------------------
-- Printed and read back
-- --------------------------------------------------------------------------

-- | Compared as terms, not as text. Two declarations that differ only in a
-- binder's name print the same and are the same; one that lost an index does
-- not, and would slip past a string comparison of the header alone.
roundTripTests :: [TestTree]
roundTripTests =
  [ testCase name $ case lookupInductive (named name) natVec of
      Nothing -> assertFailure (name ++ " was not declared")
      Just d  -> case reread (renderInductive natVecCounter d) of
        Left e   -> assertFailure e
        Right d' -> do
          formerType d' @?= formerType d
          map (constructorType d') (inductiveConstructors d')
            @?= map (constructorType d) (inductiveConstructors d)
          map constructorName (inductiveConstructors d')
            @?= map constructorName (inductiveConstructors d)
  | name <- ["Nat", "Vec"]
  ]
  where
    -- The printer emits the whole command; the parser is handed what follows
    -- the command word, and the grammar does not care about the line breaks.
    reread ls = case parseDeclaration natVec natVecCounter (drop 5 (unwords ls)) of
      Left e       -> Left (show e)
      Right (d, _) -> Right d

-- --------------------------------------------------------------------------
-- Little helpers
-- --------------------------------------------------------------------------

accepted :: String -> String -> TestTree
accepted name src = testCase name $ case declareAll [natDecl, vecDecl, src] of
  Left e  -> assertFailure e
  Right _ -> pure ()

refused :: String -> String -> DeclareError -> TestTree
refused name src expect = testCase name $ case afterFixtures src of
  Left e   -> e @?= expect
  Right _  -> assertFailure "admitted, and it should not have been"

-- | Run one declaration against the fixtures' environment, keeping the
-- 'DeclareError' rather than rendering it.
afterFixtures :: String -> Either DeclareError ()
afterFixtures src = case parseDeclaration natVec 0 src of
  Left e       -> error ("fixture does not parse: " ++ show e)
  Right (d, n) -> () <$ declare natVec n d

-- --------------------------------------------------------------------------
-- generalised (MS3 phase 33b)
-- --------------------------------------------------------------------------

-- | @qed@'s half of level polymorphism: the metas a finished proof is still
-- carrying become the definition's prenex parameters, and the kernel's residue
-- becomes the constraints every use will owe.
generaliseTests :: [TestTree]
generaliseTests =
  [ testCase "a proof with no unknown level generalises to nothing" $
      let (d, n) = gen 50 [] (universe 1) (universe 0)
       in (definitionLevels d, definitionConstraints d, n) @?= ([], [], 50)

  , testCase "a meta in the type becomes a parameter" $
      levelsOf (gen 50 [] (Universe (LVar p)) (universe 0)) @?= [LRigid 50]

  , -- **Fresh, not the meta's own number under another constructor.** MS2
    -- closeout 4f is one counter across every sort precisely so that a number
    -- the user has seen as @?ℓ7@ is never reissued as something else.
    testCase "and it is a fresh number, not the meta's" $
      levelsOf (gen 50 [] (Universe (LVar (LMeta 7))) (universe 0)) @?= [LRigid 50]

  , testCase "the type's metas come first, in the order it reads" $
      levelsOf (gen 50 [] (arrow (LVar q) (LVar p)) (universe 0))
        @?= [LRigid 50, LRigid 51]

  , -- **A meta only the body mentions is defaulted, not generalised** (phase
    -- 51). It used to come last, on the reasoning that a use supplies level
    -- arguments positionally and reads the type to know what they mean — which
    -- is exactly why this one could never be read: nothing in the type names
    -- it, so every use had to write a level that said nothing at all.
    testCase "a meta only the body mentions is defaulted away" $
      levelsOf (gen 50 [] (Universe (LVar p)) (Universe (LVar q))) @?= [LRigid 50]

  , testCase "and it is defaulted to zero, its least value" $
      bodyOf (gen 50 [] (Universe (LVar p)) (Universe (LVar q))) @?= Universe LZero

  , -- Least, not zero unconditionally: a lower bound is met exactly.
    testCase "a bounded body-only meta is defaulted to the bound" $
      bodyOf (gen 50 [AtMost (levelOfNat 2) (LVar q)]
                (Universe (LVar p)) (Universe (LVar q)))
        @?= Universe (levelOfNat 2)

  , -- **And when there is no least value it refuses** — his ruling, 2026-09-02.
    -- @2 ≤ max ?q ?q2@ has minimal solutions @(2,0)@ and @(0,2)@, incomparable.
    testCase "and refuses when no least value exists" $
      refuses (generalised 50 [AtMost (levelOfNat 2) (LMax (LVar q) (LVar q2))]
                 (Universe (LVar p)) (arrow (LVar q) (LVar q2)))
        @?= True

  , testCase "the same meta twice is one parameter" $
      levelsOf (gen 50 [] (arrow (LVar p) (LVar p)) (universe 0)) @?= [LRigid 50]

  , testCase "the type is rewritten to mention the parameters" $
      typeOf' (gen 50 [] (Universe (LVar p)) (universe 0))
        @?= Universe (LVar (LRigid 50))

  , -- The body is rewritten too. It has to share the type's meta to show it:
    -- a meta of the body's own is now defaulted rather than generalised.
    testCase "and so is the body" $
      bodyOf (gen 50 [] (Universe (LVar p)) (Universe (LVar p)))
        @?= Universe (LVar (LRigid 50))

  , -- **The residue is not filtered.** A relation between two of the new
    -- parameters is exactly what a scheme constraint is for; asking 'levelLeq'
    -- to decide it here would refuse it, because a rigid is not bounded by
    -- another rigid — which is the whole reason it has to travel to the use.
    testCase "the residue becomes the constraints, over the new parameters" $
      constraintsOf (gen 50 [AtMost (LVar p) (LVar q)]
                       (arrow (LVar p) (LVar q)) (Universe (LVar q)))
        @?= [AtMost (LVar (LRigid 50)) (LVar (LRigid 51))]

  , testCase "the counter comes back advanced by one per parameter" $
      snd (gen 50 [] (arrow (LVar p) (LVar q)) (universe 0)) @?= 52
  ]
  where
    -- Generalisation may refuse since phase 51. Every case here but one is an
    -- acceptance, so a refusal is a broken fixture rather than a failed
    -- assertion; the one that expects a refusal asks through 'isRefusal'.
    gen n obs ty body = case generalised n obs ty body of
      Left u  -> error ("generalised refused: " ++ show u)
      Right r -> r

    refuses = either (const True) (const False)

    levelsOf      = definitionLevels . fst
    bodyOf        = definitionBody . fst
    typeOf'       = definitionType . fst
    constraintsOf = definitionConstraints . fst
    p  = LMeta 900
    q  = LMeta 901
    q2 = LMeta 902

    universe = Universe . levelOfNat

    -- A non-dependent function type between two universes, built by hand: the
    -- concrete syntax cannot write a meta down.
    arrow a b = Pi (Ident "_") (Universe a) (close (fst (fresh 990)) (Universe b))
