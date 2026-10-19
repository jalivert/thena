-- | Specialisation by unification (MS9 phase 177).
--
-- __The phase's deliverable is 'vtailTests' and it is one claim__: of the two
-- methods an elimination of @v : Vec A (succ n)@ hands over, the @nil@ one
-- __vanishes__ and the @cons@ one loses the binder its equation determined. That
-- is the difference between the elimination a user writes today
--
-- @
-- (elim Vec (A) (λ x t -> Eq Nat x (succ n) -> Vec A n)
--    ( (λ q -> absurdly (Vec A n) (noConfusionNat zero (succ n) q))
--      (λ n1 a v1 ih q ->
--         transport Nat (λ k -> Vec A k) n1 n (noConfusionNat (succ n1) (succ n) q) v1) )
--    ((succ n)) v) (refl Nat (succ n))
-- @
--
-- and the one clause @vtail A n (cons n a v) = v@ a split should leave.
--
-- __The method types are asserted as exact strings__, for
-- "Thena.EliminateTests"' reason: two method types that print identically are
-- the same method type, because every binder that could differ is printed.
--
-- What is deliberately not tested here is that the terms typecheck.
-- 'Thena.Tactics.Specialise.specialise' runs 'Thena.Core.Typing.check' on what
-- it built and answers 'Thena.Errors.SpecialisedIllTyped' if it does not, so
-- every success below is already a typechecked term — checked by different code
-- from the code that built it, which is the standing lesson.
module Thena.SpecialiseTests (tests) where

import Data.List (isInfixOf)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Context (Context, Entry (..))
import Thena.Core.Term (Core, GlobalName (..), Ident (..), fresh)
import Thena.Declared (eqNat, eqNatCounter, eqNatVec, eqNatVecCounter)
import Thena.Driver
  ( Loaded (..)
  , Response (..)
  , Session
  , loadRuleBases
  , loadSource
  , newSession
  , parseCore
  , withRuleBases
  )
import Thena.Errors (SpecialiseError (..))
import Thena.Global.Env (GlobalEnv)
import Thena.Render (Rendering (..), renderCore)
import Thena.Tactics.Eliminate (Elimination (..), eliminate)
import Thena.Tactics.Specialise (Specialisation (..), specialise)
import Thena.Standard (expectedBase)

tests :: TestTree
tests =
  testGroup
    "specialisation by unification (MS9 phase 177)"
    [ testGroup "vtail — the milestone's own case" vtailTests
    , testGroup "one transition at a time" transitionTests
    , testGroup "what it leaves alone" residualTests
    , testGroup "what it refuses" refusalTests
    , testGroup "through a rule base, with the kernel as the judge" engineTests
    ]

-- --------------------------------------------------------------------------
-- vtail
-- --------------------------------------------------------------------------

-- | @A : Type₀@, @n : Nat@, @v : Vec A (succ n)@ at the goal @Vec A n@ — the
-- state @vtail@'s one interesting clause is reached in.
vecContext :: Context
vecCounter :: Int
(vecContext, vecCounter) =
  contextOf eqNatVec eqNatVecCounter
    [ ("A", "Type\8320")
    , ("n", "Nat")
    , ("v", "Vec A (succ n)")
    ]

-- | The elimination the clause starts from. Its one index @succ n@ is not a
-- variable, so it is tied and each method carries one equation.
vtail :: Elimination
vtail = run "vtail" eqNatVec vecContext vecCounter "Vec A n" "v"

vtailTests :: [TestTree]
vtailTests =
  [ testCase "the elimination states one equation per method" $
      elimEquations vtail @?= 1

    -- The methods as the user is handed them, so that what the two cases below
    -- change is visible here rather than taken on trust.
  , testCase "nil's method, before: an equation that cannot hold" $
      shown vecContext (methodOf 0) @?= "Eq {0} Nat zero (succ n) -> Vec A n"

  , testCase "cons's, before: a binder, a vector at it, and an equation" $
      shown vecContext (methodOf 1)
        @?= "\8704 (n1 : Nat) -> A -> Vec A n1 -> \
            \(Eq {0} Nat n1 (succ n) -> Vec A n) \
            \-> Eq {0} Nat (succ n1) (succ n) -> Vec A n"

    -- __The impossible case vanishes.__ @zero@ against @succ n@ is a conflict,
    -- so there is no subgoal at all and nothing is left for the user to close.
  , testCase "nil's method, after: no subgoal at all" $
      vecGoal "nil" (methodOf 0) @?= Nothing

    -- __And the determined binder goes.__ @succ n1 ≃ succ n@ is injectivity and
    -- then solution, so @n1@ is gone, @as@ is a @Vec A n@ rather than a
    -- @Vec A n1@ — which is exactly the transport the user writes today — and
    -- the induction hypothesis follows it.
  , testCase "cons's method, after: n1 is solved and the vector is at n" $
      vecGoal "cons" (methodOf 1)
        @?= Just ( "consCase"
                 , "A -> Vec A n -> \
                   \(Eq {0} Nat n (succ n) -> Vec A n) -> Vec A n" )
  ]
  where
    methodOf k = case drop k (elimMethods vtail) of
      (_, _, ty) : _ -> ty
      []             -> error ("no method " ++ show k)

    vecGoal c mty =
      goalIn vecContext (run' eqNatVec vecContext vecCounter c 1 mty)

-- --------------------------------------------------------------------------
-- One transition at a time
-- --------------------------------------------------------------------------

-- | Each transition on its own, over @Nat@ alone, so that a failure says which
-- one broke.
--
-- __The method types here are written rather than produced by an elimination__,
-- and that is the only way to reach one transition at a time: an elimination's
-- methods carry whatever equations its target's indices imply, all of them at
-- once. Each is a method of @succ@, whose telescope is its argument and its
-- induction hypothesis — two binders — and then the equation.
transitionTests :: [TestTree]
transitionTests =
  [ -- __deletion.__ The equation holds by @refl@ and constrains nothing, so its
    -- binder is dropped and nothing else moves.
    specialises "deletion: an equation of a term with itself" "succ" 1
      "\8704 (m : Nat) -> Nat -> Eq {0} Nat zero zero -> Eq {0} Nat m k"
      (Just "\8704 (m : Nat) -> Nat -> Eq {0} Nat m k")

    -- __conflict.__ Nothing is claimed; the method is closed outright.
  , specialises "conflict: two different constructors" "succ" 1
      "\8704 (m : Nat) -> Nat -> Eq {0} Nat zero (succ k) -> Eq {0} Nat m k"
      Nothing

    -- __injectivity.__ The equation is replaced by the one its arguments imply.
    -- No further transition applies to that one: @j@ and @k@ are both ambient,
    -- so both are rigid.
  , specialises "injectivity: the same constructor over two rigid arguments" "succ" 1
      "\8704 (m : Nat) -> Nat -> Eq {0} Nat (succ j) (succ k) -> Eq {0} Nat m k"
      (Just "\8704 (m : Nat) -> Nat -> Eq {0} Nat j k -> Eq {0} Nat m k")

    -- __solution, with the binder on the left__, which is the orientation
    -- @vtail@ meets. Everything to the right of @m@ is substituted, the goal
    -- included, and the binder goes.
  , specialises "solution: the binder on the left of the equation" "succ" 1
      "\8704 (m : Nat) -> Nat -> Eq {0} Nat m k -> Eq {0} Nat m k"
      (Just "Nat -> Eq {0} Nat k k")

    -- __and on the right__, which is the orientation the paper writes. The same
    -- answer, by the other branch of the coercion's motive.
  , specialises "solution: and on the right" "succ" 1
      "\8704 (m : Nat) -> Nat -> Eq {0} Nat k m -> Eq {0} Nat m k"
      (Just "Nat -> Eq {0} Nat k k")

    -- __Two transitions, cascading__: injectivity exposes an equation solution
    -- then fires on. This is the composition @vtail@ needs, and the only case
    -- that tests the recursion threading a coercion through another
    -- transition's term.
  , specialises "injectivity then solution" "succ" 1
      "\8704 (m : Nat) -> Nat -> Eq {0} Nat (succ m) (succ k) -> Eq {0} Nat m k"
      (Just "Nat -> Eq {0} Nat k k")
  ]

-- --------------------------------------------------------------------------
-- What it leaves alone
-- --------------------------------------------------------------------------

-- | __An equation no transition applies to is kept__, which is the whole of how
-- the missing cycle transition is survived.
--
-- @eliminating.pdf@ Definition 19 makes "no transition applies" a /failure/.
-- Keeping the equation is weaker and strictly more useful: it is the hypothesis
-- the user is handed today, so the specialiser's worst case is the behaviour
-- that preceded it.
residualTests :: [TestTree]
residualTests =
  [ -- A cycle. @noCycle@ does not exist, so this equation is refutable and not
    -- refuted — and what happens is that it survives, not that the split is
    -- withdrawn.
    specialises "a cyclic equation is kept, not refuted" "succ" 1
      "\8704 (m : Nat) -> Nat -> Eq {0} Nat m (succ m) -> Eq {0} Nat m k"
      (Just "\8704 (m : Nat) -> Nat -> Eq {0} Nat m (succ m) -> Eq {0} Nat m k")

    -- Two ambient variables: neither is a binder of this method, so neither may
    -- be solved. §6.2's note is the reason — moving a declaration leftwards is
    -- @raise@, and @raise@ is deliberately not in the op vocabulary at all.
  , specialises "two ambient variables are both rigid" "succ" 1
      "\8704 (m : Nat) -> Nat -> Eq {0} Nat j k -> Eq {0} Nat m k"
      (Just "\8704 (m : Nat) -> Nat -> Eq {0} Nat j k -> Eq {0} Nat m k")

    -- No equations at all, which is every method of a family with no indices:
    -- the method comes back as it went in and nothing is built.
  , specialises "no equations: the method is handed straight back" "succ" 0
      "\8704 (m : Nat) -> Nat -> Eq {0} Nat m k"
      (Just "\8704 (m : Nat) -> Nat -> Eq {0} Nat m k")
  ]

-- --------------------------------------------------------------------------
-- Refusals
-- --------------------------------------------------------------------------

-- | The two things a caller can get wrong, and they are the two arguments it
-- supplies. Nothing about the /problem/ is ever a refusal.
refusalTests :: [TestTree]
refusalTests =
  [ testCase "a name that is not a constructor" $
      refused "Nat" 1 "\8704 (m : Nat) -> Eq {0} Nat m k"
        @?= Just (NotThatConstructor (GlobalName "Nat"))

    -- @succ@'s method binds its argument and its induction hypothesis, so two
    -- binders and an equation is three — and a type with one Π is not it.
  , testCase "fewer binders than the constructor's telescope needs" $
      case refused "succ" 1 "\8704 (m : Nat) -> Nat" of
        Just (MethodNotShaped 2 1 _) -> pure ()
        other -> assertFailure ("expected a mis-shaped method, got " ++ show other)

  , testCase "a binder in the equation block that is not an equation" $
      case refused "succ" 1 "\8704 (m : Nat) -> Nat -> Nat -> Nat" of
        Just (NotAnEquation [_]) -> pure ()
        other -> assertFailure ("expected one non-equation, got " ++ show other)
  ]

-- --------------------------------------------------------------------------
-- Through the engine
-- --------------------------------------------------------------------------

-- | The op at a real focus, in a real development, over the shipped rule base.
--
-- __Everything above runs the tactic and never the op__, so the engine's half —
-- claiming the subgoal above the method hole, turning the method into the guess
-- that uses it, and claiming /nothing/ where the method vanished — is untested
-- by it. This is that half, and __the kernel is the judge__: each script ends in
-- @:revalidate@, so a development the specialised term does not fit is caught
-- even though the op itself would still have said @subgoals:@.
--
-- The rule is this module's and not the shipped base's. Walking the splitting
-- tree is a later phase of `~kq4kc`, and a half-built tactic in
-- @rules\/standard.thena.rules@ would be offered to a user at every hole.
engineTests :: [TestTree]
engineTests =
  [ -- __Both methods, found by the rule and not named by the caller__ (MS9
    -- phase 180). @nil@'s closes outright and @cons@'s leaves one subgoal, so
    -- one run says both things — and the walk reached each hole by the
    -- /variable/ @prim-eliminate@ handed back.
    testCase "the rule walks the constructors and specialises every method" $
      splits "split-all core`v` \"Vec\"" ["no subgoals", "subgoals: consCase"]

    -- __Pins the ORDER__, which the walk above cannot: the shape phase
    -- 177 had. Kept because it is the one case that pins the /order/: the
    -- second method's hole is the second element of the list.
  , testCase "and the second hole in the list is the second constructor's" $
      splits "split-second core`v` \"cons\"" ["subgoals: consCase"]
  ]
  where
    splits call wants = case loadedError loaded of
      Just e  -> assertFailure (show e)
      Nothing ->
        let said = map show (loadedResponses loaded)
         in if all (\w -> any (w `isInfixOf`) said) wants
               && any ("valid" `isInfixOf`) said
              then pure ()
              else assertFailure (unlines said)
      where
        loaded = loadSource splitSession (unlines (script call))

    script call =
      declarations
        ++ [ ":theorem vtail : \8704 (A : Type\8320) (n : Nat) (v : Vec A (succ n)) -> Vec A n"
           , "attack", "intro", "intro", "intro", "into", "along", "along", "along"
           , call
           , ":revalidate"
           ]

-- | Prelude-free, like every script in the suite (phase 11) — so the four
-- prelude types the specialiser's terms are built out of are declared here.
-- @Eq@ first and @And@ after it, because @And@'s own no-confusion states
-- equations.
declarations :: [String]
declarations =
  [ "data Eq (A : Type) : A -> A -> Type where { refl : \8704 (x : A) -> Eq A x x }"
  , "data Unit : Type where { unit : Unit }"
  , "data Empty : Type where { }"
  , "data And (A : Type) (B : Type) : Type where { both : \8704 (a : A) (b : B) -> And A B }"
  , "data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
  , "data Vec (A : Type\8320) : Nat -> Type\8320 where { nil : Vec A zero ; cons : \8704 (n : Nat) (a : A) (as : Vec A n) -> Vec A (succ n) }"
  ]

-- | An elimination and a specialisation of /every/ method, as a rule.
--
-- __This is the shape `~w23j5` was blocked on__, and his ruling of 2026-10-19
-- unblocked it: @prim-eliminate@ answers with the method holes it claimed and
-- the equation count, as a pair, so @split-all@ below walks the constructors
-- and the holes in step and nothing has to be told a hole's name.
--
-- Two things make the walk work and both are decisions, not accidents.
-- @constructors-of@ answers __in declaration order__, which is the order the
-- methods are claimed in, so the two lists correspond without either side
-- being told. And a hole is reached by @goto@, which takes the __variable__ —
-- the only handle that survives 'Thena.Development.Cursor.freshIdent'
-- renaming a method's display name, as a nested split makes it do.
--
-- __The count is one number for the whole elimination__, so it is passed down
-- the recursion unchanged rather than paired with each hole.
--
-- @split-second@ exists for one assertion the walk cannot make on its own:
-- that the /second/ hole belongs to the /second/ constructor. It takes the
-- list apart positionally, there being no indexing op — a rule destructures a
-- list and that is all it can do with one.
splitBase :: String
splitBase = unlines
  [ "rule base splitting where"
  , "split-all : Core -> Name -> ()"
  , "rule split-all t d :- when focus-is-hole"
  , "  do (hs, k) = prim-eliminate t"
  , "     ; cs = constructors-of d"
  , "     ; split-each cs hs k"
  , ""
  , "split-each : List Name -> List Core -> Int -> ()"
    -- Nothing left to split, and a bare `do` is the empty body — the same
    -- spelling E⟦_⟧ uses in the shipped base.
  , "rule split-each [] [] k :- do"
  , "rule split-each [c, ...cs] [h, ...hs] k :-"
    -- `goto h` is exact, and it still is after the method before this one was
    -- turned into a guess: the variable names the hole wherever it has moved to
    -- on the spine.
  , "  do goto h"
  , "     ; specialise c k"
  , "     ; split-each cs hs k"
  , ""
  , "split-second : Core -> Name -> ()"
  , "rule split-second t c :- when focus-is-hole"
  , "  do ([_, h], k) = prim-eliminate t"
  , "     ; goto h"
  , "     ; specialise c k"
  ]

-- | The shipped base and this one, which is a list and not an addition: a load
-- __replaces__ the bases a session is searching — his ruling of 2026-08-25 —
-- so the standard rules go back in beside this one. A refusal is a fixture bug
-- and errors loudly, because otherwise every script below would turn into an
-- unrelated assertion about @split-one@ not existing.
splitSession :: Session
splitSession = case loadRuleBases newSession [("split.thena.rules", splitBase)] of
  (s, BasesLoaded bs) -> withRuleBases (expectedBase ++ bs) s
  (_, other)          -> error ("the fixture's base did not load: " ++ show other)

-- --------------------------------------------------------------------------
-- The harness
-- --------------------------------------------------------------------------

-- | @j k : Nat@ — the ambient, rigid variables the written methods above state
-- their equations against.
natContext :: Context
natCounter :: Int
(natContext, natCounter) = contextOf eqNat eqNatCounter [("j", "Nat"), ("k", "Nat")]

-- | Specialise a written method of @c@ and assert the goal that comes back.
specialises :: String -> String -> Int -> String -> Maybe String -> TestTree
specialises what c k src want = testCase what $
  fmap snd (goalIn natContext (run' eqNat natContext natCounter c k mty)) @?= want
  where mty = term eqNat natContext natCounter src

-- | The refusal, for a fixture that is meant to be refused.
refused :: String -> Int -> String -> Maybe SpecialiseError
refused c k src =
  case fst (specialise eqNat natContext natCounter (GlobalName c) k
              (term eqNat natContext natCounter src)) of
    Left e  -> Just e
    Right _ -> Nothing

-- | Run it and insist it worked; a refusal in these fixtures is a bug in the
-- fixture, not a test result.
run' :: GlobalEnv -> Context -> Int -> String -> Int -> Core -> Specialisation
run' env ctx n c k mty = case fst (specialise env ctx n (GlobalName c) k mty) of
  Right s -> s
  Left e  -> error (c ++ ": " ++ show e)

-- | The subgoal's name and type, rendered — or 'Nothing' where the method was
-- closed outright.
goalIn :: Context -> Specialisation -> Maybe (String, String)
goalIn ctx s = case specialisedGoal s of
  [(_, Ident i, ty)] -> Just (i, shown ctx ty)
  _                  -> Nothing

shown :: Context -> Core -> String
shown ctx = unwords . words . renderCore (Rendering [] 0) ctx

-- | Build a context by parsing each entry's type against what precedes it, so
-- that a dependent context reads as the user would type it —
-- "Thena.EliminateTests"' @contextOf@, which is private to that module.
contextOf :: GlobalEnv -> Int -> [(String, String)] -> (Context, Int)
contextOf env n0 = foldl one ([], n0)
  where
    one (ctx, n) (name, src) = case parseCore [] env ctx n src of
      Left e -> error ("fixture does not parse: " ++ show e)
      Right (ty, n1) ->
        let (v, n2) = fresh n1
         in (ctx ++ [Hypothesis v (Ident name) ty], n2)

term :: GlobalEnv -> Context -> Int -> String -> Core
term env ctx n src = case parseCore [] env ctx n src of
  Left e       -> error ("fixture does not parse: " ++ show e)
  Right (t, _) -> t

-- | Run the elimination tactic and insist it worked.
run :: String -> GlobalEnv -> Context -> Int -> String -> String -> Elimination
run label env ctx n goal tgt = case parseCore [] env ctx n goal of
  Left e -> error ("fixture does not parse: " ++ show e)
  Right (g, n1) -> case parseCore [] env ctx n1 tgt of
    Left e -> error ("fixture does not parse: " ++ show e)
    Right (t, n2) -> case fst (eliminate env ctx n2 g t) of
      Right el -> el
      Left e   -> error (label ++ ": " ++ show e)
