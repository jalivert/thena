-- | Unification (§6): decomposition, Miller patterns, deferral into the chain,
-- and wake-up to fixpoint.
--
-- Two groups do the real work, and both are the standing lesson — look for the
-- invariant that is checked by different code from the code that maintains it:
--
--   * 'agreementTests' runs @unify@ and then asks "Thena.Core.Convert" whether
--     the two terms are now equal. Conversion does its own whnf-driven walk and
--     knows nothing about holes, positions or constraints, so a solution
--     unification is merely pleased with does not pass — only one that actually
--     makes the equation true.
--   * 'typeTests' takes every hole unification promoted and asks
--     "Thena.Core.Typing" whether its new value has the type the hole was
--     declared at. Nothing in @unify@ consults a type except to record one on a
--     parked constraint, so this is an outside check on every solution it made.
--
-- Developments are built by hand rather than driven through the REPL, because
-- @claim@ and @assume@ both insert immediately above the focus and so can never
-- put a hole /before/ an assumption — which is exactly the shape the scope
-- cases need.
module Thena.Core.UnifyTests (tests) where

import Data.List (isInfixOf)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertFailure, testCase, (@?=))

import Thena.Core.Level (Level (..))
import Thena.Core.Context (Context)
import Thena.Core.Convert (convert)
import Thena.Core.Term (Core (..), Ident (..), Var, fresh)
import Thena.Core.Typing (check)
import Thena.Core.Unify (UnifyResult (..), blockers, constraintsOf, unify, unifyInto)
import Thena.Declared (natVec, natVecCounter)
import Thena.Development.Component (Component (..), forget)
import Thena.Development.Cursor (Cursor, enter, rebuild)
import Thena.Development.Partial (Partial (..))
import Thena.Driver (parseCore)

tests :: TestTree
tests =
  testGroup
    "Thena.Core.Unify"
    [ testGroup "decomposition" decompositionTests
    , testGroup "Miller patterns" patternTests
    , testGroup "what fails, and what only waits" failureTests
    , testGroup "deferral parks at the minimal legal position" positionTests
    , testGroup "wake-up, to fixpoint" wakeTests
    , testGroup "a guess is a blocked neutral, never solved" guessTests
    , testGroup "unify agrees with convert" agreementTests
    , testGroup "every solution type-checks" typeTests
    , testGroup "all or nothing, and the counter" disciplineTests
    , testGroup "the degenerate flex-flex case is solved" flexFlexTests
    , testGroup "unify-into is directed at universes" directedTests
    ]

-- --------------------------------------------------------------------------
-- Building a development by hand
-- --------------------------------------------------------------------------

data Decl
  = Hole    String String          -- ^ @? x : S@
  | Assumed String String          -- ^ @λ x : S@
  | Guessed String String String   -- ^ @? x ≐ g : S@

-- | A development, in chain order, with a trailing @Type₀@ and the focus at the
-- root. Also gives back the context every component is in scope in, the counter
-- to carry on from, and the variables by name.
data Dev = Dev
  { devCursor  :: Cursor
  , devContext :: Context
  , devNames   :: Int
  , devVars    :: [(String, Var)]
  }

devOf :: [Decl] -> Dev
devOf ds = Dev
  { devCursor  = enter (foldr Under (Trailing (Universe (LZero))) comps)
  , devContext = map forget comps
  , devNames   = n
  , devVars    = vars
  }
  where
    (comps, vars, n) = foldl one ([], [], natVecCounter) ds

    one (cs, vs, k) d =
      let (v, k1) = fresh k
          ctx     = map forget cs
       in case d of
            Hole nm ty ->
              let (t, k2) = readIn ctx k1 ty
               in (cs ++ [Claim v (Ident nm) t], vs ++ [(nm, v)], k2)
            Assumed nm ty ->
              let (t, k2) = readIn ctx k1 ty
               in (cs ++ [Assume v (Ident nm) t], vs ++ [(nm, v)], k2)
            Guessed nm body ty ->
              let (t, k2) = readIn ctx k1 ty
                  (g, k3) = readIn ctx k2 body
               in (cs ++ [Guess v (Ident nm) (Trailing g) t], vs ++ [(nm, v)], k3)

readIn :: Context -> Int -> String -> (Core, Int)
readIn ctx n src = case parseCore natVec ctx n src of
  Left e  -> error ("fixture term does not resolve: " ++ show e)
  Right r -> r

-- | Unify two terms, written as source, against a development.
run :: [Decl] -> String -> String -> String -> (UnifyResult, Cursor, Dev)
run ds a b ty = (result, cur', dev)
  where
    dev = devOf ds
    (ta, n1) = readIn (devContext dev) (devNames dev) a
    (tb, n2) = readIn (devContext dev) n1 b
    (tt, n3) = readIn (devContext dev) n2 ty
    (result, cur', _) = unify natVec (devCursor dev) n3 ta tb tt

resultOf :: [Decl] -> String -> String -> String -> UnifyResult
resultOf ds a b ty = let (r, _, _) = run ds a b ty in r

-- | 'run', through the directed entry point (MS4 phase 41g).
--
-- Written out rather than parameterising 'run', because every existing caller
-- wants the symmetric one and threading an argument through all of them to say
-- so would be noise.
runInto :: [Decl] -> String -> String -> String -> (UnifyResult, Cursor, Dev)
runInto ds a b ty = (result, cur', dev)
  where
    dev = devOf ds
    (ta, n1) = readIn (devContext dev) (devNames dev) a
    (tb, n2) = readIn (devContext dev) n1 b
    (tt, n3) = readIn (devContext dev) n2 ty
    (result, cur', _) = unifyInto natVec (devCursor dev) n3 ta tb tt

intoResultOf :: [Decl] -> String -> String -> String -> UnifyResult
intoResultOf ds a b ty = let (r, _, _) = runInto ds a b ty in r

-- | The chain of a finished run, as a list of one-word tags plus names, which
-- is what a position assertion can be written against without depending on how
-- anything prints.
shapeOf :: Cursor -> [String]
shapeOf = go . rebuild
  where
    go p = case p of
      Trailing _      -> []
      Pending _ rest  -> "constraint" : go rest
      Under c rest    -> tag c : go rest

    tag c = case c of
      Assume _ (Ident i) _   -> "assume " ++ i
      Define _ (Ident i) _ _ -> "define " ++ i
      Claim  _ (Ident i) _   -> "hole "   ++ i
      Guess  _ (Ident i) _ _ -> "guess "  ++ i
      Quantify _ (Ident i) _ -> "forall " ++ i

nameOf :: Dev -> Var -> String
nameOf dev v = case [ nm | (nm, w) <- devVars dev, w == v ] of
  nm : _ -> nm
  []     -> "?"

-- --------------------------------------------------------------------------

decompositionTests :: [TestTree]
decompositionTests =
  [ testCase "two identical terms need no work" $
      resultOf [] "succ zero" "succ zero" "Nat" @?= Solved [] []
  , testCase "reduction first: a redex meets its value" $
      resultOf [] "(\\ (x : Nat) -> x) zero" "zero" "Nat" @?= Solved [] []
  , testCase "a former's arguments are decomposed, and a hole inside is solved" $
      solvedNames ([Hole "h" "Nat"]) "succ h" "succ (succ zero)" "Nat" @?= ["h"]
  , testCase "two holes, one on each side, both solved in one run" $
      solvedNames ([Hole "h" "Nat", Hole "k" "Nat"])
        "cons Nat h zero (nil Nat)" "cons Nat zero k (nil Nat)" "Vec Nat (succ zero)"
        @?= ["h", "k"]
  , testCase "an elimination decomposes field by field" $
      solvedNames ([Hole "h" "Nat"])
        "elim Nat () (\\ (_ : Nat) -> Nat) (h succ) () zero"
        "elim Nat () (\\ (_ : Nat) -> Nat) (zero succ) () zero"
        "Nat"
        @?= ["h"]
  ]
  where
    solvedNames ds a b ty =
      let (r, _, dev) = run ds a b ty
       in case r of
            Solved xs _     -> map (nameOf dev) xs
            Deferred xs _ _ -> map (nameOf dev) xs ++ ["<deferred>"]
            Failed e      -> ["<failed: " ++ show e ++ ">"]

patternTests :: [TestTree]
patternTests =
  [ testCase "a bare hole takes the other side" $
      resultOf [Hole "h" "Nat"] "h" "succ zero" "Nat" `isSolved` 1
  , testCase "under a lambda: ?f x meets succ x, and f is abstracted" $
      -- The binder is minted into Ξ while decomposing, so @x@ is a local
      -- variable and @?f x@ is a pattern. The solution must be @λ x. succ x@,
      -- not @succ x@ with a variable that escaped.
      --
      -- Compared by 'convert' and not by @==@: decomposition whnf'd the
      -- right-hand side on the way, so what is stored is @λ x. ‹succ x›@ while
      -- the source spells the wrapper applied. The two are the same term and
      -- only one of them is written down here. The 'Lam' check is what keeps
      -- this from passing for a solution that forgot to abstract at all.
      solutionIs [Hole "f" "Nat -> Nat"]
        "\\ (x : Nat) -> f x" "\\ (x : Nat) -> succ x" "Nat -> Nat"
        "\\ (x : Nat) -> succ x"
  , testCase "two binders deep" $
      resultOf [Hole "f" "Nat -> Nat -> Nat"]
        "\\ (x : Nat) (y : Nat) -> f x y" "\\ (x : Nat) (y : Nat) -> x" "Nat -> Nat -> Nat"
        `isSolved` 1
  , testCase "a repeated argument is not a pattern, so it waits" $
      resultOf [Hole "f" "Nat -> Nat -> Nat"]
        "\\ (x : Nat) -> f x x" "\\ (x : Nat) -> x" "Nat -> Nat"
        `isDeferred` 1
  , testCase "a non-variable argument is not a pattern either" $
      resultOf [Hole "f" "Nat -> Nat"]
        "f zero" "zero" "Nat" `isDeferred` 1
  , testCase "a chain variable in argument position is not a pattern argument" $
      -- Abstracting it would change what the hole means: @a@ is not local to
      -- the equation, it is a component of the development.
      resultOf [Assumed "a" "Nat", Hole "f" "Nat -> Nat"]
        "f a" "zero" "Nat" `isDeferred` 1
  ]
  where
    solutionIs ds a b ty expected =
      let (_, cur, dev) = run ds a b ty
          (want, n1) = readIn (devContext dev) (devNames dev) expected
       in case [ v | Define _ _ v _ <- componentsOf (rebuild cur) ] of
            []    -> assertFailure "nothing was solved"
            t : _ -> case t of
              Lam {} -> case verdict (convert natVec (solvedContext cur) n1 t want) of
                Nothing  -> pure ()
                Just why -> assertFailure ("wrong solution: " ++ show why)
              _ -> assertFailure ("the pattern arguments were not abstracted: " ++ show t)

failureTests :: [TestTree]
failureTests =
  [ testCase "two different constructors cannot be made equal" $
      failsWith [] "zero" "succ zero" "Nat" "Mismatch"
  , testCase "the occurs check fires on a cyclic solution" $
      failsWith [Hole "h" "Nat"] "h" "succ h" "Nat" "OccursCheck"
  , testCase "two universes, with no cumulativity to relate them" $
      failsWith [] "Type\8320" "Type\8321" "Type\8322" "UniverseMismatch"
  , testCase "a solution naming a RIGID variable bound after the hole fails" $
      -- Nothing will ever change @a@'s position, so this is a real
      -- ScopeViolation and not a wait. Repairing it means moving a declaration
      -- leftwards, which is `raise`'s job and not the unifier's.
      failsWith [Hole "h" "Nat", Assumed "a" "Nat"] "h" "a" "Nat" "ScopeViolation"
  , testCase "a solution naming a HOLE bound after it only waits" $
      -- @k@ may yet be solved to something in scope, so the equation defers
      -- rather than failing. This is the case the two must be told apart.
      resultOf [Hole "h" "Nat", Hole "k" "Nat"] "h" "succ k" "Nat" `isDeferred` 1
  ]
  where
    failsWith ds a b ty needle = case resultOf ds a b ty of
      Failed e
        | needle `isInfixOf` show e -> pure ()
        | otherwise -> assertFailure ("wrong reason: " ++ show e)
      other -> assertFailure ("expected a failure, got " ++ show other)

-- | The user's decision, 2026-08-22 (@AGENDA.md@ item 16 q1): a deferred
-- constraint parks immediately below the last component it mentions — the
-- highest position that is scope-legal — and not at the focus and not at the
-- bottom.
positionTests :: [TestTree]
positionTests =
  [ testCase "above a later hole it does not mention" $
      shapeAfter [Hole "h" "Nat", Hole "k" "Nat", Hole "spare" "Nat"]
        "f h" "zero" "Nat" [Hole "f" "Nat -> Nat"]
        @?= [ "hole f", "hole h", "constraint", "hole k", "hole spare" ]
  , testCase "below every hole when it mentions the last of them" $
      shapeAfter [Hole "h" "Nat", Hole "k" "Nat"] "f h k" "zero" "Nat"
        [Hole "f" "Nat -> Nat -> Nat"]
        @?= [ "hole f", "hole h", "hole k", "constraint" ]
  , testCase "immediately below its own head hole when it mentions nothing else" $
      -- Not at the top: the equation names @f@, and a constraint may not sit
      -- above something it mentions.
      shapeAfter [Hole "spare" "Nat"] "f zero" "zero" "Nat" [Hole "f" "Nat -> Nat"]
        @?= [ "hole f", "constraint", "hole spare" ]
  , testCase "blockers are derived from the constraint, never stored" $
      let (r, cur, dev) = run [Hole "f" "Nat -> Nat", Hole "h" "Nat"] "f h" "zero" "Nat"
       in case r of
            Deferred _ _ [k] -> map (nameOf dev) (blockers cur k) @?= ["f", "h"]
            other          -> assertFailure (show other)
  ]
  where
    -- The hole that heads the equation is declared first, so that the position
    -- being asserted is decided by the OTHER variables the constraint mentions.
    shapeAfter ds a b ty leading =
      let (_, cur, _) = run (leading ++ ds) a b ty in shapeOf cur

wakeTests :: [TestTree]
wakeTests =
  [ testCase "a solution naming a later hole waits rather than failing" $
      -- @h@ is bound before @k@, so @h = succ k@ is not well-founded yet. It is
      -- not refused: @k@ may still be solved to something in scope.
      let (_, cur, _) = run [Hole "h" "Nat", Hole "k" "Nat"] "h" "succ k" "Nat"
       in length (constraintsOf (rebuild cur)) @?= 1
  , testCase "a second run wakes the first run's constraint and clears it" $
      twoRuns @?= ([], ["define h", "define k"])
  , testCase "the fixpoint runs more than one round" $
      -- Solving @c@ wakes @b ≟ succ c@, whose solution wakes @a ≟ succ b@.
      -- One sweep is not enough; the loop has to go round until nothing moves.
      threeDeep @?= []
  ]
  where
    twoRuns =
      let dev = devOf [Hole "h" "Nat", Hole "k" "Nat"]
          (t1, n1) = readIn (devContext dev) (devNames dev) "h"
          (t2, n2) = readIn (devContext dev) n1 "succ k"
          (ty, n3) = readIn (devContext dev) n2 "Nat"
          (_, cur1, n4) = unify natVec (devCursor dev) n3 t1 t2 ty
          (u1, n5) = readIn (devContext dev) n4 "k"
          (u2, n6) = readIn (devContext dev) n5 "zero"
          (_, cur2, _) = unify natVec cur1 n6 u1 u2 ty
       in (constraintsOf (rebuild cur2), definedIn cur2)

    threeDeep =
      let dev = devOf [Hole "a" "Nat", Hole "b" "Nat", Hole "c" "Nat"]
          ctx = devContext dev
          step cur n (l, r) =
            let (tl, k1) = readIn ctx n l
                (tr, k2) = readIn ctx k1 r
                (ty, k3) = readIn ctx k2 "Nat"
                (_, cur', k4) = unify natVec cur k3 tl tr ty
             in (cur', k4)
          (cur1, n1) = step (devCursor dev) (devNames dev) ("a", "succ b")
          (cur2, n2) = step cur1 n1 ("b", "succ c")
          (cur3, _)  = step cur2 n2 ("c", "zero")
       in constraintsOf (rebuild cur3)

    definedIn cur = [ "define " ++ i | Define _ (Ident i) _ _ <- componentsOf (rebuild cur) ]

guessTests :: [TestTree]
guessTests =
  [ testCase "a guessed hole is never promoted — the equation waits (§6.3)" $
      resultOf [Guessed "g" "zero" "Nat"] "g" "succ zero" "Nat" `isDeferred` 1
  , testCase "and the guess is left exactly as it was" $
      let (_, cur, _) = run [Guessed "g" "zero" "Nat"] "g" "succ zero" "Nat"
       in [ tag | tag <- shapeOf cur, "guess" `isInfixOf` tag ] @?= ["guess g"]
  ]

-- | See the module header. Conversion is different code from unification, and
-- it is the outside judge of whether a run actually made the equation true.
agreementTests :: [TestTree]
agreementTests =
  [ agrees "a bare hole" [Hole "h" "Nat"] "h" "succ zero" "Nat"
  , agrees "a hole inside a former" [Hole "h" "Nat"] "succ h" "succ (succ zero)" "Nat"
  , agrees "a Miller pattern under a binder"
      [Hole "f" "Nat -> Nat"] "\\ (x : Nat) -> f x" "\\ (x : Nat) -> succ x" "Nat -> Nat"
  , agrees "two holes at once" [Hole "h" "Nat", Hole "k" "Nat"]
      "cons Nat h zero (nil Nat)" "cons Nat zero k (nil Nat)" "Vec Nat (succ zero)"
  , agrees "a hole under an elimination that then computes" [Hole "h" "Nat"]
      "elim Nat () (\\ (_ : Nat) -> Nat) (h succ) () zero" "zero" "Nat"
  ]
  where
    agrees name ds a b ty = testCase name $
      let (result, cur, dev) = run ds a b ty
       in case result of
            Failed e -> assertFailure ("unify failed: " ++ show e)
            _ ->
              let ctx = solvedContext cur
                  (ta, n1) = readIn (devContext dev) (devNames dev) a
                  (tb, n2) = readIn (devContext dev) n1 b
               in case verdict (convert natVec ctx n2 ta tb) of
                    Nothing  -> pure ()
                    Just why -> assertFailure ("still not convertible: " ++ show why)

-- | And the other outside judge: every promoted hole's value must have the type
-- the hole was declared at.
typeTests :: [TestTree]
typeTests =
  [ typechecks "a bare hole" [Hole "h" "Nat"] "h" "succ zero" "Nat"
  , typechecks "a Miller pattern" [Hole "f" "Nat -> Nat"]
      "\\ (x : Nat) -> f x" "\\ (x : Nat) -> succ x" "Nat -> Nat"
  , typechecks "a dependent one, where the index has to line up"
      [Hole "n" "Nat"] "cons Nat n zero (nil Nat)" "cons Nat zero zero (nil Nat)"
      "Vec Nat (succ zero)"
  , typechecks "two at once" [Hole "h" "Nat", Hole "k" "Nat"]
      "cons Nat h zero (nil Nat)" "cons Nat zero k (nil Nat)" "Vec Nat (succ zero)"
  ]
  where
    typechecks name ds a b ty = testCase name $
      let (result, cur, dev) = run ds a b ty
       in case result of
            Failed e -> assertFailure ("unify failed: " ++ show e)
            _ -> mapM_ (one cur dev) [ c | c@Define {} <- componentsOf (rebuild cur) ]

    one cur dev c = case c of
      Define _ _ v declared ->
        case verdict (check natVec (solvedContext cur) (devNames dev + 500) v declared) of
          Right () -> pure ()
          Left e   -> assertFailure ("a solution does not have its hole's type: " ++ show e)
      _ -> pure ()

-- | @check@ and @convert@ return their level obligations too (phase 33);
-- nothing here builds a level meta, so the list is always empty.
verdict :: (a, b, c) -> a
verdict (r, _, _) = r

-- | The degenerate flex-flex case — two bare holes, no spine (MS4 phase 41g).
--
-- **It has a most general unifier, so solving it is not eager guessing.**
-- Miller's pattern condition is that the arguments are distinct locally-bound
-- variables; with no arguments it holds vacuously. Huet's reason for deferring
-- flex-flex — no mgu, always solvable, so branching would be guessing — is
-- about the spined case, which still defers below.
flexFlexTests :: [TestTree]
flexFlexTests =
  [ testCase "two bare holes solve" $
      resultOf [Hole "a" "Nat", Hole "b" "Nat"] "a" "b" "Nat" `isSolved` 1

    -- **The direction is forced by the chain**, which is the whole of the side
    -- condition: a hole may only be solved by a term mentioning what is above
    -- it, so the LATER hole is the one that gets solved. Asserted on the shape
    -- rather than on a message, because it is a fact about the development.
  , testCase "and it is the later hole that is solved" $
      let (_, cur, _) = run [Hole "a" "Nat", Hole "b" "Nat"] "a" "b" "Nat"
       in shapeOf cur @?= ["hole a", "define b"]

  , testCase "whichever side of the equation it is written on" $
      let (_, cur, _) = run [Hole "a" "Nat", Hole "b" "Nat"] "b" "a" "Nat"
       in shapeOf cur @?= ["hole a", "define b"]

    -- Huet's case, and §6.1 keeps it: a spine means there may be no most
    -- general unifier, so nothing is chosen.
  , testCase "but flex-flex with a spine still defers" $
      resultOf [Hole "f" "Nat -> Nat", Hole "h" "Nat"] "f h" "h" "Nat"
        `isDeferred` 1
  ]

-- | @unify-into@ relaxes a universe comparison, and only where there is
-- nothing left to solve (MS4 phase 41g).
directedTests :: [TestTree]
directedTests =
  [ -- The defect this phase exists for: @try-core ⌜ Nat ⌝@ at a claim of
    -- @Type₁@ succeeded and @elaborate Nat@ did not.
    testCase "a smaller universe fits a larger one" $
      intoResultOf [] "Type\8320" "Type\8321" "Type\8322" `isSolved` 0
  , testCase "and the symmetric one still refuses it" $
      isFailure (resultOf [] "Type\8320" "Type\8321" "Type\8322")
    -- Cumulativity has a direction; this is the wrong way round.
  , testCase "a larger universe does not fit a smaller one" $
      isFailure (intoResultOf [] "Type\8321" "Type\8320" "Type\8322")

    -- **The boundary, and a golden caught it going wrong.** @0 ≤ ?ℓ@ is
    -- decidably true, so answering it would discharge the problem without
    -- solving @?ℓ@ — and the meta would survive to generalisation as a level
    -- parameter nothing can determine. A level with a meta in it is a solving
    -- problem, not a deciding one.
  , testCase "but a level meta is still SOLVED, not merely satisfied" $
      intoResultOf [Hole "h" "Type"] "Type\8320" "h" "Type\8321" `isSolved` 1

    -- **The direction stops at an argument, and this is where it DIVERGES from
    -- 'Thena.Core.Convert.related'** — which inherits here and should not.
    -- @F@ is opaque, so nothing relates @F Type₀@ to @F Type₁@; Coq compares
    -- application arguments at equality for the same reason. That
    -- @Convert@ accepts it is @ms4/CLOSEOUT.md@ 12, a soundness bug this
    -- phase found rather than caused.
  , testCase "a neutral spine's argument is invariant" $
      isFailure
        (intoResultOf [Assumed "F" "Type\8322 -> Type\8320"]
           "F Type\8320" "F Type\8321" "Type\8320")

    -- A Π's codomain is the one covariant position, so the direction does
    -- survive there.
  , testCase "but a Pi's codomain still varies" $
      intoResultOf [] "Nat -> Type\8320" "Nat -> Type\8321" "Type\8322"
        `isSolved` 0
    -- And its domain does not, which is Coq's rule and the sound one.
  , testCase "while a Pi's domain does not" $
      isFailure (intoResultOf [] "Type\8321 -> Nat" "Type\8320 -> Nat" "Type\8322")
  ]

disciplineTests :: [TestTree]
disciplineTests =
  [ testCase "a failure leaves the development exactly as it was" $
      -- Sub-problems are solved in sequence, so the first pair here succeeds
      -- and the second fails; nothing of the first may survive.
      let ds = [Hole "h" "Nat", Hole "k" "Nat"]
          (result, cur, _) = run ds
            "cons Nat h zero (nil Nat)" "cons Nat zero (succ zero) (cons Nat zero zero (nil Nat))"
            "Vec Nat (succ zero)"
       in case result of
            Failed _ -> shapeOf cur @?= ["hole h", "hole k"]
            other    -> assertFailure ("expected a failure, got " ++ show other)
  , testCase "the counter comes back advanced when a binder was opened" $
      let dev = devOf [Hole "f" "Nat -> Nat"]
          (ta, n1) = readIn (devContext dev) (devNames dev) "\\ (x : Nat) -> f x"
          (tb, n2) = readIn (devContext dev) n1 "\\ (x : Nat) -> succ x"
          (tt, n3) = readIn (devContext dev) n2 "Nat -> Nat"
          (_, _, n4) = unify natVec (devCursor dev) n3 ta tb tt
       in (n4 > n3) @?= True
  ]

-- --------------------------------------------------------------------------
-- Small shared helpers
-- --------------------------------------------------------------------------

componentsOf :: Partial -> [Component]
componentsOf p = case p of
  Trailing _     -> []
  Under c rest   -> c : componentsOf rest
  Pending _ rest -> componentsOf rest

-- | The context after a run: every component of the finished development,
-- forgotten. Solved holes are 'Definition's here, which is what lets δ unfold
-- them — the whole reason no substitution is needed (§5.1, §6.1).
solvedContext :: Cursor -> Context
solvedContext = map forget . componentsOf . rebuild

isSolved :: UnifyResult -> Int -> Assertion
isSolved r k = case r of
  Solved xs _ | length xs == k -> pure ()
  _ -> assertFailure ("expected " ++ show k ++ " solved, got " ++ show r)

isFailure :: UnifyResult -> Assertion
isFailure r = case r of
  Failed _ -> pure ()
  _        -> assertFailure ("expected a failure, got " ++ show r)

isDeferred :: UnifyResult -> Int -> Assertion
isDeferred r k = case r of
  Deferred _ _ ks | length ks == k -> pure ()
  _ -> assertFailure ("expected " ++ show k ++ " parked, got " ++ show r)
