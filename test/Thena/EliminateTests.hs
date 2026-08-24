-- | The elimination tactic (§3.7, thesis §3.5–§3.6, phase 17).
--
-- **The scheme is checked as exact strings, and that is the right shape here**
-- for "Thena.EliminatorTests"' reason: two schemes that print identically are
-- the same scheme, because every binder that could differ is printed. It is
-- also the only way to check the thing that matters — @PLAN.md@ §3.7 /displays/
-- the method type it wants for the running example, so the test can be that
-- displayed type and nothing weaker.
--
-- What is deliberately not tested here: that the scheme typechecks.
-- 'Thena.Tactics.Eliminate.eliminate' runs 'Thena.Core.Typing.check' on what it
-- built and returns 'Thena.Errors.SchemeIllTyped' if it does not, so every
-- success below is already a typechecked one — by different code from the code
-- that built it, which is the standing lesson. The end-to-end cases are the
-- golden transcripts, where the kernel accepts the finished proofs.
module Thena.EliminateTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Context (Context, Entry (..))
import Thena.Core.Term (Core, GlobalName (..), Ident (..), fresh)
import Thena.Declared
  ( eqNat
  , eqNatCounter
  , eqStep
  , eqStepCounter
  , declared
  , finDecl
  , natDecl
  )
import Thena.Driver (parseCore)
import Thena.Errors (ElimError (..))
import Thena.Global.Env (GlobalEnv)
import Thena.Repl (renderCore)
import Thena.Tactics.Eliminate (Elimination (..), eliminate)

tests :: TestTree
tests =
  testGroup
    "the elimination tactic (§3.7)"
    [ testGroup "the scheme, against §3.7's worked example" workedTests
    , testGroup "no indices: the target is what gets generalised" simpleTests
    , testGroup "friendly indices are abstracted, not equated" friendlyTests
    , testGroup "what it refuses" refusalTests
    ]

-- --------------------------------------------------------------------------
-- §3.7's worked example
-- --------------------------------------------------------------------------

-- | §3.7 works the second @Step@ elimination of the determinacy proof and
-- displays the method it wants for @eIfTrue@:
--
-- > (u₂ u₃ : Term) -> Eq Term (if true u₂ u₃) (if true t₂ t₃)
-- >               -> Eq Term u₂ t''
-- >               -> Eq Term t₂ u₂
--
-- The first case below is that **minus its second equation**, in §2.6's
-- concrete syntax. Two kinds of difference, and only the second is the
-- tactic's.
--
-- The syntax's: @∀ (x : T) (y : T) ->@ for the thesis's @(x y : T) ->@,
-- @ifthen@ for @if@ because that is what the fixture calls the constructor,
-- and the binder names the /constructor's own arguments/ carry — @t2@ and @t3@
-- freshened to @t21@, @t31@ against the goal's @t2@, @t3@ — rather than the
-- document's @u₂@, @u₃@.
--
-- The tactic's, decided planning phase 18: @Eq Term u₂ t''@ is **gone**. The
-- second index of the target is @t''@, a plain context variable, so it is
-- thesis §3.5.2's /friendly/ case — abstracting it in the motive generalises
-- every occurrence there is, and an equation tying it back adds nothing to a
-- method and destroys the induction hypothesis of any method that has one.
-- §3.7 is amended to say so. The first index, @if true t₂ t₃@, is not a
-- variable and keeps its equation, which is what the impossible branches close
-- on.
--
-- The other two cases are the schemes the same elimination hands to the
-- branches that cannot occur; determinacy closes both by discrimination, and
-- what makes that possible is the constraint the first index carries.
workedTests :: [TestTree]
workedTests =
  [ method "eIfTrue — §3.7's own displayed method" 0
      "∀ (t21 : Term) (t31 : Term) -> Eq Term (ifthen true t21 t31) (ifthen true t2 t3) \
      \-> Eq Term t2 t21"

  , method "eIfFalse — the branch ruled out by conflict on true/false" 1
      "∀ (t21 : Term) (t31 : Term) -> Eq Term (ifthen false t21 t31) (ifthen true t2 t3) \
      \-> Eq Term t2 t31"

    -- The inductive hypothesis is the motive at the recursive argument's own
    -- indices, so it carries its own copy of whatever the motive constrains.
    -- Here that is the /first/ index only — thesis §3.5.4's \"unfriendly\"
    -- constraint, which narrows what the hypothesis may be used at rather than
    -- telling you anything. An inversion does not want the hypothesis, so this
    -- one is harmless; 'friendlyTests' is where it would not have been.
  , method "eIf — and its induction hypothesis is constrained too" 2
      "∀ (t1 : Term) (t1' : Term) (t21 : Term) (t31 : Term) -> Step t1 t1' \
      \-> (Eq Term t1 (ifthen true t2 t3) -> Eq Term t2 t1') \
      \-> Eq Term (ifthen t1 t21 t31) (ifthen true t2 t3) \
      \-> Eq Term t2 (ifthen t1' t21 t31)"

  , testCase "one subgoal per constructor, in declaration order" $
      names worked
        @?= ["eIfTrueMethod", "eIfFalseMethod", "eIfMethod"]

    -- The equations are reflexive at the use site, which is the whole point of
    -- the scheme (§3.7): @P a⃗ target@ applied to @refl …@ is the goal again.
    -- One @refl@ per /tied/ index, and none for a friendly one. The motive
    -- still binds both — the eliminator's type demands it — so what changes is
    -- the equations it states and the spine that discharges them.
  , testCase "the equations are discharged with refl at the use site" $
      rendered (withMethods stepContext worked) (elimTerm worked)
        @?= "(elim Step () (λ (x : Term) (x1 : Term) (target : Step x x1) \
            \-> Eq Term x (ifthen true t2 t3) -> Eq Term t2 x1) \
            \(eIfTrueMethod eIfFalseMethod eIfMethod) ((ifthen true t2 t3) u) d) \
            \(refl Term (ifthen true t2 t3))"
  ]
  where
    method label k want = testCase label $
      case drop k (elimMethods worked) of
        (_, _, ty) : _ -> rendered stepContext ty @?= want
        []             -> assertFailure ("no method " ++ show k)

    names el = [ i | (_, Ident i, _) <- elimMethods el ]

-- | @t2 t3 u : Term@, @d : Step (ifthen true t2 t3) u@ — the state the second
-- @Step@ elimination of the determinacy proof is reached in.
stepContext :: Context
stepCounter :: Int
(stepContext, stepCounter) =
  contextOf eqStep eqStepCounter
    [ ("t2", "Term")
    , ("t3", "Term")
    , ("u",  "Term")
    , ("d",  "Step (ifthen true t2 t3) u")
    ]

worked :: Elimination
worked = run "§3.7's worked example" eqStep stepContext stepCounter "Eq Term t2 u" "d"

-- --------------------------------------------------------------------------
-- No indices
-- --------------------------------------------------------------------------

-- | With no indices there are no equations at all, and the only generalisation
-- the scheme performs is **abstracting the target in the goal**.
--
-- That half of §3.7 is not in its displayed formula, and it is the half an
-- induction over @Nat@ lives or dies by: a motive that did not abstract @n@
-- would be constant, and @succMethod@'s induction hypothesis would say
-- nothing. The two cases below are the same elimination with @n@ occurring in
-- the goal and not occurring in it.
simpleTests :: [TestTree]
simpleTests =
  [ testCase "the target is abstracted in the goal" $
      map (rendered natContext . thirdOf) (elimMethods natEq)
        @?= [ "Eq Nat zero zero"
            , "∀ (x : Nat) -> Eq Nat x x -> Eq Nat (succ x) (succ x)"
            ]

  , testCase "a goal not mentioning the target gets a constant motive" $
      map (rendered natContext . thirdOf) (elimMethods natConst)
        @?= [ "Eq Nat m m"
            , "Nat -> Eq Nat m m -> Eq Nat m m"
            ]

  , testCase "no indices, so nothing is applied to the elimination" $
      rendered (withMethods natContext natEq) (elimTerm natEq)
        @?= "elim Nat () (λ (target : Nat) -> Eq Nat target target) \
            \(zeroMethod succMethod) () n"
  ]
  where
    thirdOf (_, _, ty) = ty

    natEq    = run "target abstracted" eqNat natContext natCounter' "Eq Nat n n" "n"
    natConst = run "constant motive"   eqNat natContext natCounter' "Eq Nat m m" "n"

natContext :: Context
natCounter' :: Int
(natContext, natCounter') =
  contextOf eqNat eqNatCounter [("n", "Nat"), ("m", "Nat")]

-- --------------------------------------------------------------------------
-- Friendly indices
-- --------------------------------------------------------------------------

-- | Thesis §3.5.2, "what to fix, what to abstract", **decided planning phase
-- 18**: an index the target supplies as a plain context variable is abstracted
-- and carries no equation.
--
-- The first case is why. Before this, induction over any inductively defined
-- relation was worthless, because the method's induction hypothesis is the
-- motive at the recursive argument's own indices — so it arrived guarded by
-- @Eq Nat m1 m -> Eq Nat n1 n -> …@, and the method holds only
-- @Eq Nat (succ m1) m@. Discharging the guard would need @Eq Nat m1 (succ m1)@,
-- which is refutable. @weaken@ below is the smallest statement that shows it,
-- and MS1's determinacy proof is the same shape at ten constructors.
--
-- The other three are the conditions under which an index is /not/ friendly,
-- each of which is a case that breaks if it is ignored.
friendlyTests :: [TestTree]
friendlyTests =
  [ testCase "the induction hypothesis arrives unguarded" $
      map (rendered leContext . thirdOf') (elimMethods leWeaken)
        @?= [ "∀ (n1 : Nat) -> Le zero (succ n1)"
            , "∀ (m1 : Nat) (n1 : Nat) -> Le m1 n1 -> Le m1 (succ n1) \
              \-> Le (succ m1) (succ (succ n1))"
            ]

    -- Nothing is applied to the elimination: both indices were abstracted, so
    -- there is no equation left to discharge reflexively.
  , testCase "and no refl spine is needed at all" $
      rendered (withMethods leContext leWeaken) (elimTerm leWeaken)
        @?= "elim Le () (λ (x : Nat) (x1 : Nat) (target : Le x x1) \
            \-> Le x (succ x1)) (leZeroMethod leSuccMethod) (m n) p"

    -- Two abstractions would race for the same occurrences, and the second
    -- would find none left. @Eq Nat a a@ is the case; it keeps both equations
    -- and is exactly as provable as it was.
  , testCase "an index variable repeated in the spine is tied" $
      let (env, n0) = declared [eqDecl', natDecl]
          (ctx, n1) = contextOf env n0 [("a", "Nat"), ("e", "Eq Nat a a")]
       in map (rendered ctx . thirdOf') (elimMethods (run "repeated" env ctx n1 "Eq Nat a a" "e"))
            @?= [ "∀ (a1 : Nat) -> Eq Nat a1 a -> Eq Nat a1 a -> Eq Nat a1 a1" ]

    -- Every premise of the goal stays fixed (§3.7), so a premise that still
    -- mentions the index is precisely the specificity the equation exists to
    -- carry. The pair below is the same elimination with and without @k@.
  , testCase "an index another hypothesis mentions is tied" $
      let (env, n0) = declared [eqDecl', natDecl, finDecl]
          (with, n1) = contextOf env n0
            [("n", "Nat"), ("k", "Eq Nat n n"), ("i", "Fin n")]
          (without, n2) = contextOf env n0 [("n", "Nat"), ("i", "Fin n")]
       in do
            map (rendered with . thirdOf') (elimMethods (run "tied" env with n1 "Eq Nat n n" "i"))
              @?= [ "∀ (n1 : Nat) -> Eq Nat (succ n1) n -> Eq Nat (succ n1) (succ n1)"
                  , "∀ (n1 : Nat) -> Fin n1 -> (Eq Nat n1 n -> Eq Nat n1 n1) \
                    \-> Eq Nat (succ n1) n -> Eq Nat (succ n1) (succ n1)"
                  ]
            map (rendered without . thirdOf') (elimMethods (run "free" env without n2 "Eq Nat n n" "i"))
              @?= [ "∀ (n1 : Nat) -> Eq Nat (succ n1) (succ n1)"
                  , "∀ (n1 : Nat) -> Fin n1 -> Eq Nat n1 n1 -> Eq Nat (succ n1) (succ n1)"
                  ]

    -- Phase 19. Both of @Below@'s indices are plain variables, so the second
    -- is friendly and states no equation — and its type may therefore mention
    -- the first freely. Before phase 19 this whole family was refused.
  , testCase "a dependent index telescope is fine when the dependent index is friendly" $
      map (rendered belowContext . thirdOf') (elimMethods belowProbe)
        @?= [ "∀ (m : Nat) -> Eq Nat (succ m) n -> Nat"
            , "∀ (m : Nat) (j : Fin m) -> Below m j -> (Eq Nat m n -> Nat) \
              \-> Eq Nat (succ m) n -> Nat"
            ]

    -- The load-bearing artifact of phase 19, and the thing @check@ alone would
    -- not have caught: the motive's own telescope is dependent, and its second
    -- binder names /this motive's/ first binder rather than the one in the
    -- declaration, which is not in scope here at all.
  , testCase "and the motive's telescope carries the dependency" $
      rendered (withMethods belowContext belowProbe) (elimTerm belowProbe)
        @?= "(elim Below () (λ (n1 : Nat) (i1 : Fin n1) (target : Below n1 i1) \
            \-> Eq Nat n1 n -> Nat) (bzMethod bsMethod) (n i) b) (refl Nat n)"

    -- A 'Definition' has a value as well as a type, and abstracting the
    -- variable would leave the value behind. Conservative on purpose: tying it
    -- is what the tactic did for every index before this change.
  , testCase "an index bound by a definition is tied" $
      let (env, n0)  = declared [eqDecl', natDecl, finDecl]
          (zeroT, n1) = parsed env [] n0 "Nat"
          (zeroV, n2) = parsed env [] n1 "zero"
          (dv,    n3) = fresh n2
          defCtx      = [Definition dv (Ident "n") zeroV zeroT]
          (ctx,   n4) = contextOf' env defCtx n3 [("i", "Fin n")]
       in map (rendered ctx . thirdOf') (elimMethods (run "defined" env ctx n4 "Eq Nat n n" "i"))
            @?= [ "∀ (n1 : Nat) -> Eq Nat (succ n1) n -> Eq Nat (succ n1) (succ n1)"
                , "∀ (n1 : Nat) -> Fin n1 -> (Eq Nat n1 n -> Eq Nat n1 n1) \
                  \-> Eq Nat (succ n1) n -> Eq Nat (succ n1) (succ n1)"
                ]
  ]
  where
    thirdOf' (_, _, ty) = ty

-- | @n : Nat@, @i : Fin n@, @b : Below n i@ — a family whose index telescope
-- is dependent, eliminated at plain variables so the dependent index is
-- friendly. Phase 19's case.
belowContext :: Context
belowProbe :: Elimination
(belowContext, belowProbe) =
  let (env, n0) = declared [eqDecl', natDecl, finDecl, belowDecl]
      (ctx, n1) = contextOf env n0
        [("n", "Nat"), ("i", "Fin n"), ("b", "Below n i")]
   in (ctx, run "below" env ctx n1 "Nat" "b")

-- | @m n : Nat@, @p : Le m n@ — the state @weaken@ reaches after three
-- @intro@s, and the smallest induction over an indexed family there is.
leContext :: Context
leWeaken :: Elimination
(leContext, leWeaken) =
  let (env, n0) = declared [eqDecl', natDecl, leDecl]
      (ctx, n1) = contextOf env n0 [("m", "Nat"), ("n", "Nat"), ("p", "Le m n")]
   in (ctx, run "weaken" env ctx n1 "Le m (succ n)" "p")

leDecl :: String
leDecl =
  "Le : Nat -> Nat -> Type\8320 \
  \{ leZero : \8704 (n : Nat) -> Le zero n \
  \; leSucc : \8704 (m : Nat) (n : Nat) (p : Le m n) -> Le (succ m) (succ n) }"

-- --------------------------------------------------------------------------
-- Refusals
-- --------------------------------------------------------------------------

refusalTests :: [TestTree]
refusalTests =
  [ testCase "a term whose type is not a datatype is not a target" $
      case fst (attempt eqNat natContext natCounter' "Eq Nat n n" "succ") of
        Left (TargetNotInductive {}) -> pure ()
        other                        -> assertFailure (show (fmap (const ()) other))

    -- §3.7's limit, and it binds a /tied/ index only (phase 19). Here index 2
    -- is @fz m@ — a constructor application, so it states an equation, and
    -- @Eq (Fin i1) i2 (fz m)@ is the one that cannot be written down.
  , testCase "a dependent index that is tied is refused, by position and name" $
      let (env, n0) = declared [eqDecl', natDecl, finDecl, belowDecl]
          (ctx, n1) = contextOf env n0
            [("m", "Nat"), ("b", "Below (succ m) (fz m)")]
       in case fst (attempt env ctx n1 "Nat" "b") of
            Left e  -> e @?= IndexTypeDepends 2 (Ident "i")
            Right _ -> assertFailure "expected a refusal"

    -- §3.7, decided 2026-08-11: @Eq@ and @refl@ are named, not designated. A
    -- family with no indices states no equations and so needs neither, which
    -- is why this is checked at an indexed one.
  , testCase "eliminating at indices without Eq says so" $
      let (env, n0) = declared [natDecl, finDecl]
          (ctx, n1) = contextOf env n0 [("n", "Nat"), ("i", "Fin n")]
       in case fst (attempt env ctx n1 "Nat" "i") of
            Left e  -> e @?= NoEquality (GlobalName "Eq")
            Right _ -> assertFailure "expected a refusal"

    -- Thesis §3.5.2, \"what to fix, what to abstract\", arriving as a refusal.
    -- §3.7's scheme generalises the target and its indices and **fixes every
    -- premise of the goal**, so a second hypothesis at the same index cannot
    -- follow the target when it is abstracted: @w : Vec Nat n@ is still at @n@
    -- while the goal now reads @Eq (Vec Nat i) x w@.
    --
    -- §3.5.3 allows either reporting this or falling back to the unabstracted
    -- goal. MS1 reports: falling back would silently hand back an induction
    -- too weak to be worth doing, and nothing in the op vocabulary can
    -- generalise a premise (that is @justify@'s and @postpone@'s territory,
    -- which no MS1 tactic needs). Matched on shape, not text — the message
    -- ends in a clash naming two variables by number.
  , testCase "a premise at the target's index cannot be left behind" $
      let (env, n0) = declared [eqDecl', natDecl, vecDecl']
          (ctx, n1) = contextOf env n0
            [("n", "Nat"), ("v", "Vec Nat n"), ("w", "Vec Nat n")]
       in case fst (attempt env ctx n1 "Eq (Vec Nat n) v w" "v") of
            Left (MotiveIllTyped _) -> pure ()
            Left e                  -> assertFailure ("wrong refusal: " ++ show e)
            Right _                 -> assertFailure "expected a refusal"

  , testCase "without indices it needs no Eq at all" $
      let (env, n0) = declared [natDecl]
          (ctx, n1) = contextOf env n0 [("n", "Nat")]
       in case fst (attempt env ctx n1 "Nat" "n") of
            Right el -> length (elimMethods el) @?= 2
            Left e   -> assertFailure (show e)
  ]

-- --------------------------------------------------------------------------
-- Fixtures and plumbing
-- --------------------------------------------------------------------------

eqDecl' :: String
eqDecl' = "Eq (A : Type\8320) : A -> A -> Type\8320 { refl : \8704 (a : A) -> Eq A a a }"

vecDecl' :: String
vecDecl' =
  "Vec (A : Type\8320) : Nat -> Type\8320 \
  \{ nil : Vec A zero \
  \; cons : \8704 (n : Nat) (a : A) (as : Vec A n) -> Vec A (succ n) }"

-- | An index whose /type/ mentions an earlier index — the shape §3.7's limit
-- is about, and the one nothing else in the suite has. Note it is /not/ @Vec@:
-- a one-element index telescope has no earlier index to depend on.
--
-- @bs@ is recursive, so a method carries an induction hypothesis at @Below m j@
-- and the motive's dependent telescope has to be right for it to typecheck.
belowDecl :: String
belowDecl =
  "Below : \8704 (n : Nat) (i : Fin n) -> Type\8320 \
  \{ bz : \8704 (m : Nat) -> Below (succ m) (fz m) \
  \; bs : \8704 (m : Nat) (j : Fin m) (b : Below m j) -> Below (succ m) (fs m j) }"

-- | Build a context by parsing each entry's type against what precedes it, so
-- that a dependent context can be written down as the user would type it.
contextOf :: GlobalEnv -> Int -> [(String, String)] -> (Context, Int)
contextOf env = contextOf' env []

-- | 'contextOf' onto a context that already has entries — the one fixture that
-- needs a 'Definition' cannot state it as a @(name, type)@ pair.
contextOf' :: GlobalEnv -> Context -> Int -> [(String, String)] -> (Context, Int)
contextOf' env ctx0 n0 = foldl one (ctx0, n0)
  where
    one (ctx, n) (name, src) = case parseCore env ctx n src of
      Left e -> error ("fixture does not parse: " ++ show e)
      Right (ty, n1) ->
        let (v, n2) = fresh n1
         in (ctx ++ [Hypothesis v (Ident name) ty], n2)

parsed :: GlobalEnv -> Context -> Int -> String -> (Core, Int)
parsed env ctx n src = case parseCore env ctx n src of
  Left e        -> error ("fixture does not parse: " ++ show e)
  Right (t, n1) -> (t, n1)

-- | Run the tactic and insist it worked; a refusal in these fixtures is a bug
-- in the fixture, not a test result.
run :: String -> GlobalEnv -> Context -> Int -> String -> String -> Elimination
run label env ctx n goal tgt = case fst (attempt env ctx n goal tgt) of
  Right el -> el
  Left e   -> error (label ++ ": " ++ show e)

attempt
  :: GlobalEnv -> Context -> Int -> String -> String
  -> (Either ElimError Elimination, Int)
attempt env ctx n goal tgt = case parseCore env ctx n goal of
  Left e -> error ("fixture does not parse: " ++ show e)
  Right (g, n1) -> case parseCore env ctx n1 tgt of
    Left e        -> error ("fixture does not parse: " ++ show e)
    Right (t, n2) -> eliminate env ctx n2 g t

-- | The context the refinement is well typed in: the goal's, plus the holes
-- the tactic asked for. 'Thena.Engine' puts them there with @insertAbove@; a
-- renderer that did not would print them as @‹Var 281›@.
withMethods :: Context -> Elimination -> Context
withMethods ctx el =
  ctx ++ [ Hypothesis v i ty | (v, i, ty) <- elimMethods el ]

-- | One line, so that an exact-string case reads as one line.
rendered :: Context -> Core -> String
rendered ctx = unwords . words . renderCore 0 ctx
