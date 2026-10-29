-- | Trust accounting (MS8 phase 151).
--
-- **What is under test is a judgement nothing else in the system makes**: given
-- a trusted claim, is it met, could it still be met, or can it never be? And
-- given a /term/, which claims does it rest on and at which site was each one
-- read?
--
-- **Four of these would catch a wrong design.**
--
--   * /the same node is honest in a definition and a lie at a use/ — the
--     measured case of his ruling of 2026-10-06, and the whole reason the
--     accounting classifies at the use site where it can. Definition-site
--     classification alone is Coq's @Print Assumptions@ shape and reports
--     @cheatNat zero (succ zero)@ as resting on one discharged claim.
--   * /discharged is exactly what the reducer contracts/ — crossed against
--     'whnf' over every pair below rather than asserted pair by pair. A report
--     that called a claim met where reduction leaves the node standing would be
--     describing a term the system never produces.
--   * /the clash is looked for positionally, and the heads agree/ — the test
--     asserts that a head-only comparison would pass, so it cannot quietly
--     become one.
--   * /δ runs before the heads are read at every position, not only the top/ —
--     the fixture differs at argument 1 only through an alias, and if the
--     recursion compared syntactically it would call an open claim impossible.
--
-- **The fixtures are parsed** through the real reader in a real environment,
-- and only the definitions' records are assembled by hand.
module Thena.Core.TrustTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))

import Thena.Core.Context (Context, Entry (..))
import Thena.Core.Level (Level (..), LevelVar (..))
import Thena.Core.Reduce (whnf)
import Thena.Core.Term (Core (..), GlobalName (..), Ident (..), Var, fresh)
import Thena.Core.Trust
  ( TrustClaim (..)
  , TrustClass (..)
  , TrustLevel (..)
  , TrustSite (..)
  , classify
  , permits
  , trustIn
  )
import Thena.Driver (parseCore)
import Thena.Global.Env (Definition (..), GlobalEnv, addDefinition, restingOnTrust)

import Thena.Declared (eqNat, eqNatCounter)

-- --------------------------------------------------------------------------
-- Fixtures
-- --------------------------------------------------------------------------

-- | The prelude and @Nat@, plus four definitions.
--
--   * @Alias@ is @Nat@ with a body, so δ relates two types that are not
--     α-equal. That is the whole purpose of it.
--   * @cheatNat@ is **his measured example**: @∀ a b -> Eq Nat a b@, proved by
--     a trusted node whose claim is met for its own generic binders and false at
--     almost every instance.
--   * @through@ calls @cheatNat@ saturated from inside its own body, which is
--     the case his ruling sends to the definition site.
--   * @plain@ holds no trusted node at all, so a walk that reported something
--     for it would be reporting the walk rather than the term.
env :: GlobalEnv
env =
  define "plain" "Nat" "zero"
    . define "through"
        "\8704 (x : Nat) -> Eq {0} Nat zero (succ zero)"
        "\955 (x : Nat) -> cheatNat zero (succ zero)"
    . define "cheatNat"
        "\8704 (a : Nat) -> \8704 (b : Nat) -> Eq {0} Nat a b"
        "\955 (a : Nat) -> \955 (b : Nat) -> \
        \trusted (Eq {0} Nat a b) (Eq {0} Nat a a) (refl {0} Nat a)"
    $ aliased
  where
    aliased =
      addDefinition
        (GlobalName "Alias")
        (MkDefinition [] [] (Universe LZero) (core eqNat "Nat"))
        eqNat

    -- Each definition is read in the environment built so far, so a later one
    -- may call an earlier one — which is what @through@ needs and is also the
    -- order the dependency graph's acyclicity comes from.
    define nm ty body e =
      addDefinition
        (GlobalName nm)
        (MkDefinition [] [] (core e ty) (core e body))
        e

-- | Read a core term. A fixture that will not parse is a bug in the fixture, so
-- it stops the suite rather than failing a test about something else.
core :: GlobalEnv -> String -> Core
core e src = case parseCore [] e [] eqNatCounter src of
  Left err     -> error ("fixture does not parse: " ++ show err)
  Right (t, _) -> t

-- | Two hypotheses of type @Nat@, numbered from the environment's own counter
-- and never from zero — a context numbered from scratch can collide with a
-- variable a declaration minted (@HAZARDS.md@).
ctx :: Context
ctx = [Hypothesis a (Ident "a") nat, Hypothesis b (Ident "b") nat]
  where
    nat = core env "Nat"

a, b :: Var
a = fst (fresh eqNatCounter)
b = fst (fresh (eqNatCounter + 1))

-- | A term read where @a@ and @b@ are in scope.
open2 :: String -> Core
open2 src = case parseCore [] env ctx eqNatCounter src of
  Left err     -> error ("fixture does not parse: " ++ show err)
  Right (t, _) -> t

term :: String -> Core
term = core env

-- | Classify in the empty context.
classed :: Core -> Core -> TrustClass
classed claimed actual = fst (classify env [] eqNatCounter claimed actual)

-- | Classify where @a@ and @b@ stand.
classedOpen :: Core -> Core -> TrustClass
classedOpen claimed actual = fst (classify env ctx eqNatCounter claimed actual)

rests :: Core -> [TrustClaim]
rests t = fst (trustIn env [] eqNatCounter t)

tests :: TestTree
tests =
  testGroup
    "trust accounting"
    [ testGroup "the three classes" classes
    , testGroup "the positional test is deep" positional
    , testGroup "the walk, and which site each verdict came from" walk
    , testGroup "what a level permits" rungs
    , testGroup "which definitions rest on trust, stored once" stored
    ]

-- --------------------------------------------------------------------------
-- The stored answer
-- --------------------------------------------------------------------------

-- | __'restingOnTrust' is the pre-pass's whole input now__ (MS9 phase 207,
-- @~2dqc3@). @reaches@ used to walk out from a term through every definition it
-- mentioned, reading each body in full, on every @certify@;
-- 'Thena.Global.Env.addDefinition' answers the same question once.
--
-- **The fixture already had the three cases this needs**, which is why it is
-- asserted here and not against a new one: @cheatNat@ holds a trusted node of
-- its own, @through@ holds none and calls @cheatNat@, and @plain@ and @Alias@
-- hold none and call nothing that does. **So the list is the transitivity, and
-- the two absences are what keeps it from being everything.**
stored :: [TestTree]
stored =
  [ testCase "a definition holding a trusted node, and one that only calls it" $
      restingOnTrust env @?= map GlobalName ["through", "cheatNat"]

    -- __And the term's own claim is still the term's__: the stored list says
    -- nothing about a 'Trusted' node standing in the term being examined, so
    -- both halves of @reaches@ are needed and this is the half that is not
    -- stored.
  , testCase "a bare trusted node rests on itself with nothing stored" $
      assertBool "the claim is reported"
        (not (null (rests (term "trusted Nat Nat zero"))))
  ]

-- --------------------------------------------------------------------------
-- Classifying
-- --------------------------------------------------------------------------

-- | The pairs the crossing below runs over, each with the class expected of it.
-- Written once so that 'whnf' is asked about the same list.
pairs :: [(String, Core, Core, TrustClass)]
pairs =
  [ ( "the same type twice"
    , term "Eq {0} Nat zero zero", term "Eq {0} Nat zero zero", Discharged )
  , ( "two types \948-equal and not \945-equal"
    , term "Eq {0} Alias zero zero", term "Eq {0} Nat zero zero", Discharged )
  , ( "a clash at argument 3"
    , term "Eq {0} Nat zero (succ zero)", term "Eq {0} Nat zero zero"
    , Undischargeable )
  , ( "two different formers"
    , term "Empty {0}", term "Eq {0} Nat zero zero", Undischargeable )
    -- **The two level clashes phase 166 added**, in this list rather than
    -- beside it so the crossing below asks the reducer about them too: a
    -- verdict of 'Undischargeable' is worthless if the node contracts anyway.
  , ( "a clash in the former's level argument"
    , term "Eq {1} Nat zero zero", term "Eq {0} Nat zero zero"
    , Undischargeable )
  , ( "two closed universe levels that differ"
    , term "Type\8320", term "Type\8321", Undischargeable )
    -- **A 'Canonical' carries a level argument too, and it is a second branch
    -- of the same test** — @Eq {1} Nat zero zero@ above is a 'Global' spine,
    -- because a datatype former applied to its arguments is one; a saturated
    -- /constructor/ is the 'Canonical' case.
  , ( "a clash in a constructor's level argument"
    , term "refl {1} Nat zero", term "refl {0} Nat zero"
    , Undischargeable )
  ]

classes :: [TestTree]
classes =
  [ testCase name (classed claimed actual @?= expected)
  | (name, claimed, actual, expected) <- pairs
  ]
    ++
  [ -- **The crossing, and it is the one that matters.** 'Discharged' is defined
    -- as the contraction's own condition, so the two must agree on every pair:
    -- a node contracts exactly when its claim is discharged.
    testCase "discharged is exactly what the reducer contracts" $
      [ (name, classed claimed actual == Discharged)
      | (name, claimed, actual, _) <- pairs
      ]
        @?= [ (name, contracts claimed actual)
            | (name, claimed, actual, _) <- pairs
            ]

    -- **The hazard, pinned a second time.** @convert@ answers /yes/ here and
    -- owes two level obligations for it; 'whnf' has no collector so it declines,
    -- and the report must say the same thing the reducer does — 'Pending', not
    -- 'Discharged'. See @HAZARDS.md@ and @Thena.Core.TrustedTests@.
  , testCase "a yes that owes a level obligation is pending, not discharged" $
      fst (classify env [] 900 (metaLevel 801) (metaLevel 802)) @?= Pending

    -- **A variable is flexible here, which is the opposite of what
    -- unification means by it.** @b@ is a definition's own binder and is
    -- instantiated at every use, so a clash against it settles nothing.
  , testCase "a variable in the clashing position is pending, never hopeless" $
      classedOpen (open2 "Eq {0} Nat a b") (open2 "Eq {0} Nat a a") @?= Pending

    -- η relates a λ with a spine, and this module declines rather than
    -- reimplementing it: the cost of a wrong /impossible/ is a refused proof.
  , testCase "a \955 against something else declines rather than guessing" $
      classed (term "\955 (A : Type\8320) -> A") (term "Nat") @?= Pending

    -- **WHERE THE LEVEL TEST STOPS, AND IT IS THE WHOLE OF WHY IT IS SAFE**
    -- (MS8 phase 166). A closed level cannot change, so two closed levels that
    -- differ are a permanent clash — that is the pair in 'pairs'. A level that
    -- is still a parameter is instantiated at a use exactly as a term binder
    -- is, so the same two universes answer 'Pending' the moment one of them
    -- carries a variable. The two tests below are the same shape as that pair
    -- with one level opened, and they are what stops a wrong /impossible/ from
    -- refusing a sound proof.
  , testCase "a universe level that is still a parameter is pending" $
      classed (Universe (LVar (LRigid 900))) (term "Type\8321") @?= Pending
  , testCase "a parameter in the former's level argument is pending too" $
      classed (atLevel (LVar (LRigid 900)) (term "Eq {1} Nat zero zero"))
              (term "Eq {0} Nat zero zero")
        @?= Pending
  , testCase "and a parameter in a constructor's level argument as well" $
      classed (atLevel (LVar (LRigid 900)) (term "refl {1} Nat zero"))
              (term "refl {0} Nat zero")
        @?= Pending
  ]
  where
    metaLevel k = Universe (LVar (LMeta k))

-- | The same head at a different level argument, reaching through an
-- application spine to find it.
--
-- **Two constructors carry a level argument and both are reached from here** —
-- a 'Canonical', which is a saturated constructor, and a 'Global', which is
-- what a datatype former applied to its arguments has at its head. A fixture
-- with neither is a bug in the fixture, so it stops the suite.
atLevel :: Level -> Core -> Core
atLevel l = go
  where
    go t = case t of
      Canonical g _ as -> Canonical g [l] as
      Global g _       -> Global g [l]
      App f x          -> App (go f) x
      _ -> error "fixture has no level argument to move"

-- | Does the reducer contract this node away?
contracts :: Core -> Core -> Bool
contracts claimed actual =
  whnf env [] (Trusted claimed actual body) /= Trusted claimed actual body
  where
    body = term "refl {0} Nat zero"

positional :: [TestTree]
positional =
  [ -- **His worked example, and the assertion that makes it a test of /deep/.**
    -- A head-only comparison passes on this pair, so a shallow implementation
    -- would answer 'Pending' and the undischargeable case would be unreachable.
    testCase "the heads agree, so a head-only test would miss the clash" $ do
      let claimed = term "Eq {0} Nat zero (succ zero)"
          actual  = term "Eq {0} Nat zero zero"
      assertBool "the fixture clashes at its head, so it tests nothing"
        (headOf claimed == headOf actual)
      classed claimed actual @?= Undischargeable

    -- **δ at every position and not only at the top.** These differ at argument
    -- 1 only through an alias and at argument 3 by two variables, so a
    -- recursion that compared syntactically would call @Alias@ against @Nat@ a
    -- clash and report an open claim as impossible.
  , testCase "an alias deep in the arguments is unfolded before it is judged" $ do
      assertBool "the fixture is \945-equal at argument 1, so it tests nothing"
        (term "Alias" /= term "Nat")
      classedOpen (open2 "Eq {0} Alias zero a") (open2 "Eq {0} Nat zero b")
        @?= Pending
  ]
  where
    headOf (App f _) = headOf f
    headOf t         = t

-- --------------------------------------------------------------------------
-- The walk
-- --------------------------------------------------------------------------

walk :: [TestTree]
walk =
  [ testCase "a term that rests on nothing rests on nothing" $
      rests (term "plain") @?= []

    -- A node standing in the term under examination is read as written, with
    -- nothing of any use substituted in — his /\"a node in the term itself
    -- answers definition site\"/.
  , testCase "a node written here is read here" $
      verdicts (rests (Trusted (term "Empty {0}") (term "Eq {0} Nat zero zero")
                               (term "refl {0} Nat zero")))
        @?= [([], AtDefinition, Undischargeable)]

    -- **THE MEASURED CASE — his, 2026-10-06.** The same node, twice, and the
    -- two verdicts disagree. This is the whole reason the accounting classifies
    -- at the use site where it can.
    --
    -- **His word for the definition-site verdict is /dischargeable/, and the
    -- class it names is 'Pending'.** @Eq Nat a b@ against @Eq Nat a a@ with the
    -- definition's own two binders is not convertible — so the claim is not
    -- /met/ — and neither position is a closed former, so nothing says it never
    -- can be. @cheatNat zero zero@ is the instance where it is.
  , testCase "the definition's own claim is open, not met and not impossible" $
      verdicts (rests (term "cheatNat"))
        @?= [(["cheatNat"], AtDefinition, Pending)]
  , testCase "and the very same node at a saturated use is a lie" $
      verdicts (rests (term "cheatNat zero (succ zero)"))
        @?= [(["cheatNat"], AtUse, Undischargeable)]
    -- The honest instance of the same use, so the use-site verdict is not
    -- simply /undischargeable whenever anything was substituted/.
  , testCase "a saturated use that is honestly true is discharged at the use" $
      verdicts (rests (term "cheatNat zero zero"))
        @?= [(["cheatNat"], AtUse, Discharged)]

    -- **Arity, which is the one place the walk earns a comment.** A partial
    -- application leaves a λ standing, so the instance is not determined and a
    -- verdict read off it would be a verdict about an argument nobody passed.
  , testCase "a partial application answers the definition site" $
      verdicts (rests (term "cheatNat zero"))
        @?= [(["cheatNat"], AtDefinition, Pending)]

    -- **A use reached through another definition answers the definition site**
    -- — his, and it is what keeps this a one-hop walk rather than a
    -- normaliser. @through@'s body holds a saturated @cheatNat@ spine, and the
    -- arguments are not threaded a second time.
    --
    -- **So the lie is invisible from here, by design, and this test exists to
    -- stop anybody \"fixing\" that.** @through zero@ really does rest on
    -- @Eq Nat zero (succ zero)@, and chasing it would mean threading arguments
    -- through every hop — which is full normalisation, refused outright and able
    -- to diverge in @qed@'s path. **It is also exactly why
    -- 'NoUndischargeableTrust' is not a soundness guarantee**: the rung admits
    -- this, and the measured proof of @Empty@ is one hop away from looking like
    -- it.
  , testCase "a use reached through another definition is not threaded again" $
      verdicts (rests (term "through zero"))
        @?= [(["through", "cheatNat"], AtDefinition, Pending)]

    -- Reported once however often it is mentioned: the same verdict twice is
    -- the walk talking about itself.
  , testCase "a definition mentioned twice is reported once" $
      length (rests (term "Eq {0} (Alias) (cheatNat zero) (cheatNat zero)"))
        @?= 1

    -- The walk opens every binder it descends under, and a variable it minted
    -- is printed inside a claim — so §7.4's counter must come back advanced.
  , testCase "the counter comes back past what the report shows" $
      assertBool "the counter did not move"
        (snd (trustIn env [] eqNatCounter (term "cheatNat")) > eqNatCounter)
  ]
  where
    verdicts cs =
      [ ([ g | GlobalName g <- claimRoute c ], claimSite c, claimClass c)
      | c <- cs
      ]

-- --------------------------------------------------------------------------
-- The level
-- --------------------------------------------------------------------------

rungs :: [TestTree]
rungs =
  [ -- **'NoTrust' admits a discharged claim, and that is not a hole in the
    -- guarantee**: the two types are convertible, so the body already has the
    -- type the node claims and the trust is carrying nothing at all. What the
    -- rung refuses is every claim that is doing work.
    testCase "no trust still admits a claim that is carrying nothing" $
      map (permits NoTrust) everyClass @?= [True, False, False]
  , testCase "no undischargeable trust refuses only the impossible" $
      map (permits NoUndischargeableTrust) everyClass @?= [True, True, False]
  , testCase "any trust refuses nothing" $
      map (permits AnyTrust) everyClass @?= [True, True, True]
  ]
  where
    everyClass = [Discharged, Pending, Undischargeable]
