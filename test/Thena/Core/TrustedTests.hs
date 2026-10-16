-- | The trusted core term, @trusted claimed actual body@ (MS8 phase 149).
--
-- **What is under test is a gap and the one thing that closes it.** The typing
-- rule gives the node the type it /claims/ and relates that to nothing, so
-- @trusted Empty (Eq Nat zero zero) (refl Nat zero)@ is a well-typed proof of
-- @Empty@ — stated below as a test, because it is the feature and not a defect.
-- What closes the gap is 'whnf''s contraction: the node disappears exactly when
-- the claim and the body's own type turn out to be convertible.
--
-- **Three of these tests are the ones that would catch a wrong design.**
--
--   * /the contraction decides full convertibility/ — the claim and the body's
--     type are α-different and δ-equal, so a syntactic test would leave the
--     node standing. His ruling of 2026-10-05 is that 'convert' decides it.
--   * /a comparison that owes a level obligation does not fire/ — 'whnf'
--     returns a bare 'Core' and has nowhere to put an obligation, and this is
--     the one site in the system where 'convert' is called without a collector,
--     so acting on a verdict that owed one would drop it past every later pass
--     including @certify@'s. See @HAZARDS.md@.
--   * /the body is held to @actual@/ — @actual@ is derived data, and if nothing
--     checked it against the body a substitution could leave the recorded type
--     no longer describing the recorded term, which is the contraction firing
--     on a lie.
--
-- The 'Core' fixtures are **parsed**, through the real reader in the real
-- environment, and only the 'Trusted' node itself is built by hand — there is
-- no surface syntax for it until phase 150.
module Thena.Core.TrustedTests (tests) where

import Data.Either (isLeft)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))

import Thena.Core.Context (Context)
import Thena.Core.Convert (convert)
import Thena.Core.Level (Level (..), LevelVar (..))
import Thena.Core.Reduce (whnf)
import Thena.Core.Term (Core (..), GlobalName (..))
import Thena.Core.Typing (infer)
import Thena.Development.Cursor
  ( Cursor
  , Part (..)
  , back
  , down
  , enter
  , focus
  , Focus (..)
  , rebuild
  )
import Thena.Development.Partial (Partial (..))
import Thena.Driver (parseCore)
import Thena.Global.Env
  ( Definition (..)
  , GlobalEnv
  , addDefinition
  )
import Thena.Render (Rendering (..), renderCore)

import Thena.Declared (eqNat, eqNatCounter)

-- --------------------------------------------------------------------------
-- Fixtures
-- --------------------------------------------------------------------------

-- | The prelude and @Nat@, plus one alias — @Alias@ is @Nat@ with a body, so δ
-- relates two types that are not α-equal. That is the whole purpose of it.
env :: GlobalEnv
env =
  addDefinition
    (GlobalName "Alias")
    MkDefinition
      { definitionLevels = []
      , definitionConstraints = []
      , definitionType = Universe LZero
      , definitionBody = core eqNat "Nat"
      }
    eqNat

ctx :: Context
ctx = []

-- | Read a core term in an environment. A fixture that will not parse is a bug
-- in the fixture, so it stops the suite rather than failing a test about
-- something else.
core :: GlobalEnv -> String -> Core
core e src = case parseCore [] e ctx eqNatCounter src of
  Left err     -> error ("fixture does not parse: " ++ show err)
  Right (t, _) -> t

eqZeroZero, eqZeroOne, eqOneOne, eqZeroZeroAliased, reflZero, zero, empty :: Core
eqZeroZero        = core env "Eq {0} Nat zero zero"
eqZeroOne         = core env "Eq {0} Nat zero (succ zero)"
eqOneOne          = core env "Eq {0} Nat (succ zero) (succ zero)"
eqZeroZeroAliased = core env "Eq {0} Alias zero zero"
reflZero          = core env "refl {0} Nat zero"
zero              = core env "zero"
empty             = core env "Empty {0}"

-- | @trusted claimed actual body@, with the body always @refl {0} Nat zero@ and
-- so always of type @Eq {0} Nat zero zero@.
trustedRefl :: Core -> Core -> Core
trustedRefl claimed actual = Trusted claimed actual reflZero

reduced :: Core -> Core
reduced = whnf env ctx

typeOf :: Core -> Either String Core
typeOf t = case infer env ctx eqNatCounter t of
  (Left e, _, _)   -> Left (show e)
  (Right ty, _, _) -> Right ty

tests :: TestTree
tests =
  testGroup
    "a trusted core term"
    [ testGroup "the typing rule, and the gap in it" typing
    , testGroup "the contraction" contraction
    , testGroup "two stuck nodes compare field by field" congruence
    , testGroup "it prints with both halves of the pair" printing
    , testGroup "the cursor reaches all three fields" cursor
    ]

-- --------------------------------------------------------------------------
-- Typing
-- --------------------------------------------------------------------------

typing :: [TestTree]
typing =
  [ testCase "the node has the type it claims, not the one its body has" $
      typeOf (trustedRefl eqZeroOne eqZeroZero) @?= Right eqZeroOne

    -- **The feature, said out loud.** Verification is modulo the trusted claims
    -- a development rests on; phase 151 makes them visible rather than safe.
  , testCase "so a trusted term proves Empty, and that is the deal" $
      typeOf (trustedRefl empty eqZeroZero) @?= Right empty

    -- @actual@ is derived data and this is what holds it to the body.
  , testCase "but the body must really have the type recorded as actual" $
      assertBool "a wrong actual was accepted"
        (isLeft (typeOf (trustedRefl eqZeroOne eqZeroOne)))

  , testCase "and the claim must be a type" $
      assertBool "a claim that is not a type was accepted"
        (isLeft (typeOf (trustedRefl zero eqZeroZero)))

  , testCase "as must the recorded type of the body" $
      assertBool "an actual that is not a type was accepted"
        (isLeft (typeOf (Trusted eqZeroZero zero zero)))
  ]

-- --------------------------------------------------------------------------
-- The contraction
-- --------------------------------------------------------------------------

contraction :: [TestTree]
contraction =
  [ testCase "it unwraps when the two types are the same type" $
      reduced (trustedRefl eqZeroZero eqZeroZero) @?= reduced reflZero

  , testCase "and stands as a value when they are not" $
      reduced (trustedRefl eqZeroOne eqZeroZero) @?= trustedRefl eqZeroOne eqZeroZero

    -- **The ruling of 2026-10-05**: the side condition is full convertibility,
    -- decided by 'convert'. These two types are δ-equal and not α-equal, so a
    -- syntactic test — which is all the α fast path is — would leave the node
    -- standing.
  , testCase "the two types are compared by conversion and not syntactically" $ do
      assertBool "the fixture is α-equal, so it tests nothing"
        (eqZeroZero /= eqZeroZeroAliased)
      reduced (trustedRefl eqZeroZero eqZeroZeroAliased) @?= reduced reflZero

    -- **The hazard, pinned.** @convert@ answers /yes/ here and owes two level
    -- obligations for it; 'whnf' has no collector, so it must decline. Nothing
    -- is lost by declining — a node left standing is still well typed.
  , testCase "a verdict that owes a level obligation is not acted on" $ do
      let metaLevel k = Universe (LVar (LMeta k))
          owed = case convert env ctx 900 (metaLevel 801) (metaLevel 802) of
            (verdict, obligations, _) -> (verdict == Nothing, null obligations)
      owed @?= (True, False)   -- convertible, and it owes something for it
      reduced (Trusted (metaLevel 801) (metaLevel 802) zero)
        @?= Trusted (metaLevel 801) (metaLevel 802) zero

    -- It is a head, not a binder: an application of one reduces through it.
  , testCase "an application reduces through a node that unwraps" $
      let idTy = core env "Nat -> Nat"
          idFn = core env "\\ (n : Nat) -> n"
       in reduced (App (Trusted idTy idTy idFn) zero) @?= reduced zero
  ]

-- --------------------------------------------------------------------------
-- Congruence
-- --------------------------------------------------------------------------

-- | Both sides of every pair here are **stuck**, so what is being tested is the
-- comparison of two trusted nodes and never the contraction.
congruence :: [TestTree]
congruence =
  [ testCase "a δ-step inside a field does not make two nodes differ" $
      converts (trustedRefl eqZeroOne eqZeroZero) (trustedRefl eqZeroOne eqZeroZeroAliased)
        @?= True

    -- Two nodes that agree on the claim can still contract at different
    -- moments, so @actual@ is compared and this is why.
  , testCase "but a different actual does" $
      converts (trustedRefl eqZeroOne eqZeroZero) (trustedRefl eqZeroOne eqOneOne)
        @?= False

  , testCase "and a different claim does" $
      converts (trustedRefl eqZeroOne eqZeroZero) (trustedRefl eqOneOne eqZeroZero)
        @?= False
  ]
  where
    converts s t = case convert env ctx eqNatCounter s t of
      (verdict, _, _) -> verdict == Nothing

-- --------------------------------------------------------------------------
-- Printing
-- --------------------------------------------------------------------------

printing :: [TestTree]
printing =
  [ -- **All three, because @actual@ is the half that says whether the trust is
    -- still load-bearing** (his observation, 2026-10-05). A printer showing the
    -- claim alone would hide it.
    testCase "all three operands, in the node's own order" $
      renderCore (Rendering [] eqNatCounter) ctx (trustedRefl eqZeroOne eqZeroZero)
        @?= "trusted (Eq {0} Nat zero (succ zero)) (Eq {0} Nat zero zero) (refl {0} Nat zero)"
  ]

-- --------------------------------------------------------------------------
-- The cursor
-- --------------------------------------------------------------------------

-- | 'Part' and 'TermStep' are derived from 'Core' (§4.2), so a new node owes
-- three descents. There is no surface syntax yet, so @CursorTests@' generated
-- corpus cannot contain one and this is where the three are exercised.
cursor :: [TestTree]
cursor =
  [ testCase "claimed, actual and body are each reachable" $
      map focused [Claimed, Actual, Body] @?= map Just [eqZeroOne, eqZeroZero, reflZero]

  , testCase "and back undoes each descent" $
      map (fmap rebuild . descend) [Claimed, Actual, Body]
        @?= map (const (Just (Trailing node))) [Claimed, Actual, Body]

  , testCase "a part the node does not have is refused" $
      assertBool "a motive was found on a trusted node"
        (isLeft (down Motive 0 start))
  ]
  where
    node  = trustedRefl eqZeroOne eqZeroZero
    start = enter (Trailing node)

    descend :: Part -> Maybe Cursor
    descend part = case down part 0 start of
      Right (c, _) -> either (const Nothing) Just (back c)
      Left _       -> Nothing

    focused part = case down part 0 start of
      Right (c, _) | OnTerm _ _ t <- focus c -> Just t
      _                                     -> Nothing
