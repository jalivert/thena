-- | The prelude's products, and what the no-confusion generator does with them
-- (phase 20).
--
-- @examples\/products.thena.script@ is the deliverable: @Sigma@ with its projections,
-- @And@ with its own, and §3.7's no-confusion table at @Type₀@ where phase 14
-- had to write it in continuation-passing style at @Type₁@. Loaded the way
-- phase 11 loads any file, and for 'Thena.DeterminacyTests'\'s reason — the
-- golden is what the kernel admitted, not a transcript of the moves.
--
-- The unit cases beside it pin the two things a golden cannot say: that
-- @snd@\'s type really does depend on @fst@, and that the generator's
-- precondition is asked per datatype.
module Thena.ProductTests (tests) where

import Data.ByteString.Builder (stringUtf8, toLazyByteString)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Term (GlobalName (..))
import Thena.Driver (Session (..))
import Thena.Engine (Machine (..))
import Thena.Global.Env (Definition (..), lookupDefinition)
import Thena.Repl (startingSession, loadFile, renderCore)

target :: FilePath
target = "examples/products.thena.script"

tests :: TestTree
tests =
  testGroup
    "the prelude's products (phase 20)"
    [ goldenVsString "products" "test/golden/products.golden" $ do
        (s, problems) <- startingSession
        (_, out, _) <- loadFile s target
        pure (toLazyByteString (stringUtf8 (unlines (problems ++ out))))

    , testCase "the file runs to the end" $ do
        (s, _) <- startingSession
        (_, _, stopped) <- loadFile s target
        stopped @?= []

      -- The whole point of a *dependent* pair, and the one thing that would
      -- still typecheck if @Sigma@ were the non-dependent @And@ under another
      -- name: @snd@'s result type mentions @fst@ applied to the same pair, so
      -- the method's @b : B a@ is accepted only because
      -- @fst A B (pair A B a b)@ δ-then-ι-reduces to @a@.
    , statementOf "snd"
        "∀ (A : Type₀) (B : A -> Type₀) (s : Sigma A B) -> B (fst A B s)"

      -- @Sigma@ is exactly the shape 'Thena.Global.NoConfusion.dependentArgument'
      -- refuses — @b@'s type mentions @a@ — so the prelude declares a type that
      -- gets no lemma. Deliberate, and the reason @And@ is a separate
      -- declaration rather than @Sigma A (λ _ . B)@: @And@ keeps its lemma.
    , declares "NoConfusionAnd" True
    , declares "NoConfusionSigma" False
    ]
  where
    statementOf g ty = testCase ("the prelude's " ++ g ++ " has its dependent type") $ do
      (s, _) <- startingSession
      case lookupDefinition (GlobalName g) (globals (sessionMachine s)) of
        Nothing -> assertFailure (g ++ " is not in the prelude")
        Just d  -> renderCore (names (sessionMachine s)) [] (definitionType d) @?= ty

    declares g want =
      testCase (g ++ (if want then " is generated" else " is not")) $ do
        (s, _) <- startingSession
        let there = lookupDefinition (GlobalName g) (globals (sessionMachine s))
        (there /= Nothing) @?= want
