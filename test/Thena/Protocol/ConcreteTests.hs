-- | The as-written trees, through JSON and back (phase 112a).
--
-- **The corpus is the real project**, not a generator: every surface module and
-- every rule file that ships — the prelude, the standard base, and all of
-- @examples\/@. Writing generators for thirty-five mutually recursive syntax
-- types would be a second description of the grammar, and a wrong one would
-- agree with a wrong codec. These files are the same ones the suite already
-- loads, so they are known to parse and known to mean something.
--
-- **What a round trip catches here and does not catch elsewhere.** The two
-- directions are hand-written per constructor, so a field dropped by 'toJson'
-- cannot be put back by 'fromJson' and the comparison fails. That is a real
-- check rather than a self-consistent one, which is why the hand-written
-- instances were chosen over deriving. What it does not check is the /shape/ —
-- both sides could agree on a shape nobody else can read — and that is what
-- "Thena.Protocol.JsonTests"'s written-out assertions are for, one layer down.
module Thena.Protocol.ConcreteTests (tests) where

import Data.List (isSuffixOf, sort)
import System.Directory (listDirectory)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase)

import Thena.Driver (Item, parseSurfaceModule, rawRuleDecls)
import Thena.Instral.Concrete (RawDecl)
import Thena.Protocol.Codec (FromJson (..), ToJson (..))
import Thena.Protocol.Concrete ()
import Thena.Protocol.Json (Json, decode, encode)

tests :: TestTree
tests =
  testGroup
    "Thena.Protocol.Concrete"
    [ testCase "every surface module round trips" surfaceCorpus
    , testCase "every rule file round trips" ruleCorpus
    , testCase "and the corpus is not empty" notEmpty
    ]

-- | Every file the project ships, by kind.
corpus :: IO ([FilePath], [FilePath])
corpus = do
  es <- map ("examples/" <>) . sort <$> listDirectory "examples"
  let thena = [p | p <- es, ".thena" `isSuffixOf` p]
      rules = [p | p <- es, ".thena.rules" `isSuffixOf` p]
  pure (thena <> ["prelude/prelude.thena"], rules <> ["rules/standard.thena.rules"])

-- | Encode, print, read, decode — the whole path a saved file takes, not just
-- the codec. A value that encodes but whose text will not parse back is the
-- failure this catches and a codec-only round trip would not.
through :: (ToJson a, FromJson a, Eq a) => a -> Either String Bool
through x =
  case decode (encode (toJson x :: Json)) of
    Left e  -> Left ("the printed JSON did not read back: " <> show e)
    Right j -> case fromJson j of
      Left e   -> Left ("decoding failed: " <> show e)
      Right y  -> Right (y == x)

check :: (ToJson a, FromJson a, Eq a) => FilePath -> a -> IO ()
check p x = case through x of
  Left e      -> assertFailure (p <> ": " <> e)
  Right True  -> pure ()
  Right False -> assertFailure (p <> ": the value came back different")

surfaceCorpus :: IO ()
surfaceCorpus = do
  (ps, _) <- corpus
  mapM_ one ps
  where
    one p = do
      src <- readFile p
      case parseSurfaceModule src of
        Left e -> assertFailure (p <> ": did not parse: " <> take 200 (show e))
        Right (_, items) -> check p (items :: [Item])

ruleCorpus :: IO ()
ruleCorpus = do
  (_, ps) <- corpus
  mapM_ one ps
  where
    one p = do
      src <- readFile p
      case rawRuleDecls src of
        Left e -> assertFailure (p <> ": did not parse: " <> take 200 (show e))
        Right (_, _, ds) -> check p (ds :: [RawDecl])

-- | A corpus that quietly became empty would make both tests above pass while
-- checking nothing — the failure @CLAUDE.md@ records three goldens once having.
notEmpty :: IO ()
notEmpty = do
  (ts, rs) <- corpus
  if length ts >= 5 && not (null rs)
    then pure ()
    else assertFailure ("the corpus is too small: " <> show (length ts, length rs))
