-- | Does a surface term survive being printed and read back? (phase 112b probe)
--
-- **This is the measurement MS7's fourth done-when rests on.** A project must
-- round-trip through text as well as through JSON, because the textual medium is
-- protected (his standing constraint, `discussion/editor-protocol.md` §4 A3) —
-- and saving as text needs a printer whose output the reader accepts.
--
-- 'Thena.Repl.renderSurface' is the only candidate that exists. It was written to
-- show a term at the prompt, not to be read back, so whether it is faithful is a
-- fact to establish rather than assume.
module Thena.Protocol.TextTests (tests) where

import Data.List (isSuffixOf, sort)
import System.Directory (listDirectory)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase)

import Thena.Driver (Item (..), parseSurfaceModule, parseSurfaceTerm)
import Thena.Repl (renderSurface)
import Thena.Surface.Concrete
  ( Surface
  , SurfaceConstructor (..)
  , SurfaceData (..)
  )

tests :: TestTree
tests =
  testGroup
    "Thena.Protocol.Text"
    [ testCase "every surface term in the corpus re-parses from its rendering" corpus
    , testCase "and the corpus really holds terms" notVacuous
    ]

-- | **A green test over an empty corpus is the failure @CLAUDE.md@ records three
-- goldens once having**, and this one collects its terms through a function that
-- returns @[]@ for two of the four item kinds — so the count is asserted rather
-- than assumed. The number is a floor, not a fact about today.
notVacuous :: IO ()
notVacuous = do
  n <- length . concatMap termsOf . concat <$> (mapM itemsOf =<< paths)
  if n >= 100
    then pure ()
    else assertFailure ("the corpus yielded only " <> show n <> " surface terms")

-- | Every surface term an item carries, at the top level.
termsOf :: Item -> [Surface]
termsOf i = case i of
  ItemTheorem _ ty body -> [ty, body]
  ItemData d ->
    surfaceDataType d
      : map snd (surfaceDataParameters d)
      <> map (\(SurfaceConstructor _ t) -> t) (surfaceDataConstructors d)
  ItemBlock _ -> []
  ItemGrammar _ -> []

-- | Every surface file the project ships.
paths :: IO [FilePath]
paths = do
  es <- map ("examples/" <>) . sort <$> listDirectory "examples"
  pure
    ( [p | p <- es, ".thena" `isSuffixOf` p, not (".thena.rules" `isSuffixOf` p)]
        <> ["prelude/prelude.thena"]
    )

itemsOf :: FilePath -> IO [Item]
itemsOf p = do
  src <- readFile p
  pure (either (const []) snd (parseSurfaceModule src))

corpus :: IO ()
corpus = do
  ps <- paths
  rs <- mapM one ps
  let bad = concat rs
      total = length bad
  if null bad
    then pure ()
    else
      assertFailure
        ( show total
            <> " terms did not survive printing and reading. First few:\n"
            <> unlines (map describe (take 3 bad))
        )
  where
    one p = do
      src <- readFile p
      case parseSurfaceModule src of
        Left e -> pure [(p, "did not parse", take 120 (show e))]
        Right (_, items) ->
          pure
            [ (p, take 150 (show t), take 150 (renderSurface t))
            | t <- concatMap termsOf items
            , parseSurfaceTerm (renderSurface t) /= Right t
            ]
    describe (p, was, ren) = "  " <> p <> "\n    tree: " <> was <> "\n    text: " <> ren
