-- | A module, written back as source and read again ("Thena.View.Source").
--
-- **Text is the only stored form** — his ruling of 2026-09-27 — so saving needs a
-- printer whose output the reader accepts, and this is where that is established
-- rather than assumed. 'Thena.Repl.renderSurface' was written to show a term at
-- the prompt, not to be read back; 'Thena.View.Source.printItem' is built on it.
--
-- **'printItem' and 'printSurfaceModule' had no reader until MS7 phase 125, and
-- no caller either.** \"A printer is only fixed if something reads its output
-- back\" is the standing rule and they were the counterexample: the module's own
-- test module, despite its name, crossed 'renderSurface' and 'renderValue' and
-- never touched them. The corpus walk below was already here for the terms; the
-- module cases reuse it, which is why the printer's reader costs almost nothing
-- now that it is asked for.
module Thena.View.SourceTests (tests) where

import Data.List (isSuffixOf, sort)
import System.Directory (listDirectory)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase)

import Thena.Core.Term (Literal (..))
import Thena.Driver
  ( Item (..)
  , parseSurfaceModule
  , parseSurfaceTerm
  )
import Thena.Instral.Ops (Value (..))
import Thena.Render (renderSurface, renderValue)
import Thena.Language.Reader
  ( Block (..)
  , Production (..)
  , RawRule (..)
  )
import Thena.View.Source (printSurfaceModule)
import Thena.Surface.Concrete
  ( Surface (..)
  , SurfaceConstructor (..)
  , SurfaceData (..)
  )

tests :: TestTree
tests =
  testGroup
    "Thena.View.Source"
    [ testCase "every surface term in the corpus re-parses from its rendering" corpus
    , testCase "every module in the corpus re-parses from its printing" modules
    , testCase "a printed value re-reads, tabs and all" valueReReads
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

-- | @ms6\/CLOSEOUT.md@ 2, asserted rather than assumed.
--
-- **The whole suite passed the moment 'renderValue' was fixed, which is the
-- reason this exists**: nothing in the corpus holds a tab or a non-ASCII
-- character inside a printed value, so the bug was invisible and so was its
-- repair. A printer is only fixed if something reads its output back.
--
-- The crossing is the real reader: the text goes through 'parseSurfaceTerm',
-- not through a second copy of the escaping rules.
valueReReads :: IO ()
valueReReads = mapM_ one ["a\tb", "\8704", "quote \" and \\ back", "\n", "ℓ≐⌜x⌝"]
  where
    one txt = case parseSurfaceTerm (renderValue [] 0 [] (VText txt)) of
      Right (SurfaceLiteral (LString back))
        | back == txt -> pure ()
        | otherwise   -> assertFailure ("came back as " <> show back <> " from " <> show txt)
      other -> assertFailure ("did not re-read " <> show txt <> ": " <> take 120 (show other))

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

-- | The printer's reader, over the same corpus.
--
-- **The claim is the items, not the text.** A printed module lays its items out
-- canonically — one blank line apart, a datatype's constructors indented two —
-- so it is not the file that comes back but the same list of 'Item's, which is
-- what a save has to preserve.
--
-- **Minus the line numbers, and "Thena.View.Source"'s own comment predicted
-- exactly this**: a @language@, @context@ or @judgment@ block records the source
-- line each of its productions and rules was written on, and a printer that lays
-- the block out canonically cannot reproduce them. Nothing outside
-- "Thena.Language.Reader" reads those numbers, so they never reach a session —
-- which is the reason this is a normalisation and not a defect being papered
-- over. They are the two fields @ms7\/CLOSEOUT.md@ 3 is about.
modules :: IO ()
modules = do
  ps <- paths
  bad <- concat <$> mapM one ps
  if null bad
    then pure ()
    else assertFailure (show (length bad) <> " modules did not survive printing:\n" <> unlines bad)
  where
    one p = do
      src <- readFile p
      case parseSurfaceModule src of
        Left e -> pure [p <> ": did not parse: " <> take 120 (show e)]
        Right (nm, items) ->
          case parseSurfaceModule (printSurfaceModule nm items) of
            Left e -> pure [p <> ": its printing did not parse: " <> take 200 (show e)]
            Right (nm', items')
              | nm' /= nm -> pure [p <> ": came back as module " <> nm']
              | map unlined items' /= map unlined items ->
                  pure (p <> ": items differ" : firstDifference (map unlined items) (map unlined items'))
              | otherwise -> pure []
    firstDifference (a : as) (b : bs)
      | a == b = firstDifference as bs
      | otherwise = ["    was:  " <> take 200 (show a), "    came: " <> take 200 (show b)]
    firstDifference as bs = ["    lengths differ: " <> show (length as) <> " vs " <> show (length bs)]

-- | An item with every recorded source line set to zero.
unlined :: Item -> Item
unlined i = case i of
  ItemGrammar b ->
    ItemGrammar
      b
        { blockProductions = [ pr { productionLine = 0 } | pr <- blockProductions b ]
        , blockRules = [ r { ruleLine = 0 } | r <- blockRules b ]
        }
  other -> other
