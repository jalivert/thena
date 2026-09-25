-- | The surface term display (MS7 phase 115h).
--
-- **The test is the whole argument for the design, same as every phase
-- before it.** 'Thena.Protocol.Redraw.redrawSurface' is what an editor
-- would be: it takes only a 'SurfaceShape' — no grammars, no environment,
-- nothing session-shaped (see the module header on 'Thena.Protocol.Surface'
-- for why there is nothing else to take) — and produces text. If that text
-- is what 'Thena.Repl.renderSurface' produces for the same tree, the
-- display carries what the printer needs.
--
-- **The corpus is 'Thena.SurfaceTests.genSurface'**, exported there for
-- exactly this reuse (@SurfaceZipperTests@ already walks the same
-- generator, "a second copy of a generator drifts") — real, arbitrarily
-- shaped surface trees, not a hand-built sample.
module Thena.Protocol.SurfaceTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (forAll, testProperty, withNumTests, (===))

import Thena.Protocol.Redraw (redrawSurface)
import Thena.Protocol.Surface (displaySurface)
import Thena.Repl (renderSurface)
import Thena.SurfaceTests (genSurface)

tests :: TestTree
tests =
  testGroup
    "Thena.Protocol.Surface"
    [ testProperty "the display carries everything the printer needed"
        (withNumTests 500 (forAll genSurface prop))
    ]
  where
    prop t = redrawSurface (displaySurface t) === renderSurface t
