module Main (main) where

import Test.Tasty (defaultMain, testGroup)

import qualified Thena.Core.TermTests
import qualified Thena.DevelopmentTests
import qualified Thena.DriverTests
import qualified Thena.EngineTests
import qualified Thena.GoldenTests
import qualified Thena.SyntaxTests

main :: IO ()
main =
  defaultMain $
    testGroup
      "thena"
      [ Thena.Core.TermTests.tests
      , Thena.DevelopmentTests.tests
      , Thena.DriverTests.tests
      , Thena.EngineTests.tests
      , Thena.GoldenTests.tests
      , Thena.SyntaxTests.tests
      ]
