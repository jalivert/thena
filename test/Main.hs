module Main (main) where

import Test.Tasty (defaultMain, testGroup)

import qualified Thena.Core.TermTests
import qualified Thena.DriverTests

main :: IO ()
main =
  defaultMain $
    testGroup
      "thena"
      [ Thena.Core.TermTests.tests
      , Thena.DriverTests.tests
      ]
