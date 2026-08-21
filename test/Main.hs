module Main (main) where

import Test.Tasty (defaultMain, testGroup)

import qualified Thena.DriverTests

main :: IO ()
main =
  defaultMain $
    testGroup
      "thena"
      [ Thena.DriverTests.tests
      ]
