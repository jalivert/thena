module Main (main) where

import Test.Tasty (defaultMain, testGroup)

import qualified Thena.Core.ConvertTests
import qualified Thena.Core.ReduceTests
import qualified Thena.Core.TermTests
import qualified Thena.Core.TypingTests
import qualified Thena.CursorTests
import qualified Thena.DevelopmentTests
import qualified Thena.DriverTests
import qualified Thena.EngineTests
import qualified Thena.GlobalTests
import qualified Thena.GoldenTests
import qualified Thena.SyntaxTests

main :: IO ()
main =
  defaultMain $
    testGroup
      "thena"
      [ Thena.Core.ConvertTests.tests
      , Thena.Core.ReduceTests.tests
      , Thena.Core.TermTests.tests
      , Thena.Core.TypingTests.tests
      , Thena.CursorTests.tests
      , Thena.DevelopmentTests.tests
      , Thena.DriverTests.tests
      , Thena.EngineTests.tests
      , Thena.GlobalTests.tests
      , Thena.GoldenTests.tests
      , Thena.SyntaxTests.tests
      ]
