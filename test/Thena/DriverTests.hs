module Thena.DriverTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

import Thena.Driver (Response (..), command, newSession)

tests :: TestTree
tests =
  testGroup
    "Thena.Driver"
    [ testCase ":quit leaves the loop" $
        snd (command newSession ":quit") @?= Quit
    , testCase "any other line is echoed" $
        snd (command newSession "hello") @?= Echoed "hello"
    , testCase "a line that merely starts with a colon is not a command" $
        snd (command newSession ":quitter") @?= Echoed ":quitter"
    ]
