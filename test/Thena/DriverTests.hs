module Thena.DriverTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

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
    , testCase ":core resolves a term" $
        case snd (command newSession ":core λ (x : Type₀) -> x") of
          Rendered _ -> pure ()
          other      -> assertFailure ("expected Rendered, got " ++ show other)
    , testCase ":core reports a scope error" $
        case snd (command newSession ":core y") of
          Failed _ -> pure ()
          other    -> assertFailure ("expected Failed, got " ++ show other)
    , testCase "a command that merely starts with :core is not :core" $
        snd (command newSession ":corex") @?= Echoed ":corex"
    ]
