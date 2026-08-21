-- | Commands: what they compile to, what they refuse, and where they leave the
-- session.
module Thena.DriverTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Term (Core (..), Ident (..), Level (..))
import Thena.Development.Component (Component (..))
import Thena.Development.Partial (Partial (..))
import Thena.Driver
  ( CommandError (..)
  , Response (..)
  , Session (..)
  , Stop (..)
  , answer
  , command
  , newSession
  )
import Thena.Development.Cursor (rebuild)
import Thena.Engine (Machine (..), Question (..), proof, proofDevelopment)
import Thena.Errors (FailReason (..))
import Thena.Ops (AnswerKind (..))

-- | Run a script of command lines, answering nothing, and give back the last
-- response and the session it left.
say :: [String] -> (Session, Response)
say = foldl next (newSession, Blank)
  where
    next (s, _) l = command s l

devOf :: Session -> Partial
devOf = proofDevelopment . proof . sessionMachine

tests :: TestTree
tests =
  testGroup
    "Thena.Driver"
    [ testGroup
        "the command line"
        [ testCase "an empty line does nothing" $
            snd (command newSession "") @?= Blank
        , testCase ":quit leaves the loop" $
            snd (command newSession ":quit") @?= Quit
        , testCase "an unknown word is not a term, it is a mistake" $
            snd (command newSession "hello") @?= Rejected (NoSuchCommand "hello")
        , testCase "a command that merely starts with :core is not :core" $
            snd (command newSession ":corex") @?= Rejected (NoSuchCommand ":corex")
        , testCase "a view command with no argument says so" $
            snd (command newSession ":core") @?= Rejected (MissingArgument ":core")
        , testCase "cross must say which field" $
            snd (command newSession "cross") @?= Rejected (MissingArgument "cross")
        , testCase "and it must be one of the two there are" $
            snd (command newSession "cross body") @?= Rejected (UnexpectedArgument "cross")
        , testCase "a positional descent needs a number" $
            snd (command newSession "param") @?= Rejected (MissingArgument "param")
        , testCase "and it has to be one" $
            snd (command newSession "param x") @?= Rejected (UnexpectedArgument "param")
        , testCase "a plain descent takes no argument" $
            snd (command newSession "cod 2") @?= Rejected (UnexpectedArgument "cod")
        , testCase ":where answers with the cursor, not with text" $
            case snd (command newSession ":where") of
              Where _ -> pure ()
              other   -> assertFailure ("expected Where, got " ++ show other)
        , testCase ":show takes no argument" $
            snd (command newSession ":show x") @?= Rejected (UnexpectedArgument ":show")
        , testCase ":step takes on, off, or nothing" $
            snd (command newSession ":step sideways") @?= Rejected (UnexpectedArgument ":step")
        ]
    , testGroup
        "views"
        [ testCase ":core resolves a term" $
            case snd (command newSession ":core λ (x : Type₀) -> x") of
              Rendered _ -> pure ()
              other      -> assertFailure ("expected Rendered, got " ++ show other)
        , testCase ":core reports a scope error" $
            case snd (command newSession ":core y") of
              Failed _ -> pure ()
              other    -> assertFailure ("expected Failed, got " ++ show other)
        , testCase ":core sees what the development binds" $
            -- The whole reason a view command takes the development's context.
            case snd (say ["assume A : Type₀", ":core A"]) of
              Rendered _ -> pure ()
              other      -> assertFailure ("expected Rendered, got " ++ show other)
        , testCase ":dev resolves a development" $
            case snd (command newSession ":dev let ? h : Type₀ in h") of
              RenderedDev _ -> pure ()
              other         -> assertFailure ("expected RenderedDev, got " ++ show other)
        , testCase ":core rejects a hole, which is development-only" $
            case snd (command newSession ":core let ? h : Type₀ in h") of
              Failed _ -> pure ()
              other    -> assertFailure ("expected Failed, got " ++ show other)
        , testCase ":show renders the development the machine holds" $
            case snd (say ["assume A : Type₀", ":show"]) of
              Shown c | Under (Assume _ (Ident "A") _) _ <- rebuild c -> pure ()
              other -> assertFailure ("expected the assumption, got " ++ show other)
        ]
    , testGroup
        "commands that run"
        [ testCase "assume changes the development, through the machine" $
            case devOf (fst (say ["assume A : Type₀"])) of
              Under (Assume _ (Ident "A") _) (Under Claim {} (Trailing _)) -> pure ()
              other -> assertFailure ("wrong shape: " ++ show other)
        , testCase "and says so" $
            snd (say ["assume A : Type₀"]) @?= Ran ["assumed A"] Completed
        , testCase "claim says so in its own words" $
            snd (say ["claim h : Type₀"]) @?= Ran ["claimed h"] Completed
        , testCase "a nameless assume asks, quoting the type as written" $
            case snd (say ["assume : Type₀"]) of
              Ran [] (Waiting (Question p k)) ->
                (p, k) @?= ("name for the assumption? it will have type Type₀", AName)
              other -> assertFailure ("expected a question, got " ++ show other)
        , testCase "the answer is used, and the message is built from it" $
            let (s, _) = say ["assume : Type₀"]
             in snd (answer s "B") @?= Ran ["assumed B"] Completed
        , testCase "and the binder carries the answered name" $
            let (s, _) = say ["assume : Type₀"]
             in case devOf (fst (answer s "B")) of
                  Under (Assume _ (Ident "B") _) _ -> pure ()
                  other -> assertFailure ("wrong shape: " ++ show other)
        , testCase "an answer that is not a name gets stuck, and keeps the machine" $
            let (s, _) = say ["assume : Type₀"]
             in snd (answer s "let") @?= Ran [] (Halted (NotAnIdentifier "let"))
        , testCase "answering when nothing was asked is refused" $
            snd (answer newSession "B") @?= Rejected NotAsking
        , testCase "assume needs a type" $
            case snd (command newSession "assume A") of
              Failed _ -> pure ()
              other    -> assertFailure ("expected Failed, got " ++ show other)
        , testCase "assume resolves its type in the development's context" $
            case snd (say ["assume A : Type₀", "assume x : A"]) of
              Ran ["assumed x"] Completed -> pure ()
              other -> assertFailure ("expected success, got " ++ show other)
        ]
    , testGroup
        "the goal"
        [ testCase ":goal claims a new one, in context" $
            case snd (say ["assume A : Type₀", ":goal A -> A"]) of
              Shown c
                | Under Assume {} (Under (Claim _ (Ident "goal") _) (Trailing _)) <-
                    rebuild c -> pure ()
              other -> assertFailure ("wrong shape: " ++ show other)
        , testCase ":goal replaces the old one rather than stacking" $
            case devOf (fst (say [":goal Type₀", ":goal Type₁"])) of
              Under (Claim _ _ ty) (Trailing _) -> ty @?= Universe (Level 1)
              other -> assertFailure ("wrong shape: " ++ show other)
        , testCase "an assumption made later still lands outside the goal" $
            case devOf (fst (say [":goal Type₀", "assume A : Type₀"])) of
              Under Assume {} (Under Claim {} (Trailing _)) -> pure ()
              other -> assertFailure ("wrong shape: " ++ show other)
        ]
    , testGroup
        "stepping"
        [ testCase ":step on makes a command stop after one instruction" $
            case snd (say [":step on", "assume A : Type₀"]) of
              Ran [] Paused -> pure ()
              other         -> assertFailure ("expected Paused, got " ++ show other)
        , testCase "and :step takes the next one" $
            case snd (say [":step on", "assume A : Type₀", ":step"]) of
              Ran ["assumed A"] Paused -> pure ()
              other -> assertFailure ("expected the message, got " ++ show other)
        , testCase ":run finishes the program whatever the mode" $
            case snd (say [":step on", "assume A : Type₀", ":run"]) of
              Ran ["assumed A"] Completed -> pure ()
              other -> assertFailure ("expected Completed, got " ++ show other)
        , testCase ":step off puts it back" $
            case snd (say [":step on", ":step off", "assume A : Type₀"]) of
              Ran ["assumed A"] Completed -> pure ()
              other -> assertFailure ("expected Completed, got " ++ show other)
        , testCase "stepping is a session setting and does not touch the machine" $
            sessionStepping (fst (say [":step on"])) @?= True
        ]
    ]
