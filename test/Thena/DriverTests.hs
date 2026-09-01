-- | Commands: what they compile to, what they refuse, and where they leave the
-- session.
module Thena.DriverTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Level (levelOfNat)
import Thena.Core.Term (Core (..), GlobalName (..), Ident (..))
import Thena.Development.Component (Component (..))
import Thena.Development.Partial (Partial (..))
import Thena.Standard (withRules)
import Thena.Driver
  ( CommandError (..)
  , Response (..)
  , Session (..)
  , Stop (..)
  , answer
  , command
  , commandSummary
  , newSession
  )
import Thena.Development.Cursor (rebuild)
import Thena.Engine (Machine (..), Question (..), globals, development, flatten)
import Thena.Errors (FailReason (..))
import Thena.Global.Declare (DeclareError (..))
import Thena.Global.Env (isDeclared)
import Thena.Ops (AnswerKind (..), partWords)

-- | Run a script of command lines, answering nothing, and give back the last
-- response and the session it left.
say :: [String] -> (Session, Response)
say = foldl next (newSession, Blank)
  where
    next (s, _) l = command s l

devOf :: Session -> Partial
devOf = flatten . development . sessionMachine

-- | What is typed to declare the running example. The @data@ word is the
-- command; everything after it is the grammar's (§2.4).
natCommand :: String
natCommand = "data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"

declaredIn :: Session -> String -> Bool
declaredIn s g = isDeclared (GlobalName g) (globals (sessionMachine s))

-- | The words of every spelling @:help@ shows, and those of them that are
-- colon words.
wordsIn :: [(String, String)] -> [String]
wordsIn = concatMap (words . fst)

-- A colon and something: the bare @:@ of @assume \8249x\8250 : \8249S\8250@ is
-- ascription\'s, not a command\'s.
colonWordsIn :: [(String, String)] -> [String]
colonWordsIn = filter (\w -> take 1 w == ":" && length w > 1) . wordsIn

unknown :: String -> Bool
unknown w = case snd (command withRules w) of
  Rejected (NoSuchCommand _) -> True
  _                          -> False

-- | The driver\'s own words, written out. **Hand-written and not total** — no
-- function can enumerate a @case@ — so this is a mirror that has to be kept up
-- by the same hand that adds a command. It is here rather than in the driver
-- because a mirror in the same module as the thing it mirrors checks nothing.
everyColonCommand :: [String]
everyColonCommand =
  [ ":help", ":quit", ":core", ":surface", ":dev", ":show", ":elim", ":where", ":matches"
  , ":choices", ":goal", ":whnf", ":infer", ":load", ":bases", ":rules"
  , ":revalidate", ":extract", ":theorem", ":suspend", ":resume", ":abandon"
  , ":proofs", ":undo", ":convert", ":step", ":run"
  ]

everyBareCommand :: [String]
everyBareCommand =
  [ "assume", "claim", "data", "along", "into", "back", "reduce", "unify"
  , "prove", "retry", "goto", "cross", "certify", "qed"
  ] ++ partWords

tests :: TestTree
tests =
  testGroup
    "Thena.Driver"
    [ testGroup
        "the command line"
        [ testCase "an empty line does nothing" $
            snd (command withRules "") @?= Blank
        , testCase ":quit leaves the loop" $
            snd (command withRules ":quit") @?= Quit
        , testCase "an unknown word is not a term, it is a mistake" $
            snd (command withRules "hello") @?= Ran [] (Halted (NoClauseMatched (GlobalName "hello") 0 []))
        , testCase "a command that merely starts with :core is not :core" $
            snd (command withRules ":corex") @?= Rejected (NoSuchCommand ":corex")
        , testCase "a view command with no argument says so" $
            snd (command withRules ":core") @?= Rejected (MissingArgument ":core")
        , testCase "cross must say which field" $
            snd (command withRules "cross") @?= Rejected (MissingArgument "cross")
        , testCase "and it must be one of the two there are" $
            snd (command withRules "cross body") @?= Rejected (UnexpectedArgument "cross")
        , testCase "a positional descent needs a number" $
            snd (command withRules "param") @?= Rejected (MissingArgument "param")
        , testCase "and it has to be one" $
            snd (command withRules "param x") @?= Rejected (UnexpectedArgument "param")
        , testCase "a plain descent takes no argument" $
            snd (command withRules "cod 2") @?= Rejected (UnexpectedArgument "cod")
        , testCase ":where answers with the cursor, not with text" $
            case snd (command withRules ":where") of
              Where _ -> pure ()
              other   -> assertFailure ("expected Where, got " ++ show other)
        , testCase ":show with an argument is a global, not a mistake" $
            snd (command withRules ":show x") @?= Rejected (NoSuchGlobal "x")
        , testCase ":step takes on, off, or nothing" $
            snd (command withRules ":step sideways") @?= Rejected (UnexpectedArgument ":step")
        ]
    , testGroup
        "the help list"
        -- 'commandSummary' is a second place a command word is written and
        -- 'dispatch' is a @case@, so nothing can derive one from the other.
        -- These three cross them as far as anything can: the first direction
        -- is total, the other two lean on a hand-written list below, exactly
        -- as @RuleSyntaxTests@\' @everyOp@ does and with the same admitted
        -- incompleteness.
        [ testCase "every colon word it lists is a command" $
            filter unknown (colonWordsIn commandSummary) @?= []
        , testCase "every colon command is listed" $
            filter (`notElem` colonWordsIn commandSummary) everyColonCommand @?= []
        , testCase "every bare command the driver has is listed" $
            filter (`notElem` wordsIn commandSummary) everyBareCommand @?= []
        ]
    , testGroup
        "views"
        [ testCase ":core resolves a term" $
            case snd (command withRules ":core λ (x : Type₀) -> x") of
              Rendered _ -> pure ()
              other      -> assertFailure ("expected Rendered, got " ++ show other)
        , testCase ":core reports a scope error" $
            case snd (command withRules ":core y") of
              Failed _ -> pure ()
              other    -> assertFailure ("expected Failed, got " ++ show other)
        , testCase ":core sees what the development binds" $
            -- The whole reason a view command takes the development's context.
            case snd (say ["assume A : Type₀", ":core A"]) of
              Rendered _ -> pure ()
              other      -> assertFailure ("expected Rendered, got " ++ show other)
        , testCase ":dev resolves a development" $
            case snd (command withRules ":dev let ? h : Type₀ in h") of
              RenderedDev _ -> pure ()
              other         -> assertFailure ("expected RenderedDev, got " ++ show other)
        , testCase ":core rejects a hole, which is development-only" $
            case snd (command withRules ":core let ? h : Type₀ in h") of
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
            case snd (command withRules "assume A") of
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
              Under (Claim _ _ ty) (Trailing _) -> ty @?= Universe (levelOfNat 1)
              other -> assertFailure ("wrong shape: " ++ show other)
        , testCase "an assumption made later still lands outside the goal" $
            case devOf (fst (say [":goal Type₀", "assume A : Type₀"])) of
              Under Assume {} (Under Claim {} (Trailing _)) -> pure ()
              other -> assertFailure ("wrong shape: " ++ show other)
        ]
    , testGroup
        "declarations"
        [ testCase "data says what it declared" $
            snd (say [natCommand]) @?= Ran ["declared Nat"] Completed
        , testCase "and the globals hold it afterwards" $
            declaredIn (fst (say [natCommand])) "Nat" @?= True
        , testCase "so do the names it generated" $
            map (declaredIn (fst (say [natCommand]))) ["zero", "succ"] @?= [True, True]
        , testCase "the development is untouched: globals are not Development (§7.4)" $
            devOf (fst (say [natCommand])) @?= devOf newSession
        , testCase "data needs an argument" $
            snd (command withRules "data") @?= Rejected (MissingArgument "data")
        , testCase "a declaration that does not fit the form is a syntax error" $
            case snd (command withRules "data T : Type\8320 where { c }") of
              Failed _ -> pure ()
              other    -> assertFailure ("expected Failed, got " ++ show other)
        , testCase "a declaration the checker refuses stops the run" $
            snd (say [natCommand, "data T : Type\8320 where { c : (T -> T) -> T }"])
              @?= Ran [] (Refused (NotStrictlyPositive (GlobalName "c") (Ident "x")))
        , testCase "and writes nothing" $
            declaredIn (fst (say [natCommand, "data T : Type\8320 where { c : (T -> T) -> T }"])) "T"
              @?= False
        , testCase "while what was already declared survives it" $
            declaredIn (fst (say [natCommand, "data T : Type\8320 where { c : (T -> T) -> T }"])) "Nat"
              @?= True
        , testCase "a refused declaration abandons the rest of the program" $
            case fst (say [natCommand, "data T : Type\8320 where { c : (T -> T) -> T }", ":run"]) of
              s' -> snd (command s' ":run") @?= Ran [] Completed
        , testCase ":show ‹datatype› is the declaration" $
            case snd (say [natCommand, ":show Nat"]) of
              ShownData _ -> pure ()
              other       -> assertFailure ("expected ShownData, got " ++ show other)
        , testCase ":show ‹former› is the generated wrapper, type and body" $
            case snd (say [natCommand, ":show succ"]) of
              ShownGlobal (GlobalName "succ") _ _ _ (Just _) -> pure ()
              other -> assertFailure ("expected ShownGlobal, got " ++ show other)
        , testCase "a global is in scope for an ordinary term" $
            case snd (say [natCommand, ":core succ zero"]) of
              Rendered _ -> pure ()
              other      -> assertFailure ("expected Rendered, got " ++ show other)
        , testCase "and can be assumed at" $
            snd (say [natCommand, "assume n : Nat"]) @?= Ran ["assumed n"] Completed
        , testCase "stepping installs the declaration before it pauses" $
            let s' = fst (say [":step on", natCommand])
             in declaredIn s' "Nat" @?= True
        , testCase "and the message is still to come" $
            snd (say [":step on", natCommand]) @?= Ran [] Paused
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
