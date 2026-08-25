-- | The shipped rule base, read off disk, and what it is supposed to say.
--
-- **Two independent encodings of the same nine rules**, which is the whole
-- point. 'standardBases' reads @rules/standard.thena.rules@ through the same
-- path the REPL uses at startup; 'expectedStandard' is the same nine rules as
-- Haskell literals, moved here from @Thena.Rules@ when phase 22 deleted
-- @standardRules@. "Thena.RuleSyntaxTests" asserts they agree.
--
-- Phase 21's load-bearing check was written text against a Haskell literal.
-- Deleting the literal from the library would have left it comparing the file
-- with itself, so the literal moved rather than went — the standing lesson from
-- phases 2–5 about an invariant that must be checked by different code from the
-- code that maintains it.
module Thena.Standard
  ( standardBases
  , standardVisible
  , expectedStandard
  , expectedBase
  ) where

import Thena.Core.Term (GlobalName (..))
import Thena.Driver (Session (..), newSession)
import Thena.Engine (Machine (..))
import Thena.Ops
  ( Instr (..)
  , Op (..)
  , Operand (..)
  , Rule (..)
  , Test (..)
  , hintName
  )
import qualified Thena.Ops as Op
import Thena.Repl (loadStandardRules)
import Thena.Rules (RuleBase (..), allRules, ruleBase)

-- | The shipped base, loaded exactly as @thena@ loads it.
--
-- A failure to load is a fixture failure and errors loudly: every other test
-- that asks for the base would otherwise turn into an unrelated assertion about
-- an empty one. It is also, in itself, the regression that the shipped file
-- parses, resolves and validates.
standardBases :: IO [RuleBase]
standardBases = do
  (s, problems) <- loadStandardRules newSession
  case problems of
    [] -> pure (rules (sessionMachine s))
    ps -> error ("the shipped rule base did not load:\n" ++ unlines ps)

-- | Its rules, flattened — what 'Thena.Rules.resolveRule' wants as the rules
-- visible to a further rule being read.
standardVisible :: IO [Rule]
standardVisible = allRules <$> standardBases

-- | What @rules/standard.thena.rules@ is supposed to contain, in order.
--
-- **One rule per bare word the REPL already has for the life of a hole**
-- (thesis tables 2.7 and 2.8), chosen by the user 2026-08-23. @intro@ is two
-- rules and not one because table 2.8 has two.
expectedStandard :: [Rule]
expectedStandard =
  [ Rule (GlobalName "attack")     []    [FocusIsHole]                 [Do Attack]
  , Rule (GlobalName "try") ["t"] [FocusIsHole] [Do (Try (Ref "t"))]
  , Rule (GlobalName "abandon")    []    [FocusIsHole]                 [Do Abandon]
  , Rule (GlobalName "intro-pi")   []    [FocusIsGuess, GoalTypeIsPi]  [Do Intro]
  , Rule (GlobalName "intro-let")  []    [FocusIsGuess, GoalTypeIsLet] [Do Intro]
  , Rule (GlobalName "solve")      []    [FocusIsGuess]                [Do Solve]
  , Rule (GlobalName "regret")     []    [FocusIsGuess]                [Do Regret]
  , Rule (GlobalName "eliminate")  ["t"] [FocusIsHole]                 [Do (Op.Eliminate (Ref "t"))]
  , elabVar
  ]

-- | 'expectedStandard' as a base, for the suites that want one and do not want
-- IO. They were testing against a Haskell literal before phase 22 and still
-- are; "Thena.RuleSyntaxTests" is where the literal is tied to the file, and
-- "Thena.GoldenTests" is where the file itself is driven.
expectedBase :: [RuleBase]
expectedBase = [ruleBase "standard" Nothing "" expectedStandard]

-- | The one elaboration rule (§8, phase 17b): resolve the hint in the context
-- at the focus, attach it, commit.
elabVar :: Rule
elabVar = Rule (GlobalName "elab-var") [] [FocusIsHole, HintIsName]
  [ Bind "t" (Op.Resolve (Ref hintName))
  , Do (Call (GlobalName "try") [Ref "t"])
  , Do Solve
  ]
