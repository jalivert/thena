-- | The shipped rule base, read off disk, and what it is supposed to say.
--
-- **Two independent encodings of the same ten rules**, which is the whole
-- point. 'standardBases' reads @rules/standard.thena.rules@ through the same
-- path the REPL uses at startup; 'expectedStandard' is the same ten rules as
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
  , withRules
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
  )
import Thena.Ops (Value (VText))
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
  , Rule (GlobalName "try-core") ["t"] [FocusIsHole] [Do (Try (Ref "t"))]
  , Rule (GlobalName "abandon")    []    [FocusIsHole]                 [Do Abandon]
    -- **Two clauses of one name** (phase 23b): table 2.8 has two intro rules and
    -- they differ only in their head, which is exactly what a second clause is
    -- for. Before phase 23 a call could not backtrack, so they had to be
    -- @intro-pi@ and @intro-let@; now they are @intro@, and typing @intro@ at
    -- the REPL reaches whichever one applies.
  , Rule (GlobalName "intro")      []    [FocusIsGuess, GoalTypeIsPi]  [Do (Intro Nothing)]
  , Rule (GlobalName "intro")      []    [FocusIsGuess, GoalTypeIsLet] [Do (Intro Nothing)]
  , Rule (GlobalName "solve")      []    [FocusIsGuess]                [Do Solve]
  , Rule (GlobalName "regret")     []    [FocusIsGuess]                [Do Regret]
  , Rule (GlobalName "eliminate-core")  ["t"] [FocusIsHole]                 [Do (Op.Eliminate (Ref "t"))]
  , proveRule
  , proveGuess
  , elaborateRule
  , fillRule
  , unifyRefine
  , applyRule
  ]

-- | Brady's @FILL@ — **his request, 2026-09-01** (MS4 phase 48):
-- /"Can you maybe add two new tactics @fill@ and @solve@ and define
-- @unify-refine@ with them instead of just replacing @unify-refine@? It is
-- Conor's tactic and I would like to keep it."/
--
-- The @=@-binding is the load-bearing part: the term being refined with does
-- not yet have the goal's type, so it is parked in a definition until
-- unification makes the two converge, and only then attached.
--
-- **@unify-into@ and not @unify@**, which is where this rule and
-- "Thena.Elaborate"\'s inline @fill@ had come apart. Phase 41g gave the
-- elaborator the directed sibling — the term's type need only be /usable/
-- where the goal is wanted, and @prim-try@ on the next line does the real
-- check — and left this rule symmetric, so the same operation answered
-- differently depending on which one you reached it through.
fillRule :: Rule
fillRule = Rule (GlobalName "fill-core") ["t"] [FocusIsHole]
  [ Bind "n" (FreshName (Lit (VText "refined")))
  , Bind "x" (Define (Ref "n") (Ref "t"))
  , Bind "s" (Typing (Ref "x"))
  , Bind "g" Goal
  , Do (Op.UnifyInto (Ref "s") (Ref "g"))
  , Do (Try (Ref "x"))
  ]

-- | Thesis §2.7's two-phase tactic, less the claiming half (which is phase
-- 25's @apply@) and the arity search (phase 27's @fit@).
--
-- **Two calls, and that is the whole rule now** (MS4 phase 48): fill, then
-- discharge. It calls the /rules/ and not the primitives, so the seam Brady
-- needs — @FILL@, the two @FOCUS@es, @SOLVE@ — is one a caller can get at.
unifyRefine :: Rule
unifyRefine = Rule (GlobalName "unify-refine-core") ["t"] [FocusIsHole]
  [ Do (Call (GlobalName "fill-core") [Ref "t"])
  , Do (Call (GlobalName "solve") [])
  ]

-- | Phase 25's claiming half — §2.7's @naive-refine@ with the search left out.
--
-- Two instructions, and that is the phase's argument: @prim-apply@ builds the
-- saturated spine and 'unifyRefine' is what makes it fit, unchanged. @apply@
-- adds no capability the two of them did not already have.
applyRule :: Rule
applyRule = Rule (GlobalName "apply-core") ["f"] [FocusIsHole]
  [ Bind "s" (Op.Apply (Ref "f"))
  , Do (Call (GlobalName "unify-refine-core") [Ref "s"])
  ]

-- | A fresh session with 'expectedBase' installed, for the suites that drive
-- the driver without IO.
--
-- **Needed as of phase 23b**: @attack@, @try@ and @solve@ are rules now, so a
-- session with no base cannot run the commands every REPL test types.
withRules :: Session
withRules =
  newSession { sessionMachine = (sessionMachine newSession) { rules = expectedBase } }

-- | 'expectedStandard' as a base, for the suites that want one and do not want
-- IO. They were testing against a Haskell literal before phase 22 and still
-- are; "Thena.RuleSyntaxTests" is where the literal is tied to the file, and
-- "Thena.GoldenTests" is where the file itself is driven.
expectedBase :: [RuleBase]
expectedBase = [ruleBase "standard" Nothing "" expectedStandard]

-- | Search: every rule whose head passes, in definition order (MS4 phase 41).
--
-- @prove@ is a rule and no longer a special case in the driver — his ruling,
-- 2026-09-01. The op under it is @prim-prove@, the good word having gone to the
-- rule (phase 23b's convention).
--
-- **Two clauses, and that is how the rule language spells a disjunction** —
-- @intro@ has had two for the same reason since phase 15. Search makes sense
-- wherever a component is focused, and there is no single test for /hole or
-- guess/; one clause with @focus-is-hole@ would have made @prove@ silent at a
-- guess, where the base has @intro@, @solve@ and @regret@ waiting, and an
-- empty head would have offered it in the core fragment, where nothing can
-- act at all.
proveRule :: Rule
proveRule = Rule (GlobalName "prove") [] [FocusIsHole] [Do Prove]

proveGuess :: Rule
proveGuess = Rule (GlobalName "prove") [] [FocusIsGuess] [Do Prove]

-- | Elaboration (MS4 phase 41): one clause over the large instruction.
--
-- It replaces @elab-var@, whose head asked about the retired hint and whose
-- body resolved it. Step 2 of the two-step (@MS4.md@) is what turns this into
-- a clause per surface node.
elaborateRule :: Rule
elaborateRule = Rule (GlobalName "elaborate") ["t"] [FocusIsHole]
  [Do (Op.Elaborate (Ref "t"))]
