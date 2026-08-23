-- | The rule engine, read-only (§7.6, §8).
--
-- This module /finds/ rules. It does not run them: dispatch, the @Choice@
-- frame and backtracking are phase 16's, and the tactics the rules will
-- eventually be are phase 17's. What is here is the part everything else needs
-- first — a rule base in definition order, a persistent iterator over the rules
-- whose heads pass at the focus, and the validation pass that says whether a
-- rule is well formed at all.
--
-- 'Rule' and 'Test' themselves are "Thena.Ops"' — §2.5's layering was wrong and
-- the user corrected it 2026-08-23 (@AGENDA.md@ item 25). The rest of §2.5's
-- listing for this module stands.
module Thena.Rules
  ( -- * The rule base
    RuleBase
  , ruleBase
  , allRules
  , standardRules

    -- * Finding rules (§7.6)
  , RuleIter
  , matches
  , dispatch
  , next
  , hasNext

    -- * Well-formedness (§2.4, §7.2)
  , RuleError (..)
  , validate
  , validateBase
  ) where

import Thena.Core.Reduce (whnf)
import Thena.Core.Term (Core (..), GlobalName (..))
import qualified Thena.Development.Component as Component
import Thena.Development.Cursor (Cursor, Focus (..), context, expectedType, focus)
import Thena.Global.Env (GlobalEnv)
import qualified Thena.Ops as Op
import Thena.Ops
  ( Instr (..)
  , Name
  , Op (..)
  , Operand (..)
  , Rule (..)
  , Test (..)
  , Value (..)
  , hintName
  , produces
  , usesHint
  )
import Thena.Syntax.Concrete (Raw (..))

-- --------------------------------------------------------------------------
-- The rule base
-- --------------------------------------------------------------------------

-- | The rules that exist, **in definition order** — which is dispatch order
-- (§8, DECIDED 2026-08-10). Order is the whole of the structure here, so this
-- is a list and not a map: a lookup by name would lose it.
--
-- It is a field of 'Thena.Engine.Machine' and not of 'Thena.Global.Env', and
-- that is forced: @Thena.Global.Env@ sits below "Thena.Ops", so it cannot
-- mention a 'Rule'. Decided by the user 2026-08-23, who also said where this
-- goes next — *\"Rule-base will eventually be a user-written modules… Eventually
-- we will have a 'rule loading phase' the same way we will be loading
-- user-written modules for theorems and such.\"* MS1 ships 'standardRules' and
-- has no loading phase.
newtype RuleBase = RuleBase [Rule]
  deriving (Eq, Show)

-- | Build a base. Nothing is checked here — 'validateBase' is separate, so that
-- a caller who wants the errors gets them all rather than the first.
ruleBase :: [Rule] -> RuleBase
ruleBase = RuleBase

allRules :: RuleBase -> [Rule]
allRules (RuleBase rs) = rs

-- | MS1's built-in collection: **one rule per bare word the REPL already has
-- for the life of a hole** (thesis tables 2.7 and 2.8).
--
-- Chosen by the user 2026-08-23. The bodies are single ops the driver already
-- compiles and runs for those same words, so no rule body here is speculative —
-- what is new at this phase is the /heads/, and heads are what @:matches@
-- reads. Phase 17 adds the compound tactics; §8's plan that rules eventually
-- come from a written collection is unchanged, and this is that collection
-- written in Haskell because there is no rule syntax yet.
--
-- **Four** match at a hole — @attack@, @try@, @abandon@ and, from phase 17,
-- @eliminate@ — which is what makes the match list a list, and what phase 16
-- dispatches between. @eliminate@ is the first rule here whose body is /not/ a
-- word the driver already had: it is §3.7's tactic, and it is a rule rather
-- than a driver command because §8's whole claim is that a tactic and a rule
-- are the same kind of thing. Like @try@ it takes a parameter, so 'dispatch'
-- skips it and @:matches@ still shows it.
--
-- @intro@ is **two rules and not one**, because table 2.8 has two: @intro-∀@
-- and @intro-let@. §8's \"a rule that wants an alternative is two rules\" is the
-- same principle from the other side.
standardRules :: RuleBase
standardRules = RuleBase
  [ Rule (GlobalName "attack")     []    [FocusIsHole]                 [Do Attack]
  , tryRule
  , Rule (GlobalName "abandon")    []    [FocusIsHole]                 [Do Abandon]
  , Rule (GlobalName "intro-pi")   []    [FocusIsGuess, GoalTypeIsPi]  [Do Intro]
  , Rule (GlobalName "intro-let")  []    [FocusIsGuess, GoalTypeIsLet] [Do Intro]
  , Rule (GlobalName "solve")      []    [FocusIsGuess]                [Do Solve]
  , Rule (GlobalName "regret")     []    [FocusIsGuess]                [Do Regret]
  , Rule (GlobalName "eliminate")  ["t"] [FocusIsHole]                 [Do (Op.Eliminate (Ref "t"))]
  , elabVar
  ]

-- | @try ‹t›@ — table 2.7's @try@, wrapped as a rule.
--
-- Named rather than written inline because 'elabVar' calls it: a body names a
-- rule by writing @Lit (VRule …)@ (§7.2, and the user's answer 2026-08-23), so
-- the Haskell binding /is/ the name until there is a rule syntax to write one
-- in.
tryRule :: Rule
tryRule = Rule (GlobalName "try") ["t"] [FocusIsHole] [Do (Try (Ref "t"))]

-- | MS1's one elaboration rule (§8, phase 17b).
--
-- The hint is a bare identifier; resolve it in the context at the focus, attach
-- it to the goal, and commit. That is §8's own @elab-var@ — /hint is a name in
-- scope, whose body is @try ?y x; solve ?y@/ — written in the instruction
-- language, where the hole is the focus and so is not named.
--
-- **The @try@ step goes through 'Call'**, and that is the phase's point rather
-- than a flourish: @try@ is already a rule with a parameter, so calling it is
-- what finally /supplies/ a 'Thena.Ops.ruleParams' (phase 15 validated the
-- field, phase 16 skipped over it). Writing @Do (Try (Ref "t"))@ inline here
-- would have been one instruction shorter and would have left @Call@ with
-- nothing in MS1 to do.
--
-- **Elaborating a compound hint is not MS1.** §8's @elab-app@ needs
-- 'Thena.Ops.Test'\'s @HintIsApp@ and a way to take an application apart; the
-- milestone implements the identifier case, which is the one it exercises.
elabVar :: Rule
elabVar = Rule (GlobalName "elab-var") [] [FocusIsHole, HintIsName]
  [ Bind "t" (Op.Resolve (Ref hintName))
  , Do (Call (Lit (VRule tryRule)) [Ref "t"])
  , Do Solve
  ]

-- --------------------------------------------------------------------------
-- Finding rules (§7.6)
-- --------------------------------------------------------------------------

-- | The rules still to be offered, in definition order.
--
-- **Persistent, and a lazy list rather than a state-and-step pair** (§7.6). Two
-- things follow that a mutable iterator would not give. A frame may hold one
-- while the UI holds the same one, and advancing either cannot disturb the
-- other. And 'Thena.Engine.Frame' derives @Eq@ and @Show@, which phase 16's
-- @Choice@ constructor needs and which a function inside the iterator would
-- have made impossible.
--
-- Laziness is not a nicety here: 'matches' filters by running heads, heads run
-- 'whnf' (§8), so the tail is real work that 'hasNext' should not do more of
-- than it must.
newtype RuleIter = RuleIter [Rule]
  deriving (Eq, Show)

-- | Every rule whose head passes at the focus, in definition order (§7.6).
--
-- It takes a 'Cursor' rather than a 'Thena.Engine.ProofState' because
-- @ProofState@ is "Thena.Engine"'s and this module sits below it — and it can,
-- since @ProofState@ is a newtype over exactly this cursor. It takes a
-- 'GlobalEnv' because §8's head matching runs 'whnf' and 'whnf' unfolds
-- globals. It needs no name counter: the type a head reads is the one the
-- development /writes down/ ('expectedType'), never one @infer@ derives.
--
-- §7.6's signature is corrected to this.
--
-- **This is a query and nothing more.** No body runs, and nothing is
-- speculatively executed to see whether it would succeed — that is a real
-- feature, a far more expensive one, and it is not MS1 (§2.2, §7.6).
--
-- **A hint partitions the base** — 'Thena.Ops.usesHint', decided by the user
-- 2026-08-23, and the argument is there. It is applied /here/ and not only in
-- 'dispatch' so that the two cannot disagree: @:matches@ would otherwise offer
-- @attack@ under a hint that the engine, dispatching, would never run it for.
-- The consequence at the REPL is that @:matches@ with no argument lists exactly
-- what it listed before this phase, and @:matches ‹hint›@ is a separate
-- question with a separate answer.
matches :: RuleBase -> GlobalEnv -> Cursor -> Maybe Raw -> RuleIter
matches (RuleBase rs) env cur hint =
  RuleIter [ r | r <- rs, usesHint r == isHinted, all (holds env cur hint) (ruleHead r) ]
  where
    isHinted = case hint of
      Just _  -> True
      Nothing -> False

-- | The rules @Prove@ may actually run: 'matches', less the ones it could not
-- supply arguments for.
--
-- **A parameterised rule is @Call@-only** — §8 says @ruleParams@ are "for
-- @Call@" and @Prove@ passes nothing, so a rule with parameters would be
-- dispatched into a body whose first @Ref@ is unbound. Decided by the user
-- 2026-08-23 (@AGENDA.md@ item 34); asking the user for each parameter was the
-- alternative and was declined.
--
-- **'matches' is deliberately not filtered.** The two answer different
-- questions: this one is /what the engine can run/, and 'matches' is /what
-- could be done here/, which includes @try ‹t›@ because the user can type
-- @try x@. @:matches@ keeps showing it.
dispatch :: RuleBase -> GlobalEnv -> Cursor -> Maybe Raw -> RuleIter
dispatch base env cur hint =
  let RuleIter rs = matches base env cur hint
   in RuleIter [ r | r <- rs, null (ruleParams r) ]

next :: RuleIter -> Maybe (Rule, RuleIter)
next (RuleIter rs) = case rs of
  []      -> Nothing
  r : rest -> Just (r, RuleIter rest)

-- | Is there another? Phase 16's peek asks this to decide whether a @Choice@
-- frame is worth building at all (§7.3), so it must not force more of the list
-- than one more head match.
hasNext :: RuleIter -> Bool
hasNext (RuleIter rs) = not (null rs)

-- | One shape question, answered against the focus.
--
-- **The cost of shallow heads, in one concrete case** (§8). @GoalTypeIsPi@ asks
-- about the focused component's own type, so at
-- @? x ≐ (λ A . ? h : Nat . h) : ∀ (A : Type₀) -> Nat@ it passes — the guess's
-- type is a Π — while @intro@ itself would fail, because the hole it actually
-- reaches is at @Nat@. That is §8's stated cost arriving, not a bug: the rule
-- matches, runs and fails in its body, and failing in a body is already handled
-- (§7.3). Asking about the hole at the bottom of the guess instead would make
-- the head a traversal, which is what \"shallow\" rules out.
holds :: GlobalEnv -> Cursor -> Maybe Raw -> Test -> Bool
holds env cur hint t = case t of
  FocusIsHole   -> case focus cur of
    OnComponent (Component.Claim {}) -> True
    _                                -> False
  FocusIsGuess  -> case focus cur of
    OnComponent (Component.Guess {}) -> True
    _                                -> False
  GoalTypeIsPi  -> case reduced of
    Just (Pi {}) -> True
    _            -> False
  -- The one test that does NOT reduce, and it cannot: 'whnf' δ-reduces a
  -- term-level @let@ away (§5.1), so a reduced type is never a 'Let' and this
  -- would be a test that no state can pass. Table 2.8's @intro-let@ reads its
  -- type as written for the same reason, which is the bug this phase found in
  -- 'Thena.Engine' — the two now agree by construction.
  GoalTypeIsLet -> case written of
    Just (Let {}) -> True
    _             -> False
  -- The hint is the tree as parsed, not as resolved: whether the name is in
  -- scope is @resolve@'s answer and it is given in the body, where failing is
  -- ordinary (§7.3). A head that resolved would be doing the work twice and
  -- would be a head that is not shallow (§8).
  HintIsName    -> case hint of
    Just (RawName _) -> True
    _                -> False
  where
    -- Written down, then reduced: §8's "head matching runs whnf", because a
    -- goal typed @id Type₀ (Nat -> Nat)@ is a Π and must match.
    written = expectedType cur
    reduced = whnf env (context cur) <$> written

-- --------------------------------------------------------------------------
-- Well-formedness (§2.4, §7.2)
-- --------------------------------------------------------------------------

-- | Why a rule is not well formed.
--
-- It lives here and not in "Thena.Errors" for that module's own stated reason:
-- @Thena.Errors@ imports nothing above @Core@, and every one of these names an
-- instruction.
data RuleError
  = DeclarationInBody GlobalName Int
    -- ^ @define-data@ named in a rule body — §3.7's line that a declaration is
    -- a command and not a rule-body operation. Carries the rule and the
    -- instruction's position in the body.
  | BoundNonProducing GlobalName Int Name
    -- ^ @x = attack@: a destination on an op that leaves nothing ('produces')
  | UnboundInRule     GlobalName Int Name
    -- ^ a @Ref@ to a name no parameter and no earlier @Bind@ introduced
  deriving (Eq, Show)

-- | The load-time pass (§2.4, §7.2). Three checks, one traversal, **every**
-- error rather than the first.
--
-- §9 asks for the first two. The third is the same walk: the environment a body
-- reads is built entirely by its parameters and its own earlier @Bind@s (§8 —
-- heads bind nothing, because there is no pattern language), so an unbound
-- @Ref@ is decidable here, and catching it at load time is the difference
-- between a rule that cannot be written and one that fails halfway through,
-- having already changed the development.
--
-- What it deliberately does not check: that the ops in a body /apply/ at the
-- states the head admits. That is not decidable shallowly, and §8 already
-- states the answer — a rule may match, run and fail.
validate :: Rule -> [RuleError]
validate r = go 0 (initiallyBound r) (ruleBody r)
  where
    nm = ruleName r

    go _ _ [] = []
    go i bound (instr : rest) =
      let o     = operationOf instr
          errs  = declaration i o ++ binding i instr o ++ scope i bound o
          bound' = case instr of
            Bind n _ -> n : bound
            Do _     -> bound
       in errs ++ go (i + 1) bound' rest

    operationOf instr = case instr of
      Bind _ o -> o
      Do     o -> o

    declaration i o = case o of
      DefineData _ -> [DeclarationInBody nm i]
      _            -> []

    binding i instr o = case instr of
      Bind n _ | not (produces o) -> [BoundNonProducing nm i n]
      _                           -> []

    scope i bound o =
      [ UnboundInRule nm i n | Ref n <- operandsOf o, n `notElem` bound ]

-- | The names a body may read before it binds anything of its own: its
-- parameters, and — when its head asks about the hint — 'Thena.Ops.hintName',
-- which @Prove@ seeds the environment with (§8, phase 17b).
--
-- Without this line 'elabVar' fails its own load-time check, because @hint@ is
-- a 'Ref' that no @Bind@ introduces.
initiallyBound :: Rule -> [Name]
initiallyBound r
  | usesHint r = hintName : ruleParams r
  | otherwise  = ruleParams r

-- | Every operand an op reads. A total case split, so @-Wall@ makes a new op
-- say whether it reads anything.
operandsOf :: Op -> [Operand]
operandsOf o = case o of
  Assume a b   -> [a, b]
  Claim  a b   -> [a, b]
  Ask    a _   -> [a]
  Say    a     -> [a]
  Concat a b   -> [a, b]
  Unify  a b   -> [a, b]
  Try    a     -> [a]
  Certify a    -> [a]
  Op.Eliminate a -> [a]
  Parse   a    -> [a]
  Op.Resolve a -> [a]
  Call r as    -> r : as
  Prove h      -> maybe [] (: []) h
  DefineData _ -> []
  Along        -> []
  Into         -> []
  CrossType    -> []
  CrossValue   -> []
  Down _       -> []
  Back         -> []
  Reduce       -> []
  Attack       -> []
  Intro        -> []
  Regret       -> []
  Solve        -> []
  Abandon      -> []

-- | Every rule in the base, checked. The shipped 'standardRules' is asserted
-- clean by "Thena.RulesTests"; when rules become a file this is what a load
-- runs (§8, and the user's note about a rule-loading phase).
validateBase :: RuleBase -> [RuleError]
validateBase (RuleBase rs) = concatMap validate rs
