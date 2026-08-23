-- | The instruction language (§7.2).
--
-- Imperative and assignment-style: a body is a list of instructions, each
-- either binding its result to a name or discarding it. The stepper in
-- "Thena.Engine" is what runs them; nothing here executes anything.
--
-- INCOMPLETE BY DESIGN. §12 invariant 5: the op vocabulary is discovered by
-- writing tactics, not designed up front. Phase 4 has the five ops its two
-- commands need, and every later phase adds the ops its own deliverable
-- exercises.
module Thena.Ops
  ( Name
  , Env
  , Value (..)
  , Operand (..)
  , Instr (..)
  , Op (..)
  , produces
  , Part (..)
  , AnswerKind (..)

    -- * Rules (§8)
  , Rule (..)
  , Test (..)
  ) where

import Thena.Core.Term (GlobalName)
import Thena.Development.Cursor (Part (..))
import Thena.Development.Partial (Partial)
import Thena.Global.Env (InductiveDefinition)
import Thena.Syntax.Concrete (Raw)

-- | A name in a rule body's environment. Not a 'Thena.Core.Term.Var' and not an
-- 'Thena.Core.Term.Ident': those name things in the development, this names an
-- intermediate result inside one body.
type Name = String

-- | What 'Bind' introduces; scoped to the body, and rewound structurally when a
-- frame is popped (§7.5).
type Env = [(Name, Value)]

-- | 'VTerm' is deliberately one case and holds a 'Partial', not a 'Core'
-- (§7.2): a core term is @Trailing t@ and a variable is @Trailing (Free x)@, so
-- there is no separate @VVar@, @VCore@ and @VPartial@ to keep in step. The
-- price is stated once in §7.2 — an op that needs a plain term checks at
-- runtime and fails with 'Thena.Errors.ExpectedTerm' if it does not have one.
--
-- 'VRule' arrives at phase 15, with 'Rule' itself: §7.2's \"rules are values, so
-- 'Call' and higher-order rules fall out\" needs 'Rule' in /this/ module, which
-- is what the user decided 2026-08-23 (@AGENDA.md@ item 25). 'VSurface',
-- 'VPair' and 'VRule' are all on @AGENDA.md@'s standing list of things defined
-- in MS1 and not yet exercised.
data Value
  = VText    String    -- ^ what @Ask@ returns and @Say@ consumes
  | VTerm    Partial   -- ^ a term, a variable, or a whole development
  | VSurface Raw       -- ^ an unelaborated tree — elaboration's input
  | VRule    Rule      -- ^ rules are values, so @Call@ costs no machinery (§8)
  | VPair    Value Value
  deriving (Eq, Show)

data Operand
  = Ref Name  -- ^ read a name bound earlier in this body
  | Lit Value -- ^ a value the compiler or rule author wrote down
  deriving (Eq, Show)

-- | @x = op …@ or @op …@. Binding an op that produces nothing is caught by the
-- load-time validation pass that rules will need anyway (§2.4, §7.2, phase 15);
-- that is what keeps 'Op' free of a @Maybe@.
data Instr
  = Bind Name Op
  | Do   Op
  deriving (Eq, Show)

-- | Phase 4's five, phase 5's six moves, and phase 6's @define-data@.
--
-- @Assume@ is not in §7.2's sketch of this type. It is added here per §12
-- invariant 5, because phase 4's deliverable needs it and the thesis's @intro@
-- (table 2.7) cannot stand in: @intro@ turns a hole whose type is a Π into a λ,
-- and phase 4 has neither @attack@ nor a guess to work under.
--
-- **The moves are ops, not driver commands.** The cursor /is/
-- 'Thena.Engine.ProofState' (§7.2), so moving the focus changes exactly what
-- backtracks — §12 invariant 3's hazard, and the reason §2.4 spells them as
-- bare words. 'Down' takes its 'Part' as a field rather than an 'Operand' for
-- the same reason 'Ask' takes an 'AnswerKind' that way: it is chosen when the
-- instruction is written, not computed while it runs.
data Op
  = Assume Operand Operand    -- ^ name, type — extend the development with @λ x : S@
  | Claim  Operand Operand    -- ^ name, type — extend it with a hole @? x : S@
  | Ask    Operand AnswerKind -- ^ prompt text, and what the frontend should offer
  | Say    Operand            -- ^ message text
  | Concat Operand Operand    -- ^ building prompt and message text
  | Along                     -- ^ past the head of the focus (§4.3)
  | Into                      -- ^ into a guess's body
  | CrossType                 -- ^ into the focused component's type
  | CrossValue                -- ^ into a definition's value
  | Down Part                 -- ^ into a named field of a core term (§4.7)
  | Back                      -- ^ undo the last move
  | Reduce                    -- ^ commit a whnf at the core focus (§4.7, phase 7)
  | Unify Operand Operand     -- ^ two terms — solve holes, or park the equation (§6, phase 9)
  | DefineData InductiveDefinition
    -- ^ hand a declaration out through the channel (§7.5)
    -- The life of a hole — thesis tables 2.7 and 2.8, phase 13. Each acts on
    -- the component at the focus, so none takes a name: §4.0 C1's rule that a
    -- command means one thing wherever it is applies to these too.
  | Attack                    -- ^ @?x : S@ ⟹ @?x ≐ (?x' : S . x') : S@
  | Intro                     -- ^ move a hole through a Π or a @let@ in its type
  | Try     Operand           -- ^ attach a guess to the hole at the focus
  | Regret                    -- ^ discard it again
  | Solve                     -- ^ commit a guess whose body is pure
  | Abandon                   -- ^ drop a hole nothing refers to
  | Prove
    -- ^ dispatch the rule engine at the focus (§7.3, phase 16). It takes no
    -- operand for the same reason the six hole ops take none: it acts at the
    -- focus, and 'Value' has no case for "a hole" — §7.2 refused one twice.
    -- §7.2 and §7.3 sketch it as @Prove goal hint@; the goal is the focus, and
    -- the hint waits for phase 17, where elaboration is.
  | Certify Operand
    -- ^ the development must be pure; yields the closed term it stands for and
    -- the type it is claimed to have, for the driver to run the kernel on
    -- (§7.5, §5.3)
  | Eliminate Operand
    -- ^ the term to eliminate — §3.7's elimination tactic, phase 17. It
    -- generalises the target and its indices in the motive, claims a hole per
    -- constructor above the goal, and attaches the elimination as a guess.
    --
    -- **One coarse op, and deliberately so** (decided 2026-08-23,
    -- @AGENDA.md@ item 35): see "Thena.Tactics.Eliminate"'s header. §7.2's
    -- \"large and small instructions coexist\" is what permits it, and §12
    -- invariant 5 is what makes it the right call — a granular version needs a
    -- term-construction vocabulary nothing else has asked for.
    --
    -- It takes an operand where the six hole ops take none, for 'Try'\'s
    -- reason: the goal is the focus, but the target has nowhere else to come
    -- from.
  deriving (Eq, Show)

-- @Reduce@ is a move, not a value-producing op, for the same reason 'Along'
-- and 'Down' are not (§7.2): it rewrites the cursor and that is the whole of
-- what it does. It differs from the other moves in one way — it can have
-- something worth saying (an orphaned hole, §4.7), which is why
-- "Thena.Engine" answers it with 'Thena.Engine.Saying' rather than always
-- 'Thena.Engine.Continue', the same distinction 'Say' already makes.

-- @Unify@ is §7.2's own sketch, arriving at the phase that writes the unifier.
-- It is an op rather than a driver command for §12 invariant 3's reason: it
-- rewrites 'Thena.Engine.ProofState', so it must backtrack with everything else
-- that does. That is also why §9's @:unify@ is spelled without the colon —
-- §2.4's rule is that a bare word acts and a colon looks, and this acts.
--
-- It takes two terms and no type, and infers the type from the left one: a
-- parked equation records the type it was asked at (§3.3), and phase 8 made
-- inferring it possible where §7.2's sketch could not have.

-- @DefineData@ carries the declaration as a field rather than an 'Operand',
-- for the same reason 'Down' carries a 'Part' and 'Ask' an 'AnswerKind': a
-- datatype is written down, never computed by a body. It is also why 'Value'
-- gains no case here — nothing ever binds a declaration to a name.
--
-- **No instruction writes globals, here or ever** (§7.5, §3.7). This op yields;
-- the driver checks the declaration with "Thena.Global.Declare" and installs
-- it. That is what keeps §3.7's line — @define-data@ is a command, not a
-- rule-body operation — structural rather than a rule someone has to remember.

-- | A hint to the frontend, not a type the machine enforces (§7.5).
--
-- The one predefined vocabulary in the whole instruction language: without
-- knowing what is being asked for, a frontend can offer no help. It is watched
-- so that it does not quietly grow. @ATerm@ and @ARule@ are on @AGENDA.md@'s
-- standing list — MS1's terminal offers no completion, so nothing reads them.
data AnswerKind = AText | AName | ATerm | ARule
  deriving (Eq, Show)

-- @Certify@ produces no value: what it yields goes out through the channel
-- rather than into @env@ (§7.5). It is the third op of that shape, after @Ask@
-- and @DefineData@.
--
-- **It takes one operand where §7.2's sketch took none** — the type the
-- development is claimed to prove. The sketch assumed the term alone was
-- enough, and it is not: §5.3's @certify@ checks a term /against a stated
-- type/, and a development does not in general carry one. Phase 5 settled the
-- same point from the other side — at the top of a development \"nothing is
-- written down, so nothing is claimed\". So somebody must say it: at phase 12
-- the @certify@ command's argument, at phase 13 the theorem's declared type,
-- and the op is the same either way.
--
-- It is an op and not a driver command for §12 invariant 3's reason, even
-- though it does not itself rewrite 'Thena.Engine.ProofState': @qed@ at phase
-- 13 certifies /and then/ admits and closes the proof, and admitting a theorem
-- must be a step you can watch in stepping mode rather than something the
-- driver does invisibly between commands (§7.5, §1).
--
-- **Purity is checked here, extraction is not implemented here.** The op calls
-- 'Thena.Development.Partial.extract', which is one traversal that either
-- reads the term off or says what stopped it — a predicate plus a fold would
-- be two codes that could disagree about what pure means.

-- The six hole ops are thesis tables 2.7 and 2.8, less the five phase 13 does
-- not need — decided by the user 2026-08-22, and §12 invariant 5's rule that
-- the vocabulary is discovered rather than designed.
--
-- **@cut@, @postpone@, @justify@ and @retreat@ are not in MS1, and that is now
-- a decision rather than a wait.** They were held for \"phase 17\'s tactics\";
-- phase 17 wrote the tactics and none of them needs one. Thesis §3.6.5 uses
-- @cut@ and @retreat@ to tidy up after @eliminate@, and Thena does not have to:
-- the methods are claimed as holes /above/ the goal and never sit inside the
-- guess, so there is nothing to retreat and nothing to cut. @raise@ waits
-- longer still, because phase 9 decided a scope violation is /reported/ and
-- not repaired, and repairing it is what @raise@ is for (§6.2).
--
-- **None takes a hole as an operand.** They act at the focus, like the moves,
-- so a rule body says @along@ then @attack@ rather than naming a variable it
-- would have had to get from somewhere. That also keeps @Value@ free of a case
-- for "a hole", which §7.2 already refused once.
--
-- @Try@ is the exception and takes the term to attach — there is nowhere else
-- that could come from.

-- --------------------------------------------------------------------------
-- Which ops produce a value (§7.2)
-- --------------------------------------------------------------------------

-- | Does this op leave something for a @Bind@ to name?
--
-- §7.2 keeps 'Op' free of a @Maybe@ and answers the question here instead, so
-- that @x = attack@ is rejected by 'Thena.Rules.validate' before a body runs
-- rather than binding nothing quietly.
--
-- **The engine is what makes this true, and it is checked against the engine**,
-- not against this list: 'Thena.RulesTests' runs each op through 'Thena.Engine'
-- on a fixture and asserts that a name appears in @env@ exactly when this
-- function says it should. That is the standing lesson about finding an
-- invariant maintained by different code from the code that checks it — a table
-- agreeing with itself would agree with itself while being wrong.
--
-- Written as a total case split rather than a list of the four, so @-Wall@
-- makes every op added later answer the question.
produces :: Op -> Bool
produces o = case o of
  -- 'Ask' produces through 'Thena.Engine.resumeAt', which is why the asking
  -- instruction stays at the head of @pc@ (§7.5): the destination has to still
  -- be there when the answer comes back.
  Ask _ _      -> True
  Concat _ _   -> True
  Assume _ _   -> True   -- the variable it bound; §7.3's @?x <- claim S@
  Claim  _ _   -> True

  Say _        -> False
  DefineData _ -> False
  Certify _    -> False
  Unify _ _    -> False
  Reduce       -> False
  Along        -> False
  Into         -> False
  CrossType    -> False
  CrossValue   -> False
  Down _       -> False
  Back         -> False
  Attack       -> False
  Intro        -> False
  Try _        -> False
  Regret       -> False
  Solve        -> False
  Abandon      -> False
  Prove        -> False
  Eliminate _  -> False

-- --------------------------------------------------------------------------
-- Rules (§8)
-- --------------------------------------------------------------------------

-- | A rule is a head and a body: a list of shape questions that must all pass,
-- and a procedure (§8).
--
-- **It lives here rather than in "Thena.Rules"** — decided by the user
-- 2026-08-23, @AGENDA.md@ item 25. 'Value'\'s 'VRule' case needs 'Rule' and a
-- rule's body is @[Instr]@, so the two modules would each need the other;
-- §7.2's own \"rules are values\" is the argument for which way to break it.
-- "Thena.Rules" keeps the engine — 'Thena.Rules.RuleBase',
-- 'Thena.Rules.RuleIter', 'Thena.Rules.matches', 'Thena.Rules.validate'.
--
-- **A tactic is a rule**, and that is the whole point (§8): the match list the
-- user sees must contain @intro@ beside an elaborate search strategy without
-- fragmenting by implementation category.
data Rule = Rule
  { ruleName   :: GlobalName
  , ruleParams :: [Name]   -- ^ bound by @Call@; they land in the body's own 'Env'
  , ruleHead   :: [Test]   -- ^ all must pass
  , ruleBody   :: [Instr]
  }
  deriving (Eq, Show)

-- | A shallow shape question — **a small closed set, and there is no pattern
-- language** (§8, DECIDED 2026-08-20).
--
-- The body pulls things apart with ordinary instructions; a head only asks
-- whether the rule is worth trying. §8 states the cost once: a rule needing a
-- deeper condition matches, runs and fails in its body, so the match list can
-- offer something that will not work. Prolog has exactly this.
--
-- Phase 15 defines the four its rule base asks, and no more (§12 invariant 5).
-- §8's @HintIsApp@ and @HintIsName@ are deliberately absent: there is no hint
-- until @Prove@ carries one, and elaboration's rules are phase 17's.
data Test
  = FocusIsHole     -- ^ the focus is a @? x : S@ component
  | FocusIsGuess    -- ^ the focus is a @? x ≐ g : S@ component
  | GoalTypeIsPi    -- ^ the focused component's type whnfs to a Π
  | GoalTypeIsLet   -- ^ … or to a @let@, which is table 2.8's other intro
  deriving (Eq, Show)
