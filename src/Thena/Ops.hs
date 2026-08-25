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
  , opKeyword
  , partWords
  , partOf
  , Part (..)
  , AnswerKind (..)

    -- * Rules (§8)
  , Rule (..)
  , Test (..)
  , usesHint
  , hintName
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
-- **'VRule' was deleted at phase 23**, and with it §7.2's \"rules are values, so
-- @Call@ and higher-order rules fall out\". A call names a rule and the base is
-- searched at run time (§8), so nothing constructs a rule value and nothing
-- consumes one. 'Rule' stays in this module for the other half of that argument
-- — a body is @[Instr]@, so \"Thena.Rules\" would need this module anyway.
data Value
  = VText    String    -- ^ what @Ask@ returns and @Say@ consumes
  | VTerm    Partial   -- ^ a term, a variable, or a whole development
  | VSurface Raw       -- ^ an unelaborated tree — elaboration's input
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
  | Prove (Maybe Operand)
    -- ^ dispatch the rule engine at the focus, with an optional hint (§7.3,
    -- §8; phase 16 without the hint, phase 17b with it).
    --
    -- **One op and not two.** §7.2 and §7.3 sketch it as @Prove goal hint@:
    -- the goal went at phase 16, because it is the focus and 'Value' has no
    -- case for \"a hole\" (§7.2 refused one twice); the hint arrives here as a
    -- 'Maybe'. §8's own sentence is why it is not @Prove@ beside @ProveWith@ —
    -- /same engine, same frames — the only difference is whether a hint is
    -- present/.
    --
    -- The operand must be a 'VSurface'. It is bound into the callee\'s
    -- environment under the name @hint@, which is how §8's rule bodies already
    -- read it (@h₁ = app-fun hint@); see "Thena.Engine"\'s @Prove@ case.
  | Parse Operand
    -- ^ text → 'VSurface' (§7.2, phase 17b). Lexing and parsing only: turning
    -- the tree into 'Thena.Core.Term.Core' is 'Resolve', because that needs a
    -- context and this does not.
  | Resolve Operand
    -- ^ 'VSurface' → 'VTerm', in the context at the focus (phase 17b).
    --
    -- Not in §7.2's sketch, and discovered rather than designed (§12 invariant
    -- 5): @elab-var@ has to get a term out of its hint, and §8's own sketch of
    -- @elab-app@ already pulls hints apart with ordinary instructions. It is
    -- one op and not a name-lookup, because "Thena.Syntax.Resolve" answers
    -- 'Thena.Syntax.Concrete.RawName' against the local context, the
    -- development's own names and the global environment in one pass, and
    -- splitting that into three would be three ways to disagree about scope.
  | Call GlobalName [Operand]
    -- ^ **call a rule by name — the same search as 'Prove', with a narrower
    -- candidate list** (§8, phase 23, and the user's own framing):
    --
    -- > @Prove@ means \"search any rule that fits and wants to try solving the
    -- > goal\" and @Call@ means \"see if any rules named like this can succeed\".
    -- > Calling is not that different from searching. Calling is essentially
    -- > what Prolog does.
    --
    -- So it takes a 'GlobalName' and not an 'Operand'. Candidates are the rules
    -- of that name **whose arity matches the number of arguments given** and
    -- **whose head passes** — 'Thena.Rules.clauses' — tried in search order,
    -- with a @Choice@ frame and backtracking, exactly as a dispatch is.
    --
    -- Three things this reverses, all decided by the user 2026-08-25:
    --
    --   * it **does** test the callee's head. Phase 15's note that a direct
    --     call has already chosen was written when there was one callee.
    --   * clauses of one name **need not share arity**. Arity is a filter, not
    --     an error, so the load-time check @MS2.md@ proposed was dropped rather
    --     than added.
    --   * the callee is resolved **when the call runs**, not when the rule is
    --     read, so a rule may call itself and may call a rule defined later or
    --     in a base loaded after it.
    --
    -- **A call carries no hint**, so a rule whose head asks about one is never
    -- a call candidate; it is reached by @prove ‹hint›@. Hints are on MS2's
    -- closeout list.
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
  Prove _      -> False
  Call _ _     -> False   -- what the callee builds is in the development
  Parse _      -> True
  Resolve _    -> True
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
-- Phase 15 defines the four its rule base asks, and no more (§12 invariant 5);
-- phase 17b adds the fifth, when @Prove@ starts carrying a hint. §8's
-- @HintIsApp@ is still absent — elaborating a compound surface term is beyond
-- MS1's identifier case.
data Test
  = FocusIsHole     -- ^ the focus is a @? x : S@ component
  | FocusIsGuess    -- ^ the focus is a @? x ≐ g : S@ component
  | GoalTypeIsPi    -- ^ the focused component's type whnfs to a Π
  | GoalTypeIsLet   -- ^ … or to a @let@, which is table 2.8's other intro
  | HintIsName      -- ^ there is a hint, and it is a bare identifier (§8)
  deriving (Eq, Show)

-- | Does this head ask about the hint?
--
-- **The partition, decided by the user 2026-08-23.** A hint changes the
-- question being asked — /build a term for this goal out of this surface
-- syntax/, rather than /make progress on this goal/ — so
-- 'Thena.Rules.dispatch' offers hint rules when there is a hint and the rest
-- when there is not. Without it @attack@ would win every elaboration, being
-- first in definition order and matching on 'FocusIsHole' like everything else
-- at a hole.
--
-- The other two answers were declined: ordering @elab-var@ first leaves rules
-- that ignore the hint sitting in the retry list underneath it, and a @NoHint@
-- test would be boilerplate on every rule ever written.
--
-- It is a function of the /head/ and not of the body, so it is decidable
-- without running anything — which is what lets 'Thena.Rules.matches' apply it
-- too, and keeps @:matches@ from listing rules the engine would not run.
usesHint :: Rule -> Bool
usesHint r = any hintTest (ruleHead r)
  where
    hintTest t = case t of
      HintIsName    -> True
      FocusIsHole   -> False
      FocusIsGuess  -> False
      GoalTypeIsPi  -> False
      GoalTypeIsLet -> False

-- | The name a hint is bound to in the environment of the body it dispatches
-- into (§8).
--
-- A reserved name, and the one magic name in the instruction language. §8 wrote
-- it this way — @h₁ = app-fun hint@ reads @hint@ as an ordinary operand — and
-- the alternative was a @Hint@ read op, which would have made the machine carry
-- the current hint somewhere for it to read. This way @Prove@ seeds the
-- callee's environment and everything downstream is ordinary.
--
-- 'Thena.Rules.validate' knows it: a body whose head asks about the hint starts
-- with this name in scope, so an @elab-@ rule reading it is not an unbound
-- 'Ref'.
hintName :: Name
hintName = "hint"

-- --------------------------------------------------------------------------
-- How an op is written (§2.4, phase 21)
-- --------------------------------------------------------------------------

-- | The word this op is written with, at the REPL and inside a rule body.
--
-- **They are the same word, and that is the whole point** — the user,
-- 2026-08-24: /"they absolutely are the same as in the REPL. That was the whole
-- point of non-colon commands — they are just statements in the instruction
-- language."/ So this is one table where phase 21 found two, and a new op gets
-- its REPL word and its rule-syntax word at once because it gets them here.
--
-- Written as a total case split for 'produces'\' reason: @-Wall@ then makes
-- every op added later say how it is spelled, rather than silently having no
-- written form. "Thena.RuleSyntaxTests" crosses it against the parser, which is
-- code of a different shape — a table checked against itself would agree with
-- itself while being wrong.
--
-- 'Down' answers with its field's word and drops the position, which is all a
-- coverage table needs; 'partOf' below is what actually reads one back.
--
-- 'DefineData' has a word and no written form: §3.7 keeps a declaration out of
-- a rule body, and 'Thena.Rules.validate' is what enforces that. The word is
-- here because the case split is total, not because a body may say it.
opKeyword :: Op -> String
opKeyword o = case o of
  Assume _ _   -> "assume"
  Claim  _ _   -> "claim"
  Ask    _ _   -> "ask"
  Say    _     -> "say"
  Concat _ _   -> "concat"
  Along        -> "along"
  Into         -> "into"
  CrossType    -> "cross"
  CrossValue   -> "cross"
  Down p       -> partWord p
  Back         -> "back"
  Reduce       -> "reduce"
  Unify _ _    -> "unify"
  DefineData _ -> "data"
  Attack       -> "attack"
  Intro        -> "intro"
  Try _        -> "try"
  Regret       -> "regret"
  Solve        -> "solve"
  Abandon      -> "abandon"
  Prove _      -> "prove"
  Parse _      -> "parse"
  Resolve _    -> "resolve"
  Call _ _     -> "call"
  Certify _    -> "certify"
  Eliminate _  -> "eliminate"

-- | The words that name a field of a core term (§4.3, phase 5). One word per
-- field, so that none of them changes meaning with what is in focus.
partWords :: [String]
partWords =
  [ "fun", "arg", "dom", "cod", "val", "type", "body"
  , "motive", "target", "param", "method", "index"
  ]

-- | A field word, and the position written after it if there was one.
--
-- 'Nothing' covers both mistakes — a word that names no field, and a word given
-- the wrong kind of argument. "Thena.Driver" tells those apart for its own
-- error messages; a rule body has one error for both.
--
-- @arg@ is the one word that means two things: bare it is an application's
-- argument, numbered it is a canonical form's (§4.7).
partOf :: String -> Maybe Int -> Maybe Part
partOf w k = case (w, k) of
  ("fun",    Nothing) -> Just Fun
  ("arg",    Nothing) -> Just Arg
  ("dom",    Nothing) -> Just Dom
  ("cod",    Nothing) -> Just Cod
  ("val",    Nothing) -> Just Val
  ("type",   Nothing) -> Just Type
  ("body",   Nothing) -> Just Body
  ("motive", Nothing) -> Just Motive
  ("target", Nothing) -> Just Target
  ("arg",    Just i)  -> Just (CanonArg i)
  ("param",  Just i)  -> Just (Param i)
  ("method", Just i)  -> Just (Method i)
  ("index",  Just i)  -> Just (Index i)
  _                   -> Nothing

-- | The inverse, for 'opKeyword'. Total, so a new field must be spelled.
partWord :: Part -> String
partWord p = case p of
  Fun        -> "fun"
  Arg        -> "arg"
  Dom        -> "dom"
  Cod        -> "cod"
  Val        -> "val"
  Type       -> "type"
  Body       -> "body"
  Motive     -> "motive"
  Target     -> "target"
  CanonArg _ -> "arg"
  Param _    -> "param"
  Method _   -> "method"
  Index _    -> "index"
