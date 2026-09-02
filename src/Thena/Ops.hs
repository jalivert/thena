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
  , operandsOf
  , opKeyword
  , partWords
  , partOf
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
import Thena.Surface.Concrete (Surface)

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
  | VSurface Surface
    -- ^ **a surface term — elaboration's input** (MS4 phase 41).
    --
    -- It held a 'Thena.Syntax.Concrete.Raw' from phase 17b until here, which
    -- was the badly named constructor @CLAUDE.md@ kept having to correct:
    -- @Raw@ is a concrete syntax for the /development/ language, and turning
    -- one into a term is resolution, not elaboration. Now it holds what its
    -- name says.
    --
    -- There is deliberately no @VRaw@. Nothing wants development syntax as a
    -- value any more: the REPL resolves a core argument before the call
    -- (phase 38's corners), and elaboration takes this.
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
-- 'Thena.Engine.Development' (§7.2), so moving the focus changes exactly what
-- backtracks — §12 invariant 3's hazard, and the reason §2.4 spells them as
-- bare words. 'Down' takes its 'Part' as a field rather than an 'Operand' for
-- the same reason 'Ask' takes an 'AnswerKind' that way: it is chosen when the
-- instruction is written, not computed while it runs.
data Op
  = Assume Operand Operand    -- ^ name, type — extend the development with @λ x : S@
  | Quantify Operand Operand
    -- ^ name, type — extend the development with @∀ x : S@ (MS4 phase 41f).
    --
    -- **@assume@'s twin, and the only op that can start a Π.** The two build
    -- the same binding and differ in what the chain below them turns out to
    -- be: 'Thena.Development.Partial.extract' folds an assumption into a λ and
    -- this into a Π. Elaborating @∀ (x : A) -> B@ needs @x@ in Γ while @B@ is
    -- elaborated, and writing a component is the only way anything gets into
    -- Γ — so without this the surface language's @∀@ has no image in the
    -- development at all.
    --
    -- Its word is **@quantify@** and not @forall@, because @forall@ is a
    -- keyword (§2.6) and an op word is an @ident@ (§8).
  | Claim  Operand Operand    -- ^ name, type — extend it with a hole @? x : S@
  | Ask    Operand AnswerKind -- ^ prompt text, and what the frontend should offer
  | Say    Operand            -- ^ message text
  | Concat Operand Operand    -- ^ building prompt and message text
  | Along                     -- ^ past the head of the focus (§4.3)
  | Into                      -- ^ into a guess's body
  | CrossType                 -- ^ into the focused component's type
  | CrossValue                -- ^ into a definition's value
  | Down Part                 -- ^ into a named field of a core term (§4.7)
  | Goto Operand
    -- ^ focus the hole or guess this variable binds, wherever it is on the
    -- spine (phase 24b, the user's request).
    --
    -- **The one move that is not a step.** The others go one link from where
    -- you are; this one goes to a component you are holding the variable of.
    -- After a refinement the holes still owed are /above/ the focus and @back@
    -- only pops the path you came down — countable when @unify-refine@ claims
    -- two, not when @apply@ claims several.
    --
    -- It takes the variable and not a name: an 'Thena.Core.Term.Ident' is a
    -- display hint, two components may carry the same one, and a rule body
    -- already holds the variable because @claim@ and @define@ produce it.
  | Back                      -- ^ undo the last move
  | Reduce                    -- ^ commit a whnf at the core focus (§4.7, phase 7)
  | Unify Operand Operand     -- ^ two terms — solve holes, or park the equation (§6, phase 9)
  | UnifyInto Operand Operand
    -- ^ two terms — **solve so the first becomes usable where the second is
    -- wanted** (MS4 phase 41g). @unify@'s directed sibling, standing to it as
    -- 'Thena.Core.Convert.subsumes' stands to @convert@.
    --
    -- **Elaboration's @FILL@ is its caller**, and the reason it must exist is
    -- that unification there is a /solver/: @fill@ runs @prim-try@ right after,
    -- which is @check@, which subsumes — so the relation is enforced one
    -- instruction later with the right variance, and @unify@ was refusing where
    -- it merely had nothing to solve. Before it, @try-core ⌜ Nat ⌝@ at a claim
    -- of @Type₁@ succeeded and @elaborate Nat@ did not: the elaborator was
    -- strictly weaker than the core it elaborates into.
    --
    -- **@unify@ keeps no direction**, deliberately — the argument is stated
    -- once in "Thena.Core.Convert" and holds here: making the symmetric one
    -- directional would make every caller that wants an equality state a
    -- direction it does not have.
  | DefineData InductiveDefinition
    -- ^ hand a declaration out through the channel (§7.5)
    -- The life of a hole — thesis tables 2.7 and 2.8, phase 13. Each acts on
    -- the component at the focus, so none takes a name: §4.0 C1's rule that a
    -- command means one thing wherever it is applies to these too.
  | Attack                    -- ^ @?x : S@ ⟹ @?x ≐ (?x' : S . x') : S@
  | Intro (Maybe Operand)
    -- ^ move a hole through a Π or a @let@ in its type, **optionally naming
    -- the binder it opens** (MS4 phase 41b).
    --
    -- Without a name the binder keeps the one written in the /type/, which is
    -- what it has always done and what a user typing @intro@ wants. With one,
    -- the name is the caller's — Brady's @LAMBDA Γ n@, and elaboration needs it:
    -- @\ y -> y@ against a goal @∀ (x : A) -> A@ must bind **y**, or the body's
    -- @y@ resolves to nothing.
    --
    -- **An optional argument, not an optional mode.** @Prove (Maybe Operand)@
    -- was deleted one phase ago for being the latter — two mechanisms behind
    -- one constructor. This is one operation with a default.
  | Try     Operand           -- ^ attach a guess to the hole at the focus
  | Regret                    -- ^ discard it again
  | Solve                     -- ^ commit a guess whose body is pure
  | Abandon                   -- ^ drop a hole nothing refers to
  | Prove
    -- ^ **dispatch the rule engine at the focus** (§7.3, §8) — every rule whose
    -- head passes, in definition order, with a choice point if there is more
    -- than one.
    --
    -- **It carries nothing** (MS4 phase 41). It was @Prove (Maybe Operand)@,
    -- the operand being the surface term to elaborate, and the base was
    -- /partitioned/ on whether a rule's head asked about one. Both are gone,
    -- and the reason is that **elaboration was never a dispatch**: it is a rule
    -- of many clauses called by name, which is @Call@. The user, 2026-09-01:
    -- /"There is no `elaborate` command — there will be an elaborate rule!"/
    --
    -- So this op's only customers are search — a bare @prove@ at the REPL,
    -- which is now the rule @prove@ over this, and the body of a strategy rule
    -- like @auto@ when one is written.
    --
    -- Its written word is **@prim-prove@**: the good word belongs to the rule
    -- (phase 23b's convention).
  | Elaborate Operand
    -- ^ **elaborate a surface term into the focused hole** (MS4 phase 41) —
    -- the operand is a 'VSurface'.
    --
    -- **One large instruction, and step 1 of a two-step** (@MS4.md@). His
    -- design, 2026-09-02: elaboration is written in Haskell behind one op
    -- first, and then broken into the clauses of a rule. §7.2's /large and
    -- small instructions coexist/ is the licence, and @eliminate@ is the
    -- precedent.
    --
    -- **It does not do the work; it emits the instructions that do.** Each
    -- surface node compiles to a short program of ops that already exist —
    -- and to an @Elaborate@ of each sub-term, so the op recurses through
    -- itself. That is what makes step 2 a /decomposition/: the rule clauses
    -- that replace this will emit the same instructions from a body instead of
    -- from Haskell, and until they do, @:step@ shows the elaboration running
    -- as ordinary instructions.
    --
    -- See "Thena.Elaborate".
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
  | FreshName Operand
    -- ^ a name nothing has taken, from a hint (phase 24c, the user's
    -- correction).
    --
    -- **Inventing a name is the rule's job, not @claim@'s.** Until this op,
    -- @claim@, @assume@ and @define@ silently renamed a taken identifier — a
    -- repair rather than a check, and it hid from the body what it had actually
    -- got. His words: *"They shouldn't be deciding whether the name given to
    -- them is unique or not, that's breaking the separation of responsibility
    -- and abstraction."* Now a body asks for a name, holds it, and passes it
    -- on.
    --
    -- It avoids the development's identifiers **and the global environment's
    -- names**, so a generated hole never shadows a datatype or a theorem.
  | Here
    -- ^ **the variable of the focused component** (MS4 phase 41c) — the
    -- companion to 'Goal', which gives the type it is claimed at.
    --
    -- **There was no way to ask "which component am I standing on?"**
    -- @claim@ and @define@ yield the variables of the holes /they/ make, and
    -- @goto@ takes a variable — but a rule that wanted to come back to the hole
    -- it was called at had to count its own moves and undo them. The λ case did
    -- exactly that (phase 41b), and every later case would have.
    --
    -- With this, @h = here@ then @goto h@ is exact where balancing @back@s was
    -- only careful. That retires @elaboration-in-rules.md@'s **gap 1** rather
    -- than working around it — and it does so with **one read op** instead of
    -- making every hole-creating op produce its hole, which was that document's
    -- own suggestion and touches every caller.
    --
    -- It yields the variable as a term, @Trailing (Free x)@, which is the shape
    -- @goto@ already reads.
  | Goal
    -- ^ the type the focused hole is claimed at (§7.2, phase 24). **The first
    -- op that reads the development** — §7.2's sketch called it @GoalType@ and
    -- listed it under "reads — always named, never a general getState", which
    -- is the rule it arrives under: a body asks a named question, it does not
    -- get handed the state.
  | Typing Operand
    -- ^ the type of a term, inferred in the context at the focus (§7.2,
    -- phase 24). §7.2 sketched it and @t = typeof x@ has been this language's
    -- standing example of its own surface since 2026-08-20.
  | Define Operand Operand
    -- ^ name, value — extend the development with @x = v : S@, above the focus,
    -- at the type @v@ is inferred to have (phase 24).
    --
    -- **Thesis §2.7's @=@-binding**, and it is the load-bearing part of
    -- @unify-refine@ rather than a convenience: the application being refined
    -- with does /not/ yet have the goal's type — that is the whole thing
    -- unification is there to fix — so it cannot be attached to the hole. It is
    -- *"temporarily stored in a `=`-binding"* until unification makes the two
    -- types converge, and only then filled in as the hole's value.
    --
    -- The type is inferred rather than given, which is what makes it a
    -- definition and not a claim: a definition's type is determined by its
    -- value. That is also why it takes two operands where 'Assume' and 'Claim'
    -- take a name and a /type/.
  | Arrow Operand Operand
    -- ^ two terms → the non-dependent @Π@ between them (MS4 phase 41d).
    --
    -- **The first op that BUILDS a term**, and
    -- @discussion/elaboration-in-rules.md@'s **gap 2** — /"we have no op that
    -- constructs a term at all"/, which that document called the real wall.
    -- It arrives with a caller and not before: elaborating @e a@ must claim
    -- @f : A -> B@ where @A@ and @B@ are holes claimed **at run time**, so the
    -- arrow cannot be built by whatever wrote the program.
    --
    -- **The binder is anonymous** — @_@, the convention @prim-apply@ already
    -- uses for a domain with no name — and the codomain does not mention it,
    -- which is what makes it an arrow rather than a Π.
    --
    -- **It builds; it does not check.** @Θ ⊢ S : Type@ is @claim@'s side
    -- condition (phase 25f) and @try@'s (25b), and this is neither: a
    -- constructed term is checked where it is used, which is the same line
    -- §3.4 draws everywhere else.
  | ApplyTo Operand Operand
    -- ^ two terms → the application of the first to the second (MS4 phase 41d).
    --
    -- Brady's @FILL (f s)@, where @f@ and @s@ are holes claimed at run time.
    -- Named @apply-to@ and not @apply@ because @apply@ is a tactic.
    --
    -- **@App (Canonical …) x@ is constructible here and is not well formed.**
    -- That is @PLAN-representation.md@ §3.4's line, deliberately: the checker
    -- refuses it, and no abstraction boundary is put in the way of building it.
  | Certify Operand
    -- ^ the development must be pure; yields the closed term it stands for and
    -- the type it is claimed to have, for the driver to run the kernel on
    -- (§7.5, §5.3)
  | Apply Operand
    -- ^ the head to apply — thesis §2.7's @naive-refine@ with the search
    -- taken out (phase 25). Walks the head's Π telescope, claims a hole for
    -- every domain, and yields the saturated spine.
    --
    -- **It saturates; it does not search.** §2.7 says the argument count
    -- /"need not be given in advance: try successively longer sequences
    -- afforded by the @∀@s"/ — that is @fit@, and it is a later phase's,
    -- because making it two rule clauses and backtracking rather than a loop
    -- in here is the demonstration the rule engine is for.
    --
    -- **Holes, not assumptions.** @claim@ and not @assume@: an assumption
    -- adds @λ x : S@ and abstracts, so applying @Just@ would start building
    -- a term of @Type₀ -> Maybe Bool@. §5.3's distinction arriving in a new
    -- place.
    --
    -- It names each hole from the Π binder it came from, freshened with
    -- 'Thena.Development.Cursor.freshIdent' — the same licence 'Attack' and
    -- 'Eliminate' have. Phase 24c's @fresh-name@ is for names a /rule body/
    -- chooses; these the engine chooses for itself.
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
-- rewrites 'Thena.Engine.Development', so it must backtrack with everything else
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
-- though it does not itself rewrite 'Thena.Engine.Development': @qed@ at phase
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
  Quantify _ _ -> False  -- a hole-life op, like 'Attack' and 'Intro'
  Claim  _ _   -> True

  Say _        -> False
  DefineData _ -> False
  Certify _    -> False
  FreshName _  -> True
  Here         -> True
  Arrow _ _    -> True
  ApplyTo _ _  -> True
  Goal         -> True
  Typing _     -> True
  Define _ _   -> True   -- the variable it bound, as 'Assume' and 'Claim' do
  Unify _ _    -> False
  UnifyInto _ _ -> False
  Reduce       -> False
  Along        -> False
  Into         -> False
  CrossType    -> False
  CrossValue   -> False
  Down _       -> False
  Goto _       -> False   -- a move; it rewrites the cursor and yields nothing
  Back         -> False
  Attack       -> False
  Intro _      -> False
  Try _        -> False
  Regret       -> False
  Solve        -> False
  Abandon      -> False
  Prove        -> False
  Call _ _     -> False   -- what the callee builds is in the development
  Elaborate _  -> False
  Eliminate _  -> False
  Apply _      -> True   -- the spine it built

-- | Every operand an op reads, in the order it is written.
--
-- **Here rather than in "Thena.Rules", where it lived until phase 25c**, so
-- that the three total functions over 'Op' — this, 'produces' and 'opKeyword' —
-- are one place and a new constructor answers all three at once. It moved
-- because 'Thena.Repl.renderOp' needs it: that function kept a second spelling
-- table beside 'opKeyword', the two drifted at phase 23b, and deleting the
-- duplicate is what stops it happening again.
--
-- A total case split, so @-Wall@ makes a new op say whether it reads
-- anything.
operandsOf :: Op -> [Operand]
operandsOf o = case o of
  Assume a b   -> [a, b]
  Quantify a b -> [a, b]
  Claim  a b   -> [a, b]
  Ask    a _   -> [a]
  Say    a     -> [a]
  Concat a b   -> [a, b]
  Unify  a b   -> [a, b]
  UnifyInto a b -> [a, b]
  Try    a     -> [a]
  Certify a    -> [a]
  FreshName a  -> [a]
  Here         -> []
  Arrow a b    -> [a, b]
  ApplyTo a b  -> [a, b]
  Goal         -> []
  Typing a     -> [a]
  Define a b   -> [a, b]
  Eliminate a  -> [a]
  Apply a      -> [a]
  Elaborate a  -> [a]
  Call _ as    -> as
  Prove        -> []
  DefineData _ -> []
  Along        -> []
  Into         -> []
  CrossType    -> []
  CrossValue   -> []
  Down _       -> []
  Goto a       -> [a]
  Back         -> []
  Reduce       -> []
  Attack       -> []
  Intro m      -> maybe [] (: []) m
  Regret       -> []
  Solve        -> []
  Abandon      -> []

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
  deriving (Eq, Show)



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
-- **The seven @prim-@ words — DECIDED by the user 2026-08-25, phase 23b.** Ops
-- and rules share one namespace, and the good words belong to the /tactics/:
-- @attack@ is a rule, and an instruction called @attack@ *"would be absurd"*.
-- These seven were named after their rule counterparts by mistake, and the
-- prefix marks them for what they are — temporary machine-level primitives that
-- rules will replace. It invents no vocabulary, which matters because phase 26
-- is where the op set is actually redesigned.
--
-- 'DefineData' has a word and no written form: §3.7 keeps a declaration out of
-- a rule body, and 'Thena.Rules.validate' is what enforces that. The word is
-- here because the case split is total, not because a body may say it.
opKeyword :: Op -> String
opKeyword o = case o of
  Assume _ _   -> "assume"
  Quantify _ _ -> "quantify"
  Claim  _ _   -> "claim"
  Ask    _ _   -> "ask"
  Say    _     -> "say"
  Concat _ _   -> "concat"
  Along        -> "along"
  Into         -> "into"
  CrossType    -> "cross"
  CrossValue   -> "cross"
  Down p       -> partWord p
  Goto _       -> "goto"
  Back         -> "back"
  Reduce       -> "reduce"
  Unify _ _    -> "unify"
  UnifyInto _ _ -> "unify-into"
  DefineData _ -> "data"
  Attack       -> "prim-attack"
  Intro _      -> "prim-intro"
  Try _        -> "prim-try"
  Regret       -> "prim-regret"
  Solve        -> "prim-solve"
  Abandon      -> "prim-abandon"
  Prove        -> "prim-prove"
  Elaborate _  -> "prim-elaborate"
  Call _ _     -> "call"
  FreshName _  -> "fresh-name"
  Here         -> "here"
  Arrow _ _    -> "arrow"
  ApplyTo _ _  -> "apply-to"
  Goal         -> "goal"
  Typing _     -> "typeof"
  Define _ _   -> "define"
  Certify _    -> "certify"
  Eliminate _  -> "prim-eliminate"
  Apply _      -> "prim-apply"

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
