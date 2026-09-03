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
  , operandIn
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
import Thena.Surface.Concrete (Plicity)
import Thena.Surface.Zipper (SurfaceZipper)

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
  | VSurface SurfaceZipper
    -- ^ **a focused surface term — elaboration's input** (MS4 phase 41,
    -- focused at phase 46).
    --
    -- **It carries a zipper and not a bare tree**, which is his shape D
    -- (@discussion\/surface-and-elaboration.md@ §1): the subterm plus the path
    -- it sits at. A value in @env@ is already rewound by a 'Thena.Engine.Choice'
    -- frame, so a zipper that is a value backtracks for free and no op has to
    -- ask which cursor it is moving — the Ξ precedent. See
    -- "Thena.Surface.Zipper".
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

-- | What an operand denotes, or the name that had nothing bound to it.
--
-- **One definition, read by two callers** — "Thena.Engine" running a body, and
-- "Thena.Rules" answering a head that asks about an argument (MS4 phase 47).
-- It lives here because 'Env', 'Operand' and 'Value' all do, and because the
-- alternative was three lines written twice, which is exactly the confusion his
-- 2026-08-29 ruling is against.
--
-- It returns the unbound name rather than an error, so that each caller says
-- what an unbound name means to it: to a body it is
-- 'Thena.Errors.UnboundInBody' and fatal, and to a head it is a question about
-- an argument nobody supplied.
operandIn :: Env -> Operand -> Either Name Value
operandIn e o = case o of
  Lit v -> Right v
  Ref n -> maybe (Left n) Right (lookup n e)

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
  | Yield Operand
    -- ^ hand control to the REPL and stay where you are (MS4 phase 45b).
    --
    -- **It is 'Ask''s mechanism without 'Ask''s question.** The instruction is
    -- not consumed — @pc@ is unchanged, exactly as it is for 'Ask' — so the
    -- machine keeps arriving back here and the user keeps getting the prompt.
    -- His words: /"that instruction simply enters the REPL again and again and
    -- again."/ Nothing duplicates itself onto the tape and no program modifies
    -- itself; @yield@ the driver word is what finally advances past it, the way
    -- 'Thena.Engine.resumeAt' advances past an 'Ask'.
    --
    -- **The operand is why it stopped**, and one op with a message covers both
    -- callers: a rule body saying what it wants looked at, and elaboration's
    -- named-placeholder clause saying which @?foo@ you are standing in. Two ops
    -- differing only by carrying a string would be the special case §12's first
    -- principle is about.
  | Block [Instr]
    -- ^ play a written block of instructions (MS4 phase 45).
    --
    -- **It carries the block as a field, not as an 'Operand'**, because the
    -- block is /written down and never computed/ — the same reason
    -- 'DefineData' carries its declaration and 'Down' its 'Part'. There is a
    -- precedent for the shape and it is the settled way to carry a written
    -- thing into an op.
    --
    -- **It is 'Call' with the body supplied instead of looked up.** Same frame,
    -- same return, same backtracking below it; what it does not do is choose,
    -- because there is nothing to choose between — a block is one body, so
    -- there is no candidate list and no choice point. That is the whole of the
    -- difference.
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
  | FreshUniverse
    -- ^ a universe at a **freshly minted level meta** (MS4 phase 48) — what
    -- the surface writes as a bare @Type@, and what typical ambiguity means at
    -- an operand.
    --
    -- **It is the literal the elaborator does not write.** Seven of
    -- "Thena.Elaborate"\'s nine @Lit (VTerm …)@ operands are a @Universe@ at a
    -- level drawn from the counter — the type a claimed domain, codomain or
    -- ascription is claimed at, before anything is known about it. A rule
    -- cannot write that down: the point of the meta is that it is fresh at
    -- every node.
    --
    -- Yielded as a term, not as a level: 'Value' has no level case, and
    -- @Universe@ is the only place the elaborator puts one.
  | ResolveName Operand
    -- ^ what a name denotes, with its level arguments inserted (MS4 phase 48).
    -- The other two of those nine operands.
    --
    -- **Γ first, then the globals**, which is what one namespace (§3.6)
    -- requires and the order "Thena.Syntax.Resolve" uses: a binder shadows a
    -- global of the same name. A definition's prenex level parameters each get
    -- a fresh meta, which is his /"obviously we have them implicitly
    -- inserted"/ (MS4 phase 44) arriving at an op.
    --
    -- **Not @Op.Resolve@ come back.** That took a 'Thena.Syntax.Concrete.Raw'
    -- and resolved it in Γ, and phase 41 deleted it with the rest of the hint
    -- machinery. This takes a /name/ and answers with level arguments already
    -- in place, which is the question elaboration actually asks.
  | SurfaceNameOf Operand
    -- ^ the name a surface term's focus is written with, as text (MS4 phase
    -- 49). Paired with 'SurfaceIsName', which is what makes it total in the
    -- clause that uses it.
    --
    -- **@Of@, because 'Thena.Surface.Concrete.SurfaceName' is a different thing
    -- with the same word** — that constructor /is/ a surface term, this op
    -- /reads one/, and every module resolving a rule imports both.
  | ArrowDomain Operand      -- ^ the @A@ of a surface @A -> B@ (MS4 phase 49b)
  | ArrowCodomain Operand    -- ^ … its @B@
  | AscriptionType Operand   -- ^ the @T@ of a surface @e : T@
  | AscriptionTerm Operand   -- ^ … its @e@
    -- ^ **Moves, not readers**: each answers with a 'VSurface' focused on that
    -- part, so the path the zipper carries is extended rather than thrown away
    -- (MS4 phase 46). A clause pairs each with the test that makes it total —
    -- @when (surface-is-arrow t) then a = arrow-domain t@.
    --
    -- **They do not reuse the cursor's words.** @dom@ and @cod@ already move the
    -- development's ambient cursor; these produce a value, and one word for two
    -- different things is what @CLAUDE.md@'s /no confusions/ rules out.
  | AppFunction Operand
    -- ^ a spine minus its last argument — @f a b@ gives @f a@, @f a@ gives @f@
    -- (MS4 phase 49d)
  | AppLastArgument Operand  -- ^ … that last argument
  | LambdaName Operand
    -- ^ the first binder's name in a surface λ, as text (MS4 phase 49c).
    -- **It refuses an annotated or implicit binder**, which is the whole of
    -- what the λ case still cannot elaborate.
  | LambdaTail Operand
    -- ^ … what the λ abstracts once that binder is peeled off: the rest of the
    -- group if there was one, otherwise the body
  | LambdaBody Operand
    -- ^ … the body, past every binder of the group
  | LetName Operand          -- ^ the @x@ of a surface @let x = v in b@, as text
  | LetType Operand          -- ^ … its written annotation
  | LetValue Operand         -- ^ … its @v@
  | LetBody Operand          -- ^ … its @b@
  | ForallName Operand       -- ^ the first binder's name in a surface @∀@
  | ForallDomain Operand     -- ^ … that binder's annotation
  | ForallTail Operand
    -- ^ … what the @∀@ quantifies over once the first binder is peeled off:
    -- the rest of the group if there was one, otherwise the body.
  | Play Operand
    -- ^ run the block a surface @do { … }@ holds (MS4 phase 49b).
    --
    -- **A block is written down and never computed**, so elaborating one is
    -- playing it — the whole of @E⟦do { … }⟧@. It is an op and not a value a
    -- body could hold, because 'Value' has no case for instructions and the
    -- @do@ node keeps 'Thena.Syntax.Concrete.RawInstr' until something runs it.
  | SurfaceUniverseOf Operand
    -- ^ the universe a surface @Typeₙ@ denotes, as a term (MS4 phase 49).
    --
    -- **A term and not a level**, for 'FreshUniverse'\'s reason: 'Value' has no
    -- level case, and a universe is the only place a written level appears.
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
  | Expose Operand
    -- ^ **a type with elaboration's own bookkeeping reduced out of it**
    -- (MS4 phase 42, widened at 44b) — §5.1's 'Thena.Core.Reduce.whnf', and
    -- then again under every Π binder, so the whole telescope is exposed and
    -- not merely the head.
    --
    -- **A declaration's type is what wanted it.** What @pop-development@ hands
    -- back is what @extract@ built, and elaboration's own bookkeeping is in
    -- there: @fill@ parks every term in a @=@-binding, so the type of
    -- @foo : Nat@ comes out as @let refined = Nat in let goal = refined in
    -- goal@. That is δ-equal to @Nat@ and still wrong to store, and it does not
    -- merely look wrong — 'Thena.Engine.introduce' reads a @Let@ /as written/
    -- and before any reduction (phase 15, deliberately), so @intro@ on a
    -- @let@-typed goal opens a definition where the λ should have been.
    --
    -- **Going under the binders is the half phase 42 missed.** A plain @whnf@
    -- clears the head, so @declare idn : Nat -> Nat@ worked; it leaves the
    -- codomain alone, so **no dependent signature could be declared at all** —
    -- @declare idty : ∀ (A : Type₀) -> A -> A ; idty = \\ A x -> x@ failed with
    -- /"Type₀ and x -> A cannot be made equal"/, which is @intro-let@ firing
    -- one binder down. Found at 44b, fixed here.
    --
    -- **It is not a normaliser and §5.1 is untouched.** Reduction is still to
    -- whnf; this iterates it at the positions a telescope has, which is what
    -- storing a signature needs and nothing more. Clearing a @let@ from a
    -- /type/ is free — types are compared up to conversion — where clearing one
    -- from a proof term would not be, and this is only ever applied to a type.
    --
    -- **It is a move on a term, not on the development**, which is what
    -- separates it from the @reduce@ move: that one commits a whnf at the core
    -- focus, this one answers a question about a term a body is holding.
  | PushDevelopment Operand
    -- ^ **start a development of its own, nested inside this one** (MS4 phase
    -- 42, his decision) — the operand is the type its goal is claimed at.
    -- Brady's @NEW PROOF@ (@IDRIS.md@ §4.6).
    --
    -- **It exists because a declaration cannot be elaborated in the
    -- development that is already there.** @certify@ extracts the /whole/
    -- chain, so a signature elaborated beside the body would land inside the
    -- proof term — which is why phase 37 made @:theorem@ start fresh, and why
    -- Brady gives the signature a proof of its own.
    --
    -- The stack is 'Thena.Engine.enclosing', and it backtracks: a body that
    -- pushes and then fails unwinds to the stack it had.
  | PopDevelopment
    -- ^ **finish the innermost development and yield the term it built** (MS4
    -- phase 42) — Brady's @TERM@, and 'PushDevelopment'\'s other half.
    --
    -- **It insists the development is pure**, through the same
    -- 'Thena.Development.Partial.extract' @certify@ uses, so a hole left open
    -- is reported here rather than becoming a term with a gap in it.
    --
    -- Refused at the outermost development: there is nothing to pop back to,
    -- and a machine with no development is not a state this language has.
  | MakeData GlobalName Int [GlobalName] [Operand]
    -- ^ **assemble a datatype from elaborated types and hand it out through
    -- the channel** (MS4 phase 42b) — the datatype's name, how many parameters
    -- were written, the constructors' names, and the types: the datatype's own
    -- first and then one per constructor, in order.
    --
    -- The names and the parameter count are fields rather than operands for
    -- 'DefineData'\'s reason — they are written down, never computed — and the
    -- count is what lets 'Thena.Global.Declare.buildInductive' make §3.7's
    -- parameter/index split by /peeling/, where @resolveData@ makes it
    -- syntactically on 'Thena.Syntax.Concrete.Raw'.
    --
    -- **It yields; the driver checks and installs**, exactly as 'DefineData'
    -- does — the whole of "Thena.Global.Declare"'s @declare@ runs on the
    -- result, so a surface datatype is checked by the same code a written one
    -- is.
  | DefineGlobal [Plicity] Operand Operand Operand
    -- ^ the plicities its signature wrote, then name, type and term — **hand a finished definition out through the
    -- channel** (MS4 phase 42), the way 'DefineData' hands out a datatype.
    --
    -- **No instruction writes globals** (§7.5, §3.3.1), here or ever: this
    -- yields and the driver installs, running the kernel and generalising the
    -- level metas exactly as @qed@ does. That is what keeps a surface
    -- declaration and a hand-built proof arriving in the environment the same
    -- way.
    --
    -- **It says nothing.** His instruction, 2026-09-02: the instruction
    -- /"doesn't really need to yield anything… Having it print something to the
    -- REPL in the middle of the elaboration might be distracting."/ The command
    -- that ran it reports when it is over; this does not report as it goes.
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
  | MakeApply Operand [Operand]
    -- ^ **a head, and the names its argument holes are to carry** — claim one
    -- per Π domain of the head's type and yield the saturated spine (MS4 phase
    -- 44).
    --
    -- **This is Brady's @E⟦x ⃗a⟧@, and it exists because his @E⟦e a⟧@ cannot do
    -- a dependent function.** That rule claims @f : A -> B@ — an /arrow/, with
    -- no way for @B@ to mention the argument — so applying @Eq@, whose later
    -- domains mention the earlier ones, made unification try to solve a hole
    -- with a term mentioning a binder out of its scope: /"A3 is not bound
    -- before A1"/. Walking the real telescope claims each domain in the scope
    -- of the holes already claimed, which is what @prim-apply@ has always done
    -- and never handed back.
    --
    -- **The caller supplies the names**, as 'MakeElim' does and for the same
    -- reason (his decision, 2026-09-02): a body reaches the holes by name.
  | MakeElim GlobalName [Operand]
    -- ^ **build a saturated elimination, claiming a hole for every field**
    -- (MS4 phase 41i) — the datatype is written, the operands are the names
    -- those holes are to carry, in 'Thena.Core.Term.Eliminate'\'s own field
    -- order: parameters, motive, methods, indices, target.
    --
    -- **It is @prim-apply@ for the eliminator**, and it exists because the
    -- eliminator has no global name to apply: §3.7 generates nothing for it,
    -- and its type is computed on demand by
    -- 'Thena.Global.Env.eliminatorType'. That type is a Π telescope in exactly
    -- this field order, so the walk is 'Thena.Core.Typing.spine'\'s in
    -- reverse — claim where that checks.
    --
    -- **The caller supplies the names, and that is what makes the holes
    -- reachable** (his decision, 2026-09-02). @prim-apply@ claims holes and
    -- yields only the spine, so a body cannot reach them —
    -- @discussion\/elaboration-in-rules.md@ named that gap and nothing had
    -- closed it. A body asks @fresh-name@ for one name per field, hands them
    -- here, and @goto ‹name›@ reaches each hole afterwards. **Phase 41f is
    -- what made that sound**: @claim@ takes the name as given, where it used
    -- to freshen or refuse.
    --
    -- The alternative — yielding the holes as a list — was rejected because a
    -- list a rule cannot take apart is inert, so it would pull in indexing or
    -- head\/tail ops that nothing has asked for.
    --
    -- The datatype is a field rather than an 'Operand' for 'DefineData'\'s
    -- reason: it is written down, never computed.
    --
    -- **The motive's level is a fresh meta.** It is derived, not written —
    -- §3.7's /"the level is read from the motive"/ — and typical ambiguity is
    -- exactly the machinery for a level nobody spells.
    --
    -- **The datatype's own level arguments are empty**, as
    -- 'Thena.Core.Term.Global' is given @[]@ by every other elaborator case.
    -- A polymorphic datatype therefore fails in @infer@ with
    -- 'Thena.Errors.WrongNumberOfLevelArguments', which is phase 44's to fix
    -- for all of them at once.
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
  -- **A yield produces nothing.** It is not a question: control comes back
  -- because the user handed it back, not because they supplied a value.
  Yield _      -> False
  -- **A block produces nothing.** Its instructions produce whatever they
  -- produce, into the block's own environment; the block itself is a body being
  -- played, and a body has no value — the same answer 'Call' gives.
  Block _      -> False
  Concat _ _   -> True
  Assume _ _   -> True   -- the variable it bound; §7.3's @?x <- claim S@
  Quantify _ _ -> False  -- a hole-life op, like 'Attack' and 'Intro'
  Claim  _ _   -> True

  Say _        -> False
  DefineData _ -> False
  Certify _    -> False
  DefineGlobal {} -> False
  MakeData {} -> False
  Expose _ -> True
  PushDevelopment _ -> False
  PopDevelopment -> True   -- the term the nested development built
  FreshName _  -> True
  Here         -> True
  Arrow _ _    -> True
  ApplyTo _ _  -> True
  FreshUniverse  -> True
  ResolveName _  -> True
  SurfaceNameOf _ -> True
  SurfaceUniverseOf _ -> True
  ArrowDomain _ -> True
  AppFunction _ -> True
  AppLastArgument _ -> True
  LambdaName _ -> True
  LambdaTail _ -> True
  LambdaBody _ -> True
  LetName _ -> True
  LetType _ -> True
  LetValue _ -> True
  LetBody _ -> True
  ForallName _ -> True
  ForallDomain _ -> True
  ForallTail _ -> True
  ArrowCodomain _ -> True
  AscriptionType _ -> True
  AscriptionTerm _ -> True
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
  Play _       -> False
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
  MakeApply _ _ -> True  -- the saturated spine
  MakeElim _ _ -> True   -- the assembled node
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
  Yield a      -> [a]
  -- **A block reads no operand.** It is written down, not computed, so there is
  -- nothing here for a rule to have bound — see 'Block'.
  Block _      -> []
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
  DefineGlobal _ a b c -> [a, b, c]
  MakeData _ _ _ as -> as
  Expose a -> [a]
  PushDevelopment a -> [a]
  PopDevelopment -> []
  FreshName a  -> [a]
  Here         -> []
  Arrow a b    -> [a, b]
  ApplyTo a b  -> [a, b]
  FreshUniverse  -> []
  ResolveName x  -> [x]
  SurfaceNameOf x -> [x]
  SurfaceUniverseOf x -> [x]
  ArrowDomain x -> [x]
  AppFunction x -> [x]
  AppLastArgument x -> [x]
  LambdaName x -> [x]
  LambdaTail x -> [x]
  LambdaBody x -> [x]
  LetName x -> [x]
  LetType x -> [x]
  LetValue x -> [x]
  LetBody x -> [x]
  ForallName x -> [x]
  ForallDomain x -> [x]
  ForallTail x -> [x]
  Play x -> [x]
  ArrowCodomain x -> [x]
  AscriptionType x -> [x]
  AscriptionTerm x -> [x]
  Goal         -> []
  Typing a     -> [a]
  Define a b   -> [a, b]
  Eliminate a  -> [a]
  MakeApply h as -> h : as
  MakeElim _ as -> as
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
-- phase 17b adds a fifth when @Prove@ carries a hint, and phase 41 removes it
-- again with the hint itself.
--
-- == A test may ask about an argument — MS4 phase 47
--
-- 'SurfaceIsName' is the first test that takes one, and it is a **new shape in
-- the head language** rather than only a new test: every other asks about the
-- focus, which the machine is standing at, where this asks about a value the
-- caller supplied. 'Thena.Rules.holds' therefore takes the environment binding
-- a clause's parameters to a call's arguments, and 'Thena.Rules.validate'
-- refuses a head naming anything that is not one of them.
--
-- **The operand is not restricted to a 'Ref'.** A head is written in the same
-- operand language a body is, so a literal is accepted where a parameter name
-- is — for the reason §8 gives about string literals, that a grammar policing
-- operand kinds would be the rule language's type system in the wrong place
-- (@ms2\/CLOSEOUT.md@ 4b, deferred at his direction 2026-09-03).
data Test
  = FocusIsHole     -- ^ the focus is a @? x : S@ component
  | FocusIsGuess    -- ^ the focus is a @? x ≐ g : S@ component
  | FocusIsComponent
    -- ^ the focus is a component of the chain rather than a core term (MS4
    -- phase 49c). What @along@ and the other component moves need, and the one
    -- thing that is true throughout a walk over a binder group.
  | GoalTypeIsPi    -- ^ the focused component's type whnfs to a Π
  | GoalTypeIsLet   -- ^ … or to a @let@, which is table 2.8's other intro
  | SurfaceIsName Operand
    -- ^ the operand is a surface term whose focus is a name (MS4 phase 47)
    --
    -- **The twelve below complete the set** (MS4 phase 49) — one per 'Surface'
    -- constructor, so every clause of @elaborate@ can say which node it is for
    -- and **no two heads can match the same term**. His ruling, 2026-09-03:
    -- /"those head-predicates can be useful in the future. And what's more —
    -- adding them is not payed in design. They are not a design decision. If we
    -- never use them after MS4, we just drop them during a cleanup refactor."/
  | SurfaceIsUniverse Operand      -- ^ @Typeₙ@
  | SurfaceIsUniverseOpen Operand  -- ^ a bare @Type@
  | SurfaceIsPlaceholder Operand   -- ^ @_@
  | SurfaceIsHole Operand          -- ^ @?foo@
  | SurfaceIsApp Operand           -- ^ a spine
  | SurfaceIsLambda Operand        -- ^ @\ x -> b@
  | SurfaceIsForall Operand        -- ^ @∀ (x : A) -> B@
  | SurfaceIsArrow Operand         -- ^ @A -> B@
  | SurfaceIsLet Operand           -- ^ @let x = v in b@
  | SurfaceIsAscription Operand    -- ^ @e : T@
  | SurfaceIsElim Operand          -- ^ @elim D … t@
  | SurfaceIsDo Operand            -- ^ @do { … }@
  | AppArgsAreExplicit Operand
    -- ^ a spine with no argument written in braces (MS4 phase 49d).
    --
    -- **The binary clause has no notion of plicity at all**, so it must decline
    -- a written implicit rather than take it as an ordinary argument and report
    -- a type mismatch about a term the user never meant to write explicitly.
  | AppHeadIsName Operand
    -- ^ a spine whose head is a name (MS4 phase 49d) — Brady's split, and the
    -- clause that begins with @EXPAND@.
  | LambdaBindsMore Operand        -- ^ a λ whose group has a binder after the
                                   --   first (MS4 phase 49c)
  | LambdaBindsOne Operand         -- ^ … and one whose group has just the one
    -- ^ **Two positive tests, as @let@'s are**: they are how a clause that
    -- peels one binder knows whether to recurse, and the head language has no
    -- negation.
  | LetIsAnnotated Operand         -- ^ a @let@ whose type was written (49b)
  | LetIsBare Operand              -- ^ … and one whose type was not
    -- ^ **Two positive tests rather than one and its negation.** The head
    -- language has no negation, and the two clauses of @E⟦let⟧@ differ by
    -- whether there is an annotation to elaborate.
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
  Yield _      -> "yield"
  -- Like 'DefineData', a word with no written form of its own: a block is
  -- written @do { … }@ in the surface language and is never spelled in a rule
  -- body. The word is here because the case split is total.
  Block _      -> "do"
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
  FreshUniverse  -> "fresh-universe"
  ResolveName _  -> "resolve-name"
  SurfaceNameOf _ -> "surface-name"
  SurfaceUniverseOf _ -> "surface-universe"
  ArrowDomain _ -> "arrow-domain"
  AppFunction _ -> "app-function"
  AppLastArgument _ -> "app-last-argument"
  LambdaName _ -> "lambda-name"
  LambdaTail _ -> "lambda-tail"
  LambdaBody _ -> "lambda-body"
  LetName _ -> "let-name"
  LetType _ -> "let-type"
  LetValue _ -> "let-value"
  LetBody _ -> "let-body"
  ForallName _ -> "forall-name"
  ForallDomain _ -> "forall-domain"
  ForallTail _ -> "forall-tail"
  Play _ -> "play"
  ArrowCodomain _ -> "arrow-codomain"
  AscriptionType _ -> "ascription-type"
  AscriptionTerm _ -> "ascription-term"
  Goal         -> "goal"
  Typing _     -> "typeof"
  Define _ _   -> "define"
  Certify _    -> "certify"
  DefineGlobal {} -> "define-global"
  MakeData {} -> "make-data"
  Expose _ -> "expose"
  PushDevelopment _ -> "push-development"
  PopDevelopment -> "pop-development"
  Eliminate _  -> "prim-eliminate"
  MakeApply _ _ -> "make-apply"
  MakeElim _ _ -> "make-elim"
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
