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
  , Part (..)
  , AnswerKind (..)
  ) where

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
-- @VRule@ is NOT here, and cannot be until 'Thena.Rules.Rule' exists (phase
-- 15); see the plan for phase 4 §10. 'VSurface' and 'VPair' are on
-- @AGENDA.md@'s standing list of things defined in MS1 and not yet exercised.
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
  | DefineData InductiveDefinition
    -- ^ hand a declaration out through the channel (§7.5)
  deriving (Eq, Show)

-- @Reduce@ is a move, not a value-producing op, for the same reason 'Along'
-- and 'Down' are not (§7.2): it rewrites the cursor and that is the whole of
-- what it does. It differs from the other moves in one way — it can have
-- something worth saying (an orphaned hole, §4.7), which is why
-- "Thena.Engine" answers it with 'Thena.Engine.Saying' rather than always
-- 'Thena.Engine.Continue', the same distinction 'Say' already makes.

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
