-- | The stepper (§7.1, §7.2).
--
-- The control state is data, not Haskell's call stack: 'step' takes a 'Machine'
-- and returns an 'Outcome', and everything the machine cannot do itself it
-- yields through that one channel (§7.5). There is no @IO@ here and no
-- continuation anywhere inside a 'Machine' — the whole point is that an
-- in-flight execution is a value you can print, store, diff or send.
--
-- What phase 4 does not have yet, and where it arrives:
--
--   * @globals :: GlobalEnv@ in 'Machine' — phase 6, when there is a global
--     environment to hold.
--   * 'Frame'\'s @Choice@ constructor, @unwind@ past a live alternative, and
--     the peek that builds one — phase 16. They need alternatives to exist,
--     and alternatives need the rule engine.
module Thena.Engine
  ( -- * The machine
    Machine (..)
  , Exec (..)
  , Frame (..)
  , ProofState (..)
  , newProof
  , proofContext
  , proofDevelopment
  , setGoal

    -- * Running it
  , Outcome (..)
  , Question (..)
  , Message
  , Answer
  , load
  , isAsking
  , step
  , resumeAt
  , failure
  ) where

import Thena.Core.Context (Context)
import Thena.Core.Term
  ( Core (..)
  , Ident (..)
  , Level (..)
  , Var
  , fresh
  )
import qualified Thena.Development.Component as Component
import Thena.Development.Cursor
  ( Cursor
  , along
  , back
  , crossType
  , crossValue
  , down
  , enter
  , insertAbove
  , into
  , rebuild
  , replaceFocus
  )
import qualified Thena.Development.Cursor as Cursor
import Thena.Development.Partial (Partial (..))
import Thena.Errors (FailReason (..), MoveError)
import Thena.Ops
  ( AnswerKind
  , Env
  , Instr (..)
  , Op (..)
  , Operand (..)
  , Value (..)
  )
import Thena.Syntax.Lexer (isIdentifier)

-- --------------------------------------------------------------------------
-- The machine
-- --------------------------------------------------------------------------

-- | §7.2's four fields, less @globals@ (phase 6).
--
-- The field boundary is the backtracking boundary: 'proof' rewinds in full and
-- nothing else does (§7.4). That is why 'ProofState' is its own type rather
-- than a few fields here — a @Choice@ frame's snapshot has the same type as the
-- whole of what backtracks, so there is no sub-record to snapshot correctly or
-- incorrectly.
--
-- §7.2 calls the counter @fresh@. It is 'names' here because
-- 'Thena.Core.Term.fresh' is the function that mints from it, and a field and a
-- function of the same name are ambiguous to GHC and to the ear.
data Machine = Machine
  { exec  :: Exec
  , proof :: ProofState
  , names :: Int        -- ^ NOT backtrackable (§7.4)
  }
  deriving (Eq, Show)

data Exec = Exec
  { pc    :: [Instr]
  , env   :: Env
  , stack :: [Frame]
  }
  deriving (Eq, Show)

-- | Phase 4 pushes none of these — nothing nests until @Prove@ dispatches the
-- rule engine (phase 16) — but 'Exec' carries the stack because that is the
-- settled shape, and 'step'\'s return case below is written for it.
--
-- @Choice@ is missing on purpose: its @alts@ field is a @RuleIter@, which is
-- "Thena.Rules"' and does not exist. Adding the constructor at phase 16 does
-- not disturb 'Exec' or anything written here.
data Frame = Call
  { resume    :: [Instr]
  , resumeEnv :: Env
  }
  deriving (Eq, Show)

-- | Exactly the backtrackable part of the machine, and nothing else (§7.2,
-- §12 invariant 1).
--
-- The cursor is the whole of it: the development /is/ the cursor (§4.2), and
-- postponed constraints are @Pending@ links inside it (§3.3, §6.4), so there is
-- no second structure to keep in step and a checkpoint is one pointer copy.
--
-- **The focus backtracks with it**, and that is the point of it being in here
-- rather than beside it: a retried alternative must start where the abandoned
-- one started, not wherever the abandoned one wandered to.
newtype ProofState = ProofState { cursor :: Cursor }
  deriving (Eq, Show)

-- | The development a session starts with: one hole, at the least interesting
-- type there is.
--
-- Phase 13's @:theorem@ replaces this, and @:goal@ (this phase) replaces the
-- hole. It is a real hole rather than a placeholder term because every later
-- phase wants a goal to point at, and because @let ? goal : Type₀ in goal@ is
-- an honest development where @Trailing Type₀@ would be scaffolding pretending
-- to be a proof.
newProof :: Int -> (ProofState, Int)
newProof n =
  let (v, n1) = fresh n
   in (ProofState (enter (goalAt v (Universe (Level 0)))), n1)

goalAt :: Var -> Core -> Partial
goalAt v ty = Under (Component.Claim v (Ident "goal") ty) (Trailing (Free v))

-- | Γ at the focus (§4.5), which is what an identifier typed at the REPL must
-- be in scope in (§4.0 E1).
--
-- One line, and it is the whole of what phase 4's own @proofContext@ was
-- approximating: that one forgot the /entire/ chain, because there was no
-- focus to take a prefix of.
proofContext :: ProofState -> Context
proofContext = Cursor.context . cursor

-- | The development, rebuilt. O(depth), with most structure shared (§4.2).
proofDevelopment :: ProofState -> Partial
proofDevelopment = rebuild . cursor

-- | Replace the goal: retract the trailing hole, if the chain ends in one, and
-- claim a new one at the given type.
--
-- A session command, not an op, and deliberately: it is @:theorem@ in miniature
-- (§7.8 puts @:theorem@ on the session side, because starting a proof is what
-- creates a machine rather than something a machine does). Phase 13 replaces it.
-- | Throw the focus away and start it again as a hole at the given type.
--
-- The prefix is kept, so @assume A : Type₀@ then @:goal A -> A@ still means
-- something — @A@ is in scope for the new goal precisely because it is above
-- the focus. Everything from the focus down is discarded, which is what
-- "start again" means and is @abandon@ followed by @claim@ (table 2.7).
--
-- Refused in the core fragment, because a core focus cannot be replaced by a
-- chain. Phase 13 replaces the whole command.
setGoal :: Core -> Machine -> Either MoveError Machine
setGoal ty m =
  let (v, n1) = fresh (names m)
   in case replaceFocus (goalAt v ty) (cursor (proof m)) of
        Left e    -> Left e
        Right cur -> Right m { proof = ProofState cur, names = n1 }

-- --------------------------------------------------------------------------
-- Running it
-- --------------------------------------------------------------------------

-- | Whatever a rule body builds, a question is a prompt and a hint: nothing
-- about the question itself is predefined (§7.5).
data Question = Question String AnswerKind
  deriving (Eq, Show)

type Message = String

-- | Answers come back as text, always. A body that wants something richer turns
-- the text into it with ordinary instructions (§7.5).
type Answer = String

data Outcome
  = Continue Machine
  | Asking   Question   Machine  -- ^ the driver must supply an 'Answer'
  | Saying   Message    Machine  -- ^ the driver renders, then steps again
  | Finished Machine
  | Stuck    FailReason Machine  -- ^ carries the machine: failure does not end it
  deriving (Eq, Show)

-- | Put a program into the machine's @pc@ (§7.8). A command is a program loaded
-- into the /current/ machine, not a new machine.
load :: [Instr] -> Machine -> Machine
load is m = m { exec = (exec m) { pc = is, env = [] } }

-- | Is the machine waiting for an answer? The driver asks this before it calls
-- 'resumeAt', so that a line typed when nothing was asked is reported rather
-- than silently swallowed.
isAsking :: Machine -> Bool
isAsking m = case pc (exec m) of
  Bind _ (Ask _ _) : _ -> True
  Do     (Ask _ _) : _ -> True
  _                    -> False

-- | One instruction.
--
-- Stepping a 'Stuck' machine returns the same 'Stuck' with the same reason, and
-- stepping one that is 'Asking' asks again: both are idempotent, so no driver
-- loop can fall off the end of one (§7.5).
step :: Machine -> Outcome
step m = case pc (exec m) of
  [] -> case stack (exec m) of
    []        -> Finished m
    fr : stk  -> Continue m { exec = Exec (resume fr) (resumeEnv fr) stk }
  instr : rest -> perform instr rest m

-- | Deposit an answer into @env@ at the destination the asking instruction
-- named, and step past it.
--
-- The instruction is still at the head of @pc@ — 'perform' does not advance
-- past an 'Ask' — which is what lets this function know the destination without
-- 'Machine' carrying a field that is meaningful only sometimes. Decided by the
-- user 2026-08-21; §7.5's "already advanced past the request instruction" is
-- corrected to this, and its actual content (the state is data, not a
-- continuation) is untouched.
--
-- Called on a machine that is not asking, it changes nothing. The driver checks
-- first and reports; see "Thena.Driver".
resumeAt :: Answer -> Machine -> Machine
resumeAt a m = case pc (exec m) of
  Bind n (Ask _ _) : rest -> m { exec = (exec m) { pc = rest, env = (n, VText a) : env (exec m) } }
  Do     (Ask _ _) : rest -> m { exec = (exec m) { pc = rest } }
  _                       -> m

-- | An op that fails returns its reason and 'step' hands it here; nothing is
-- stored in the machine (§7.2).
--
-- Phase 16 gives this the unwind of §7.3 — pop frames until one has an
-- alternative left, restore the state it saved, run the next alternative. Until
-- @Choice@ exists there is nothing to unwind /to/, so every failure is 'Stuck'.
failure :: FailReason -> Machine -> Outcome
failure r m = Stuck r m

-- --------------------------------------------------------------------------
-- Performing one instruction
-- --------------------------------------------------------------------------

perform :: Instr -> [Instr] -> Machine -> Outcome
perform instr rest m = case operation instr of
  Ask prompt kind -> case text prompt of
    Left r  -> failure r m
    Right s -> Asking (Question s kind) m       -- NB: pc unchanged; see 'resumeAt'

  Say message -> case text message of
    Left r  -> failure r m
    Right s -> Saying s (advance m)

  Concat l r -> case (,) <$> text l <*> text r of
    Left e         -> failure e m
    Right (ls, rs) -> produce (VText (ls ++ rs)) m

  Assume name ty -> component Component.Assume name ty
  Claim  name ty -> component Component.Claim  name ty

  Along      -> navigate (keeping along)
  Into       -> navigate (keeping into)
  CrossType  -> navigate (keeping crossType)
  CrossValue -> navigate (keeping crossValue)
  Back       -> navigate (keeping back)
  Down part  -> navigate (down part)
  where
    operation i = case i of
      Bind _ o -> o
      Do     o -> o

    text = operandText (env (exec m))
    term = operandTerm (env (exec m))

    advance m' = m' { exec = (exec m') { pc = rest } }

    -- Bind the result if the instruction named a destination. An unbound
    -- destination on a producing op is fine; a bound one on an op that produces
    -- nothing is what phase 15's load-time pass rejects (§7.2).
    produce v m' = Continue $ case instr of
      Bind n _ -> advance m' { exec = (exec m') { env = (n, v) : env (exec m') } }
      Do _     -> advance m'

    -- 'Assume' and 'Claim' differ only in which component they build, and both
    -- produce the variable they bound: §7.3's sketch reads @?x <- claim S@.
    -- A move rewrites the cursor and produces no value, so there is nothing to
    -- bind: a @Bind@ on one is what phase 15's load-time pass rejects (§7.2).
    -- The counter comes back because descending under a core binder mints a
    -- variable, and only 'Thena.Core.Term.fresh' can (§4.0 D3).
    navigate f = case f (names m) (cursor (proof m)) of
      Left e          -> failure (CannotMove e) m
      Right (cur, n1) ->
        Continue (advance m { proof = ProofState cur, names = n1 })

    -- Every move but 'down' leaves the counter alone.
    keeping g n cur = fmap (\cur' -> (cur', n)) (g cur)

    component build name ty =
      case (,) <$> operandIdent (env (exec m)) name <*> term ty of
        Left r -> failure r m
        Right (i, t) ->
          let (v, n1) = fresh (names m)
              cur     = insertAbove (build v i t) (cursor (proof m))
           in produce (VTerm (Trailing (Free v))) m { proof = ProofState cur, names = n1 }

operandValue :: Env -> Operand -> Either FailReason Value
operandValue e o = case o of
  Lit v -> Right v
  Ref n -> maybe (Left (UnboundInBody n)) Right (lookup n e)

operandText :: Env -> Operand -> Either FailReason String
operandText e o = operandValue e o >>= \v -> case v of
  VText s -> Right s
  _       -> Left ExpectedText

-- | A 'VTerm' holding a chain rather than a term is not a term (§7.2).
operandTerm :: Env -> Operand -> Either FailReason Core
operandTerm e o = operandValue e o >>= \v -> case v of
  VTerm (Trailing t) -> Right t
  _                  -> Left ExpectedTerm

-- | The name a component will display. Checked against the lexer's own notion
-- of an identifier, because an 'Ident' that does not lex is one the printer
-- cannot print back (§2.6).
operandIdent :: Env -> Operand -> Either FailReason Ident
operandIdent e o = do
  s <- operandText e o
  if isIdentifier s then Right (Ident s) else Left (NotAnIdentifier s)
