-- | The stepper (§7.1, §7.2).
--
-- The control state is data, not Haskell's call stack: 'step' takes a 'Machine'
-- and returns an 'Outcome', and everything the machine cannot do itself it
-- yields through that one channel (§7.5). There is no @IO@ here and no
-- continuation anywhere inside a 'Machine' — the whole point is that an
-- in-flight execution is a value you can print, store, diff or send.
--
-- What is not here yet, and where it arrives:
--
--   * 'Frame'\'s @Choice@ constructor, @unwind@ past a live alternative, and
--     the peek that builds one — phase 16. They need alternatives to exist,
--     and alternatives need the rule engine.
module Thena.Engine
  ( -- * The machine
    Machine (..)
  , Exec (..)
  , Frame (..)
  , Development (..)
  , newDevelopment
  , focusContext
  , flatten
  , setGoal
  , newDevelopmentNamed

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
  , whereImpure

    -- * Going back (§7.7)
  , ChoicePoint (..)
  , choicePoints
  , RetryError (..)
  , retryFrom
  ) where

import Data.List (intercalate, nub)

import Thena.Core.Level (Level (..), levelVarName)
import Thena.Core.Context (Context)
import Thena.Core.Term
  ( Core (..)
  , close
  , GlobalName (..)
  , Ident (..)
  , Var
  , fresh
  , instantiate
  )
import Thena.Core.Reduce (whnf)
import Thena.Core.Typing (check, infer, sortOf)
import Thena.Core.Unify (UnifyResult (..), blockers, unify)
import qualified Thena.Development.Component as Component
import Thena.Development.Cursor
  ( Cursor
  , Focus (..)
  , along
  , back
  , crossType
  , crossValue
  , down
  , enter
  , focus
  , insertAbove
  , into
  , rebuild
  , dropFocus
  , replaceComponent
  , replaceCore
  , replaceFocus
  )
import qualified Thena.Development.Cursor as Cursor
import Thena.Development.Partial (Impure (..), Partial (..), extract)
import Thena.Errors (FailReason (..), MoveError (..), Position (..))
import Thena.Ops
  ( AnswerKind
  , Env
  , Rule (..)
  , Instr (..)
  , Op (..)
  , Operand (..)
  , Value (..)
  )
import Thena.Global.Env (GlobalEnv, InductiveDefinition, declaredNames)
import qualified Thena.Ops as Op
import Thena.Tactics.Eliminate (Elimination (..), eliminate)
import Thena.Rules (RuleBase, RuleIter, arities, clauses, dispatch, hasNext, next)
import Thena.Syntax.Lexer (isIdentifier)
import qualified Thena.Elaborate as Elaborate
import Thena.Surface.Concrete (Surface)

-- --------------------------------------------------------------------------
-- The machine
-- --------------------------------------------------------------------------

-- | §7.2's four fields.
--
-- The field boundary is the backtracking boundary: 'proof' rewinds in full and
-- nothing else does (§7.4). That is why 'Development' is its own type rather
-- than a few fields here — a @Choice@ frame's snapshot has the same type as the
-- whole of what backtracks, so there is no sub-record to snapshot correctly or
-- incorrectly.
--
-- 'rules' is the fifth field, added phase 15 and chosen by the user: the rule
-- base cannot live in 'GlobalEnv', because "Thena.Global.Env" sits below
-- "Thena.Ops" and so cannot mention a 'Thena.Ops.Rule' (@AGENDA.md@ item 25).
-- It does not backtrack for 'globals'\' reason — proving something is not what
-- changes the set of rules that exist.
--
-- §7.2 calls the counter @fresh@. It is 'names' here because
-- 'Thena.Core.Term.fresh' is the function that mints from it, and a field and a
-- function of the same name are ambiguous to GHC and to the ear.
data Machine = Machine
  { exec        :: Exec
  , development :: Development
    -- ^ the development, focused. **Named for what it is** (phase 37): it was
    -- @proof@, beside a @Session.sessionProof@ that meant a theorem, and one
    -- word for two things is where @docs/SESSION-STATE.md@ §5.5 came from.
  , globals     :: GlobalEnv  -- ^ NOT backtrackable (§7.4, §3.3.1)
  , rules       :: [RuleBase] -- ^ NOT backtrackable (§7.4) — phase 15; a list
                              -- of loaded bases, leftmost searched first (phase 22)
  , names       :: Int        -- ^ NOT backtrackable (§7.4)
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
-- **@Call@ is spelled twice in §7.2** — this frame, and phase 17b's op that
-- applies a 'Rule'. They are one apart, exactly as @Eliminate@'s two are: the
-- op /decides/ to call, the frame /is/ the call it is inside. This module sees
-- both, so it qualifies both — @Op.Call@ for the instruction and
-- @Thena.Engine.Call@ for the frame.
data Frame
  = Call
      { resume    :: [Instr]
      , resumeEnv :: Env
      }
  | Choice
      { resume    :: [Instr]
      , resumeEnv :: Env
      , alts      :: RuleIter    -- ^ the matches not yet tried, lazily (§7.6)
      , saved     :: Development  -- ^ the state before the first alternative ran
      , choiceId  :: Int         -- ^ what @retry ‹n›@ names it by
      , chosen    :: GlobalName  -- ^ the rule this frame is currently running
      , returned  :: Bool
        -- ^ has control already passed back out of this call? See 'resumeFrom'.
      , callArgs  :: [Value]
        -- ^ the arguments a @call@ was given, or @[]@ for a dispatch (phase
        -- 23). Kept beside 'entryEnv' rather than folded into it because each
        -- clause binds them to **its own** parameter names — clauses of one
        -- name need not agree on those, or even on how many there are. See
        -- 'seedFor', which is the one place the two are put together.
      , entryEnv  :: Env
        -- ^ the environment /every/ alternative of this choice point starts in
        -- (phase 17b). Empty for a plain @prove@; @[(hint, …)]@ when the
        -- dispatch carried one, because a hint belongs to the dispatch and not
        -- to the alternative that happened to be tried first.
        --
        -- Without it, backtracking into a second elaboration rule would enter
        -- it with @hint@ unbound and it would fail as an unbound 'Ref'. MS1
        -- never reaches that — the partition (\'Thena.Ops.usesHint\') leaves one
        -- hint rule, so a hinted dispatch is always deterministic and builds a
        -- @Call@ — so this field is on @AGENDA.md@'s standing list of things
        -- defined and not exercised. It is here rather than deferred because a
        -- second elaboration rule would otherwise be broken by construction.
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
newtype Development = Development { cursor :: Cursor }
  deriving (Eq, Show)

-- | The development a session starts with: one hole, at the least interesting
-- type there is.
--
-- Phase 13's @:theorem@ replaces this, and @:goal@ (this phase) replaces the
-- hole. It is a real hole rather than a placeholder term because every later
-- phase wants a goal to point at, and because @let ? goal : Type₀ in goal@ is
-- an honest development where @Trailing Type₀@ would be scaffolding pretending
-- to be a proof.
newDevelopment :: Int -> (Development, Int)
newDevelopment n =
  let (v, n1) = fresh n
   in (Development (enter (goalAt v (Universe (LZero)))), n1)

goalAt :: Var -> Core -> Partial
goalAt = goalAtNamed (Ident "goal")

goalAtNamed :: Ident -> Var -> Core -> Partial
goalAtNamed i v ty = Under (Component.Claim v i ty) (Trailing (Free v))

-- | Γ at the focus (§4.5), which is what an identifier typed at the REPL must
-- be in scope in (§4.0 E1).
--
-- One line, and it is the whole of what phase 4's own @focusContext@ was
-- approximating: that one forgot the /entire/ chain, because there was no
-- focus to take a prefix of.
focusContext :: Development -> Context
focusContext = Cursor.context . cursor

-- | The development, rebuilt. O(depth), with most structure shared (§4.2).
flatten :: Development -> Partial
flatten = rebuild . cursor

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
-- | @:theorem ‹name› : T@ — the same, but the hole carries the theorem's own
-- name rather than @goal@.
--
-- That name is what @:show@ and every error message will call it, and it is
-- also what the extracted term's outermost @let@ binds, so a proof of @id@
-- reads @let id = … in id@ rather than @let goal = … in goal@.
-- | @:theorem ‹name› : T@ — a **fresh** development, whose one hole is the
-- theorem's goal and carries the theorem's own name.
--
-- **Fresh, and not @:goal@ with a name** (phase 37, his ruling). Until then
-- @:theorem@ went through the same @replaceFocus@ that @:goal@ does, which
-- keeps everything above the focus — deliberate for @:goal@, where
-- @assume A : Type₀@ then @:goal A -> A@ still means something, and inherited
-- by @:theorem@, where nobody decided it. The effect was that a @claim@ left
-- open in the scratch development became part of the theorem's, and @qed@ then
-- failed with /"the hole h is still open"/ for a reason that had nothing to do
-- with the theorem.
--
-- **It could never have been a loss.** An inherited prefix can only be
-- @assume@s and @claim@s; an @assume@ puts a λ in the extracted term, and @qed@
-- certifies that term against the attempt's claim — so an inherited prefix
-- could not have produced something that certifies. It could only fail.
--
-- It cannot fail, which is why it returns no 'Either' where @setGoalNamed@ did:
-- 'enter' takes any 'Partial', where 'replaceFocus' has a focus to be wrong
-- about.
newDevelopmentNamed :: GlobalName -> Core -> Int -> (Development, Int)
newDevelopmentNamed (GlobalName x) ty n =
  let (v, n1) = fresh n
   in (Development (enter (goalAtNamed (Ident x) v ty)), n1)

setGoal :: Core -> Machine -> Either MoveError Machine
setGoal = goalNamed (Ident "goal")

goalNamed :: Ident -> Core -> Machine -> Either MoveError Machine
goalNamed i ty m =
  let (v, n1) = fresh (names m)
   in case replaceFocus (goalAtNamed i v ty) (cursor (development m)) of
        Left e    -> Left e
        Right cur -> Right m { development = Development cur, names = n1 }

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

-- | The single channel, in five shapes (§7.5).
--
-- 'Declaring' is the first that is neither a question nor a message: the
-- machine hands out a declaration it cannot install itself, because the global
-- environment is outside 'Development' and no instruction writes it (§3.7,
-- §7.4). Like 'Saying' it carries a machine already advanced past the
-- instruction — there is nothing to bind, so nothing has to be told where to
-- put an answer, which is what kept the 'Ask' instruction at the head of @pc@.
--
-- The driver checks and installs it (decided by the user, planning phase 6);
-- §7.5 gives @Certify@ the same shape at phase 12.
data Outcome
  = Continue  Machine
  | Asking    Question   Machine  -- ^ the driver must supply an 'Answer'
  | Saying    Message    Machine  -- ^ the driver renders, then steps again
  | Declaring InductiveDefinition Machine
                                  -- ^ the driver checks, installs, then steps again
  | Certifying Core Core Machine
                                  -- ^ the closed term the development stands for
                                  -- and the type it claims: the driver runs the
                                  -- kernel, then steps again (§5.3, §7.5)
  | Finished  Machine
  | Stuck     FailReason Machine  -- ^ carries the machine: failure does not end it
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
  [] -> case resumeFrom (stack (exec m)) of
    Nothing            -> Finished m
    Just (is, e, stk') -> Continue m { exec = Exec is e stk' }
  instr : rest -> perform instr rest m

-- | Where control goes when a body runs out of instructions.
--
-- **A 'Choice' frame is kept on success, not popped** (§7.3, DECIDED
-- 2026-08-20): the alternatives are still live, and the user may ask for
-- another solution after one has been found. §7.3's own sketch of this case
-- pops the frame, which contradicts the sentence immediately under it; the
-- 'returned' flag is how the two are reconciled. A frame that has already
-- served its return is stepped /over/ — it stays exactly where it is, because
-- it is an /inner/ choice point and 'unwind' must reach it before anything
-- below it — and the search continues for the next live return target.
--
-- 'returned' is not lateral validity (§4.0 I1): every other field stays
-- meaningful, and 'unwind' clears it again when it re-enters the call.
resumeFrom :: [Frame] -> Maybe ([Instr], Env, [Frame])
resumeFrom [] = Nothing
resumeFrom (fr : stk) = case fr of
  Thena.Engine.Call {} -> Just (resume fr, resumeEnv fr, stk)
  Choice { returned = False } ->
    Just ( resume fr
         , resumeEnv fr
         , Choice (resume fr) (resumeEnv fr) (alts fr) (saved fr)
                  (choiceId fr) (chosen fr) True (callArgs fr) (entryEnv fr)
             : stk
         )
  Choice { returned = True } ->
    (\(is, e, stk') -> (is, e, fr : stk')) <$> resumeFrom stk

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
failure r0 m = unwind (stack (exec m))
  where
    unwind [] = Stuck r0 m
    unwind (fr : stk) = case fr of
      Thena.Engine.Call {} -> unwind stk
      Choice {} -> case next (alts fr) of
        -- Cannot arise: the peek in 'perform' never builds a 'Choice' without
        -- a live alternative, and 'demote' unbuilds one the moment its last is
        -- taken. Written out rather than left to a pattern-match failure.
        Nothing       -> unwind stk
        -- **Announced, not silent.** §1 asks that search be a transparent,
        -- inspectable part of the machine rather than something that happens
        -- between commands, and an alternative taken inside a failing command
        -- is otherwise invisible: the user typed @retry 77@, @solve@ failed,
        -- @regret@ ran, and only the development moved.
        Just (r, it') -> Saying (took "backtracking to" fr r) m
          { development = saved fr
          , exec  = Exec (ruleBody r) (seedFor fr r) (demote fr r it' : stk)
          }

    took verb fr r = verb ++ " " ++ show (choiceId fr) ++ ": " ++ nameOfRule r

-- | Taking the /last/ alternative demotes the frame to a 'Call', by the same
-- peek that created it, so an exhausted 'Choice' never exists (§7.3). Three
-- things follow, and the third is the one that matters: @retry@ can only name a
-- choice that really has something left; a whole development snapshot is held
-- only where it can be used; and the choice-point view shows exactly the live
-- decisions and nothing dead.
demote :: Frame -> Rule -> RuleIter -> Frame
demote fr r it'
  | hasNext it' =
      Choice (resume fr) (resumeEnv fr) it' (saved fr) (choiceId fr) (ruleName r)
             False (callArgs fr) (entryEnv fr)
  | otherwise = Thena.Engine.Call (resume fr) (resumeEnv fr)

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

  -- Nothing to check here: the checks are "Thena.Global.Declare"'s and the
  -- driver runs them (§7.5). The op's whole job is to make the declaration a
  -- step you can watch rather than something that happens between commands.
  DefineData d -> Declaring d (advance m)

  -- Purity and extraction are one traversal (§5.3); the kernel itself is the
  -- driver's to run, exactly as a declaration's checks are.
  Certify stated -> case term stated of
    Left r   -> failure r m
    Right ty -> case extract (flatten (development m)) of
      Left why -> failure (NotYetPure (whereImpure why)) m
      Right t  -> Certifying t ty (advance m)

  -- The life of a hole (thesis tables 2.7, 2.8). All six act on the component
  -- at the focus, and all six rewrite 'Development', which is why they are ops
  -- and not driver commands (§12 invariant 3).
  -- The inner hole gets its **own** identifier, which the thesis writes @x'@ —
  -- @?x : S@ ⟹ @?x ≐ (?x' : S . x')@. It shared the outer one until phase 24b,
  -- and two components with one name is what stopped @goto ‹name›@ working.
  Attack -> onHole $ \c -> case c of
    Component.Claim x i s ->
      let (v, n1) = fresh (names m)
          i'      = Cursor.freshIdent (Cursor.identsIn (cursor (development m))) i
       in Right ( Component.Guess x i (Under (Component.Claim v i' s) (Trailing (Free v))) s
                , n1 )
    _ -> Left NotAHole

  -- Table 2.8's intro-∀ and intro-let, which "only replace constructions of the
  -- shape @?x : S . x@" — anything else is made ready by @attack@ first. So the
  -- shape test is the specification, not a shortcut.
  -- **The name is optional** (MS4 phase 41b). Given, it is the binder's; absent,
  -- the binder keeps the one written in the type. Read through 'operandIdent',
  -- so it is checked to be something the printer can print back (§2.6).
  Intro mn -> case traverse (operandIdent (env (exec m))) mn of
    Left r    -> failure r m
    Right nm  -> onHole $ \c -> case c of
      Component.Guess x i g ty ->
        (\(g', n1) -> (Component.Guess x i g' ty, n1))
          <$> introduce (globals m) contextAt (names m) nm g
      _ -> Left NotReadyToIntroduce

  -- **Table 2.7's side condition @Θ ⊩ t : S@, enforced** (phase 25b). It was
  -- documented and not checked until this phase, so an ill-typed guess sat in
  -- the development until @qed@ or @:revalidate@ found it.
  --
  -- @⊩@ is the /partial/ judgement, but @try@ only ever attaches @Trailing t@ —
  -- never a nested development — so for this one op it degenerates to @check@.
  -- That is 'Thena.Development.Validate.chain' read at its @Guess@ case: what
  -- it asks of a guess is @chain … (Just s) g@, and for a trailing @g@ that is
  -- exactly this. The two agree because it is the same judgement, not because
  -- the check was written twice.
  --
  -- Γ comes from 'forget', so a hole in @t'@ is a hypothesis with no value and
  -- checks fine — @try (Just A a)@ with @A@ and @a@ still open is legal, which
  -- is what @unify-refine@ depends on.
  --
  -- Written out rather than through 'onHole' so the counter threads on the
  -- failing path too: @check@ mints variables opening scopes, and rewinding
  -- past them could hand a later @fresh@ a token an error message already used.
  Try t -> case term t of
    Left r  -> failure r m
    Right t' -> case focus (cursor (development m)) of
      OnComponent (Component.Claim x i s) ->
        -- **The level obligations are dropped**, here and at every other
        -- typing call in this module: "Thena.Core.Typing"'s header says why
        -- once, and @qed@ re-collects what the finished development owes.
        case check (globals m) contextAt (names m) t' s of
          (Left e,   _, n1) -> failure (GuessIllTyped e) m { names = n1 }
          (Right (), _, n1) ->
            case replaceComponent (Component.Guess x i (Trailing t') s)
                                  (cursor (development m)) of
              Left e    -> failure (CannotMove e) m { names = n1 }
              Right cur ->
                Continue (advance m { development = Development cur, names = n1 })
      OnComponent _ -> failure NotAHole m
      _             -> failure (CannotMove NotOnTheSpine) m

  Regret -> onHole $ \c -> case c of
    Component.Guess x i _ s -> Right (Component.Claim x i s, names m)
    _                       -> Left NotAGuessHere

  -- Table 2.7's side condition is that the guess is pure, and 'extract' is what
  -- decides that (§5.3) — the same traversal @Certify@ uses, so the two cannot
  -- come to disagree about what pure means.
  Solve -> onHole $ \c -> case c of
    Component.Guess x i g s -> case extract g of
      Right v  -> Right (Component.Define x i v s, names m)
      Left why -> Left (NotYetPure (whereImpure why))
    _ -> Left NotAGuessHere

  -- @x ∉ Θ'@: the hole may not be referred to by anything below it. Checked
  -- against the rebuilt development for 'replaceCore''s reason — an occurrence
  -- may be anywhere, not only in the neighbouring link.
  Abandon -> case focus (cursor (development m)) of
    OnComponent c
      | isHole c -> case dropFocus (cursor (development m)) of
          Left e    -> failure (CannotMove e) m
          Right cur -> Continue (advance m { development = Development cur })
      | otherwise -> failure NotAHole m
    _ -> failure (CannotMove NotOnTheSpine) m

  -- Dispatch (§7.3). The goal is the focus, so there is nothing to read: the
  -- iterator is built from the cursor, the first match's body becomes @pc@, and
  -- what would have been on Haskell's stack goes into the frame.
  --
  -- **It carries nothing** (MS4 phase 41). It took an optional surface term
  -- from phase 17b to here, and that term partitioned the rule base and seeded
  -- the callee's environment under the name @hint@. Both are gone: elaboration
  -- is a rule called by name, so it was never a dispatch, and there is no magic
  -- name in the instruction language any more.
  Prove -> case next it of
    Nothing       -> failure NoRuleMatched m
    Just (r, it')
      -- Announced only when the dispatch was a real decision, which is
      -- exactly when a 'Choice' was built. A message marks a choice; where
      -- there was one candidate there was none, and a line per deterministic
      -- call would be noise (§1, §7.5).
      | hasNext it' ->
          Saying ("chose " ++ show (names m) ++ ": " ++ nameOfRule r)
                 (entering r (Choice rest (env (exec m)) it' (development m)
                                     (names m) (ruleName r) False [] [])
                             m { names = names m + 1 })
      | otherwise ->
          Continue (entering r (Thena.Engine.Call rest (env (exec m))) m)
    where
      it = dispatch (rules m) (globals m) (cursor (development m))

      -- THE PEEK, decided 2026-08-20. A 'Choice' is built only when there
      -- really is another alternative — Prolog's determinism detection.
      -- Otherwise this is an ordinary 'Call', carrying no iterator, no
      -- snapshot and no identifier. The cost is Prolog's own: one more head
      -- match is computed than is used.
      entering r fr k =
        k { exec = Exec (ruleBody r) [] (fr : stack (exec m)) }

  -- **Elaboration: the op emits the program, it does not run it** (MS4 phase
  -- 41). "Thena.Elaborate" compiles one surface node into a short list of
  -- instructions — ops that already exist, and an @Elaborate@ of each sub-term
  -- — and they go in front of what was already queued.
  --
  -- That is what makes step 2 a decomposition: the rule clauses that replace
  -- this will emit the same instructions from a body. Until they do, @:step@
  -- shows an elaboration running as ordinary instructions.
  Elaborate t -> case surface t of
    Left r  -> failure r m
    Right s -> case Elaborate.compile (globals m) contextAt (names m) s of
      Left r          -> failure r m
      Right (is, n1)  ->
        Continue m { exec = (exec m) { pc = is ++ rest }, names = n1 }

  -- **Call by name: the same search as @Prove@, over a narrower candidate
  -- list** (§8, phase 23). The user's own framing, and it is why this case now
  -- reads almost exactly like @Prove@'s above:
  --
  -- > @Prove@ means \"search any rule that fits and wants to try solving the
  -- > goal\" and @Call@ means \"see if any rules named like this can succeed\".
  -- > Calling is not that different from searching. Calling is essentially what
  -- > Prolog does.
  --
  -- So a call gets the peek, a @Choice@ frame, @:choices@, @retry@ and
  -- backtracking, none of which it had. The @Call@ frame is **not** gone — it
  -- is still what the peek builds when exactly one clause applies, for both
  -- kinds of dispatch (@MS2.md@ guessed it might disappear; it does not).
  --
  -- Arguments are evaluated **before** the candidates are found, because their
  -- number is one of the filters.
  Op.Call nm args -> case traverse (operandValue (env (exec m))) args of
    Left e   -> failure e m
    Right vs -> case next (it vs) of
      Nothing -> failure (NoClauseMatched nm (length vs) (arities (rules m) nm)) m
      Just (r, it')
        | hasNext it' ->
            Saying ("chose " ++ show (names m) ++ ": " ++ nameOfRule r)
                   (entering vs r (Choice rest (env (exec m)) (it' ) (development m)
                                     (names m) (ruleName r) False vs [])
                            m { names = names m + 1 })
        | otherwise ->
            Continue (entering vs r (Thena.Engine.Call rest (env (exec m))) m)
    where
      it vs = clauses (rules m) (globals m) (cursor (development m)) nm (length vs)

      -- The callee's parameters, bound to the arguments. 'clauses' has already
      -- filtered on arity, so the two lists agree by construction — and the
      -- frame keeps @vs@ rather than this, because the next clause may name its
      -- parameters differently ('seedFor').
      entering vs r fr k =
        k { exec = Exec (ruleBody r) (zip (ruleParams r) vs) (fr : stack (exec m)) }

  -- §3.7's elimination tactic (phase 17). The goal is the focus, as with the
  -- six hole ops; the target is an operand, for the reason 'Try' takes one —
  -- there is nowhere else it could come from.
  --
  -- Qualified because "Thena.Core.Term" has an 'Eliminate' too. The two are
  -- exactly one apart: this op /decides/ to eliminate, that node /is/ the
  -- elimination it builds. The same shape as @Component.Claim@ beside 'Claim'.
  Op.Eliminate tgt -> case term tgt of
    Left r  -> failure r m
    Right t -> case focus (cursor (development m)) of
      OnComponent (Component.Claim x i s) ->
        case eliminate (globals m) contextAt (names m) s t of
          (Left e,   n1) -> failure (CannotEliminate e) m { names = n1 }
          (Right el, n1) ->
            -- The methods go in above the goal, innermost first, so the goal
            -- can see them; then the goal itself becomes the guess that uses
            -- them. Both halves are one op because a half-applied elimination
            -- — holes claimed, nothing attached — is not a state any rule
            -- should be able to observe.
            let holes = foldl claimAbove (cursor (development m)) (elimMethods el)
                -- Freshened one at a time, against the development as it grows,
                -- so two methods never share a name either (phase 24b).
                claimAbove c (v, hi, hty) =
                  insertAbove
                    (Component.Claim v (Cursor.freshIdent (Cursor.identsIn c) hi) hty) c
                guess = Component.Guess x i (Trailing (elimTerm el)) s
             in case replaceComponent guess holes of
                  Left e    -> failure (CannotMove e) m
                  Right cur ->
                    Saying (subgoalMessage (elimMethods el))
                           (advance m { development = Development cur, names = n1 })
      OnComponent _ -> failure NotAHole m
      _             -> failure (CannotMove NotOnTheSpine) m

  -- Thesis §2.7's @naive-refine@ with the search taken out (phase 25): the
  -- head's type is inferred here, and 'saturate' does the walking.
  Apply f -> case term f of
    Left r   -> failure r m
    Right hd -> case infer (globals m) contextAt (names m) hd of
      (Left e,   _, n1) -> failure (NotTypeable e) m { names = n1 }
      (Right ty, _, n1) -> saturate hd ty m { names = n1 }

  Concat l r -> case (,) <$> text l <*> text r of
    Left e         -> failure e m
    Right (ls, rs) -> produce (VText (ls ++ rs)) m

  Assume name ty -> component Component.Assume name ty
  Claim  name ty -> component Component.Claim  name ty

  -- The three reads (§7.2, phase 24). "Always named, never a general
  -- getState": a body asks a particular question of the development and gets a
  -- particular answer, so nothing hands it the machine.
  --
  -- The goal is the type the focused component is /claimed at/ — what the
  -- development writes down, never what @infer@ derives (§4.5). A focus with
  -- nothing written down has no goal, which is a failure and not an empty
  -- answer.
  -- A name nothing has taken (phase 24c). Avoids the development's own
  -- identifiers **and** the globals, so a generated hole never shadows a
  -- datatype or a theorem.
  FreshName hint -> case operandIdent (env (exec m)) hint of
    Left r  -> failure r m
    Right i ->
      let inUse = Cursor.identsIn (cursor (development m))
                    ++ [ Ident g | GlobalName g <- declaredNames (globals m) ]
          Ident n = Cursor.freshIdent inUse i
       in produce (VText n) m

  -- **Which component am I standing on?** (MS4 phase 41c) — the companion to
  -- @goal@, which answers what it is claimed /at/. Yielded as a term so that
  -- @goto@ reads it without a second shape.
  --
  -- Refused off the spine for the reason every component op is: a core subterm
  -- is not a component and has no variable of its own.
  Here -> case focus (cursor (development m)) of
    OnComponent c -> produce (VTerm (Trailing (Free (variableOf c)))) m
    _             -> failure (CannotMove NotOnTheSpine) m

  -- **The two term-construction ops** (MS4 phase 41d) — the first ops that
  -- build a term rather than reading, moving or installing one.
  --
  -- Neither touches the development or the focus, and neither type-checks what
  -- it builds: a constructed term is checked where it is /used/, by @claim@'s
  -- side condition or @try@'s.
  Arrow a b -> case (,) <$> term a <*> term b of
    Left r          -> failure r m
    Right (dom, cod) ->
      let (v, n1) = fresh (names m)
       in produce (VTerm (Trailing (Pi (Ident "_") dom (close v cod))))
                  m { names = n1 }

  ApplyTo f x -> case (,) <$> term f <*> term x of
    Left r         -> failure r m
    Right (f', x') -> produce (VTerm (Trailing (App f' x'))) m

  Goal -> case Cursor.expectedType (cursor (development m)) of
    Just t  -> produce (VTerm (Trailing t)) m
    Nothing -> failure NoGoalHere m

  Typing t -> case term t of
    Left r  -> failure r m
    Right t' -> case infer (globals m) contextAt (names m) t' of
      (Left e,   _, n1) -> failure (NotTypeable e) m { names = n1 }
      (Right ty, _, n1) -> produce (VTerm (Trailing ty)) m { names = n1 }

  -- Thesis §2.7's @=@-binding. The type is inferred, because that is what makes
  -- it a definition: a definition's type is determined by its value.
  Define name v -> case (,) <$> operandIdent (env (exec m)) name <*> term v of
    Left r -> failure r m
    Right (i, val) -> case infer (globals m) contextAt (names m) val of
      (Left e,   _, n1) -> failure (NotTypeable e) m { names = n1 }
      (Right ty, _, n1)
        | i `elem` Cursor.identsIn (cursor (development m)) -> failure (taken i) m { names = n1 }
        | otherwise ->
            let (x, n2) = fresh n1
                cur     = insertAbove (Component.Define x i val ty) (cursor (development m))
             in produce (VTerm (Trailing (Free x)))
                        m { development = Development cur, names = n2 }

  Along      -> navigate (keeping along)
  Into       -> navigate (keeping into)
  CrossType  -> navigate (keeping crossType)
  CrossValue -> navigate (keeping crossValue)
  Back       -> navigate (keeping back)

  -- Not 'navigate' with the others: it reads its operand first, and it takes
  -- **either** shape (phase 24b).
  --
  --   * a name — what a person types, searched from the root, so a hole is
  --     reachable from anywhere. The user's correction: *"This instruction is
  --     supposed to be useful always, not only when you already can see the
  --     hole right above you."*
  --   * a variable — what a rule body holds, since @claim@ and @define@ produce
  --     it. A body may **not** go by name: 'Cursor.freshIdent' means the name it
  --     asked for is not always the name it got.
  Goto v -> case operandValue (env (exec m)) v of
    Left r -> failure r m
    Right val -> case val of
      VText n              -> move (Cursor.gotoNamed (Ident n))
      VTerm (Trailing (Free x)) -> move (Cursor.goto x)
      _                    -> failure (CannotMove NoSuchHole) m
    where
      move f = case f (cursor (development m)) of
        Left e    -> failure (CannotMove e) m
        Right cur -> Continue (advance m { development = Development cur })
  Down part  -> navigate (down part)

  -- Commit a whnf at the core focus (§4.7). Not 'navigate': a move never has
  -- anything to say, and this one sometimes does — an orphaned hole is
  -- reported, not prevented, so a non-empty report goes out through 'Saying'
  -- exactly as 'Say' already does, rather than being silently swallowed.
  Reduce -> case focus (cursor (development m)) of
    OnTerm _ _ t ->
      let t' = whnf (globals m) (Cursor.context (cursor (development m))) t
       in case replaceCore t' (cursor (development m)) of
            Left e -> failure (CannotMove e) m
            Right (cur', orphaned) ->
              let m' = advance m { development = Development cur' }
               in case orphaned of
                    [] -> Continue m'
                    is -> Saying (orphanMessage is) m'
    _ -> failure (CannotMove NotInCore) m

  -- Unification writes to the development, so it is an op and not a driver
  -- command (§12 invariant 3): what it changes has to backtrack with the rest
  -- of the proof state. What it has to say — which holes it solved, what it
  -- parked — goes out through 'Saying', exactly as 'Reduce' reports an orphan.
  Unify l r -> case (,) <$> term l <*> term r of
    Left e       -> failure e m
    Right (a, b) ->
      let cur = cursor (development m)
       in case infer (globals m) (Cursor.context cur) (names m) a of
            (Left e, _, n1)  -> failure (NotTypeable e) m { names = n1 }
            (Right ty, _, n1) -> case unify (globals m) cur n1 a b ty of
              (Failed reason, _, n2) -> failure reason m { names = n2 }
              (result, cur', n2) ->
                Saying (unifyMessage cur' result)
                       (advance m { development = Development cur', names = n2 })
  where
    operation i = case i of
      Bind _ o -> o
      Do     o -> o

    text    = operandText (env (exec m))
    term    = operandTerm (env (exec m))
    surface = operandSurface (env (exec m))

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
    navigate f = case f (names m) (cursor (development m)) of
      Left e          -> failure (CannotMove e) m
      Right (cur, n1) ->
        Continue (advance m { development = Development cur, names = n1 })

    -- Every move but 'down' leaves the counter alone.
    keeping g n cur = fmap (\cur' -> (cur', n)) (g cur)

    contextAt = focusContext (development m)

    -- Claim a hole for every Π domain, extending the spine as it goes, and
    -- stop at the first type that is not a Π — that is what makes @apply@
    -- saturating rather than searching (§2.7, 'Thena.Ops.Apply').
    --
    -- **Each hole goes above the focus, and the context is re-read each time**,
    -- so a later domain may mention an earlier hole and still be in scope:
    -- @Just : ∀ (A : Type₀) (a : A) -> Maybe A@ claims @?A@ and then @?a : A@.
    -- That is also why 'whnf' cannot be given @contextAt@ — that one is fixed
    -- at the focus this instruction started from.
    saturate hd ty m' = case whnf (globals m') (focusContext (development m')) ty of
      Pi i dom sc ->
        let (v, n1) = fresh (names m')
            i'      = Cursor.freshIdent (Cursor.identsIn (cursor (development m'))) i
            cur     = insertAbove (Component.Claim v i' dom) (cursor (development m'))
         in saturate (App hd (Free v)) (instantiate (Free v) sc)
                     m' { development = Development cur, names = n1 }
      _ -> produce (VTerm (Trailing hd)) m'

    taken (Ident n) = NameTaken n

    isHole c = case c of
      Component.Claim {} -> True
      Component.Guess {} -> True
      _                  -> False

    -- Rewrite the component at the focus, or say why not. Every hole op has
    -- this shape, which is why it is written once.
    onHole f = case focus (cursor (development m)) of
      OnComponent c -> case f c of
        Left r         -> failure r m
        Right (c', n1) -> case replaceComponent c' (cursor (development m)) of
          Left e    -> failure (CannotMove e) m
          Right cur -> Continue (advance m { development = Development cur, names = n1 })
      _ -> failure (CannotMove NotOnTheSpine) m

    component build name ty =
      case (,) <$> operandIdent (env (exec m)) name <*> term ty of
        Left r -> failure r m
        Right (i, t)
          -- **Refused, not renamed** (phase 24c). Identifiers stay unique — so
          -- @goto ‹name›@ keeps working — but deciding /what/ the name is
          -- belongs to the rule, through @fresh-name@.
          | i `elem` Cursor.identsIn (cursor (development m)) -> failure (taken i) m
          -- Table 2.7's side condition on both @assume@ and @claim@:
          -- @Θ ⊢ S : Type@ (phase 25f). 'sortOf' is the same check
          -- @revalidate@ runs on these components through @Validate@'s
          -- @isAType@, so the op and the kernel cannot disagree about what a
          -- type is — the same argument that made phase 25b use 'check' for
          -- @try@ rather than a second opinion.
          --
          -- **The level is discarded.** The condition is "S is a type", not
          -- "S is a type at level ℓ"; nothing here compares levels, so there
          -- is nothing for a level to be constrained against.
          | otherwise -> case sortOf (globals m) contextAt (names m) t of
              (Left e,  _, n1) -> failure (BinderNotAType e) m { names = n1 }
              (Right _, _, n1) ->
                let (v, n2) = fresh n1
                    cur     = insertAbove (build v i t) (cursor (development m))
                 in produce (VTerm (Trailing (Free v)))
                            m { development = Development cur, names = n2 }

-- | What @eliminate@ says: the subgoals it opened, by the names it gave them.
--
-- It is 'Saying' rather than 'Continue' for 'Reduce'\'s reason — an op that
-- changes the development in a way the user cannot see at the focus has to say
-- so. After an elimination the focus is still the goal, now a guess, while the
-- new holes are above it and off screen.
subgoalMessage :: [(Var, Ident, Core)] -> String
subgoalMessage [] = "no subgoals"
subgoalMessage hs =
  "subgoals: " ++ intercalate ", " [ n | (_, Ident n, _) <- hs ]

-- | What 'Reduce' says when it orphans one or more holes (§4.7). Plain text:
-- these are the identifiers the user themselves wrote for a 'Claim' or a
-- 'Guess', not a term needing "Thena.Repl"'s freshening.
-- | What @unify@ reports. §9's deliverable in one line: which holes it solved,
-- or what is parked and what each is waiting on — the blockers being derived
-- from the development rather than stored (§6.1).
--
-- **Level metas are named beside the holes** (MS3 phase 33), because solving one
-- changes the development just as much and @already equal@ would otherwise be
-- said about two terms that were not equal until a level was pinned down. The
-- @?ℓ@ spelling is the printer's own, so the two sorts tell themselves apart.
unifyMessage :: Cursor -> UnifyResult -> String
unifyMessage cur result = case result of
  Failed _          -> ""     -- never reached: a failure goes out through 'Stuck'
  Solved [] []      -> "already equal"
  Solved xs ls      -> "solved: " ++ what xs ls
  Deferred xs ls ks ->
    (if null xs && null ls then "" else "solved: " ++ what xs ls ++ "; ")
      ++ "parked " ++ show (length ks) ++ " constraint(s), blocked on "
      ++ intercalate ", " (map nameOfVar (nub (concatMap (blockers cur) ks)))
  where
    what xs ls = intercalate ", " (map nameOfVar xs ++ map levelVarName ls)

    -- The identifier the user gave the hole, read off the development. A 'Var'
    -- has no name of its own (§3.5), and "Thena.Repl" is where display lives —
    -- but a message is text by the time it leaves here, so the lookup happens
    -- against the components rather than against a printer.
    nameOfVar x = case [ i | c <- componentsOf (rebuild cur), (y, Ident i) <- [named c], y == x ] of
      i : _ -> i
      []    -> "?"

    named c = case c of
      Component.Assume y i _   -> (y, i)
      Component.Define y i _ _ -> (y, i)
      Component.Claim  y i _   -> (y, i)
      Component.Guess  y i _ _ -> (y, i)

    -- **Into a guess's body too**, and that is not optional: a hole claimed
    -- inside a guess is where most of them are once @attack@ and @intro@ have
    -- run, and without this line 'nameOfVar' fell through to @"?"@ for every
    -- one of them — @unify@ said @solved: ?@ where it meant @solved: A@.
    -- Found 2026-08-26 by the user, driving @apply@ under an @intro@.
    componentsOf p = case p of
      Trailing _     -> []
      Under c rest   -> c : inside c ++ componentsOf rest
      Pending _ rest -> componentsOf rest
      where
        inside c = case c of
          Component.Guess _ _ g _ -> componentsOf g
          _                       -> []

orphanMessage :: [Ident] -> String
orphanMessage is = "reduced; now unreachable: " ++ intercalate ", " (map identString is)
  where
    identString (Ident s) = s

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

-- | An unelaborated tree, and nothing else (§7.2). Shaped like 'operandText'
-- and 'operandTerm', and phase 17b's reason for existing at all: 'VSurface' had
-- no reader before elaboration had a rule.
operandSurface :: Env -> Operand -> Either FailReason Surface
operandSurface e o = operandValue e o >>= \v -> case v of
  VSurface t -> Right t
  _          -> Left ExpectedSurface

-- | The name a component will display. Checked against the lexer's own notion
-- of an identifier, because an 'Ident' that does not lex is one the printer
-- cannot print back (§2.6).
operandIdent :: Env -> Operand -> Either FailReason Ident
operandIdent e o = do
  s <- operandText e o
  if isIdentifier s then Right (Ident s) else Left (NotAnIdentifier s)

-- | Which component stopped 'extract'. Purely a translation from
-- "Thena.Development.Partial"\'s local 'Impure' into the shared vocabulary —
-- 'Thena.Errors' may not import @Partial@ (it sits below @Core@), so the
-- mapping lives on this side.
whereImpure :: Impure -> Position
whereImpure i = case i of
  StillAHole x n     -> TheHole x n
  StillAGuess x n    -> GuessOf x n
  StillConstrained _ -> ConstraintAt 1

-- | Table 2.8's @intro-∀@ and @intro-let@, inside a guess.
--
-- The thesis's own note is the specification: the introduction tactics "only
-- replace constructions of the shape @?x : S . x@". **Within a guess body there
-- is at most one such position, and it is the bottom one** — everything above
-- it is an assumption, a definition or a guess, none of which has that shape.
-- So "find the shape" and "walk to the end of the chain" are the same
-- traversal, and there is nothing to disambiguate.
--
-- Walking rather than matching the body directly is what lets introductions
-- accumulate: after one @intro@ the body is @λ A : Type₀ . ? h : A -> A . h@,
-- and the next @intro@ has to reach past the λ it just made. Γ grows as it
-- goes, because the hole's type is whnf'd where the hole actually is.
--
-- It stays inside the guess, and that is why @attack@ exists: introducing at
-- the top of the whole development would change what the development proves,
-- whereas inside a guess the guess's own type absorbs the binders.
introduce
  :: GlobalEnv -> Context -> Int -> Maybe Ident -> Partial
  -> Either FailReason (Partial, Int)
introduce env ctx n nm p = case p of
  Under (Component.Claim v i s) (Trailing (Free v'))
    | v == v' -> case s of
        -- @intro-let@ reads the type AS WRITTEN, and must come first.
        -- 'Thena.Core.Reduce.whnf' δ-reduces a term-level @let@ away (§5.1), so
        -- a whnf'd type is never a 'Let' and this branch was unreachable when
        -- it sat inside the @case whnf@ below — table 2.8's second
        -- introduction rule could not fire at all. Found and fixed planning
        -- phase 15, while writing the @intro-let@ rule's head; §5.1 and §7.2
        -- both carry it.
        Let j val sty cod ->
          Right (opened (Component.Define y (named j) val sty) (instantiate (Free y) cod))
        -- @intro-∀@ reduces first, because a goal typed @id Type₀ (Nat -> Nat)@
        -- is a Π and must be introduced (§8's own example, from the other side).
        _ -> case whnf env ctx s of
          Pi j dom cod -> Right (opened (Component.Assume y (named j) dom) (instantiate (Free y) cod))
          _            -> Left NothingToIntroduce
      where
        -- The caller's name if there is one, the type's otherwise.
        named j = maybe j id nm
        (y, n1) = fresh n
        (h, n2) = fresh n1
        opened binder rest =
          ( Under binder (Under (Component.Claim h i rest) (Trailing (Free h)))
          , n2
          )
  Under c rest ->
    (\(rest', n1) -> (Under c rest', n1))
      <$> introduce env (ctx ++ [Component.forget c]) n nm rest
  _ -> Left NotReadyToIntroduce

-- --------------------------------------------------------------------------
-- Going back into an untried alternative (§7.7)
-- --------------------------------------------------------------------------

-- | One live choice point, for the view @:choices@ prints.
--
-- Every 'Choice' frame on the stack is live, by the peek's own invariant
-- (§7.3), so this is a projection and not a filter.
data ChoicePoint = ChoicePoint
  { pointId    :: Int          -- ^ what @retry ‹n›@ names it by
  , pointRule  :: GlobalName   -- ^ the alternative it is running now
  , pointAlts  :: [GlobalName] -- ^ the ones still untried, in dispatch order
  }
  deriving (Eq, Show)

-- | The live choice points, **nearest first** — which is also the order
-- @retry@ with no argument walks.
choicePoints :: Machine -> [ChoicePoint]
choicePoints m =
  [ ChoicePoint (choiceId fr) (chosen fr) (map ruleName (drainIter (alts fr)))
  | fr@Choice {} <- stack (exec m)
  ]

-- | A rule's name as text. 'Thena.Repl' owns display, but a 'Message' is text
-- by the time it leaves here — the same bargain 'unifyMessage' already struck.
nameOfRule :: Rule -> String
nameOfRule r = case ruleName r of GlobalName g -> g

drainIter :: RuleIter -> [Rule]
drainIter it = case next it of
  Nothing        -> []
  Just (r, rest) -> r : drainIter rest

-- | Why @retry@ could not.
--
-- Two cases and not three: there is no \"that choice is exhausted\", because
-- 'demote' unbuilds a 'Choice' the moment its last alternative is taken, so an
-- exhausted one never exists (§7.3).
data RetryError = NoChoicePoint | UnknownChoice Int
  deriving (Eq, Show)

-- | Unwind to a choice point and take its next alternative (§7.7).
--
-- **The same three moves as 'failure''s unwind**, with a target instead of a
-- reason: pop frames until the wanted one, restore the state it saved, and set
-- @pc@ to the next alternative with the frame pushed back and its iterator
-- advanced. That it /is/ the same operation is the point — §7.7's \"a user's
-- pick and the engine's pick are the same event, so going back to either is one
-- command, not two\".
--
-- Returns a note saying what it did, because @retry@ takes one /alternative/
-- and not one command: it pops past any 'Call' frames in between, which may be
-- several commands back.
-- | The environment an alternative of this choice point starts in.
--
-- **One expression covers a dispatch and a call**, which is the whole reason
-- @Call@ could stop being a separate mechanism. A dispatch has no arguments and
-- 'Thena.Rules.dispatch' skips parameterised rules, so this is just its
-- 'entryEnv' — the hint, or nothing. A call carries no hint and binds its
-- arguments to the clause's own parameters, and 'Thena.Rules.clauses' has
-- already guaranteed the two lists are the same length.
seedFor :: Frame -> Rule -> Env
seedFor fr r = entryEnv fr ++ zip (ruleParams r) (callArgs fr)

retryFrom :: Maybe Int -> Machine -> Either RetryError (Machine, String)
retryFrom target m = go (0 :: Int) (stack (exec m))
  where
    missing = maybe NoChoicePoint UnknownChoice target

    go _ [] = Left missing
    go popped (fr : stk) = case fr of
      Choice {} | maybe True (== choiceId fr) target -> case next (alts fr) of
        Nothing       -> Left missing      -- cannot arise; see 'demote'
        Just (r, it') -> Right
          ( m { development = saved fr
              , exec  = Exec (ruleBody r) (seedFor fr r) (demote fr r it' : stk)
              }
          , note (choiceId fr) (ruleName r) popped
          )
      _ -> go (popped + 1) stk

    note i (GlobalName g) popped =
      "retrying " ++ show i ++ ": " ++ g
        ++ (if popped == 0 then "" else " (" ++ show popped ++ " frame(s) dropped)")

-- | The variable a component binds. What @here@ answers.
--
-- Every component has one; the four constructors differ in what else they
-- carry, which is why this is a fold and not a field.
variableOf :: Component.Component -> Var
variableOf c = case c of
  Component.Assume v _ _   -> v
  Component.Define v _ _ _ -> v
  Component.Claim  v _ _   -> v
  Component.Guess  v _ _ _ -> v
