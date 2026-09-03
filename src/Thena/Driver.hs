-- | The session, the commands that act on it, and the loop of §7.8.
--
-- Nothing in this module or below it may assume a terminal, block on 'getLine',
-- or write to stdout (§2.1, §12 invariant 4). 'command' and 'answer' are pure
-- functions from a session and a line to a session and a 'Response'; the
-- terminal lives in "Thena.Repl" and nowhere else.
--
-- §12 invariant 3 is what shapes this module: a command that changes the
-- development compiles to @[Instr]@ and runs on the machine (§2.4). Only three
-- kinds of command are the driver's own — the ones that produce a view
-- (@:core@, @:dev@, @:show@, @:where@), the ones that set a session setting
-- (@:step on@), and the ones that create or replace a development (@:goal@, which is
-- phase 13's @:theorem@ in miniature; §7.8 puts that on the session side).
--
-- **The moves are not among them.** Moving the focus changes the cursor, and
-- the cursor is 'Thena.Engine.Development' — exactly what backtracks — so a
-- move is an op and is spelled as a bare word (§2.4, §4.3).
module Thena.Driver
  ( Session (..)
  , newSession
  , Response (..)
  , Stop (..)
  , SyntaxError (..)
  , CommandError (..)
  , Attempt (..)
  , Parked (..)
  , Working (..)
  , currentAttempt
  , Snapshot
  , ChoicePoint (..)
  , LoadError (..)
  , Loaded (..)
  , command
  , commandSummary
  , answer
  , oneLine
  , loadSource
  , loadProofSource
  , RuleFileError (..)
  , loadRuleBases
  , baseHead
  , parseCore
  , parseDevelopment
  , parseDeclaration
  , parseSurfaceTerm
  , parseSurfaceModule
  , LoadKind (..)
  , kindOf
  ) where

import Data.Maybe (fromMaybe, isJust)
import Thena.Core.Level (Level (..), LevelVar, Obligation, freshLevelMeta)
import Thena.Core.Context (Context)
import Thena.Core.Reduce (whnf)
import Thena.Core.Term (Core (..), GlobalName (..), Ident (..), substLevelsIn)
import Data.Char (isSpace)
import Data.List (dropWhileEnd, isSuffixOf, stripPrefix)
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE
import Thena.Development.Cursor (expectedType, Cursor, Focus (..), Part (..), focus, overLevels)
import Thena.Development.Partial (Partial (..), extract)
import Thena.Engine
  ( ChoicePoint (..)
  , Exec (..)
  , Machine (..)
  , Message
  , Development (..)
  , Question
  , choicePoints
  , cursor
  , isAsking
  , flatten
  , load
  , newDevelopment
  , focusContext
  , resumeAt
  , setGoal
  , newDevelopmentNamed
  , step
  )
import qualified Thena.Engine as Engine
import Thena.Engine (whereImpure)
import Thena.Errors
  ( ConversionFailure
  , FailReason (..)
  , KernelError (..)
  , MoveError (..)
  , ResolveError (..)
  , SyntaxError (..)
  , TypeError
  )
import Thena.Development.Validate (revalidate)
import Thena.Global.Declare (DeclareError, declare)
import Thena.Global.NoConfusion (Skipped (..), noConfusionNames)
import Thena.Kernel (certify)
import Thena.Global.Env
  ( Constant (..)
  , Definition (..)
  , GlobalEnv
  , InductiveDefinition
  , addDefinition
  , generalised
  , emptyGlobals
  , inductiveName
  , isDeclared
  , lookupConstant
  , lookupDefinition
  , lookupInductive
  , eliminatorType
  , inductiveLevel
  )
import Thena.Core.Convert (convert)
import Thena.Core.Typing (infer, sortOf)
import qualified Thena.Ops as Ops
import Thena.Ops
  ( AnswerKind (..)
  , partOf
  , partWords
  , Instr (..)
  , Rule (..)
  , Op (..)
  , Rule
  , Operand (..)
  , Value (..)
  )
import Data.Either (partitionEithers)
import Thena.Rules
  ( RuleBase (..)
  , RuleError
  , RuleIter
  , matches
  , next
  , resolveRule
  , resolveBlock
  , RuleError (..)
  , ruleBase
  , validate
  )
import Thena.Surface.Concrete
  ( Plicity (..)
  , Surface (..)
  , SurfaceBinder (..)
  , SurfaceConstructor (..)
  , SurfaceData (..)
  , SurfaceDecl (..)
  , SurfaceModule (..)
  , PairingError (..)
  )
import Thena.Surface.Layout (layout)
import Thena.Surface.Zipper (rootedAt)
import qualified Thena.Surface.Parser as Surface
import Thena.Syntax.Concrete (Raw (..), RawRule)
import Thena.Syntax.Lexer (Located (..), Token (..), lexTokens)
import Thena.Syntax.Parser
  ( parseData
  , parseEquation
  , parseNameAndType
  , parseRules
  , parseTerm
  )
import Thena.Syntax.Resolve (resolve, resolveData, resolvePartial)

-- | Everything the session holds.
--
-- The name counter is not here: it is the machine's 'names' field (§7.2), and
-- while there is one machine that field /is/ §2.4's session-global counter.
-- Phase 13 has several proofs and must decide how one counter is threaded
-- through them; until then a second copy here would be two homes for one
-- number.
--
-- Stepping is a session setting, so it does not backtrack and does not belong
-- to the machine (§7.4).
data Session = Session
  { sessionMachine   :: Machine
  , sessionWork      :: Working
    -- ^ what the session is working on: an 'Attempt', or an unnamed scratch
    -- development. **A named case rather than an absence** (phase 37): this
    -- was @Maybe Proof@, and @Nothing@ read as \"there is no development\"
    -- when it means \"the development belongs to nothing\". There is always a
    -- development — it is 'Thena.Engine.development', and 'Machine' always has
    -- one.
  , sessionSuspended :: [Parked]
    -- ^ left and re-enterable, most recently suspended first (§2.4)
  , sessionHistory   :: NonEmpty Snapshot
    -- ^ where each line began, most recent first — and the head is **this**
    -- line's, so it always exists.
    --
    -- **One field, not two** (phase 37). It was @sessionSaved :: Snapshot@ and
    -- @sessionUndo :: [Snapshot]@, which are the head and the tail of exactly
    -- this list: the head is what a failed line is rewound to (phase 25d), and
    -- the tail is what @:undo@ walks. A line that changed nothing replaces the
    -- head rather than pushing, which is why @:undo@ never has to step over a
    -- @:show@. 'NonEmpty' is what makes \"there is always a state this line
    -- began in\" a fact of the type rather than a discipline 'record' keeps.
    --
    -- **On the session, not on the attempt** (phase 34, his ruling of
    -- 2026-08-29). It was 'Proof''s until then, so @:undo@ and phase 25d's
    -- rewind both did nothing at the top level — where there is a development
    -- but no theorem. That is the wrong way round: a 'Snapshot' is
    -- @(Exec, Development)@ and 'Machine' always has both, so the history of a
    -- thing that always exists was being kept in a record that sometimes does.
    -- Nothing about taking a line back needs a theorem.
    --
    -- **Reset at every proof boundary** — @:theorem@, @qed@, @:abandon@,
    -- @:suspend@, @:resume@ — which is his choice of three. @qed@ writes to
    -- @globals@, and @globals@ is deliberately not in a 'Snapshot' (§7.7: the
    -- environment only ever grows), so an @:undo@ that crossed it would rewind
    -- the development and leave the theorem admitted.
  , sessionStepping  :: Bool
  }
  deriving (Eq, Show)

-- | What the session is working on.
--
-- **The scratch case is named, and that is the whole of why this type exists**
-- (phase 37, his call). Nothing is stored here that was not stored before; a
-- development that belongs to no theorem now says so.
data Working
  = Scratch              -- ^ a development nobody has named; @qed@ is refused
  | Attempting Attempt   -- ^ a theorem is being proved
  deriving (Eq, Show)

-- | The per-attempt half of the machine: @exec@ and @development@ together
-- (§7.7's own correction to §2.4).
--
-- **Not the whole 'Machine' — an amendment to §7.7, phase 13.** That section
-- says suspending stores the machine untouched, and it cannot: @globals@ and
-- @names@ are session-global (§7.4, §2.4 \"@fresh@ stays session-global\"), so a
-- stored machine would hold a second copy of both and hand back a stale
-- environment on resume — exactly what §2.4 promises cannot happen, since
-- \"the global environment only ever grows\". Storing this pair instead is what
-- makes that promise true rather than aspirational.
--
-- It is the same pair 'sessionHistory' keeps, and that is not a coincidence: a
-- 'Parked' attempt /is/ an undo snapshot with a name and a statement attached.
type Snapshot = (Exec, Development, [Development])

-- | An unfinished proof of a theorem (§2.4, §3.3.1).
--
-- **\"Attempt\" is the word for it** — his, 2026-09-01, renaming @Proof@:
-- @Claim@ is taken twice already ('Thena.Development.Component.Claim' and this
-- record's own statement), and @Conjecture@ names the statement rather than the
-- work.
--
-- **It carries no snapshot.** It used to: the field was written when the proof
-- was created, overwritten when it was suspended, and read when it was
-- resumed — so the value written at creation was dead on every path, and it was
-- written only because the field was total and something had to go there. The
-- snapshot now lives on 'Parked', where it is the whole point, and nothing can
-- write it anywhere else.
data Attempt = Attempt
  { attemptName    :: GlobalName
  , attemptClaim   :: Core       -- ^ what @qed@ will certify against
  , attemptResidue :: [Obligation]
    -- ^ what the kernel could neither discharge nor refute, from the last
    -- @certify@ (MS3 phase 33b).
    --
    -- **Written by 'progress''s @Certifying@ case and read by @qed@'s
    -- 'admitted'**, which are the two halves of one @qed@ line with the
    -- machine's own loop between them — the kernel runs inside the loop and
    -- admitting happens after it returns, so the residue has to be put down
    -- somewhere in between. It is a mailbox rather than a property, and every
    -- alternative to it is worse; @docs/SESSION-STATE.md@ §5.3 says so out
    -- loud, because reading it outside that instant is how phase 33 shipped a
    -- bug.
  }
  deriving (Eq, Show)

-- | An attempt that has been put down, and where it was put down.
--
-- **The snapshot is here and nowhere else** (phase 37). @:suspend@ is the only
-- thing that builds one of these, @:resume@ the only thing that takes one
-- apart, so an attempt cannot carry a stale parking position while it is the
-- one being worked on.
--
-- **The asymmetry with 'Working' is deliberate, not an oversight**: what is
-- live is an attempt beside a 'Machine'; what is parked is an attempt beside a
-- 'Snapshot'. A parked one may not carry a machine, for the reason 'Snapshot'
-- gives above.
data Parked = Parked
  { parkedAttempt :: Attempt
  , parkedAt      :: Snapshot
  }
  deriving (Eq, Show)

-- | The attempt being worked on, if there is one.
currentAttempt :: Session -> Maybe Attempt
currentAttempt s = case sessionWork s of
  Scratch        -> Nothing
  Attempting att -> Just att

newSession :: Session
newSession = Session
  { sessionMachine   = Machine (Exec [] [] []) ps [] emptyGlobals [] [] n
  , sessionWork      = Scratch
  , sessionSuspended = []
  , sessionHistory   = (Exec [] [] [], ps, []) :| []
  , sessionStepping  = False
  }
  where
    (ps, n) = newDevelopment 0

-- | What the driver hands back for a frontend to render. Data, never a line of
-- text: rendering is "Thena.Repl"'s (§2.5).
data Response
  = Blank                     -- ^ an empty line; nothing to do
  | RenderedSurface Surface
    -- ^ @:surface ‹term›@ — the surface term as the parser read it (phase 39)
  | Rendered Core             -- ^ @:core@ (§2.6)
  | RenderedDev Partial       -- ^ @:dev@ (§2.7)
  | Shown Cursor              -- ^ @:show@, and the new state after @:goal@
  | ShownData InductiveDefinition
    -- ^ @:show ‹name›@ on a datatype: the declaration, printed back
  | ShownEliminator GlobalName Core
    -- ^ @:elim ‹datatype› [‹universe›]@ — the datatype, and its elimination
    -- rule at the universe asked for. Not a 'ShownGlobal': the eliminator is
    -- no global (§3.7, reversed 2026-08-22), so there is no name to print on
    -- the left and no body to print underneath
  | ShownGlobal GlobalName [LevelVar] [Obligation] [Plicity] Core (Maybe Core)
    -- ^ @:show ‹name›@ on anything else: its name, its type, and its body if
    -- it has one. A former has both — the constant is the type of its
    -- saturated 'Thena.Core.Term.Canonical' and the definition is the generated
    -- wrapper (§3.3.1) — and this shows the wrapper, which is what the name
    -- means when it is written.
  | Where Cursor              -- ^ @:where@ — the focus, the path, Γ, the type
  | Inferred Core Core        -- ^ @:infer@ — the term, and the type it has
  | IllTyped TypeError        -- ^ @:infer@ — why it has none
  | Converted Core Core (Maybe ConversionFailure) [Obligation]
    -- ^ @:convert@ — the two terms, and 'Nothing' if they are convertible.
    -- Both terms are kept so the answer can restate the question: with η in
    -- play a yes is printed about two terms that still look different (§5.2).
    --
    -- **The obligations are shown rather than dropped** (MS3 phase 33), because
    -- this is the one command whose whole output /is/ conversion's answer: a
    -- yes that holds only for some levels is not the same answer as a yes
  | Revalidated (Maybe KernelError)
    -- ^ @:revalidate@ — 'Nothing' if the development is a valid state (§5.3,
    -- thesis §2.3)
  | Extracted Core
  | Proving GlobalName Core   -- ^ @:theorem@ — a proof is now current
  | Proved GlobalName [LevelVar] [Obligation] Core
    -- ^ @qed@ — admitted, and the proof is closed. The levels are the scheme
    -- generalisation produced (MS3 phase 33b), not anything that was written,
    -- and the obligations are the scheme's own constraints.
    --
    -- **The constraints travel with the parameters**, because half a scheme is
    -- worse than none: a scheme without its @(suc ℓ ≤ 2)@ reads as usable at
    -- every level and is not. @:show@ printed them from the moment 33b stored
    -- them; this line — the one the user reads at the moment the scheme comes
    -- into existence — did not.
  | Suspended GlobalName      -- ^ @:suspend@
  | Resumed GlobalName        -- ^ @:resume@
  | Abandoned GlobalName      -- ^ @:abandon@
  | Undone                    -- ^ @:undo@ — one line taken back
  | Proofs (Maybe Attempt) [Parked]
    -- ^ @:proofs@ — the current one, if any, and the suspended ones
    -- ^ @:extract@ — the closed term the development stands for (§7.5). Its
    -- own look, because @certify@ is an op and an op's answer comes back as a
    -- 'Message', which the driver may not build out of a term: rendering is
    -- "Thena.Repl"'s (§2.5)
  | InferredSurface Surface Core
    -- ^ @:infer ‹surface›@ (MS4 phase 43): the term as written and the type
    -- elaborating it produced. The **surface** term, not the core one it built,
    -- because the development it built was rewound and printing a term the
    -- session no longer holds would invite a @goto@ into nothing
  | LoadRequested FilePath
  | ProofRequested FilePath
    -- ^ @:load@ on a @.thena@ path (MS4 phase 43): a **proof module**, which is
    -- surface declarations and not command lines. Like 'LoadRequested' it only
    -- names the file; "Thena.Repl" reads it and hands the contents back to
    -- 'loadProofSource'
  | ProofLoaded String [String] Int
    -- ^ a proof module went in: its name, and what it declared, in order. **The
    -- op-level messages are discarded** — his call, 2026-09-02, the same bargain
    -- @loadPrelude@ already makes: elaborating one declaration prints a dozen
    -- @solved: ?ℓ229@ lines, and a file of them buries its own output. Typing
    -- the declaration at the prompt still prints everything.
    --
    -- **The trailing count is the top-level blocks** (MS4 phase 45). A block
    -- declares nothing this side of running it, so it cannot be named in the
    -- list — but it did run, and a summary that left it out entirely would be
    -- saying less than happened
  | RulesRequested [FilePath]
    -- ^ @:load@ on one or more @.thena.rules@ paths (phase 22). Like
    -- 'LoadRequested' it only names them — reading is "Thena.Repl"'s (§12
    -- invariant 4) — but it names /several/, because a load replaces the whole
    -- ordered list of bases and the order is the order written
  | BasesLoaded [RuleBase]      -- ^ what @:load@ on rule files installed
  | BasesListed [RuleBase]      -- ^ @:bases@ — name, description, path
  | RulesListed [RuleBase]      -- ^ @:rules@ — the rules themselves, by base
  | RuleFileRefused FilePath RuleFileError
    -- ^ @:load ‹path›@. The driver may not touch a file — §12 invariant 4 puts
    -- all IO in "Thena.Repl" — so it asks, and the caller reads the file and
    -- hands the contents back to 'loadSource'
  | Choices [ChoicePoint]
    -- ^ @:choices@ — the live choice points, nearest first (§7.7). A look
  | Helped [(String, String)]
    -- ^ @:help@ — every command the driver itself has, each with one line
    -- saying what it does. The spelling carries the grouping: §2.4's rule is
    -- that a bare word acts and a colon looks, so "Thena.Repl" splits the list
    -- on the leading colon rather than being told twice
  | Matched [Rule]
    -- ^ @:matches@ — the rules whose heads pass at the focus, in dispatch order
    -- (§7.6). A look and not an act: no body runs, and nothing is speculatively
    -- executed to find out whether one would succeed (§2.2)
  | Ran [Message] Stop        -- ^ what the machine said, and where it stopped
  | Failed SyntaxError
  | Rejected CommandError
  | Quit
  deriving (Eq, Show)

-- | Where a run of the machine came to rest — §7.8's five outcomes, less
-- 'Engine.Continue', which the loop below never hands out except as 'Paused'.
data Stop
  = Completed            -- ^ the program ran out of instructions
  | Waiting Question     -- ^ answer it with 'answer'
  | Yielded Message
    -- ^ a rule handed control to the REPL and is standing still (MS4 phase
    -- 45b). The message is why it stopped. Type anything; @yield@ hands control
    -- back.
    --
    -- **Not a 'Waiting'**, and the difference is the whole of the feature: a
    -- question wants a value and refuses everything else, while a yield wants
    -- nothing and takes every command the REPL has.
  | Halted FailReason
    -- ^ the machine ran and failed.
    --
    -- **It said "the machine is kept, so a later @retry@ can use it" until
    -- phase 25d, and that was never true.** 'Thena.Engine.Stuck' is returned
    -- only from an @unwind@ that walked the whole stack without finding a live
    -- alternative, so a halted machine has no choice point left to retry —
    -- @:choices@ after one says so. What the machine is kept /for/ is the
    -- messages and the reason; the proof itself is rewound by 'oneLine'.
  | Refused DeclareError -- ^ a @data@ declaration the checker would not admit
  | Uncertified KernelError
    -- ^ the kernel would not accept what the development built (§5.3). Shaped
    -- like 'Refused': the command is abandoned, and there is nothing to retry
  | Paused               -- ^ stepping mode: one instruction done
  deriving (Eq, Show)

-- | Everything else a command line can get wrong (§7.8's @CommandError@).
data CommandError
  = NoSuchCommand String
  | MissingArgument String
  | UnexpectedArgument String
  | NotAsking
  | NotYielding
    -- ^ @yield@ typed when no rule has handed control over (MS4 phase 45b).
    -- 'NotAsking''s twin, and it exists for the same reason: a word that did
    -- nothing would be worse than one that says so.
  | NoSuchGlobal String
  | NotProving
    -- ^ @qed@, @:suspend@, @:abandon@ or @:undo@ outside a proof. §2.4: outside
    -- a proof there is nothing to undo, and definitions are not undoable
  | AlreadyProving GlobalName
    -- ^ @:theorem@ while one is current. At most one is current (§2.4), and
    -- suspending is an explicit act rather than something @:theorem@ does
  | NoSuchProof String
  | AlreadyDeclaredHere String
    -- ^ @:theorem@ under a name the global environment already has (§3.6)
  | NothingToUndo
  | MixedLoad String
    -- ^ @:load a.thena b.thena.rules@ — a script and a rule base in one
    -- command. Two different operations, and neither is what was asked for
  | ProofUnderway GlobalName
    -- ^ a rule base loaded while a proof is current. **The base may not change
    -- under a half-built proof** — the user's reproducibility argument,
    -- 2026-08-25 — and *"loading a new rule-base in between theorems is fine
    -- for now"* is why this names the proof rather than refusing outright
  | ProofsSuspended [GlobalName]
    -- ^ … or while one is suspended, which is the same hazard postponed: a
    -- suspended proof is resumed and continued, so its replay would change
  | LevelExpected String
    -- ^ @:elim Nat Nat@ — @:elim@\'s optional second argument parsed as a term
    -- but is not a @Typeₗ@ (phase 10). Not called @NotAUniverse@ because
    -- 'Thena.Syntax.Resolve.ResolveError' has one of those already, about a
    -- different mistake: a datatype /declared/ at a non-universe
  | NothingToRetry
    -- ^ @retry@ with no live choice point anywhere on the stack
  | NoSuchChoice Int
    -- ^ @retry ‹n›@ naming an identifier that is not on the stack. There is no
    -- second case for "that one is exhausted": the peek (§7.3) demotes a frame
    -- the moment its last alternative is taken, so an exhausted 'Choice' never
    -- exists
  | NotThere MoveError
    -- ^ a driver command that needs a particular focus, run at another —
    -- @:goal@, and @:whnf@ with no argument (phase 7); the moves are ops and
    -- fail through 'Halted'.
  deriving (Eq, Show)

-- --------------------------------------------------------------------------
-- Reading terms and developments
-- --------------------------------------------------------------------------

-- | Lex, parse, resolve as a core term, in the given environment and context.
parseCore :: GlobalEnv -> Context -> Int -> String -> Either SyntaxError (Core, Int)
parseCore = parseWith resolve


-- | Lex, parse, resolve as a development (§2.7's longest-prefix convention).
parseDevelopment
  :: GlobalEnv -> Context -> Int -> String -> Either SyntaxError (Partial, Int)
parseDevelopment = parseWith resolvePartial

-- | The arguments of a rule called by name at the REPL (phase 23b): a run of
-- atoms, each resolved as a core term in the context at the focus.
--
-- **A run and not one term**, so that a REPL line means what the same line
-- means inside a rule body — @f a b@ is two arguments in both. The counter is
-- threaded through, because resolving mints display variables.
--
-- | Why an argument run did not become terms.
--
-- Two outcomes rather than one 'SyntaxError', because they are answered
-- differently: a malformed argument is the user's typo and reports as
-- 'Failed', while an argument that is merely not in corners is a 'Rejected'
-- with its own sentence (phase 38).
newtype ArgumentError = Syntax SyntaxError

-- | The arguments of a bare-word rule call — **each one a surface term, or a
-- core term in corners** (MS4 phase 41).
--
-- **This is where phase 38's error message comes true.** That phase refused a
-- bare argument and said the corners were for a core term, reserving the bare
-- spelling for the surface one; here the bare spelling starts meaning it. So
-- @try-core ⌜ x ⌝@ hands a rule a 'Thena.Ops.VTerm' and @elaborate x@ hands it
-- a 'Thena.Ops.VSurface', and which one a rule wanted is settled where every
-- other operand kind is — at run time, by the op (§7.2, and MS2 closeout 4b's
-- type system when it arrives).
--
-- The run is split by bracket depth first, because the two spellings need two
-- different grammars and one token stream cannot be handed to both.
parseArguments
  :: GlobalEnv -> Context -> Int -> String -> Either ArgumentError ([Value], Int)
parseArguments env ctx n src = do
  ts <- mapLeft Syntax (tokensOf src)
  go n (groups ts)
  where
    go k []       = Right ([], k)
    go k (g : gs) = do
      (v, k1)  <- one k g
      (vs, k2) <- go k1 gs
      Right (v : vs, k2)

    -- In corners: a development-calculus term, resolved here as it always was.
    one k (Cornered inner) = do
      raw     <- mapLeft (Syntax . ParseFailed) (parseTerm inner)
      (t, k1) <- mapLeft (Syntax . ResolveFailed) (resolve env ctx k raw)
      Right (VTerm (Trailing t), k1)
    -- Bare: a surface term. Laid out, because a surface term always is.
    one k (Bare g) = do
      g' <- mapLeft (Syntax . LayoutFailed) (layout g)
      t  <- mapLeft (Syntax . SurfaceParseFailed) (Surface.parseSurface g')
      Right (VSurface (rootedAt t), k)

-- | One written argument, before it is parsed.
data Group
  = Cornered [Located Token]  -- ^ @⌜ … ⌝@, corners stripped
  | Bare     [Located Token]

-- | Split an argument run into its arguments, by bracket depth.
--
-- **Why the driver splits and neither grammar does**: the two spellings need
-- two different grammars, and one token stream cannot be handed to both. An
-- argument is an atom (phase 23b), so its extent is a single token or a
-- balanced group — which is decidable here without either parser.
groups :: [Located Token] -> [Group]
groups [] = []
groups (t@(Located _ k) : ts) = case k of
  TOpenQuote -> let (inner, rest) = corners 1 [] ts in Cornered inner : groups rest
  TLParen    -> let (inner, rest) = bracketed 1 [t] ts in Bare inner : groups rest
  TLBrace    -> let (inner, rest) = bracketed 1 [t] ts in Bare inner : groups rest
  -- @?foo@ is two tokens and one argument (phase 39).
  TQuery     -> case ts of
    u : us -> Bare [t, u] : groups us
    []     -> [Bare [t]]
  _          -> Bare [t] : groups ts
  where
    corners _ acc [] = (reverse acc, [])
    corners d acc (u@(Located _ w) : us) = case w of
      TCloseQuote | d == (1 :: Int) -> (reverse acc, us)
                  | otherwise       -> corners (d - 1) (u : acc) us
      TOpenQuote                    -> corners (d + 1) (u : acc) us
      _                             -> corners d (u : acc) us

    bracketed _ acc [] = (reverse acc, [])
    bracketed d acc (u@(Located _ w) : us)
      | w == TLParen || w == TLBrace = bracketed (d + 1) (u : acc) us
      | w == TRParen || w == TRBrace =
          if d == (1 :: Int) then (reverse (u : acc), us)
                             else bracketed (d - 1) (u : acc) us
      | otherwise                    = bracketed d (u : acc) us

parseWith
  :: (GlobalEnv -> Context -> Int -> Raw -> Either ResolveError (a, Int))
  -> GlobalEnv -> Context -> Int -> String -> Either SyntaxError (a, Int)
parseWith res env ctx n src = do
  ts  <- tokensOf src
  raw <- mapLeft ParseFailed (parseTerm ts)
  mapLeft ResolveFailed (res env ctx n raw)

-- | Lex, parse, resolve a @data@ declaration (§3.7).
--
-- Its own entry point rather than a case of 'parseWith', because a declaration
-- is not a term: it has its own start symbol in the grammar and it is read in
-- the empty context, never in the development's.
parseDeclaration
  :: GlobalEnv -> Int -> String -> Either SyntaxError (InductiveDefinition, Int)
parseDeclaration env n src = do
  ts  <- tokensOf src
  raw <- mapLeft ParseFailed (parseData ts)
  mapLeft ResolveFailed (resolveData env n raw)

-- | Lex, parse and resolve the two sides of @:convert t ≟ u@.
--
-- Its own entry point for 'parseDeclaration'\'s reason — a different start
-- symbol — and it threads the counter from the first term into the second, so
-- the two are resolved in one continuous supply of names rather than two that
-- overlap.
parseEquated
  :: GlobalEnv -> Context -> Int -> String
  -> Either SyntaxError ((Core, Core), Int)
parseEquated env ctx n src = do
  ts       <- tokensOf src
  (r1, r2) <- mapLeft ParseFailed (parseEquation ts)
  (a, n1)  <- mapLeft ResolveFailed (resolve env ctx n r1)
  (b, n2)  <- mapLeft ResolveFailed (resolve env ctx n1 r2)
  Right ((a, b), n2)

-- | Lex, parse and resolve @‹name› : ‹type›@ for @:theorem@.
--
-- The **empty context**, not the development's: a theorem's statement is closed
-- (§5.3), and resolving it where a scratch @assume@ happens to be in scope
-- would let one in.
parseStatement
  :: GlobalEnv -> Int -> String
  -> Either SyntaxError (Maybe String, (Core, Int))
parseStatement env n src = do
  ts        <- tokensOf src
  (mx, raw) <- mapLeft ParseFailed (parseNameAndType ts)
  r         <- mapLeft ResolveFailed (resolve env [] n raw)
  Right (mx, r)

tokensOf :: String -> Either SyntaxError [Located Token]
tokensOf = mapLeft LexFailed . lexTokens

-- | Datatypes and theorems, in the order they were written (MS4 phase 42b).
--
-- **The split happens here rather than in 'paired'**, which is about theorems:
-- a signature and its equation are adjacent and a datatype is not part of that
-- pairing at all.
parseSurfaceItems
  :: String -> Either SyntaxError [Item]
parseSurfaceItems src = do
  ts  <- tokensOf src
  ts' <- mapLeft LayoutFailed (layout ts)
  ds  <- mapLeft SurfaceParseFailed (Surface.parseSurfaceDecls ts')
  regroup (reverse ds)

-- | A whole **proof module** (MS4 phase 43): its name, and its items.
--
-- The same three passes 'parseSurfaceItems' makes, through the module start
-- symbol instead — so a module's declaration block and a @declare@ line are the
-- same grammar, and layout does the same work in both.
parseSurfaceModule
  :: String
  -> Either SyntaxError (String, [Item])
parseSurfaceModule src = do
  ts  <- tokensOf src
  ts' <- mapLeft LayoutFailed (layout ts)
  m   <- mapLeft SurfaceParseFailed (Surface.parseSurfaceModule ts')
  is  <- regroup (surfaceModuleDecls m)
  Right (surfaceModuleName m, is)

-- | Why a top-level block did not resolve, in terms 'SyntaxError' can hold.
--
-- 'Thena.Elaborate.blockFailure'\'s twin, and the same reasoning: resolution can
-- only produce 'Thena.Rules.BadOperands', because a word that names no op is a
-- rule call and not an error.
blockProblem :: [RuleError] -> SyntaxError
blockProblem errs = case errs of
  BadOperands _ i w : _ -> BlockIllFormed i w
  _                     -> BlockIllFormed 0 "do"

-- | One thing a module or a @declare@ line asks for.
--
-- **A sum rather than the @Either@ it was** (MS4 phase 45): a top-level @do@
-- block is a third kind of item, and an @Either@ with a triple on one side had
-- already stopped saying what it meant.
data Item
  = ItemData SurfaceData
  | ItemTheorem String Surface Surface   -- ^ a signature and the equation after it
  | ItemBlock [Instr]
    -- ^ a top-level @do@ block (phase 45), **already resolved**: 'regroup'
    -- resolves it while the file is being read, so a block with bad operands is
    -- a syntax error at the right place rather than a failure at run time.
  deriving (Eq, Show)

-- | Pair each signature with the equation after it, and pass datatypes through.
--
-- Shared by the two above since phase 43. 'Thena.Surface.Concrete.paired' is
-- the same idea for theorems alone; this one also admits a @data@ item, which
-- is why it is here and not there.
regroup
  :: [SurfaceDecl]
  -> Either SyntaxError [Item]
regroup = go
  where
    go [] = Right []
    go (SurfaceDatatype d : rest) = (ItemData d :) <$> go rest
    go (SurfaceBlock b : rest) = case resolveBlock (GlobalName "do") b of
      Right is  -> (ItemBlock is :) <$> go rest
      Left errs -> Left (blockProblem errs)
    go (SurfaceSignature x ty : SurfaceEquation y body : rest)
      | x == y = (ItemTheorem x ty body :) <$> go rest
    go (SurfaceSignature x _ : _) =
      Left (DeclarationsUnpaired (SignatureWithNoEquation x))
    go (SurfaceEquation x _ : _) =
      Left (DeclarationsUnpaired (EquationWithNoSignature x))

-- --------------------------------------------------------------------------
-- Surface declarations, as a program (MS4 phase 42; lifted here at 43)
-- --------------------------------------------------------------------------

-- | Compile a run of surface items into the instructions that admit them.
--
-- **Lifted out of @dispatch@ at phase 43** so that a proof module and a typed
-- @declare@ line share it. It closed over nothing but the name counter, which
-- is why lifting it is a move rather than a rewrite: what an item compiles to
-- does not depend on how the driver was asked.
--
-- **A whole module is therefore one program**, which is what phase 42 decided
-- for a single declaration and for the same reason — @:step@ can watch it, and
-- phase 49 can move it into a rule body without the driver having sequenced
-- anything in Haskell.
surfaceProgram
  :: Int -> [Item] -> ([Instr], Int)
surfaceProgram n0 items = foldl item ([], n0) items
  where
  item acc (ItemData d)            = datatype acc d
  item acc (ItemTheorem x ty body) = declaring acc (x, ty, body)
  -- **A top-level block is spliced, and that is the whole of it** — his,
  -- 2026-09-03. A module is already one instruction program, so a block of
  -- instructions at the top of one is @++@: no frame, no op, and nothing that
  -- could tell it from the instructions the elaborator emitted around it.
  --
  -- **Not 'Thena.Ops.Block'**, which is the /expression/ form: that one needs a
  -- frame because it has to return to the term it stands in. A top-level block
  -- has nothing to return to, so it needs no frame and gets none.
  item (acc, n) (ItemBlock is) = (acc ++ is, n)

  -- **Brady's data rule** (@IDRIS.md@ §4.6): the datatype's own type is
  -- elaborated first /"so that the type is in scope when elaborating the
  -- constructor types"/, then each constructor the same way.
  --
  -- **Being in scope is an assumption, and then a β-step.** A constructor's
  -- type mentions the datatype, which is not declared yet, so it is
  -- elaborated under @assume D : ‹its type›@ — and popping a development
  -- extracts, so what comes back is @λ D : ty . ‹the type›@. Applying that to
  -- @D@ as a global and reducing puts the real reference in. Both ops
  -- already existed; neither needed a mode.
  datatype (acc, n) d =
    let nm      = surfaceDataName d
        dn      = GlobalName nm
        ps      = surfaceDataParameters d
        cs      = surfaceDataConstructors d
        (l, n1) = freshLevelMeta n
        full    = withParams ps (surfaceDataType d)
        tyName  = "dty" ++ show n
        conName k = "con" ++ show n ++ "_" ++ show (k :: Int)
        selfName  = Lit (VTerm (Trailing (Global dn [])))
     in ( acc ++
            [ Do (PushDevelopment (Lit (VTerm (Trailing (Universe (LVar l))))))
            , Do (Call (GlobalName "elaborate") [Lit (VSurface (rootedAt full))])
            , Bind (tyName ++ "raw") PopDevelopment
            , Bind tyName (Expose (Ref (tyName ++ "raw")))
            ]
            ++ concat
                 [ [ Do (PushDevelopment (Lit (VTerm (Trailing (Universe (LVar l))))))
                   , Do (Assume (Lit (VText nm)) (Ref tyName))
                   , Do (Call (GlobalName "elaborate") [Lit (VSurface (rootedAt (withParams ps cty)))])
                   , Bind (conName k ++ "raw") PopDevelopment
                   , Bind (conName k ++ "app")
                       (ApplyTo (Ref (conName k ++ "raw")) selfName)
                   , Bind (conName k) (Expose (Ref (conName k ++ "app")))
                   ]
                 | (k, SurfaceConstructor _ cty) <- zip [0 ..] cs
                 ]
            ++ [ Do (MakeData dn (length ps)
                       [ GlobalName cn | SurfaceConstructor cn _ <- cs ]
                       (Ref tyName : [ Ref (conName k) | k <- [0 .. length cs - 1] ]))
               ]
        , n1 )

  -- | The plicity of each argument position a signature writes.
  --
  -- Only a leading run of @∀@ groups is read: once the type stops being a
  -- quantifier there are no more named positions to speak of, and an arrow
  -- contributes an 'Explicit' one.
  plicitiesIn t = case t of
    SurfacePi bs body ->
      [ p | SurfaceBinder p _ _ <- NE.toList bs ] ++ plicitiesIn body
    SurfaceArrow _ body -> Explicit : plicitiesIn body
    _ -> []

  -- A constructor's type is written in the scope of the parameters, so they
  -- are put back in front of it and peeled off again by
  -- 'Thena.Global.Declare.buildInductive'.
  withParams ps t =
    foldr (\(x, ty) rest -> SurfacePi (SurfaceBinder Explicit x (Just ty) NE.:| []) rest) t ps

  declaring (acc, n) (x, ty, body) =
    let (l, n1) = freshLevelMeta n
     in ( acc ++
            [ Do (PushDevelopment (Lit (VTerm (Trailing (Universe (LVar l))))))
            , Do (Call (GlobalName "elaborate") [Lit (VSurface (rootedAt ty))])
              -- **Reduced before it is used or stored.** What @extract@ hands
              -- back carries @fill@'s @=@-bindings, and a @let@-headed type
              -- is not merely ugly: @intro@ reads a @Let@ as written, so the
              -- body's λ would open a definition instead. See
              -- 'Thena.Ops.Whnf'.
            , Bind ("raw" ++ show n) PopDevelopment
            , Bind ("ty" ++ show n) (Expose (Ref ("raw" ++ show n)))
            , Do (PushDevelopment (Ref ("ty" ++ show n)))
            , Do (Call (GlobalName "elaborate") [Lit (VSurface (rootedAt body))])
            , Bind ("tm" ++ show n) PopDevelopment
              -- **The plicities come from the signature as written** (MS4
              -- phase 44b): a leading run of @∀@ binder groups, each in
              -- braces or not. That is the whole of the surface signature
              -- environment — where a binder was written, not what the type
              -- turned out to be.
            , Do (DefineGlobal (plicitiesIn ty) (Lit (VText x))
                    (Ref ("ty" ++ show n)) (Ref ("tm" ++ show n)))
            ]
        , n1 )

-- | Elaborate a whole proof module (MS4 phase 43).
--
-- **One program for the whole file**, built by 'surfaceProgram' — the same
-- instructions a @declare@ line compiles to, concatenated. So a module is not a
-- new mechanism, and @:step@ can walk it declaration by declaration.
--
-- **Quiet when it works, loud when it does not** — his call, 2026-09-02. On
-- success the op-level messages are dropped and the driver reports the module
-- and what it declared, in order; on failure everything the run printed is kept,
-- because that is where the reason is. Elaborating one declaration emits a dozen
-- @solved: ?ℓ229@ lines and a file of them buries its own output, which is the
-- same bargain @loadPrelude@ has always made with a script.
--
-- **Holes left over are not an error.** A module that does not finish leaves a
-- half-built development in the session, which is what the REPL is for.
loadProofSource :: Session -> String -> (Session, Response)
loadProofSource s src = case parseSurfaceModule src of
  Left e -> (s, Failed e)
  Right (nm, items) ->
    let machine  = sessionMachine s
        (is, n1) = surfaceProgram (names machine) items
     in case progress False s { sessionMachine = load is machine { names = n1 } } [] of
          (s', Ran _ Completed) ->
            ( s'
            , ProofLoaded nm [ n | Just n <- map declaredName items ]
                             (length [ () | ItemBlock _ <- items ])
            )
          (s', other)           -> (s', other)

-- | What an item adds to the environment, for the summary line.
declaredName :: Item -> Maybe String
declaredName i = case i of
  ItemData d        -> Just (surfaceDataName d)
  ItemTheorem x _ _ -> Just x
  -- **A block declares nothing that can be read off the item.** What its
  -- instructions install is known only by running them, so it is counted rather
  -- than named — see 'ProofLoaded'.
  ItemBlock _       -> Nothing

-- | Lex and parse a **surface** term (phase 39). No context, because nothing is
-- resolved: what a name denotes is elaboration's answer, and elaboration is
-- phase 41.
parseSurfaceTerm :: String -> Either SyntaxError Surface
parseSurfaceTerm src = do
  ts  <- tokensOf src
  ts' <- mapLeft LayoutFailed (layout ts)
  case Surface.parseSurface ts' of
    Left e  -> Left (SurfaceParseFailed e)
    Right t -> Right t

-- --------------------------------------------------------------------------
-- Commands
-- --------------------------------------------------------------------------

-- | Bare word acts, colon looks (decided by the user 2026-08-21). @assume@ and
-- @claim@ are ops and read exactly as they will read inside a rule body;
-- everything with a colon is the driver's own.
command :: Session -> String -> (Session, Response)
command s line = case break (== ' ') (dropWhile (== ' ') line) of
  ("", _)      -> (s, Blank)
  -- **A line that is only a comment is a blank line** (MS4 phase 43). The lexer
  -- drops @-- @ wherever it appears, but a command word is split off before
  -- anything is lexed, so a comment standing alone would otherwise be
  -- dispatched as a rule named @--@.
  _ | commentLine line -> (s, Blank)
  (name, rest) -> dispatch s name (dropWhile (== ' ') rest)

dispatch :: Session -> String -> String -> (Session, Response)
dispatch s name arg = case name of
  -- The driver's own commands, and only those: a bare word this function does
  -- not name is a rule call, and 'commandSummary' says so rather than listing
  -- the rule base a second time.
  ":help"  -> noArgument (s, Helped commandSummary)
  ":quit"  -> noArgument (s, Quit)
  ":core"  -> withArgument (view s parseCore Rendered arg)
  -- | @:surface ‹term›@ — parse a **surface** term and print it back (phase
  -- 39). The analogue of @:core@, and for the same reason: it is the only way
  -- to see what the parser made of what you wrote, and until phase 41 it is the
  -- only thing that can be done with a surface term at all.
  --
  -- It takes no context and changes no state — nothing is resolved, because
  -- resolving a surface term is elaborating it.
  ":surface" -> withArgument $ case parseSurfaceTerm arg of
    Left e  -> (s, Failed e)
    Right t -> (s, RenderedSurface t)
  ":dev"   -> withArgument (view s parseDevelopment RenderedDev arg)
  -- The only command that means two things, and they do not overlap: with no
  -- argument it is the development, with one it is a global (§9, phase 6).
  ":show"  -> case arg of
    "" -> (s, Shown (cursor (development machine)))
    _  -> showGlobal arg
  -- The eliminator is not a global, so it is not reachable through @:show@
  -- (§3.7, reversed by the user 2026-08-22). Its own word, and its own second
  -- argument: the level comes from the motive at every use site, so there is
  -- no one rule to print and the command has to be told which one is wanted.
  ":elim"  -> withArgument (eliminator arg)
  ":where" -> noArgument (s, Where (cursor (development machine)))
  -- Autocomplete, and it is a read-only query on the iterator (§7.6): the
  -- driver asks for the matches at the current state and shows them. Picking
  -- one and running its body is phase 16's.
  --
  -- **The optional argument is a hint** (phase 17b), read exactly as @prove@\'s
  -- is. A hint partitions the base, so the two forms answer two questions:
  -- @:matches@ is what could be done here, @:matches ‹hint›@ is what could
  -- elaborate that.
  -- **No argument** (MS4 phase 41). @:matches ‹hint›@ asked which rules could
  -- elaborate a given term, and with the hint retired that is not a question:
  -- @elaborate ‹t›@ appears in this listing the way @try-core ‹t›@ does.
  ":matches" -> noArgument (s, Matched matching)
  -- The live choice points, nearest first (§7.7). A look, so a colon.
  ":choices" -> noArgument (s, Choices (choicePoints machine))
  ":goal"  -> goal
  -- With no argument, view-reduce the core focus (§4.7); with one, an
  -- arbitrary typed term — the same no-argument/with-argument split as
  -- @:show@, and for the same reason: two different questions share a word
  -- because neither can be mistaken for the other.
  ":whnf"  -> case arg of
    "" -> case focus (cursor (development machine)) of
      OnTerm _ _ t -> (s, Rendered (whnf (globals machine) ctx t))
      _            -> (s, Rejected (NotThere NotInCore))
    _  -> view s parseCore (Rendered . whnf (globals machine) ctx) arg
  -- The same no-argument/with-argument split as @:whnf@ and @:show@: with no
  -- argument it is the core focus, with one it is a term the user writes.
  -- **A bare argument is a surface term; corners are a core one** (MS4 phase
  -- 43), which is the rule everywhere else an argument is written. With no
  -- argument it is still the core focus.
  ":infer" -> case arg of
    "" -> case focus (cursor (development machine)) of
      OnTerm _ _ t -> inferred t (names machine)
      _            -> (s, Rejected (NotThere NotInCore))
    _ | Just inner <- cornered arg ->
          case parseCore (globals machine) ctx (names machine) inner of
            Left e        -> (s, Failed e)
            Right (t, n1) -> inferred t n1
      | otherwise -> case parseSurfaceTerm arg of
          Left e  -> (s, Failed e)
          Right t -> inferSurface t
  -- Reading the file is the caller's; this only names it (§12 invariant 4).
  -- **Two different loads behind one word, told apart by extension** — the
  -- user, 2026-08-25. A @.thena.rules@ path is a rule base and there may be
  -- several, leftmost searched first; anything else is one script of command
  -- lines, exactly as phase 11 left it. Reading is the caller's; this only
  -- names them (§12 invariant 4).
  -- **Three kinds, one word** (MS4 phase 43). @:load rules …@, @:load proof …@
  -- and @:load script …@ say which; a bare @:load ‹path›@ reads the extension
  -- and answers the same question. His ruling, 2026-09-02 — see 'kindOf'.
  --
  -- A keyword is not a path, so the two forms cannot be confused: the first
  -- word is looked up, and only if it names no kind is it taken as a path.
  ":load"  -> withArgument $ case words arg of
    ("rules"  : rest) -> loadKind LoadRules  (pathsOf (unwords rest))
    ("proof"  : rest) -> loadKind LoadProof  (pathsOf (unwords rest))
    ("script" : rest) -> loadKind LoadScript (pathsOf (unwords rest))
    _ -> case pathsOf arg of
      ps@(p : _) | all ((== kindOf p) . kindOf) ps -> loadKind (kindOf p) ps
      (_ : _)  -> (s, Rejected (MixedLoad name))
      []       -> (s, Rejected (MissingArgument name))
  -- The loaded bases, in search order. A look, so a colon.
  ":bases" -> noArgument (s, BasesListed (rules machine))
  ":rules" -> noArgument (s, RulesListed (rules machine))
  -- Thesis §2.3's state-validity judgment over the whole development, at any
  -- time (§5.3). A colon: it looks and changes nothing.
  ":revalidate" -> noArgument $
    ( s
    , Revalidated . either Just (const Nothing) . fst $
        revalidate (globals machine) [] (names machine) (flatten (development machine))
    )
  -- The term the development stands for, if it is finished. A colon: it looks.
  -- 'extract' is otherwise reachable only through the op, and the whole
  -- interest of @certify@ is /what/ it built.
  ":extract" -> noArgument $
    case extract (flatten (development machine)) of
      Right t  -> (s, Extracted t)
      Left why -> (s, Ran [] (Halted (NotYetPure (whereImpure why))))
  -- A bare word: it is an op, and it is written as the op is written (§2.4).
  -- The argument is the type the development is claimed to prove — see
  -- 'Thena.Ops.Certify' for why the op needs one.
  "certify" -> withArgument $
    case parseCore (globals machine) ctx (names machine) arg of
      Left e -> (s, Failed e)
      Right (ty, n1) ->
        progress
          (sessionStepping s)
          s { sessionMachine =
                load [Do (Certify (Lit (VTerm (Trailing ty))))] machine { names = n1 } }
          []
  -- Proof mode (§2.4). A colon on the session commands, because they manage
  -- the session rather than the development; @qed@ is bare, because it is an
  -- op program and is written as the op is written. That also keeps @:abandon@
  -- (this proof) apart from @abandon@ (this hole), which are two different
  -- operations that thesis §2 gives one name.
  ":theorem" -> withArgument theorem
  "qed"      -> noArgument closeProof
  ":suspend" -> noArgument suspend
  ":resume"  -> withArgument (resume arg)
  ":abandon" -> noArgument abandonProof
  ":proofs"  -> noArgument (s, Proofs (currentAttempt s) (sessionSuspended s))
  ":undo"    -> noArgument undo
  ":convert" -> conversion
  ":step"  -> stepping
  ":run"   -> noArgument (progress False s [])
  "assume" -> tactic "assumption" "assumed" Assume
  "claim"  -> tactic "hole" "claimed" Claim
  -- @assume@'s twin (MS4 phase 41f): the same two arguments, and the chain
  -- below it extracts as a Π rather than a λ.
  "quantify" -> tactic "∀-binder" "quantified" Quantify
  "data"   -> declaration
  -- **A surface declaration** (MS4 phase 42) — a bare word, because it acts
  -- (§2.4). It compiles to instructions rather than being run here, so
  -- @:step@ can watch it and phase 49 can move the program into a rule body.
  "declare" -> withArgument (declareSurface arg)

  -- The moves (§4.3). Three take no argument, @cross@ takes which field, and
  -- every core-term descent is its own word so that none of them changes
  -- meaning with what is in focus (§4.0 C1).
  "along"  -> noArgument (run [Do Along])
  "into"   -> noArgument (run [Do Into])
  "back"   -> noArgument (run [Do Back])
  "reduce" -> noArgument (run [Do Reduce])
  -- A bare word, not @:unify@ as §9 first wrote it: unification rewrites the
  -- development, and §2.4's rule is that a bare word acts and a colon looks.
  -- The argument is @t ≟ u@, the same two-sided form @:convert@ reads.
  "unify"  -> withArgument $
    case parseEquated (globals machine) ctx (names machine) arg of
      Left e -> (s, Failed e)
      Right ((a, b), n1) ->
        progress
          (sessionStepping s)
          s { sessionMachine =
                load [Do (Unify (Lit (VTerm (Trailing a))) (Lit (VTerm (Trailing b))))]
                     machine { names = n1 } }
          []
  -- Dispatch the rule engine at the focus (§7.3). An op, so a bare word.
  --
  -- **With an argument it is elaboration** (§8, phase 17b), and the argument
  -- goes through the @parse@ op rather than being parsed here: the program is
  -- @h = parse "‹text›"; prove with h@, so a syntax error in a hint fails the
  -- way an op fails and is visible in stepping mode. The driver still parses
  -- for @try@ and @eliminate@, which want a resolved 'Core' and not a tree.
  -- @retry@ / @retry ‹n›@ (§7.7). **The driver's, not an op** — a rule body
  -- may not contain one, because §7.2 decided there is no @catch@ and no
  -- alternation inside a body: a rule that wants an alternative is two rules,
  -- and an op that re-entered a choice point would be exactly the mechanism
  -- that refused. It is still spelled bare, because §2.4's rule is that a word
  -- that /acts/ takes no colon, and this acts.
  -- **A block typed at the REPL is played** (MS4 phase 45b), and it is how the
  -- REPL types the instruction language at all.
  --
  -- **This is what makes standing inside a yield useful.** The driver's own
  -- commands take /terms/ and /names/ — @goto h@ looks for a hole called @h@,
  -- not for whatever @h@ is bound to — so nothing typed as a command can read a
  -- suspended rule's locals. A block can: its operands are references, and with
  -- 'Thena.Engine.load' prepending, the rule's environment is still there.
  --
  -- > elaborate (do { h = here ; yield "look" ; goto h })
  -- > do { goto h }          -- reads the rule's own h
  --
  -- **And a block's own bindings survive**, for the same reason — while the
  -- machine is yielding, @env@ is not cleared, so @do { x = here }@ on one line
  -- and @do { goto x }@ on the next is one environment. Outside a yield there is
  -- no suspended program to share with and @load@ clears @env@ as it always has.
  --
  -- Reusing the surface parser rather than adding a command form: @do { … }@ is
  -- already a surface atom (phase 45), so this costs a case and no syntax.
  "do" -> case parseSurfaceTerm ("do " ++ arg) of
    Left e -> (s, Failed e)
    Right (SurfaceDo body) -> case resolveBlock (GlobalName "do") body of
      Left errs -> (s, Failed (blockProblem errs))
      Right is  -> progress (sessionStepping s)
                            s { sessionMachine = load is machine } []
    Right _ -> (s, Rejected (UnexpectedArgument name))

  -- **@yield@ hands control back to a rule that yielded** — his, 2026-09-03,
  -- and the word is deliberately the same one the op has: /"yielding is
  -- something that switches from one control to the other so returning would be
  -- named the same."/
  --
  -- It is one word with one meaning, not an overload: yielding to yourself is a
  -- no-op, so the op is meaningless typed here and the driver word is
  -- meaningless inside a body. Who it transfers to is settled by who is
  -- speaking.
  --
  -- **Bare, not @:yield@** (§2.4: a bare word acts). That is also what keeps the
  -- symmetry visible — the two directions are spelled the same.
  --
  -- **The driver's, never an op.** With 'Thena.Engine.load' prepending, an op
  -- would arrive in front of the yield and would have to delete the instruction
  -- after it. @retry@ is the precedent for a bare driver word that is not an op.
  "yield" -> noArgument $
    if Engine.isYielding machine
      then progress (sessionStepping s)
                    s { sessionMachine = Engine.resumeYield machine } []
      else (s, Rejected NotYielding)
  "retry"  -> case arg of
    "" -> retryAt Nothing
    _  -> case reads arg of
      [(n, "")] -> retryAt (Just n)
      _         -> (s, Rejected (UnexpectedArgument name))
  -- A move, so a bare word, and it needs a driver case because it is an /op/
  -- and not a rule (phase 24b). Its argument is a term — a variable naming the
  -- hole to go to — which is why it cannot reach the rule-call fallback below:
  -- that would read it as a rule name. @AGENDA.md@'s closeout item 4e is this
  -- divergence in general.
  -- **The argument is a name and is not parsed as a term** (phase 24b): the
  -- hole you want may be nowhere near the focus, and a term would have to
  -- resolve in Γ, which holds only what is above you. The move searches the
  -- development from the root instead.
  "goto"   -> withArgument (run [Do (Ops.Goto (Lit (VText arg)))])
  "cross"  -> case arg of
    "type" -> run [Do CrossType]
    "val"  -> run [Do CrossValue]
    ""     -> (s, Rejected (MissingArgument name))
    _      -> (s, Rejected (UnexpectedArgument name))

  _ | name `elem` partWords -> case corePart name arg of
        Left e  -> (s, Rejected e)
        Right p -> run [Do (Down p)]
    -- **Anything else is a rule, called by name** — the user, 2026-08-25:
    -- *"They should just be called by name, like what happens in rule's body.
    -- No additional `call` keyword. The point was — REPL is literally as if you
    -- are inside a rule's body."*
    --
    -- So @attack@, @try ‹t›@, @intro@, @solve@, @regret@, @abandon@ and
    -- @eliminate ‹t›@ stopped being cases of this function: they are rules now,
    -- and this is how they are reached. The seven primitives they run were
    -- renamed @prim-…@ so the words could go to the tactics (§8).
    --
    -- Arguments are a **run of atoms**, as a rule body writes its operands, so
    -- @f a b@ is two arguments here exactly as it is there. A compound argument
    -- is parenthesised — @try (λ (x : A) -> x)@ — which is also what @elim@'s
    -- field groups have always required (§2.6).
    -- A colon word is the driver's own and is never a rule: §2.4's split says
    -- a colon looks, and nothing that looks lives in the rule base.
    | take 1 name == ":" -> (s, Rejected (NoSuchCommand name))
    | otherwise -> case parseArguments (globals machine) ctx (names machine) arg of
        Left (Syntax e) -> (s, Failed e)
        Right (vs, n1)  ->
          progress
            (sessionStepping s)
            s { sessionMachine =
                  load [Do (Ops.Call (GlobalName name) (map Lit vs))]
                       machine { names = n1 } }
            []
  where
    machine = sessionMachine s
    ctx     = focusContext (development machine)


    matching =
      unfoldIter (matches (rules machine) (globals machine)
                          (cursor (development machine)))

    -- The base may not change under a half-built proof, current or suspended
    -- (the user, 2026-08-25). Answered before the file is read, so a refusal
    -- costs no IO and is decided in the pure half.
    proofUnderway = case (currentAttempt s, sessionSuspended s) of
      (Just att, _)    -> Just (ProofUnderway (attemptName att))
      (Nothing, [])    -> Nothing
      (Nothing, ps)    -> Just (ProofsSuspended (map (attemptName . parkedAttempt) ps))

    -- | One kind, the paths it was given. **Rule bases take several and the
    -- other two take one**, which is not an accident of spelling: a load of
    -- rule bases /replaces/ the ordered list, so the order written is the search
    -- order (§8), while a script and a proof module are each just run.
    loadKind k ps = case (k, ps) of
      (_, [])             -> (s, Rejected (MissingArgument name))
      (LoadRules, _)      -> case proofUnderway of
        Just why -> (s, Rejected why)
        Nothing  -> (s, RulesRequested ps)
      (LoadScript, [one]) -> (s, LoadRequested one)
      (LoadProof,  [one]) -> (s, ProofRequested one)
      _                   -> (s, Rejected (UnexpectedArgument name))

    noArgument r
      | null arg  = r
      | otherwise = (s, Rejected (UnexpectedArgument name))

    withArgument k
      | null arg  = (s, Rejected (MissingArgument name))
      | otherwise = k

    showGlobal what = case lookupInductive g (globals machine) of
      Just d  -> (s, ShownData d)
      Nothing -> case lookupDefinition g (globals machine) of
        Just d  -> (s, ShownGlobal g (definitionLevels d) (definitionConstraints d)
                         (fromMaybe [] (lookup g (signatures machine)))
                                    (definitionType d) (Just (definitionBody d)))
        Nothing -> case lookupConstant g (globals machine) of
          Just c  -> (s, ShownGlobal g (constantLevels c) [] [] (constantType c) Nothing)
          Nothing -> (s, Rejected (NoSuchGlobal what))
      where
        g = GlobalName what

    -- | @:elim ‹datatype›@, or @:elim ‹datatype› ‹universe›@.
    --
    -- The datatype half reports through 'ResolveError'\'s own 'NotADatatype'
    -- rather than a new case, so @:elim Foo@ and @elim Foo …@ inside a term
    -- say the same thing about the same mistake.
    --
    -- The level defaults to the datatype\'s own, which is the common case and
    -- nothing more — @Nat@\'s eliminator into @Type₀@. Writing @Type₁@ is how
    -- §3.7\'s universe trick is seen: the same datatype, a second rule.
    eliminator what = case lookupInductive g (globals machine) of
      Nothing -> (s, Failed (ResolveFailed (NotADatatype name')))
      Just d  -> case level d (dropWhile (== ' ') rest) of
        Left e  -> e
        Right l -> (s, ShownEliminator g (fst (eliminatorType d l (names machine))))
      where
        (name', rest) = break (== ' ') what
        g             = GlobalName name'

    -- The universe is read with the ordinary term parser, in the empty
    -- context, so @:elim Nat Typ₀@ reports a lex error where it happened
    -- rather than a flat refusal.
    level :: InductiveDefinition -> String -> Either (Session, Response) Level
    level d u
      | null u    = Right (inductiveLevel d)
      | otherwise = case parseCore (globals machine) [] (names machine) u of
          Left e                -> Left (s, Failed e)
          Right (Universe l, _) -> Right l
          Right _               -> Left (s, Rejected (LevelExpected u))

    -- | @:theorem ‹name› : ‹type›@ — enter proof mode.
    --
    -- The statement is checked to be a type here rather than left to the first
    -- @:revalidate@: a proof of a non-type is not worth entering.
    theorem = case sessionWork s of
      Attempting att -> (s, Rejected (AlreadyProving (attemptName att)))
      Scratch -> case parseStatement (globals machine) (names machine) arg of
        Left e             -> (s, Failed e)
        Right (Nothing, _) -> (s, Rejected (MissingArgument ":theorem"))
        Right (Just x, (ty, n1))
          -- One namespace, shared with generated names (§3.6): a theorem may
          -- not take a name a datatype or a wrapper already has.
          | isDeclared g (globals machine) -> (s, Rejected (AlreadyDeclaredHere x))
          -- Level obligations are dropped: the statement is checked to be a
          -- type, not to be consistent, and a bare @Type@ in it is a meta the
          -- proof is free to pin down. @qed@ is where they are collected.
          | otherwise -> case sortOf (globals machine) [] n1 ty of
              (Left e,  _, _)  -> (s, IllTyped e)
              (Right _, _, n2) -> started g ty n2
          where g = GlobalName x

    started g ty n =
      let (dev, n1) = newDevelopmentNamed g ty n
       in ( s { sessionMachine = machine { development = dev, names = n1 }
              , sessionWork    = Attempting (Attempt g ty [])
              }
          , Proving g ty
          )

    -- | @qed@ — certify what the development built, admit it, and close.
    --
    -- The machine does purity, extraction and the yield; the driver runs the
    -- kernel (phase 12) and, only here, **admits**. The bare @certify@ command
    -- deliberately does not — admitting needs a name, and that is what a proof
    -- has and a scratch development does not.
    --
    -- The term is read off the development a second time after the run. It is
    -- the same @extract@ on the same value, so it cannot differ; doing it this
    -- way keeps the certified term out of 'Session', where it would be a
    -- second home for something the development already says.
    closeProof = case sessionWork s of
      Scratch -> (s, Rejected NotProving)
      Attempting att -> case progress False s { sessionMachine = ran } [] of
        (s', Ran msgs Completed) ->
          case extract (flatten (development (sessionMachine s'))) of
            Left why -> (s', Ran msgs (Halted (NotYetPure (whereImpure why))))
            Right t  -> admit msgs (fromMaybe att (currentAttempt s')) s' t
        other -> other
        where
          ran = load [Do (Certify (Lit (VTerm (Trailing (attemptClaim att)))))] machine

          -- **The proof record is re-read from @s'@, never the @pr@ above.**
          -- Certifying settles the levels the claim was written with and files
          -- the residue (phase 33), and the claim is what is stored as the
          -- definition's type — reading the record from before the run stored a
          -- type still carrying a meta nothing could ever solve, which is a bug
          -- phase 33 shipped and 33b fixes.
          -- **Generalisation can now refuse** (MS4 phase 51): a level the
          -- term mentions and the type does not is defaulted, and if it has no
          -- least value there is nothing to default it to. The proof is left
          -- standing rather than admitted, so the development is still there to
          -- look at.
          admit msgs att' s' t = case admitted s' att' t of
            Left u -> (s', Ran msgs (Uncertified (Levels u)))
            Right (s'', lvs, owed, scheme) ->
              (s'', Proved (attemptName att') lvs owed scheme)

    -- Admitting is the only thing that writes a theorem to globals (§3.3.1):
    -- a proved theorem is a global **definition**, type and body both.
    --
    -- **And it is where a proof becomes a level scheme** (MS3 phase 33b). Every
    -- level meta the claim and the term are still carrying becomes a prenex
    -- parameter, and the kernel's residue becomes the constraints a use site
    -- will owe. Generalisation is /admitting/, so it is policy and lives here,
    -- with the rest of what §7.5 gives the driver; 'generalised' is the rewrite
    -- itself and lives with the record it builds.
    --
    -- Returns the generalised type as well, because that — not the claim as
    -- written — is what @qed@ reports and what @:show@ will print.
    admitted s' att t = do
      let m = sessionMachine s'
      (d, n1) <- generalised (names m) (attemptResidue att) (attemptClaim att) t
      let g  = addDefinition (attemptName att) d (globals m)
          (ps, n) = newDevelopment n1
      Right
        ( s' { sessionMachine = m { globals = g, development = ps, names = n }
             , sessionWork = Scratch
             }
        , definitionLevels d
        , definitionConstraints d
        , definitionType d
        )

    suspend = case sessionWork s of
      Scratch -> (s, Rejected NotProving)
      Attempting att ->
        ( cleared { sessionSuspended =
                      Parked att (snapshotOf machine) : sessionSuspended s }
        , Suspended (attemptName att)
        )

    -- Abandoning drops the proof; suspending keeps it. Same exit, different
    -- list — which is the whole difference between the two commands.
    abandonProof = case sessionWork s of
      Scratch -> (s, Rejected NotProving)
      Attempting att -> (cleared, Abandoned (attemptName att))

    -- Leave proof mode, putting the machine back on a fresh scratch
    -- development. **The environment and the counter are not touched**, which
    -- is what makes §2.4's promise true: a proof is stored as its own half of
    -- the machine, so a datatype declared while it was away is simply there on
    -- return.
    cleared =
      let (ps, n) = newDevelopment (names machine)
       in s { sessionMachine = machine { development = ps, names = n, exec = Exec [] [] [] }
            , sessionWork = Scratch
            }

    resume what =
      case break ((== GlobalName what) . attemptName . parkedAttempt) (sessionSuspended s) of
        (_, [])          -> (s, Rejected (NoSuchProof what))
        (before, Parked att at : after)
          | Attempting cur <- sessionWork s ->
              (s, Rejected (AlreadyProving (attemptName cur)))
          | otherwise ->
              ( s { sessionMachine = restore at machine
                  , sessionWork = Attempting att
                  , sessionSuspended = before ++ after
                  }
              , Resumed (attemptName att)
              )

    -- **No proof required** (phase 34). @:undo@ takes back the line you typed,
    -- and nothing about that needs a theorem to be open.
    undo = case sessionHistory s of
      _ :| []       -> (s, Rejected NothingToUndo)
      _ :| (u : us) ->
        ( s { sessionMachine = restore u machine, sessionHistory = u :| us }
        , Undone
        )

    declaration = withArgument $
      case parseDeclaration (globals machine) (names machine) arg of
        Left e -> (s, Failed e)
        Right (d, n1) ->
          let is = [ Do (DefineData d)
                   , Do (Say (Lit (VText ("declared " ++ nameOf d))))
                   ]
           in progress
                (sessionStepping s)
                s { sessionMachine = load is machine { names = n1 } }
                []

    goal = withArgument $ case parseCore (globals machine) ctx (names machine) arg of
      Left e -> (s, Failed e)
      Right (t, n1) -> case setGoal t machine { names = n1 } of
        Left e   -> (s, Rejected (NotThere e))
        Right m' -> (s { sessionMachine = m' }, Shown (cursor (development m')))

    -- Both of these advance the session counter even when they fail. Conversion
    -- and inference mint variables to open binders with, and a name that has
    -- reached the user inside an error must never be handed out again (§7.4).
    bump n = s { sessionMachine = machine { names = n } }

    inferred t n = case infer (globals machine) ctx n t of
      (Left e,   _, n1) -> (bump n1, IllTyped e)
      (Right ty, _, n1) -> (bump n1, Inferred t ty)

    -- | @:infer ‹surface›@ — his framing, 2026-09-01: /"if this term were put
    -- here, what would its type be?"/
    --
    -- **Elaborate into a hole of unknown type, read the type off, put the
    -- development back.** The hole is claimed at a second hole @Tinfer@, which
    -- is what "unknown type" means here: unification solves it while the term
    -- is elaborated, and 'Thena.Development.Cursor.expectedType' at the focus is
    -- then the answer. @Elaborate@ leaves the focus where it found it (phase
    -- 41b), which is what makes reading it off exact rather than careful.
    --
    -- **The rewind is unconditional**, where phase 25d's is taken only when a
    -- line fails: this command is a look, so a success must undo itself too.
    -- Only the development is rewound — @names@ and @globals@ are not part of a
    -- 'Snapshot' (§7.7), and the counter must not go back or a number the user
    -- has seen would be reissued (MS2 closeout 4f).
    --
    -- **It revalidates before answering.** A level obligation is collected only
    -- by 'Thena.Development.Validate' and the kernel, so an elaboration can
    -- succeed while owing one; reporting a type for a development that does not
    -- check would be the gap @ms3\/CLOSEOUT.md@ item 25 describes, one command
    -- further on.
    inferSurface t =
      let (l, n1) = freshLevelMeta (names machine)
          before  = snapshotOf machine
          prog =
            [ Bind "T" (Claim (Lit (VText "Tinfer"))
                          (Lit (VTerm (Trailing (Universe (LVar l))))))
            , Bind "x" (Claim (Lit (VText "xinfer")) (Ref "T"))
            , Do (Ops.Goto (Lit (VText "xinfer")))
            , Do (Call (GlobalName "elaborate") [Lit (VSurface (rootedAt t))])
            ]
          asking  = s { sessionMachine = load prog machine { names = n1 } }
       in case progress False asking [] of
            (s', Ran _ Completed) ->
              let m'   = sessionMachine s'
                  back = s' { sessionMachine = restore before m' }
                  dev  = development m'
               in case revalidate (globals m') [] (names m') (flatten dev) of
                    (Left e, _) -> (back, Revalidated (Just e))
                    -- **whnf'd, and that is not cosmetic.** The type is read
                    -- off the hole the elaboration solved, so without reducing
                    -- it prints as @Tinfer@ — the hole's own variable — and says
                    -- nothing. It therefore reduces further than @:infer ⌜t⌝@
                    -- does: a saturated former where that stops at the wrapper.
                    -- **The two agree up to conversion, not syntactically**, and
                    -- they print the same.
                    (Right _, _) -> case expectedType (cursor dev) of
                      Just ty -> (back, InferredSurface t
                                          (whnf (globals m') (focusContext dev) ty))
                      -- Unreachable as the program is written — the focus is the
                      -- component @Elaborate@ was pointed at — but the cursor
                      -- type admits it and inventing an answer would be worse.
                      Nothing -> (back, Rejected (NotThere NotInCore))
            (s', other) -> (s' { sessionMachine = restore before (sessionMachine s') }, other)

    conversion = withArgument $
      case parseEquated (globals machine) ctx (names machine) arg of
        Left e -> (s, Failed e)
        Right ((a, b), n1) -> case convert (globals machine) ctx n1 a b of
          (why, owed, n2) -> (bump n2, Converted a b why owed)

    stepping = case arg of
      ""    -> progress True s []
      "on"  -> (s { sessionStepping = True }, Ran [] Completed)
      "off" -> (s { sessionStepping = False }, Ran [] Completed)
      _     -> (s, Rejected (UnexpectedArgument name))

    run is = progress (sessionStepping s) s { sessionMachine = load is machine } []

    -- Unwind to a choice point and take its next alternative, then let the
    -- machine run as any other command does. 'Thena.Engine.retryFrom' is what
    -- knows how; the driver only decides which one and reports what happened,
    -- because §7.7 asks @retry@ to say what it did — it pops past any 'Call'
    -- frames in between, which may be several commands back.
    retryAt target = case Engine.retryFrom target machine of
      Left Engine.NoChoicePoint   -> (s, Rejected NothingToRetry)
      Left (Engine.UnknownChoice n) -> (s, Rejected (NoSuchChoice n))
      Right (m, note) ->
        let (s', resp) = progress (sessionStepping s) s { sessionMachine = m } []
         in (s', withNote note resp)

    -- The note goes in front of whatever the alternative itself said, as a
    -- 'Message' — the same shape as @"declared X"@ and @"certified"@, which
    -- the driver also builds because they are things the driver decided (§7.5).
    withNote note resp = case resp of
      Ran msgs stop -> Ran (note : msgs) stop
      _             -> resp

    -- **Brady's @ELAB (x : t)@, as a program** (@IDRIS.md@ §4.6):
    --
    -- > NEW PROOF Type; E⟦t⟧; t' ← TERM; TTDECL (x : t')
    --
    -- The signature is elaborated in a development of its own — @certify@
    -- extracts the whole chain, so it could not share one with the body — and
    -- the term read off it becomes the type the body is elaborated against.
    --
    -- **The driver builds the program and the machine runs it**, which is what
    -- @assume@ and @claim@ already do. Nothing here elaborates.
    declareSurface src = case parseSurfaceItems src of
      Left e -> (s, Failed e)
      Right items ->
        let (is, n1) = surfaceProgram (names machine) items
         in progress (sessionStepping s)
                     s { sessionMachine = load is machine { names = n1 } } []

    tactic what verb op = withArgument $
      case compile what verb op (globals machine) ctx (names machine) arg of
      Left e -> (s, Failed e)
      Right (is, n1) ->
        progress (sessionStepping s) s { sessionMachine = load is machine { names = n1 } } []

-- | What @:help@ shows: one line per command the driver has, the spelling on
-- the left and what it does on the right.
--
-- **It is a second place a command word is written, and it cannot be derived
-- from 'dispatch'**, which is a @case@ over strings and so is not enumerable.
-- Three things keep the two together: this list sits next to 'dispatch', the
-- field descents are taken from 'partWords' rather than restated, and
-- "Thena.DriverTests" crosses every colon word here against 'dispatch' and a
-- hand-written list of colon words against this — the same arrangement, and
-- the same admitted incompleteness, as @RuleSyntaxTests@' @everyOp@.
--
-- **The tactics are deliberately absent.** @attack@, @intro@, @try@ and the
-- rest are rules in the rule base, not commands (§8, phase 23b); listing them
-- here would state the base's contents in a second place, and it would go
-- stale the moment a base is loaded. The last line points at @:rules@ instead.
--
-- **@prove@ was listed and is not any more** (MS4 phase 43). Phase 41 made it a
-- rule over @prim-prove@, at which point the paragraph above started applying
-- to it and nothing noticed — the same phase left @prove ‹hint›@ and
-- @:matches ‹hint›@ here after retiring hints. @declare@ and @quantify@ were
-- missing for the opposite reason: they are the driver's own and had never been
-- added. **All four were found by crossing this list against @dispatch@ by
-- hand**, which is what @ms3\/CLOSEOUT.md@ 26 exists to make unnecessary — the
-- @DriverTests@ mirrors had the same gaps, so they could not have caught it.
commandSummary :: [(String, String)]
commandSummary =
  [ ("assume ‹x› : ‹S›",        "add a hypothesis above the focus")
  , ("claim ‹x› : ‹S›",         "add a hole above the focus")
  , ("unify ‹t› ≟ ‹u›",         "solve the focus by unification")
  , ("do { ‹instruction› ; … }", "play a block of instructions here")
  , ("yield",                    "hand control back to a rule that yielded")
  , ("retry / retry ‹n›",        "backtrack to a choice point")
  , ("along  into  back",        "move on the chain")
  , ("cross type / cross val",   "move into a term")
  , (unwords bareParts,          "descend into a field of the focused term")
  , (unwords numberedParts,      "descend into a numbered field")
  , ("goto ‹hole›",              "move to a hole by name")
  , ("reduce",                   "reduce the focused term in place")
  , ("quantify ‹x› : ‹S›",       "add a ∀-binder above the focus")
  , ("data ‹D› … where { … }",   "declare an inductive family")
  , ("declare ‹sig› ; ‹equation›", "elaborate a surface declaration")
  , ("certify ‹type›",           "ask the kernel about the development")
  , ("qed",                      "certify and admit the finished proof")
  , (":show / :show ‹name›",     "the development / a global")
  , (":where",                   "focus, path, context, expected type")
  , (":core ‹t› / :dev ‹p›",     "parse a term / a development and print it")
  , (":surface ‹t›",             "parse a surface term and print it")
  , (":infer / :infer ‹t›",      "the type of the focus / of a surface term")
  , (":whnf / :whnf ‹t›",        "reduce the focus / a term, without committing")
  , (":convert ‹t› ≟ ‹u›",      "are two terms convertible")
  , (":elim ‹D› [‹universe›]",  "a datatype’s elimination rule")
  , (":matches",                 "which rules apply here")
  , (":choices",                 "the live choice points, nearest first")
  , (":bases / :rules",          "the loaded rule bases / the rules in them")
  , (":step on / :step / :step off", "single-step the machine")
  , (":run",                     "let a stepping machine run on")
  , (":theorem ‹x› : ‹T›",      "start a proof")
  , (":goal ‹T›",                "discard everything and start a scratch goal")
  , (":suspend / :resume ‹name›", "put a proof aside / take it up again")
  , (":proofs",                  "the current proof and the suspended ones")
  , (":abandon",                 "give up the current proof")
  , (":undo",                    "take back the last line")
  , (":extract",                 "the term the development stands for")
  , (":revalidate",              "recheck the whole development")
  , (":load ‹path›",             "a proof module, a script, or rule bases")
  , (":load proof / rules / script", "say which, rather than by extension")
  , (":help",                    "this list")
  , (":quit",                    "leave")
  ]
  where
    -- Taken from 'partOf' rather than written out, so a new field word joins
    -- these lines by existing (phase 5's lesson: the check that catches a
    -- mistake is the one made by different code from the code it checks).
    bareParts     = [ w | w <- partWords, isJust (partOf w Nothing) ]
    numberedParts = [ w ++ " ‹n›" | w <- partWords, isJust (partOf w (Just 1)) ]

-- | The core-term descents, as the user types them (§4.7).
--
-- One word per 'Part', and the words are the field names of §2.6's syntax. The
-- three that take a position are one-based, because the printer numbers from
-- one and nothing else here counts.
--
-- @arg@ is both @f □@\'s and a former's, and takes a position in the second
-- case only — a saturated 'Thena.Core.Term.Canonical' has many arguments and an
-- application has exactly one, so no form has both readings and no word changes
-- meaning.
-- | @fun@, @arg 2@ … — "Thena.Ops"\'s table, with this module\'s two error
-- messages laid over it.
--
-- **The table moved down in phase 21** so that a field word means the same
-- thing at the REPL and inside a rule body, from one place rather than two.
-- What stays here is the refinement a command line wants and a rule body does
-- not: @param@ with no number is a /missing/ argument, @fun 2@ an /unexpected/
-- one, and 'Thena.Ops.partOf' answers 'Nothing' to both.
corePart :: String -> String -> Either CommandError Part
corePart w a = case a of
  "" -> maybe (Left (MissingArgument w)) Right (partOf w Nothing)
  _  -> case reads a of
    [(k, "")] -> maybe (Left (UnexpectedArgument w)) Right (partOf w (Just k))
    _         -> Left (UnexpectedArgument w)

-- --------------------------------------------------------------------------
-- Rule bases (§8, phase 22)
-- --------------------------------------------------------------------------

-- | @:load@\'s argument, split on spaces and commas. **Both separators** —
-- the user asked for "comma or space separated (or both)", 2026-08-25.
-- | An argument written in corners, with them stripped (MS4 phase 43).
--
-- **The same split 'groups' makes, for a command that takes one argument
-- rather than a run of them.** A command word decides which vocabulary it is
-- reading, and this is how it asks: corners are the development calculus, a
-- bare argument is the surface language.
--
-- Textual rather than a lex-and-inspect, because it is answering a question
-- about how the argument was /written/ — and being wrong is a parse error in
-- the grammar the user did not mean, not a silent misreading.
cornered :: String -> Maybe String
cornered src = case dropWhile (== ' ') src of
  '\8988' : rest -> case break (== '\8989') rest of
    (inner, '\8989' : after) | all (== ' ') after -> Just inner
    _                                              -> Nothing
  _ -> Nothing

pathsOf :: String -> [FilePath]
pathsOf = words . map (\c -> if c == ',' then ' ' else c)

-- | Is this a rule base rather than a script? The extension is the whole test,
-- and it is the user\'s: *"Maybe `.thena.rules`, that sounds fine."*
-- | Which of the three kinds a path names. **The extension is the whole test**,
-- and it is the user's, 2026-09-02: /"The extension for thena proofs is
-- @.thena@ — that's the whole extension. I think ideally we would have
-- @:load rules@ and @:load proof@ and the universal @:load@ can load anything
-- depending on the extensions."/
--
-- The three suffixes are disjoint, so no path has two readings: a script ends
-- @.thena.script@, a rule base @.thena.rules@, and a proof module @.thena@ and
-- neither of the others.
--
-- **@.thena@ meant a script until phase 43**, which is why the four shipped
-- files were renamed rather than the proof module taking a new extension: he
-- named @.thena@ for the proof module, and a proof module is what a reader will
-- write most.
data LoadKind = LoadRules | LoadProof | LoadScript
  deriving (Eq, Show)

kindOf :: FilePath -> LoadKind
kindOf p
  | ruleExtension   `isSuffixOf` p = LoadRules
  | scriptExtension `isSuffixOf` p = LoadScript
  | otherwise                      = LoadProof

ruleExtension :: String
ruleExtension = ".thena.rules"

scriptExtension :: String
scriptExtension = ".thena.script"

-- | Why a rule-base file was not accepted.
data RuleFileError
  = NoRuleHeader
    -- ^ the file does not begin @rule base ‹name› where@, optionally preceded
    -- by a @\"\"\"…\"\"\"@ description (phase 25e). Required, because a base is a
    -- named thing that @:bases@ has to be able to list
  | RuleSyntaxError SyntaxError
    -- ^ it did not lex or parse. The position is inside, and it is the true
    -- line: the header is blanked rather than dropped so that nothing shifts
  | RuleIllFormed [RuleError]
    -- ^ it parsed, and one or more rules did not resolve or did not validate
  deriving (Eq, Show)

-- | The head of a rule-base file: an optional @\"\"\"…\"\"\"@ description, then
-- @rule base ‹name› where@.
--
-- **The description moved out of the header line and above it — his change,
-- 2026-08-26**, closing the item he had parked at phase 22 (*\"later, I will
-- want to revisit this and make it nicer and more robust\"*). It reads better
-- and it parses better, and the second is the substantive half: a triple-quoted
-- block is **delimited**, where the old description was terminated by @where@
-- and so could never contain that word. It may now run to several lines.
--
-- **Still read textually, before the lexer sees anything** — the trick phase 22
-- introduced, and the reason a description may hold commas, parentheses and
-- quotes, all of which are reserved characters that would not lex.
--
-- Returns the name, the description, and **how many lines were consumed**, so
-- the caller can blank exactly those and leave every later position naming the
-- line the user is looking at.
baseHead :: [String] -> Maybe (String, Maybe String, Int)
baseHead ls0 = do
  -- **Comment lines are skipped like blank ones** (MS4 phase 43). The header is
  -- read textually, before the lexer, so it is the one place a comment has to
  -- be recognised twice — and a rule base that could not be commented above its
  -- own header would make the uniformity his ruling asked for a fiction.
  let (blanks, ls1) = span skippable ls0
  (desc, ls2, used) <- Just (docstring ls1)
  let (blanks2, ls3) = span skippable ls2
  (nm, hdr) <- case ls3 of
    l : _ -> (\n -> (n, 1 :: Int)) <$> baseLine l
    []    -> Nothing
  Just (nm, desc, length blanks + used + length blanks2 + hdr)

skippable :: String -> Bool
skippable l = all isSpace l || commentLine l

-- | Is this whole line a comment (MS4 phase 43)?
--
-- **One place says what a comment line is**, and it says the same thing the
-- lexer's rule does: @--@ is a comment when a space follows it, and an
-- identifier-ish token when one does not. @words@ answers exactly that, because
-- it is the space that separates them.
commentLine :: String -> Bool
commentLine l = case words l of
  "--" : _ -> True
  _        -> False

-- | @rule base ‹name› where@ — the name and nothing else between.
baseLine :: String -> Maybe String
baseLine l = case words l of
  ["rule", "base", nm, "where"] -> Just nm
  _                             -> Nothing

-- | A leading @\"\"\"…\"\"\"@ block, if there is one: its text, what is left, and
-- how many lines it took. Opening and closing delimiters may share a line.
--
-- An **unterminated** block yields no description and consumes nothing, so the
-- file then fails on its header line rather than silently swallowing the rules.
docstring :: [String] -> (Maybe String, [String], Int)
docstring ls = case ls of
  l : rest
    | Just after <- stripPrefix quote (dropWhile isSpace l) ->
        case breakOn quote after of
          Just (before, _) -> (tidy [before], rest, 1)
          Nothing          -> gather [after] rest 1
  _ -> (Nothing, ls, 0)
  where
    quote = "\"\"\""

    gather _ [] _ = (Nothing, ls, 0)   -- unterminated: consume nothing
    gather acc (l : rest) n = case breakOn quote l of
      Just (before, _) -> (tidy (reverse (before : acc)), rest, n + 1)
      Nothing          -> gather (l : acc) rest (n + 1)

    tidy parts =
      let text = unlines (map (dropWhileEnd isSpace) parts)
          trimmed = dropWhile isSpace (dropWhileEnd isSpace text)
       in if null trimmed then Nothing else Just trimmed

-- | The text before the first occurrence of a needle, and the text after it.
breakOn :: String -> String -> Maybe (String, String)
breakOn needle = go ""
  where
    go acc h
      | Just t <- stripPrefix needle h = Just (reverse acc, t)
      | c : cs <- h                    = go (c : acc) cs
      | otherwise                      = Nothing

-- | Read one rule-base file: its header, then its rules.
--
-- **It needs nothing but the file** — phase 23 moved @call@'s lookup to run
-- time, so a rule no longer has to be resolved against the rules already in
-- scope, and this stopped threading them. That is what lets a rule call itself,
-- call a rule written below it, and call a rule in a base loaded after it.
--
-- Takes contents and not a path (§12 invariant 4).
readRuleBase :: FilePath -> String -> Either RuleFileError RuleBase
readRuleBase path src = case baseHead ls of
  Nothing -> Left NoRuleHeader
  Just (nm, desc, used) -> do
      -- The head is blanked, not dropped: every position the lexer reports
      -- then names the line the user is looking at.
      let rest = replicate used "" ++ drop used ls
      ts   <- mapLeft RuleSyntaxError (tokensOf (unlines rest))
      raws <- mapLeft (RuleSyntaxError . ParseFailed) (parseRules ts)
      rs   <- resolveAll raws
      Right (ruleBase nm desc path rs)
  where
    ls = lines src

-- | Resolve every rule, then validate every rule. Every error, not the first —
-- 'validate'\'s reason.
resolveAll :: [RawRule] -> Either RuleFileError [Rule]
resolveAll raws = case (concat resolveErrs, concatMap validate ok) of
  ([], [])     -> Right ok
  (res, valid) -> Left (RuleIllFormed (res ++ valid))
  where
    (resolveErrs, ok) = partitionEithers (map resolveRule raws)

-- | Install a whole ordered list of bases, or none of them.
--
-- **A load replaces the list** — the user, 2026-08-25: *"If I want to shuffle
-- them, I just run load again and that replaces the entire thing."* So this is
-- also the shuffling command, until there is a real one.
--
-- **All or nothing.** A file that will not load leaves the previous list in
-- place, so a session never ends up searching half of what was asked for.
loadRuleBases :: Session -> [(FilePath, String)] -> (Session, Response)
loadRuleBases s = go [] 
  where
    go acc [] =
      ( s { sessionMachine = (sessionMachine s) { rules = acc } }
      , BasesLoaded acc
      )
    go acc ((path, src) : more) =
      case readRuleBase path src of
        Left e  -> (s, RuleFileRefused path e)
        Right b -> go (acc ++ [b]) more

-- | Read something and hand it back for rendering.
--
-- Top-level rather than a @where@ binding in 'dispatch' because it is used at
-- 'Core' and at 'Partial' both, and a @where@ binding under a guard does not
-- generalise — the same trap phase 3 met with its @respond@.
--
-- It threads the counter: rendering a term mints display variables, and
-- rendering with a counter below the term's highest 'Thena.Core.Term.Var'
-- silently makes a colliding name (phase 3's §7).
view
  :: Session
  -> (GlobalEnv -> Context -> Int -> String -> Either SyntaxError (a, Int))
  -> (a -> Response)
  -> String
  -> (Session, Response)
view s rd f arg =
  case rd (globals machine) (focusContext (development machine)) (names machine) arg of
  Left e        -> (s, Failed e)
  Right (x, n1) -> (s { sessionMachine = machine { names = n1 } }, f x)
  where
    machine = sessionMachine s

-- | A command becomes a program (§2.4, §12 invariant 3).
--
-- Two paths, and the nameless one is §2.2's motivating example: @assume :
-- Type₀@ has no name to give the binder, so the program asks for one and the
-- answer lands in @env@ where the op reads it.
--
-- The prompt quotes the type as the user wrote it rather than as the printer
-- would render it: rendering lives in "Thena.Repl" (§2.5) and the driver
-- cannot reach it. §7.5's illustrative body builds the same prompt with a
-- @show@ op, which phase 4 does not have.
compile
  :: String -> String -> (Operand -> Operand -> Op)
  -> GlobalEnv -> Context -> Int -> String -> Either SyntaxError ([Instr], Int)
compile what verb op env ctx n arg = do
  ts       <- tokensOf arg
  (mx, ty) <- mapLeft ParseFailed (parseNameAndType ts)
  (t, n1)  <- mapLeft ResolveFailed (resolve env ctx n ty)
  let term = Lit (VTerm (Trailing t))
  pure $ case mx of
    Just x ->
      ( [ Do (op (Lit (VText x)) term)
        , Do (Say (Lit (VText (verb ++ " " ++ x))))
        ]
      , n1
      )
    Nothing ->
      ( [ Bind "name"    (Ask (Lit (VText prompt)) AName)
        , Do             (op (Ref "name") term)
        , Bind "message" (Concat (Lit (VText (verb ++ " "))) (Ref "name"))
        , Do             (Say (Ref "message"))
        ]
      , n1
      )
  where
    prompt =
      "name for the " ++ what ++ "? it will have type "
        ++ dropWhile (\c -> c == ':' || c == ' ') arg

-- --------------------------------------------------------------------------
-- The loop of §7.8
-- --------------------------------------------------------------------------

-- | Answer the question the machine is asking, then carry on.
answer :: Session -> String -> (Session, Response)
answer s a
  | isAsking (sessionMachine s) =
      progress (sessionStepping s) s { sessionMachine = resumeAt a (sessionMachine s) } []
  | otherwise = (s, Rejected NotAsking)

-- | One line of input, whichever kind it is: an answer while something is
-- asking, a command otherwise. Returns what is asking /after/ it.
--
-- Extracted at phase 11 because two callers need exactly this — "Thena.Repl"\'s
-- terminal turn and 'loadSource' below — and the pending-question bookkeeping
-- is the part a second copy would get subtly wrong.
oneLine :: Session -> Maybe Question -> String -> (Session, Response, Maybe Question)
oneLine s pending line = (record s', resp, asking)
  where
    (s', resp) = case pending of
      Just _  -> answer s line
      Nothing -> command s line

    asking = case resp of
      Ran _ (Waiting q) -> Just q
      _                 -> Nothing

    -- Keep the current proof's snapshot in step with the machine, and push the
    -- old one for @:undo@ **only if the line actually changed it**.
    --
    -- That test is what makes @:undo@ usable rather than a stack of duplicates:
    -- a @:show@ leaves @exec@ and @proof@ equal to what they were, so nothing
    -- is pushed and @:undo@ does not have to be pressed twice. It also means
    -- undo is per line rather than per machine step, which is what the user
    -- typed and therefore what they expect to take back.
    --
    -- @:undo@ itself must not record, or undoing would immediately re-record
    -- the state it just left.
    record sess = sess'
      where
       sess'
        -- **A line that did not do what it said leaves the proof exactly as it
        -- was** (phase 25d). Before this, a rule body that had already changed
        -- the development and then failed left what it built behind, and the
        -- user had to notice and type @:undo@. The user, 2026-08-25: /"it
        -- rewinds the state to what it was previously before the command ran…
        -- so that the user can try again with no change to their previously
        -- correct state."/
        --
        -- **This is not backtracking and does not want a choice point.** His
        -- own analysis: a tactic failing at the REPL has nowhere to backtrack
        -- to, and inside a search 'Thena.Engine.failure' already restores the
        -- snapshot of the choice point it unwinds to. This is the top of the
        -- stack, where there is no such frame — 'Thena.Engine.Stuck' is
        -- returned only from an @unwind@ that found none.
        --
        -- 'stopped' is reused rather than matched on 'Halted' alone, because it
        -- already means /the four ways a line does not do what it said/ and
        -- that is exactly the condition. 'Failed' and 'Rejected' never ran the
        -- machine and 'Refused' changes no development, so for those three the
        -- restore is a no-op — which is the point: one rule, no case analysis
        -- about which failures dirty the state.
        --
        -- **Per line, like @:undo@ itself.** If an @ask@ suspended the command
        -- and the answering line fails, this rewinds to the asking state and
        -- not to before the whole command, because that is where the previous
        -- snapshot was taken. §2.4's granularity, applied consistently.
        | stopped resp =
            sess { sessionMachine =
                     restore (NE.head (sessionHistory sess)) (sessionMachine sess) }
        -- **A proof boundary starts a fresh history** (phase 34, his choice of
        -- three). Done here and not in the five commands themselves, because
        -- @record@ runs /after/ the command and would push the crossing itself
        -- back on top of a stack the command had just emptied.
        | boundary resp = sess { sessionHistory = now :| [] }
        | resp == Undone || now == NE.head (sessionHistory sess) =
            sess { sessionHistory = now :| NE.tail (sessionHistory sess) }
        | otherwise = sess { sessionHistory = now NE.<| sessionHistory sess }
       now = snapshotOf (sessionMachine sess)

-- | The per-proof half of a machine.
snapshotOf :: Machine -> Snapshot
snapshotOf m = (exec m, development m, enclosing m)

-- | Put one back.
restore :: Snapshot -> Machine -> Machine
restore (e, p, encl) m = m { exec = e, development = p, enclosing = encl }

-- --------------------------------------------------------------------------
-- Loading a file (§9, phase 11)
-- --------------------------------------------------------------------------

-- | Why a load stopped early. Every case carries the **1-based line number**,
-- because the whole value of loading a file over typing the lines is that the
-- failure has an address.
data LoadError
  = LoadStopped Int
    -- ^ this line failed. **The reason is not carried here** — it is the last
    -- of 'loadedResponses', the ordinary response the REPL would have printed
    -- had the line been typed. Two encodings of one failure can disagree
    -- (§3.7's argument against emitting ι-rules, in miniature)
  | NestedLoad Int
    -- ^ @:load@ inside a loaded file. Refused in MS1 rather than followed:
    -- following it needs IO from a pure function, and a file that loads itself
    -- would not terminate
  | UnansweredQuestion Int
    -- ^ the file ended while an op was still asking (§7.5). The line is the one
    -- that asked
  deriving (Eq, Show)

-- | What running a file produced.
data Loaded = Loaded
  { loadedSession   :: Session
  , loadedResponses :: [Response]
    -- ^ one per line that ran, in order, blank lines included as 'Blank'
  , loadedError     :: Maybe LoadError
  }
  deriving (Eq, Show)

-- | Run a file\'s contents.
--
-- **A file is a script of command lines** — decided by the user 2026-08-22,
-- planning phase 11. Each line goes through 'oneLine', so it means exactly what
-- it would mean typed at the prompt, asking and answering included, and there
-- is no second syntax to keep in step with the first. The prelude is therefore
-- an ordinary sequence of @data@ lines and nothing else (§3.7).
--
-- **It stops at the first failure**, on phase 6\'s precedent that a refused
-- declaration abandons the rest of a program: a later line in a file is
-- normally written against what an earlier one declared, so carrying on past a
-- failure reports the same mistake several times over.
--
-- Takes the contents and not a path: §12 invariant 4 keeps IO in "Thena.Repl".
--
-- **A finished load leaves no undo history** (phase 34). Each line goes through
-- 'oneLine' and so pushes its own snapshot, and stepping back into the middle of
-- the prelude is not what @:undo@ is for — a file declares datatypes and admits
-- theorems, which are @globals@ changes a 'Snapshot' deliberately does not carry
-- (§7.7). Same argument as @qed@ clearing it, for the same reason.
loadSource :: Session -> String -> Loaded
loadSource s0 = go s0 Nothing 1 [] . lines
  where
    finished s acc err =
      Loaded s { sessionHistory = NE.head (sessionHistory s) :| [] } (reverse acc) err

    go s pending _ acc [] = case pending of
      -- The file ran out while an op was still asking. The line to name is the
      -- one that asked, which is the last one that ran.
      Just _  -> finished s acc (Just (UnansweredQuestion (length acc)))
      Nothing -> finished s acc Nothing
    go s pending n acc (l : ls) =
      let (s', resp, asking) = oneLine s pending l
          acc'               = resp : acc
       in case resp of
            LoadRequested _ -> finished s acc (Just (NestedLoad n))
            Quit            -> finished s' acc' Nothing
            _ | stopped resp -> finished s' acc' (Just (LoadStopped n))
              | otherwise    -> go s' asking (n + 1) acc' ls

-- | Which responses cross a proof boundary — the five ways the development you
-- are standing in is exchanged for another (§2.4).
--
-- @:undo@ does not cross one. @qed@ is the case that forces it: admitting writes
-- to @globals@, and @globals@ is deliberately not part of a 'Snapshot' (§7.7,
-- \"the environment only ever grows\"), so an @:undo@ that stepped back over a
-- @qed@ would rewind the development and leave the theorem admitted. The other
-- four are the same idea without the sharp edge.
boundary :: Response -> Bool
boundary resp = case resp of
  Proving {}   -> True
  Proved {}    -> True
  Abandoned {} -> True
  Suspended {} -> True
  Resumed {}   -> True
  _            -> False

-- | Which responses end a load.
--
-- Deliberately narrow: an @:infer@ that reports an ill-typed term is a question
-- answered, not a script that failed, so 'IllTyped' is not here. What is here
-- is the four ways a line does not do what it said.
stopped :: Response -> Bool
stopped resp = case resp of
  Failed _            -> True
  Rejected _          -> True
  Ran _ (Halted _)    -> True
  Ran _ (Refused _)   -> True
  _                   -> False

-- | Run until the machine needs the user, honouring stepping mode.
--
-- @Saying@ costs a round trip per message and buys the driver an ordered view
-- of execution as a sequence of events (§7.5), which is why the messages come
-- back as a list rather than being buffered in the machine.
--
-- Phase 13 snapshots for @:undo@ at 'Completed'; phase 16 kept the machine at
-- 'Halted' for @retry@\'s sake, which phase 25d found was never reachable —
-- see 'Halted'. The machine still comes back here; what changed is that
-- 'oneLine' does not let a failed line's development survive into the session.
progress :: Bool -> Session -> [Message] -> (Session, Response)
progress oneStep s msgs = case step (sessionMachine s) of
  Engine.Continue m
    | oneStep   -> stop m msgs Paused
    | otherwise -> progress oneStep s { sessionMachine = m } msgs
  Engine.Saying msg m
    | oneStep   -> stop m (msg : msgs) Paused
    | otherwise -> progress oneStep s { sessionMachine = m } (msg : msgs)
  -- **A yield stops the run and keeps the machine** (MS4 phase 45b), exactly as
  -- a question does. Stepping it again would yield again — the instruction is
  -- not consumed — so the driver has to stop here or spin.
  Engine.Yielding msg m -> stop m msgs (Yielded msg)
  -- The declaration is checked and installed here, outside the machine: the
  -- global environment is not part of 'Development' and no instruction writes it
  -- (§7.4, §7.5). On refusal the rest of the program is dropped — the command
  -- is abandoned, and there is nothing to retry the way there is at 'Halted'.
  Engine.Declaring d m -> case declare (globals m) (names m) d of
    Left e -> stop (load [] m) msgs (Refused e)
    Right (g, n1, skip)
      | oneStep   -> stop installed msgs' Paused
      | otherwise -> progress oneStep s { sessionMachine = installed } msgs'
      where
        installed = m { globals = g, names = n1 }
        -- Said here rather than by a 'Say' in the program, because the program
        -- is built before 'declare' runs and cannot know (§7.5: the driver owns
        -- what the driver decides).
        msgs' = maybe msgs (\why -> whyNoConfusion (inductiveName d) why : msgs) skip
  -- The kernel runs here, outside the machine, for 'Declaring'\'s reason: it is
  -- policy, and §7.5 has the driver own policy. On refusal the rest of the
  -- program is dropped.
  --
  -- **What the kernel forced is written back here** (MS3 phase 33). It returns
  -- the level solutions its check needed, and the development the term was
  -- extracted from still mentions those metas — @qed@ stores its definition
  -- from that development, and @:show@ reads it. A level meta has no component
  -- to be promoted, so the only place a solution can be recorded is the terms
  -- that mention it (§4), and that is what 'Cursor.overLevels' does.
  --
  -- Empty whenever no bare @Type@ was written, which is every use of the kernel
  -- before this phase.
  -- **A declaration arrives in the environment exactly as @qed@'s proof does**
  -- (MS4 phase 42): the kernel runs, the level metas generalise, and
  -- 'addDefinition' installs. The difference is only where the name and the
  -- type came from — an 'Attempt' there, the declaration itself here.
  --
  -- **It says nothing**, per his instruction: the command that ran it reports
  -- when it is over. See 'Thena.Ops.DefineGlobal'.
  Engine.Defining nm ps ty t m -> case certify (globals m) t ty of
    Left e -> stop (load [] m) msgs (Uncertified e)
    Right (sub, residue) -> case generalised (names m) residue (substLevelsIn sub ty) t of
      Left u -> stop (load [] m) msgs (Uncertified (Levels u))
      Right (d, n1) ->
        let
          -- **The plicities are installed beside the definition** (MS4 phase
          -- 44b) and only when there are any, so a global whose signature said
          -- nothing implicit adds no entry at all.
          m'      = m { globals    = addDefinition nm d (globals m)
                      , names      = n1
                      , signatures = if Explicit `elem` ps && Implicit `notElem` ps
                                       then signatures m
                                       else (nm, ps) : signatures m
                      }
       in if oneStep
            then stop m' msgs Paused
            else progress oneStep s { sessionMachine = m' } msgs

  Engine.Certifying t ty m -> case certify (globals m) t ty of
    Left e -> stop (load [] m) msgs (Uncertified e)
    Right (sub, residue)
      | oneStep   -> stop settled' (say : msgs) Paused
      | otherwise -> progress oneStep s' (say : msgs)
      where
        say = "certified"
        settled' = m { development = Engine.Development
                                 (overLevels sub (cursor (development m))) }
        s' = (settled sub residue s) { sessionMachine = settled' }
  Engine.Asking q m   -> stop m msgs (Waiting q)
  Engine.Finished m   -> stop m msgs Completed
  Engine.Stuck r m    -> stop m msgs (Halted r)
  where
    stop m out what = (s { sessionMachine = m }, Ran (reverse out) what)

-- | Write a level solution into the proof's own statement.
--
-- The development is rewritten beside it (see 'progress''s @Certifying@ case);
-- this is the other half, because @qed@ stores the claim as the definition's
-- type and @:show@ prints it.
-- **And it files the residue** for @qed@ to generalise (phase 33b); see
-- 'Proof''s own field.
settled :: [(LevelVar, Level)] -> [Obligation] -> Session -> Session
settled sub residue s = s { sessionWork = fmap' (sessionWork s) }
  where
    fmap' Scratch          = Scratch
    fmap' (Attempting att) = Attempting (at att)
    at att = att { attemptClaim   = substLevelsIn sub (attemptClaim att)
               , attemptResidue = residue
               }

nameOf :: InductiveDefinition -> String
nameOf d = case inductiveName d of GlobalName x -> x

-- | Why a datatype got no no-confusion (phase 14).
--
-- A message, not an error, so it is a 'String' here beside @"declared X"@ and
-- @"certified"@ rather than structured data rendered in "Thena.Repl". The
-- declaration succeeded; this says what it does not come with.
--
-- 'Thena.Global.NoConfusion.NoEquality' and
-- 'Thena.Global.NoConfusion.NoProducts' never reach here —
-- "Thena.Global.Declare" keeps both quiet, because each is a fact about the
-- environment rather than about the declaration and would fire on every @data@
-- line of a prelude-free script. They are given wordings anyway rather than an
-- @error@ call: a message that cannot be printed is still cheaper to write than
-- a partial function to explain.
whyNoConfusion :: GlobalName -> Skipped -> String
whyNoConfusion d why = "no " ++ str (snd (noConfusionNames d)) ++ ": " ++ because
  where
    str (GlobalName x) = x
    because = case why of
      NoEquality -> "there is no Eq in scope"
      NoProducts -> "there is no And, Unit and Empty in scope"
      DependentArguments c (Ident i) ->
        str c ++ "'s argument " ++ i ++ " has a type that depends on an earlier"
          ++ " argument, so its equation cannot be stated"

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right

-- | Drain the iterator (§7.6). The REPL shows the whole match list rather than
-- a few with more on scroll, because MS1's terminal has no scroll and a list
-- silently cut short would be a worse lie than a long one. The incremental
-- reads — 'Thena.Rules.next' and 'Thena.Rules.hasNext' — are what phase 16's
-- peek and a real frontend use, and this is written in terms of the first so
-- that the display and the dispatcher walk the same iterator.
unfoldIter :: RuleIter -> [Rule]
unfoldIter it = case next it of
  Nothing        -> []
  Just (r, rest) -> r : unfoldIter rest
