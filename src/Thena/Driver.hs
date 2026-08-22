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
-- (@:step on@), and the ones that create or replace a proof (@:goal@, which is
-- phase 13's @:theorem@ in miniature; §7.8 puts that on the session side).
--
-- **The moves are not among them.** Moving the focus changes the cursor, and
-- the cursor is 'Thena.Engine.ProofState' — exactly what backtracks — so a
-- move is an op and is spelled as a bare word (§2.4, §4.3).
module Thena.Driver
  ( Session (..)
  , newSession
  , Response (..)
  , Stop (..)
  , SyntaxError (..)
  , CommandError (..)
  , Proof (..)
  , Snapshot
  , LoadError (..)
  , Loaded (..)
  , command
  , answer
  , oneLine
  , loadSource
  , parseCore
  , parseDevelopment
  , parseDeclaration
  ) where

import Thena.Core.Context (Context)
import Thena.Core.Reduce (whnf)
import Thena.Core.Term (Core (..), GlobalName (..), Ident (..), Level)
import Thena.Development.Cursor (Cursor, Focus (..), Part (..), focus)
import Thena.Development.Partial (Partial (..), extract)
import Thena.Engine
  ( Exec (..)
  , Machine (..)
  , Message
  , ProofState (..)
  , Question
  , cursor
  , isAsking
  , proofDevelopment
  , load
  , newProof
  , proofContext
  , resumeAt
  , setGoal
  , setGoalNamed
  , step
  )
import qualified Thena.Engine as Engine
import Thena.Engine (whereImpure)
import Thena.Errors
  ( ConversionFailure
  , FailReason (..)
  , KernelError
  , MoveError (..)
  , TypeError
  )
import Thena.Development.Validate (revalidate)
import Thena.Global.Declare (DeclareError, declare)
import Thena.Global.NoConfusion (Skipped (..), noConfusionNames)
import Thena.Kernel (certify)
import Thena.Global.Env
  ( Definition (..)
  , GlobalEnv
  , InductiveDefinition
  , addDefinition
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
import Thena.Ops
  ( AnswerKind (..)
  , Instr (..)
  , Op (..)
  , Operand (..)
  , Value (..)
  )
import Thena.Syntax.Concrete (Raw)
import Thena.Syntax.Lexer (LexError, Located, Token, lexTokens)
import Thena.Syntax.Parser
  ( ParseError
  , parseData
  , parseEquation
  , parseNameAndType
  , parseTerm
  )
import Thena.Syntax.Resolve (ResolveError (..), resolve, resolveData, resolvePartial)

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
  , sessionProof     :: Maybe Proof
    -- ^ the proof being worked on, if any. @Nothing@ is the scratch
    -- development @:goal@ and the phase 4–12 commands still use
  , sessionSuspended :: [Proof]
    -- ^ left and re-enterable, most recently suspended first (§2.4)
  , sessionStepping  :: Bool
  }
  deriving (Eq, Show)

-- | The per-proof half of the machine: @exec@ and @proof@ together (§7.7's
-- own correction to §2.4).
--
-- **Not the whole 'Machine' — an amendment to §7.7, phase 13.** That section
-- says suspending stores the machine untouched, and it cannot: @globals@ and
-- @names@ are session-global (§7.4, §2.4 \"@fresh@ stays session-global\"), so a
-- stored machine would hold a second copy of both and hand back a stale
-- environment on resume — exactly what §2.4 promises cannot happen, since
-- \"the global environment only ever grows\". Storing this pair instead is what
-- makes that promise true rather than aspirational.
--
-- It is the same pair @:undo@ snapshots, and that is not a coincidence: a
-- suspended proof /is/ an undo snapshot with a name and a statement attached.
type Snapshot = (Exec, ProofState)

-- | A proof the session holds (§2.4, §3.3.1).
data Proof = Proof
  { proofName      :: GlobalName
  , proofClaim     :: Core       -- ^ what @qed@ will certify against
  , proofSaved     :: Snapshot
    -- ^ kept in step with the machine after every line, so suspending is a
    -- move and not a copy, and 'sessionSuspended' and the current proof are
    -- the same kind of thing
  , proofUndo      :: [Snapshot]
    -- ^ born with the proof and dies with it (§2.4). Pushed only when a line
    -- actually changed the snapshot, so @:undo@ never has to step over a
    -- @:show@
  }
  deriving (Eq, Show)

newSession :: Session
newSession = Session
  { sessionMachine   = Machine (Exec [] [] []) ps emptyGlobals n
  , sessionProof     = Nothing
  , sessionSuspended = []
  , sessionStepping  = False
  }
  where
    (ps, n) = newProof 0

-- | What the driver hands back for a frontend to render. Data, never a line of
-- text: rendering is "Thena.Repl"'s (§2.5).
data Response
  = Blank                     -- ^ an empty line; nothing to do
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
  | ShownGlobal GlobalName Core (Maybe Core)
    -- ^ @:show ‹name›@ on anything else: its name, its type, and its body if
    -- it has one. A former has both — the constant is the type of its
    -- saturated 'Thena.Core.Term.Canonical' and the definition is the generated
    -- wrapper (§3.3.1) — and this shows the wrapper, which is what the name
    -- means when it is written.
  | Where Cursor              -- ^ @:where@ — the focus, the path, Γ, the type
  | Inferred Core Core        -- ^ @:infer@ — the term, and the type it has
  | IllTyped TypeError        -- ^ @:infer@ — why it has none
  | Converted Core Core (Maybe ConversionFailure)
    -- ^ @:convert@ — the two terms, and 'Nothing' if they are convertible.
    -- Both terms are kept so the answer can restate the question: with η in
    -- play a yes is printed about two terms that still look different (§5.2)
  | Revalidated (Maybe KernelError)
    -- ^ @:revalidate@ — 'Nothing' if the development is a valid state (§5.3,
    -- thesis §2.3)
  | Extracted Core
  | Proving GlobalName Core   -- ^ @:theorem@ — a proof is now current
  | Proved GlobalName Core    -- ^ @qed@ — admitted, and the proof is closed
  | Suspended GlobalName      -- ^ @:suspend@
  | Resumed GlobalName        -- ^ @:resume@
  | Abandoned GlobalName      -- ^ @:abandon@
  | Undone                    -- ^ @:undo@ — one line taken back
  | Proofs (Maybe Proof) [Proof]
    -- ^ @:proofs@ — the current one, if any, and the suspended ones
    -- ^ @:extract@ — the closed term the development stands for (§7.5). Its
    -- own look, because @certify@ is an op and an op's answer comes back as a
    -- 'Message', which the driver may not build out of a term: rendering is
    -- "Thena.Repl"'s (§2.5)
  | LoadRequested FilePath
    -- ^ @:load ‹path›@. The driver may not touch a file — §12 invariant 4 puts
    -- all IO in "Thena.Repl" — so it asks, and the caller reads the file and
    -- hands the contents back to 'loadSource'
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
  | Halted FailReason    -- ^ the machine is kept, so a later @retry@ can use it
  | Refused DeclareError -- ^ a @data@ declaration the checker would not admit
  | Uncertified KernelError
    -- ^ the kernel would not accept what the development built (§5.3). Shaped
    -- like 'Refused': the command is abandoned, and there is nothing to retry
  | Paused               -- ^ stepping mode: one instruction done
  deriving (Eq, Show)

-- | The three ways reading a term or development can fail.
data SyntaxError
  = LexFailed LexError
  | ParseFailed ParseError
  | ResolveFailed ResolveError
  deriving (Eq, Show)

-- | Everything else a command line can get wrong (§7.8's @CommandError@).
data CommandError
  = NoSuchCommand String
  | MissingArgument String
  | UnexpectedArgument String
  | NotAsking
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
  | LevelExpected String
    -- ^ @:elim Nat Nat@ — @:elim@\'s optional second argument parsed as a term
    -- but is not a @Typeₗ@ (phase 10). Not called @NotAUniverse@ because
    -- 'Thena.Syntax.Resolve.ResolveError' has one of those already, about a
    -- different mistake: a datatype /declared/ at a non-universe
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

-- --------------------------------------------------------------------------
-- Commands
-- --------------------------------------------------------------------------

-- | Bare word acts, colon looks (decided by the user 2026-08-21). @assume@ and
-- @claim@ are ops and read exactly as they will read inside a rule body;
-- everything with a colon is the driver's own.
command :: Session -> String -> (Session, Response)
command s line = case break (== ' ') (dropWhile (== ' ') line) of
  ("", _)      -> (s, Blank)
  (name, rest) -> dispatch s name (dropWhile (== ' ') rest)

dispatch :: Session -> String -> String -> (Session, Response)
dispatch s name arg = case name of
  ":quit"  -> noArgument (s, Quit)
  ":core"  -> withArgument (view s parseCore Rendered arg)
  ":dev"   -> withArgument (view s parseDevelopment RenderedDev arg)
  -- The only command that means two things, and they do not overlap: with no
  -- argument it is the development, with one it is a global (§9, phase 6).
  ":show"  -> case arg of
    "" -> (s, Shown (cursor (proof machine)))
    _  -> showGlobal arg
  -- The eliminator is not a global, so it is not reachable through @:show@
  -- (§3.7, reversed by the user 2026-08-22). Its own word, and its own second
  -- argument: the level comes from the motive at every use site, so there is
  -- no one rule to print and the command has to be told which one is wanted.
  ":elim"  -> withArgument (eliminator arg)
  ":where" -> noArgument (s, Where (cursor (proof machine)))
  ":goal"  -> goal
  -- With no argument, view-reduce the core focus (§4.7); with one, an
  -- arbitrary typed term — the same no-argument/with-argument split as
  -- @:show@, and for the same reason: two different questions share a word
  -- because neither can be mistaken for the other.
  ":whnf"  -> case arg of
    "" -> case focus (cursor (proof machine)) of
      OnTerm _ _ t -> (s, Rendered (whnf (globals machine) ctx t))
      _            -> (s, Rejected (NotThere NotInCore))
    _  -> view s parseCore (Rendered . whnf (globals machine) ctx) arg
  -- The same no-argument/with-argument split as @:whnf@ and @:show@: with no
  -- argument it is the core focus, with one it is a term the user writes.
  ":infer" -> case arg of
    "" -> case focus (cursor (proof machine)) of
      OnTerm _ _ t -> inferred t (names machine)
      _            -> (s, Rejected (NotThere NotInCore))
    _  -> case parseCore (globals machine) ctx (names machine) arg of
      Left e        -> (s, Failed e)
      Right (t, n1) -> inferred t n1
  -- Reading the file is the caller's; this only names it (§12 invariant 4).
  ":load"  -> withArgument (s, LoadRequested arg)
  -- Thesis §2.3's state-validity judgment over the whole development, at any
  -- time (§5.3). A colon: it looks and changes nothing.
  ":revalidate" -> noArgument $
    ( s
    , Revalidated . either Just (const Nothing) . fst $
        revalidate (globals machine) [] (names machine) (proofDevelopment (proof machine))
    )
  -- The term the development stands for, if it is finished. A colon: it looks.
  -- 'extract' is otherwise reachable only through the op, and the whole
  -- interest of @certify@ is /what/ it built.
  ":extract" -> noArgument $
    case extract (proofDevelopment (proof machine)) of
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
  ":proofs"  -> noArgument (s, Proofs (sessionProof s) (sessionSuspended s))
  ":undo"    -> noArgument undo
  ":convert" -> conversion
  ":step"  -> stepping
  ":run"   -> noArgument (progress False s [])
  "assume" -> tactic "assumption" "assumed" Assume
  "claim"  -> tactic "hole" "claimed" Claim
  "data"   -> declaration

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
  -- The life of a hole (thesis tables 2.7, 2.8). Bare words: they are ops, and
  -- they rewrite the development. Each acts at the focus, so only @try@ takes
  -- an argument.
  "attack" -> noArgument (run [Do Attack])
  "intro"  -> noArgument (run [Do Intro])
  "solve"  -> noArgument (run [Do Solve])
  "regret" -> noArgument (run [Do Regret])
  "abandon" -> noArgument (run [Do Abandon])
  "try"    -> withArgument $
    case parseCore (globals machine) ctx (names machine) arg of
      Left e -> (s, Failed e)
      Right (t, n1) ->
        progress
          (sessionStepping s)
          s { sessionMachine =
                load [Do (Try (Lit (VTerm (Trailing t))))] machine { names = n1 } }
          []
  "cross"  -> case arg of
    "type" -> run [Do CrossType]
    "val"  -> run [Do CrossValue]
    ""     -> (s, Rejected (MissingArgument name))
    _      -> (s, Rejected (UnexpectedArgument name))

  _ | name `elem` partWords -> case corePart name arg of
        Left e  -> (s, Rejected e)
        Right p -> run [Do (Down p)]
    | otherwise -> (s, Rejected (NoSuchCommand name))
  where
    machine = sessionMachine s
    ctx     = proofContext (proof machine)

    noArgument r
      | null arg  = r
      | otherwise = (s, Rejected (UnexpectedArgument name))

    withArgument k
      | null arg  = (s, Rejected (MissingArgument name))
      | otherwise = k

    showGlobal what = case lookupInductive g (globals machine) of
      Just d  -> (s, ShownData d)
      Nothing -> case lookupDefinition g (globals machine) of
        Just d  -> (s, ShownGlobal g (definitionType d) (Just (definitionBody d)))
        Nothing -> case lookupConstant g (globals machine) of
          Just t  -> (s, ShownGlobal g t Nothing)
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
    theorem = case sessionProof s of
      Just pr -> (s, Rejected (AlreadyProving (proofName pr)))
      Nothing -> case parseStatement (globals machine) (names machine) arg of
        Left e             -> (s, Failed e)
        Right (Nothing, _) -> (s, Rejected (MissingArgument ":theorem"))
        Right (Just x, (ty, n1))
          -- One namespace, shared with generated names (§3.6): a theorem may
          -- not take a name a datatype or a wrapper already has.
          | isDeclared g (globals machine) -> (s, Rejected (AlreadyDeclaredHere x))
          | otherwise -> case sortOf (globals machine) [] n1 ty of
              (Left e,  _)  -> (s, IllTyped e)
              (Right _, n2) -> started g ty n2
          where g = GlobalName x

    started g ty n = case setGoalNamed g ty machine { names = n } of
      Left e  -> (s, Rejected (NotThere e))
      Right m ->
        ( s { sessionMachine = m
            , sessionProof = Just (Proof g ty (snapshotOf m) [])
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
    closeProof = case sessionProof s of
      Nothing -> (s, Rejected NotProving)
      Just pr -> case progress False s { sessionMachine = ran } [] of
        (s', Ran msgs Completed) ->
          case extract (proofDevelopment (proof (sessionMachine s'))) of
            Left why -> (s', Ran msgs (Halted (NotYetPure (whereImpure why))))
            Right t  -> (admitted s' pr t, Proved (proofName pr) (proofClaim pr))
        other -> other
        where
          ran = load [Do (Certify (Lit (VTerm (Trailing (proofClaim pr)))))] machine

    -- Admitting is the only thing that writes a theorem to globals (§3.3.1):
    -- a proved theorem is a global **definition**, type and body both.
    admitted s' pr t =
      let m  = sessionMachine s'
          g  = addDefinition (proofName pr) (MkDefinition (proofClaim pr) t) (globals m)
          (ps, n) = newProof (names m)
       in s' { sessionMachine = m { globals = g, proof = ps, names = n }
             , sessionProof = Nothing
             }

    suspend = case sessionProof s of
      Nothing -> (s, Rejected NotProving)
      Just pr ->
        ( cleared { sessionSuspended = pr { proofSaved = snapshotOf machine }
                                         : sessionSuspended s }
        , Suspended (proofName pr)
        )

    -- Abandoning drops the proof; suspending keeps it. Same exit, different
    -- list — which is the whole difference between the two commands.
    abandonProof = case sessionProof s of
      Nothing -> (s, Rejected NotProving)
      Just pr -> (cleared, Abandoned (proofName pr))

    -- Leave proof mode, putting the machine back on a fresh scratch
    -- development. **The environment and the counter are not touched**, which
    -- is what makes §2.4's promise true: a proof is stored as its own half of
    -- the machine, so a datatype declared while it was away is simply there on
    -- return.
    cleared =
      let (ps, n) = newProof (names machine)
       in s { sessionMachine = machine { proof = ps, names = n, exec = Exec [] [] [] }
            , sessionProof = Nothing
            }

    resume what = case break ((== GlobalName what) . proofName) (sessionSuspended s) of
      (_, [])          -> (s, Rejected (NoSuchProof what))
      (before, pr : after)
        | Just cur <- sessionProof s ->
            (s, Rejected (AlreadyProving (proofName cur)))
        | otherwise ->
            ( s { sessionMachine = restore (proofSaved pr) machine
                , sessionProof = Just pr
                , sessionSuspended = before ++ after
                }
            , Resumed (proofName pr)
            )

    undo = case sessionProof s of
      Nothing -> (s, Rejected NotProving)
      Just pr -> case proofUndo pr of
        []       -> (s, Rejected NothingToUndo)
        (u : us) ->
          ( s { sessionMachine = restore u machine
              , sessionProof = Just pr { proofSaved = u, proofUndo = us }
              }
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
        Right m' -> (s { sessionMachine = m' }, Shown (cursor (proof m')))

    -- Both of these advance the session counter even when they fail. Conversion
    -- and inference mint variables to open binders with, and a name that has
    -- reached the user inside an error must never be handed out again (§7.4).
    bump n = s { sessionMachine = machine { names = n } }

    inferred t n = case infer (globals machine) ctx n t of
      (Left e,   n1) -> (bump n1, IllTyped e)
      (Right ty, n1) -> (bump n1, Inferred t ty)

    conversion = withArgument $
      case parseEquated (globals machine) ctx (names machine) arg of
        Left e -> (s, Failed e)
        Right ((a, b), n1) -> case convert (globals machine) ctx n1 a b of
          (why, n2) -> (bump n2, Converted a b why)

    stepping = case arg of
      ""    -> progress True s []
      "on"  -> (s { sessionStepping = True }, Ran [] Completed)
      "off" -> (s { sessionStepping = False }, Ran [] Completed)
      _     -> (s, Rejected (UnexpectedArgument name))

    run is = progress (sessionStepping s) s { sessionMachine = load is machine } []

    tactic what verb op = withArgument $
      case compile what verb op (globals machine) ctx (names machine) arg of
      Left e -> (s, Failed e)
      Right (is, n1) ->
        progress (sessionStepping s) s { sessionMachine = load is machine { names = n1 } } []

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
partWords :: [String]
partWords =
  [ "fun", "arg", "dom", "cod", "val", "type", "body"
  , "motive", "target", "param", "method", "index"
  ]

corePart :: String -> String -> Either CommandError Part
corePart w a = case (w, a) of
  ("fun",    "") -> Right Fun
  ("arg",    "") -> Right Arg
  ("dom",    "") -> Right Dom
  ("cod",    "") -> Right Cod
  ("val",    "") -> Right Val
  ("type",   "") -> Right Type
  ("body",   "") -> Right Body
  ("motive", "") -> Right Motive
  ("target", "") -> Right Target
  -- Before the positional cases: without it @param@ with no number reaches
  -- 'position', which reports the wrong mistake.
  (_,        "") -> Left (MissingArgument w)
  ("arg",    k)  -> CanonArg <$> position w k
  ("param",  k)  -> Param    <$> position w k
  ("method", k)  -> Method   <$> position w k
  ("index",  k)  -> Index    <$> position w k
  _              -> Left (UnexpectedArgument w)

position :: String -> String -> Either CommandError Int
position w k = case reads k of
  [(i, "")] -> Right i
  _         -> Left (UnexpectedArgument w)

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
  case rd (globals machine) (proofContext (proof machine)) (names machine) arg of
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
    record sess = case sessionProof sess of
      Nothing -> sess
      Just pr
        | resp == Undone || now == proofSaved pr -> sess { sessionProof = Just pr { proofSaved = now } }
        | otherwise ->
            sess { sessionProof = Just pr
                     { proofSaved = now
                     , proofUndo  = proofSaved pr : proofUndo pr
                     } }
        where now = snapshotOf (sessionMachine sess)

-- | The per-proof half of a machine.
snapshotOf :: Machine -> Snapshot
snapshotOf m = (exec m, proof m)

-- | Put one back.
restore :: Snapshot -> Machine -> Machine
restore (e, p) m = m { exec = e, proof = p }

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
loadSource :: Session -> String -> Loaded
loadSource s0 = go s0 Nothing 1 [] . lines
  where
    go s pending _ acc [] = case pending of
      -- The file ran out while an op was still asking. The line to name is the
      -- one that asked, which is the last one that ran.
      Just _  -> Loaded s (reverse acc) (Just (UnansweredQuestion (length acc)))
      Nothing -> Loaded s (reverse acc) Nothing
    go s pending n acc (l : ls) =
      let (s', resp, asking) = oneLine s pending l
          acc'               = resp : acc
       in case resp of
            LoadRequested _ -> Loaded s (reverse acc) (Just (NestedLoad n))
            Quit            -> Loaded s' (reverse acc') Nothing
            _ | stopped resp -> Loaded s' (reverse acc') (Just (LoadStopped n))
              | otherwise    -> go s' asking (n + 1) acc' ls

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
-- Phase 13 snapshots for @:undo@ at 'Completed'; phase 16 keeps the machine at
-- 'Halted' so @retry@ can use it, which this already does.
progress :: Bool -> Session -> [Message] -> (Session, Response)
progress oneStep s msgs = case step (sessionMachine s) of
  Engine.Continue m
    | oneStep   -> stop m msgs Paused
    | otherwise -> progress oneStep s { sessionMachine = m } msgs
  Engine.Saying msg m
    | oneStep   -> stop m (msg : msgs) Paused
    | otherwise -> progress oneStep s { sessionMachine = m } (msg : msgs)
  -- The declaration is checked and installed here, outside the machine: the
  -- global environment is not part of 'ProofState' and no instruction writes it
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
  Engine.Certifying t ty m -> case certify (globals m) t ty of
    Left e -> stop (load [] m) msgs (Uncertified e)
    Right ()
      | oneStep   -> stop m (say : msgs) Paused
      | otherwise -> progress oneStep s { sessionMachine = m } (say : msgs)
      where say = "certified"
  Engine.Asking q m   -> stop m msgs (Waiting q)
  Engine.Finished m   -> stop m msgs Completed
  Engine.Stuck r m    -> stop m msgs (Halted r)
  where
    stop m out what = (s { sessionMachine = m }, Ran (reverse out) what)

nameOf :: InductiveDefinition -> String
nameOf d = case inductiveName d of GlobalName x -> x

-- | Why a datatype got no no-confusion (phase 14).
--
-- A message, not an error, so it is a 'String' here beside @"declared X"@ and
-- @"certified"@ rather than structured data rendered in "Thena.Repl". The
-- declaration succeeded; this says what it does not come with.
--
-- 'NoEquality' never reaches here — "Thena.Global.Declare" keeps it quiet,
-- because it is a fact about the environment rather than about the declaration
-- and would fire on every @data@ line of a prelude-free script.
whyNoConfusion :: GlobalName -> Skipped -> String
whyNoConfusion d why = "no " ++ str (snd (noConfusionNames d)) ++ ": " ++ because
  where
    str (GlobalName x) = x
    because = case why of
      NoEquality -> "there is no Eq in scope"
      NotAtTypeZero _ ->
        str d ++ " is not declared at Type\8320, and Eq relates only Type\8320 types"
      DependentArguments c (Ident i) ->
        str c ++ "'s argument " ++ i ++ " has a type that depends on an earlier"
          ++ " argument, so its equation cannot be stated"

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
