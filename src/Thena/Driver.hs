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
  , command
  , answer
  , parseCore
  , parseDevelopment
  , parseDeclaration
  ) where

import Thena.Core.Context (Context)
import Thena.Core.Term (Core, GlobalName (..))
import Thena.Development.Cursor (Cursor, Part (..))
import Thena.Development.Partial (Partial (..))
import Thena.Engine
  ( Exec (..)
  , Machine (..)
  , Message
  , ProofState (..)
  , Question
  , cursor
  , isAsking
  , load
  , newProof
  , proofContext
  , resumeAt
  , setGoal
  , step
  )
import qualified Thena.Engine as Engine
import Thena.Errors (FailReason, MoveError)
import Thena.Global.Declare (DeclareError, declare)
import Thena.Global.Env
  ( Definition (..)
  , GlobalEnv
  , InductiveDefinition
  , emptyGlobals
  , inductiveName
  , lookupConstant
  , lookupDefinition
  , lookupInductive
  )
import Thena.Ops
  ( AnswerKind (..)
  , Instr (..)
  , Op (..)
  , Operand (..)
  , Value (..)
  )
import Thena.Syntax.Concrete (Raw)
import Thena.Syntax.Lexer (LexError, Located, Token, lexTokens)
import Thena.Syntax.Parser (ParseError, parseData, parseNameAndType, parseTerm)
import Thena.Syntax.Resolve (ResolveError, resolve, resolveData, resolvePartial)

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
  { sessionMachine  :: Machine
  , sessionStepping :: Bool
  }
  deriving (Eq, Show)

newSession :: Session
newSession = Session
  { sessionMachine = Machine (Exec [] [] []) ps emptyGlobals n
  , sessionStepping = False
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
  | ShownGlobal GlobalName Core (Maybe Core)
    -- ^ @:show ‹name›@ on anything else: its name, its type, and its body if
    -- it has one. A former has both — the constant is the type of its
    -- saturated 'Thena.Core.Term.Canonical' and the definition is the generated
    -- wrapper (§3.3.1) — and this shows the wrapper, which is what the name
    -- means when it is written.
  | Where Cursor              -- ^ @:where@ — the focus, the path, Γ, the type
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
  | NotThere MoveError
    -- ^ a driver command that needs a particular focus, run at another. Only
    -- @:goal@ can produce it; the moves are ops and fail through 'Halted'.
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
  ":where" -> noArgument (s, Where (cursor (proof machine)))
  ":goal"  -> goal
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
    Right (g, n1)
      | oneStep   -> stop installed msgs Paused
      | otherwise -> progress oneStep s { sessionMachine = installed } msgs
      where installed = m { globals = g, names = n1 }
  Engine.Asking q m   -> stop m msgs (Waiting q)
  Engine.Finished m   -> stop m msgs Completed
  Engine.Stuck r m    -> stop m msgs (Halted r)
  where
    stop m out what = (s { sessionMachine = m }, Ran (reverse out) what)

nameOf :: InductiveDefinition -> String
nameOf d = case inductiveName d of GlobalName x -> x

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
