-- | **Reading a file, and handing what it says to the driver.**
--
-- @PLAN.md@ §12 invariant 4: "Thena.Driver" does no IO at all, so something
-- above it must read the files a command names. This module is that something,
-- and it is the whole of it — every function here reads a file and passes the
-- contents to a pure driver entry point.
--
-- **It was "Thena.Repl" until MS7 phase 130**, which is why the editor track
-- could not start a session without importing the terminal REPL's own module
-- (@..\/editor\/REPORT.md@, 2026-09-28). HIS ruling on that report: the old REPL
-- is deprecated and /will be deleted/, so nothing load-bearing may live in its
-- namespace.
--
-- **Nothing here renders.** What went wrong comes back as 'Trouble', which
-- carries the driver's own 'Response' (§12: errors carry structured data, never
-- strings) — a frontend that wants a pane reads the constructors, and one that
-- wants lines calls @Thena.Render.renderTrouble@.
module Thena.Files
  ( Trouble (..)
  , preludePath
  , loadPrelude
  , rulesPath
  , loadStandardRules
  , startingSession
  , loadRuleFiles
  , consultRuleFiles
  , loadFile
  , loadProofFile
  , importModule
  , following
  ) where

import Control.Exception (IOException, try)
import qualified Paths_thena

import Thena.Driver
  ( LoadError (..)
  , Item
  , Digest
  , digestOf
  , noteRead
  , interfaceOf
  , ModuleName
  , ReadModule (..)
  , Response (..)
  , Session
  , loadProofSource
  , loadProofModules
  , readModulePath
  , ruleBaseImports
  , ruleBaseConsults
  , rolledBack
  , consultedPool
  , scopedConsults
  , moduleImports
  , moduleFile
  , moduleLoaded
  , moduleOfFile
  , moduleDeclared
  , interfaceOf
  , preludeModule
  , LoadKind (..)
  , parseSurfaceModule
  , loadRuleBases
  , consultRuleBases
  , loadFinished
  , stopped
  , pendingQuestion
  , oneLine
  , newSession
  )

-- | What went wrong to a file, with nothing rendered.
--
-- **Three ways, and the third is not a failure of the file** — a script can run
-- part-way and stop, and the line that stopped it has already had its say.
--
-- No 'Eq': 'IOException' has none, and there is nothing to compare — the tests
-- that used to assert on these compared the rendered lines and still do.
data Trouble
  = Unreadable FilePath IOException
    -- ^ the file did not read at all
  | Unloadable FilePath Response
    -- ^ it read, and the driver would not have it: the response says why, and
    -- the session is unchanged
  | Stopped FilePath LoadError
    -- ^ it read and ran, and did not reach the end
  deriving (Show)

-- | Where the shipped prelude went.
--
-- @data-files@ and 'Paths_thena' rather than a path relative to the working
-- directory, so an installed @thena@ finds it too. This is the only place the
-- project asks cabal anything at runtime.
preludePath :: IO FilePath
preludePath = Paths_thena.getDataFileName "prelude/prelude.thena"

-- | Load the shipped prelude into a session, keeping only what went wrong.
--
-- **Silent on success**, which is what @:load@ on the same file is not: there
-- the user asked, so the declarations are printed. A module gives one response
-- rather than a line each, so this reads that response instead of discarding
-- output (MS4 phase 54).
loadPrelude :: Session -> IO (Session, [Trouble])
loadPrelude s = do
  path <- preludePath
  contents <- try (readFile path)
  pure $ case contents of
    Left e  -> (s, [Unreadable path e])
    Right c -> case loadProofSource s c of
      -- **Silent on success, and the response says which it was.** A module
      -- gives one response, so unlike 'loadFile' there is no output to discard
      -- — there is a name for the thing that happened.
      --
      -- **And the prelude's declarations are marked as the prelude's** (MS11
      -- phase 282, @~xdt8c@): every module may reach them without importing
      -- anything, which is his ruling of 2026-11-05, and the subtraction that
      -- carries it has to be able to tell them from a name typed at the prompt.
      -- 'Thena.Driver.preludeModule' says why the name is supplied here.
      -- **No interface of any kind**: the prelude states no export list, marks
      -- nothing private and passes nothing on, so everything it declares is
      -- reachable from every module (MS11 phases 285 to 287).
      -- **And the read is noted** (MS11 phase 295): the prelude comes from the
      -- installed data directory, so an engine upgrade shows up as a changed
      -- hash with nothing extra built. It is the one read where the driver
      -- cannot do it, 'loadProofSource' taking contents and no path.
      (s', ProofLoaded {}) ->
        ( noteRead path (digestOf c)
            (moduleDeclared preludeModule (interfaceOf []) s s')
        , [] )
      (s', resp)           -> (noteRead path (digestOf c) s', [Unloadable path resp])

-- | A session with everything shipped loaded: **the rule base first, then the
-- prelude**.
--
-- **The order is load-bearing, and more so since MS4 phase 54.** It was
-- already: the prelude proved @fst@, @snd@, @andLeft@ and @andRight@ with @try@
-- and @solve@, which stopped being driver commands at phase 23b. Now the
-- prelude is a **surface module**, so every line of it goes through
-- @elaborate@ — and elaboration is entirely rules (phase 49f). A prelude loaded
-- before the base does not get part-way; it declares nothing at all.
-- Everything that starts a session goes through here rather than calling the
-- two loaders in whichever order it happened to write them.
startingSession :: IO (Session, [Trouble])
startingSession = do
  (s0, ruleTrouble)   <- loadStandardRules newSession
  (s, preludeTrouble) <- loadPrelude s0
  pure (s, ruleTrouble ++ preludeTrouble)

-- | Where the shipped rule base went. 'preludePath'\'s reason, verbatim.
rulesPath :: IO FilePath
rulesPath = Paths_thena.getDataFileName "rules/standard.thena.rules"

-- | Load the shipped rule base at startup, keeping only what went wrong.
--
-- 'loadPrelude'\'s bargain, in the same words: a broken or missing rule base is
-- reported and the session starts anyway, with an empty base. @prove@ then
-- matches nothing, which says more than refusing to start would.
loadStandardRules :: Session -> IO (Session, [Trouble])
loadStandardRules s = do
  path <- rulesPath
  -- **A consult, not a load** (MS11 phase 271): the pool is empty here so the
  -- two do the same thing, and saying /consult/ is what puts the shipped base at
  -- the bottom of the stack once a user consults anything of their own.
  (s', _, trouble) <- consultRuleFiles s [path]
  pure (s', trouble)

-- | Read every named rule base and install the whole ordered list, or none.
--
-- **All the files are read before any of them is installed**, which is what
-- makes 'Thena.Driver.loadRuleBases'\' all-or-nothing promise reach as far as
-- the disk: a second path that does not exist leaves the first uninstalled too.
loadRuleFiles :: Session -> [FilePath] -> IO (Session, [Response], [Trouble])
loadRuleFiles = ruleFilesWith loadRuleBases

-- | The same read and the same all-or-nothing, pushing instead of replacing
-- (MS11 phase 271). The files named in one @:consult@ are one push, in the
-- order written.
consultRuleFiles :: Session -> [FilePath] -> IO (Session, [Response], [Trouble])
consultRuleFiles = ruleFilesWith consultRuleBases

-- | What the two share: read every path, or install nothing.
--
-- **A base's own @import@ lines are loaded first** (MS11 phase 276). A base is
-- resolved against the session's grammars as it is read, so the surface modules
-- it names have to be in before reading begins — which is why they are loaded
-- here and why 'Thena.Driver.loadRuleBases' refuses a base that imports.
-- **Unlike a surface file's consults, they stay**: the base's rules run in the
-- session later and need the language there.
ruleFilesWith
  :: (Session -> [(FilePath, String)] -> (Session, Response))
  -> Session -> [FilePath] -> IO (Session, [Response], [Trouble])
ruleFilesWith install s paths = do
  reads' <- mapM (\p -> fmap ((,) p) (try (readFile p))) paths
  case [ (p, e) | (p, Left e) <- reads' ] of
    (p, e) : _ -> pure (s, [], [Unreadable p e])
    [] -> do
      -- **What each of them consults is read underneath it** (MS11 phase
      -- 289, widened at phase 298): a base consulted here brings the bases it
      -- consults, so the closure is the same whichever door a base came in by
      -- — which is 'beneath''s own rule, said for a path rather than a module
      -- name. **Flat and not grouped**, unlike 'consulted''s answer: every
      -- base named here is the session's own pool, and nothing takes one group
      -- back out again.
      spread <- beneath [] [ (p, c) | (p, Right c) <- reads' ]
      case spread of
        Left t -> pure (s, [], [t])
        Right contents -> do
          -- **Every base the group read is noted before any of it installs**
          -- (MS11 phase 295), publications included, and 'rolledBack' keeps the
          -- notes when the install refuses. **Noted here and not in
          -- 'Thena.Driver.loadRuleBases'**, which is handed the texts but whose
          -- session 'installing' throws away on a refusal.
          let sr = foldl' (\acc (p, c) -> noteRead p (digestOf c) acc) s contents
          brought <- imported sr contents
          pure $ case brought of
            Left t -> (sr, [], [t])
            Right (s1, got) -> installing sr s1 got (install s1 contents)
  where
    -- The install's own answer, read as it always was — with whatever the
    -- imported modules had to say in front of it, and with the session put back
    -- if the install refuses: **the modules a base brought in are the base's,
    -- so they do not land without it.**
    installing s0 s1 got (s', resp) =
      let about = case paths of { p : _ -> p ; [] -> "" }
          refused t = (rolledBack s0 s1, [], [t])
       in case resp of
            RuleFileRefused p _ -> refused (Unloadable p resp)
            BasesIllTyped _     -> refused (Unloadable about resp)
            _                   -> (s', got ++ [resp], [])

-- | Load every surface module these rule files import (MS11 phase 276).
--
-- **One load for all of them**, so the all-or-nothing reaches across the whole
-- group: two bases named in one @:consult@ either both get what they depend on
-- or neither does. A module already in is skipped, 'gather''s own rule.
imported
  :: Session -> [(FilePath, String)]
  -> IO (Either Trouble (Session, [Response]))
imported s contents = go [] contents
  where
    go done [] = pure $ case loadProofModules s done of
      (s', Right rs)      -> Right (s', rs)
      -- A module nobody named: the path is the only thing that says which it
      -- was (MS11 phase 275).
      (_, Left (m, bad))  -> Left (Unloadable (readModulePath m) bad)
    go done ((_, src) : rest) = case ruleBaseImports src of
      -- It did not parse. **Said by the read and not here**, so the position is
      -- in the message: this hands the file on untouched.
      Left _   -> go done rest
      Right ms -> do
        walked <- imports s [] done ms
        case walked of
          Left t      -> pure (Left t)
          Right done' -> go done' rest

-- | Read a script and run it, **one line at a time with the disc behind each
-- line**: the session after, what its lines said, and what went wrong, kept
-- apart because the two callers want different halves.
--
-- A loaded line\'s own output is real output — a file is a script of command
-- lines (§9), so @:infer@ in a file answers what @:infer@ answers.
--
-- **IT RAN THROUGH THE PURE 'loadSource' UNTIL MS11 PHASE 296** (@~qnfcp@), and
-- that is why a @.thena.script@ could not say what it stands on: an @import@
-- needs a file read, 'loadSource' is pure (§12 invariant 4), so the line was
-- refused as a 'NestedLoad' and the five scripts in @examples/@ relied on
-- whatever the session happened to hold. **The loop is here now, where the disc
-- is** — the same two-step shape phase 273 settled for a module, and the same
-- shape 'Thena.Repl.transcriptIO' has had since MS1.
--
-- **AN @import@ AND A @consult@ ARE FOLLOWED; A @:load@ IS NOT.** The acts have
-- a cycle check behind them — 'imports' refuses a loop by name and 'publishing'
-- refuses one between bases — and @:load@ has none, so a script that loaded
-- itself would not terminate. It is also the construct the acts replace, so
-- nothing is owed it. That refusal is MS1\'s and is unchanged.
--
-- **A script\'s acts run into the live session and are still there afterwards**,
-- unlike a module's, whose pool is the module's for the length of the load (his
-- ruling of 2026-11-03, 'loadProofItems'). The asymmetry is the difference
-- between a script and a module: **a script is a batch of lines you typed, so
-- its effects are yours.** @DECISIONS.md@, /A script states what it stands on/,
-- says it for a user; the reading is @~qnfcp@\'s and is his to confirm.
--
-- **Two loops and not one**, this and 'Thena.Repl.transcriptIO': they differ in
-- what they produce (responses against the text a terminal would have shown) and
-- in what they follow (the two acts against all five, a line typed at the prompt
-- being allowed to @:load@). What they share is 'following', which is the part
-- that could drift.
loadFile :: Session -> FilePath -> IO (Session, [Response], [Trouble])
loadFile s0 path = do
  contents <- try (readFile path)
  case contents of
    Left e  -> pure (s0, [], [Unreadable path e])
    Right c -> do
      -- **The script's own file is noted here** (MS11 phase 295), and the files
      -- its lines name are noted by whichever door 'following' sends them
      -- through.
      (s, out, trouble) <- go (noteRead path (digestOf c) s0) 1 [] (lines c)
      pure (loadFinished s0 s, out, trouble)
  where
    -- The file ran out while an op was still asking. The line to name is the one
    -- that asked, which is the last one that ran.
    go s _ acc [] = pure $ case pendingQuestion s of
      Just _  -> (s, reverse acc, [halted (UnansweredQuestion (length acc))])
      Nothing -> (s, reverse acc, [])
    go s n acc (l : ls) = case resp of
      -- **The three kinds of @:load@**, refused and not followed, with the
      -- line's response dropped: it asked for something that did not happen.
      LoadRequested _    -> nested
      ProofRequested _   -> nested
      RulesRequested _   -> nested
      -- **The two acts**, read where the disc is. What the act had to say comes
      -- after the line's own response, in the order it arrived.
      ConsultRequested _ _ -> follow
      ImportRequested _ _  -> follow
      Quit               -> pure (s', reverse (resp : acc), [])
      _ | stopped resp   -> pure (s', reverse (resp : acc), [halted (LoadStopped n)])
        | otherwise      -> go s' (n + 1) (resp : acc) ls
      where
        (s', resp) = oneLine s l
        nested     = pure (s, reverse acc, [halted (NestedLoad n)])
        -- **A refusal inside the act stops the script**, whether it arrived as
        -- trouble about a file the walk reached or as a response about the one
        -- the line named: either way the line did not do what it said, which is
        -- the whole of what 'stopped' means.
        follow = case following s' resp of
          Nothing  -> go s' (n + 1) (resp : acc) ls
          Just act -> do
            (s'', rs, ts) <- act
            let acc' = reverse rs ++ resp : acc
            if null ts && not (any stopped rs)
              then go s'' (n + 1) acc' ls
              else pure ( s''
                        , reverse acc'
                        , if null ts then [halted (LoadStopped n)] else ts )

    halted = Stopped path

-- | Read a proof module, **and everything it imports**, and elaborate the lot
-- (MS4 phase 43; the import graph at MS11 phase 274).
--
-- Simpler than 'loadFile' because a module is not a sequence of lines: each
-- file is one program, so there is one response per module and no line to name
-- when one stops. What went wrong is in that response, which renders like any
-- other.
--
-- **A module that names anything on disc is read in two steps** (MS11 phases
-- 273 and 274), and both steps are here because both need the disk: the module
-- is parsed, its imports are walked and its consults are read, and only then is
-- anything elaborated. **Nothing is installed if any of it will not read**, the
-- same all-or-nothing 'loadRuleFiles' promises, and 'Thena.Driver.loadProofModules'
-- carries that promise across the whole closure.
loadProofFile :: Session -> FilePath -> IO (Session, [Response], [Trouble])
loadProofFile s path = do
  contents <- try (readFile path)
  case contents of
    Left e  -> pure (s, [], [Unreadable path e])
    Right c -> case parseSurfaceModule c of
      -- **The file the user named answers with a response, as it always has.**
      -- The line they typed is what failed and the path is in front of them; an
      -- imported file is the case that needs its path said, and 'gather' says it.
      Left e -> pure (s, [Failed e], [])
      Right (nm, items) -> do
        gathered <- assemble s [] [] (moduleOfFile path) path (digestOf c) nm items
        pure $ case gathered of
          Left t   -> (s, [], [t])
          Right ms -> case loadProofModules s ms of
            (s', Right rs)       -> (s', rs, [])
            -- **The file the user named answers with a response and an imported
            -- one with trouble** (MS11 phase 275) — the same split 'gather' makes
            -- for a file that will not read, now made for one that will not
            -- elaborate. Without it a failure inside an imported module arrives
            -- as a bare refusal about a file nobody mentioned.
            (s', Left (m, bad))
              | readModulePath m == path -> (s', [bad], [])
              | otherwise -> (s', [], [Unloadable (readModulePath m) bad])

-- | Read a module an @import@ named, and everything it imports (MS11 phase
-- 274).
--
-- **Trouble and not a response**, unlike the file the user named: nobody typed
-- this path, so a refusal that did not say which file it was about would be
-- unreadable.
gather
  :: Session -> [ModuleName] -> [ReadModule] -> ModuleName
  -> IO (Either Trouble [ReadModule])
gather s stack done m = do
  contents <- try (readFile path)
  case contents of
    Left e  -> pure (Left (Unreadable path e))
    Right c -> case parseSurfaceModule c of
      Left e -> pure (Left (Unloadable path (Failed e)))
      -- **THE HEADER IS CHECKED HERE AND NOWHERE ELSE** — his ruling of
      -- 2026-11-05, @~r58qh@: the match is asked only when the file is reached
      -- by name, and this is the only place a name was resolved to a file.
      -- 'loadProofFile' is the other door and it has a path, not a name.
      Right (nm, items)
        | nm /= m   -> pure (Left (Unloadable path (ModuleMisnamed m nm)))
        | otherwise -> assemble s stack done (Just m) path (digestOf c) nm items
  where
    path = moduleFile LoadProof m

-- | **The imports first, then the consults, then the module itself** (MS11 phase
-- 274) — which is what puts the list in dependency order: a module is appended
-- after everything it imports, and the one the user asked for is last.
--
-- **And it is that order the pool depends on** (MS11 phase 288): a module is
-- searched against whatever the modules it imports published, so those modules
-- have to be gathered before 'Thena.Driver.consultedPool' is asked what this
-- one's pool is. @done'@ and not @done@ is the whole of that.
--
-- @stack@ is the modules on the path from the root, innermost first; @done@ is
-- what has been gathered so far.
assemble
  :: Session -> [ModuleName] -> [ReadModule] -> Maybe ModuleName -> FilePath
  -> Digest -> ModuleName -> [Item] -> IO (Either Trouble [ReadModule])
assemble s stack done as path d nm items = do
  walked <- imports s inner done (moduleImports items)
  case walked of
    Left t      -> pure (Left t)
    Right done' -> do
      -- **The scoped ones are read after the file's own** (MS11 phase 292), so
      -- that 'Thena.Driver.Pool' can pair them back up by position: what a
      -- @consult … where@ names is a file the disc has to answer for, and only
      -- where it is in force is the block's business.
      got <- consulted (consultedPool s done' items ++ scopedConsults items)
      case got of
        Left t     -> pure (Left t)
        -- **THE MODULES THOSE BASES IMPORT ARE DEPENDENCIES OF THIS ONE TOO**
        -- (MS11 phase 288), walked after this module's own and so loaded before
        -- it. It is 'ruleFilesWith''s rule for a base consulted at the prompt,
        -- said for a base consulted by a file: a base is resolved against the
        -- session's grammars, so the surface module declaring the language it
        -- talks about has to be in. Without this a file could consult only a
        -- base that depended on nothing — which is no base worth consulting.
        Right srcs -> do
          walked' <- imports s inner done' (concatMap stated (concat (maybe [] id srcs)))
          pure (fmap (\gs -> gs ++ [ReadModule path d as nm srcs items]) walked')
  where
    inner = maybe stack (: stack) as
    -- It did not parse. **Said by the read and not here**, so the position is
    -- in the message: 'Thena.Driver.consultRuleBases' refuses it when the pool
    -- is resolved, with the position in it.
    stated (_, src) = either (const []) id (ruleBaseImports src)

-- | One module's imports, each walked in turn (MS11 phase 274).
--
-- **A module already gathered, or already in the session, is skipped**: a
-- diamond in the graph reaches the same module twice and elaborating it twice
-- would collide with its own declarations.
imports
  :: Session -> [ModuleName] -> [ReadModule] -> [ModuleName]
  -> IO (Either Trouble [ReadModule])
imports _ _ done [] = pure (Right done)
imports s stack done (m : rest)
  -- **The cycle is named in the order the walk met it**, the module that closed
  -- the loop last, so the list reads as the path that was taken.
  | m `elem` stack =
      pure (Left (Unloadable (moduleFile LoadProof m)
                             (ImportCycle (reverse stack ++ [m]))))
  | moduleLoaded m s || any ((== Just m) . readModuleName) done =
      imports s stack done rest
  | otherwise = do
      walked <- gather s stack done m
      case walked of
        Left t      -> pure (Left t)
        Right done' -> imports s stack done' rest

-- | The text of every base a module is searched against (MS11 phase 273), or
-- 'Nothing' where there are none and it is therefore elaborated against the
-- session's own pool.
--
-- **READING ONLY, SINCE MS11 PHASE 288** — the resolution is
-- 'Thena.Driver.loadProofModules'\'s, at the module's turn in the load, and
-- 'Thena.Driver.readModulePool' says why it had to move. What stays here is the
-- disc: every base is read before any module installs, which is the
-- all-or-nothing the whole closure promises.
--
-- **In the order 'Thena.Driver.consultedPool' gave them**, which is the order
-- the pool goes in and so the order they are read in: an 'Unreadable' names the
-- first base that would have been tried.
consulted :: [ModuleName] -> IO (Either Trouble (Maybe [[(FilePath, String)]]))
consulted [] = pure (Right Nothing)
consulted ms = do
  -- **And everything each of them consults, underneath it** (MS11 phase 289,
  -- widened from @public consult@ to every @consult@ at phase 298).
  got <- mapM (fetching []) ms
  pure (fmap Just (sequence got))

-- | __A base, and the bases it consults read underneath it__ (MS11 phase 289,
-- @~jmw4k@, his ruling of 2026-10-30; every @consult@ since his ruling of
-- 2026-11-06, @~ckp39@).
--
-- **ONE GROUP AND NOT A FLAT RUN, SINCE PHASE 298.** What one line brought in
-- is what the caller has to be able to take back out again: a @consult B where
-- { … }@ reaches the block and stops ('Thena.Driver.Held'), and the group is
-- what says which bases go on for it. Before the fetch a group was almost
-- always one base, so the split was arithmetic over a flat list, and that
-- arithmetic was already wrong where a base published one.
--
-- **Underneath it, which is the group written out by hand**: a consumer that
-- wrote the lines itself would write the library it builds on last of all, so
-- the base is tried first and its dependencies sit under it —
-- @DECISIONS.md@, /Consults are a STACK/, and the same rule
-- 'Thena.Driver.consultedPool' applies to one file's own lines. **Two
-- consults of one base are a stack between themselves too**, his ruling of
-- 2026-11-05 (@~d39jx@) that the order is one stack whatever route a base took,
-- so the last line written is tried first.
--
-- **THE WORD @public@ IS NOT READ HERE ANY MORE** — his ruling of 2026-11-06:
-- a rule file's plain @consult@ fetches what it names, /"as if it were all
-- public consult all the way down"/, and what decided it was order rather than
-- convenience. Requiring the consumer to supply the base left the position of
-- the base to whoever consulted it, so an unrelated base could land between a
-- base and its helper and answer a call the author had pinned.
-- 'Thena.Driver.rawConsults' is the read, and it never read @public@ either.
--
-- **The closure is the walk and not a stored spine**, unlike a surface module's
-- ('Thena.Driver.Published'): a base consults bases and nothing else, so
-- reading them in order /is/ the order they go in.
--
-- **A loop is refused and nothing is deduplicated.** Two bases that consult
-- each other would splice for ever; a base reached down two arms is two
-- independent pushes, which is his ruling of 2026-11-03.
fetching :: [ModuleName] -> ModuleName -> IO (Either Trouble [(FilePath, String)])
fetching stack m
  | m `elem` stack =
      pure (Left (Unloadable path (ConsultCycle (reverse stack ++ [m]))))
  | otherwise = do
      contents <- try (readFile path)
      case contents of
        Left e  -> pure (Left (Unreadable path e))
        Right c -> beneath (m : stack) [(path, c)]
  where
    path = moduleFile LoadRules m

-- | The same for bases already read, each with what it consults in front of it
-- (MS11 phase 289).
--
-- **A base that does not parse states nothing here**, and
-- 'Thena.Driver.consultRuleBases' refuses it when the pool is installed, with
-- the position in it — the bargain 'assemble' already makes for a base's
-- imports.
beneath
  :: [ModuleName] -> [(FilePath, String)]
  -> IO (Either Trouble [(FilePath, String)])
beneath _ [] = pure (Right [])
beneath stack ((path, src) : rest) = do
  let names = either (const []) id (ruleBaseConsults src)
  -- **Reversed, because they are a stack**: the last @consult@ written is the
  -- newest and so is tried first.
  mine <- mapM (fetching stack) (reverse names)
  more <- beneath stack rest
  pure $ do
    under <- sequence mine
    back  <- more
    Right ((path, src) : concat under ++ back)

-- | **The four responses the driver cannot act on itself**: each named a file,
-- and reading files is this module\'s (§12 invariant 4).
--
-- Written once (2026-09-13) because there are now two callers — the interactive
-- @loop@ and @transcriptIO@ — and three near-identical cases in each would be
-- six places for a fourth kind of load to be forgotten in.
following :: Session -> Response -> Maybe (IO (Session, [Response], [Trouble]))
following s resp = case resp of
  LoadRequested path   -> Just (loadFile s path)
  -- A proof module: the driver elaborates it, this only reads the file.
  ProofRequested path  -> Just (loadProofFile s path)
  -- Several paths rather than one — a load replaces the whole ordered list.
  RulesRequested paths -> Just (loadRuleFiles s paths)
  -- The same read, a different install: a consult pushes onto the pool where a
  -- load replaces it (MS11 phase 271).
  ConsultRequested paths _ -> Just (consultRuleFiles s paths)
  -- A module named rather than a path: the name is resolved here, where the
  -- disk is (MS11 phase 284).
  ImportRequested m _  -> Just (importModule s m)
  _                    -> Nothing

-- | __@import ‹module›@ typed at the prompt__ (MS11 phase 284, his ruling of
-- 2026-11-03 that both acts are writable there).
--
-- **It is the same walk a file's @import@ line gets**, with nothing gathered
-- and an empty stack: 'imports' resolves the name to a file, checks the header
-- against it (@~r58qh@), refuses a cycle, skips what is already in and returns
-- the closure in dependency order. So a prompt @import@ and an @import@ in a
-- file cannot drift apart, and nothing about deduplication or ordering is
-- written twice.
--
-- **An empty closure means the module is already in** — the no-op a diamond in
-- the graph gets, said out loud because a line typed at the prompt that
-- answered nothing would leave the user unable to tell it took.
--
-- **A failure in the module the user named answers with a response; one inside
-- something it pulled in answers with trouble naming that file** — the same
-- split 'loadProofFile' makes, and for its reason.
importModule :: Session -> ModuleName -> IO (Session, [Response], [Trouble])
importModule s m = do
  walked <- imports s [] [] [m]
  pure $ case walked of
    Left t   -> (s, [], [t])
    Right [] -> (s, [ModuleAlreadyIn m], [])
    Right ms -> case loadProofModules s ms of
      (s', Right rs) -> (s', rs, [])
      (s', Left (bad, resp))
        | readModuleName bad == Just m -> (s', [resp], [])
        | otherwise -> (s', [], [Unloadable (readModulePath bad) resp])
