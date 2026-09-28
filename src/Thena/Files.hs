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
  , loadFile
  , loadProofFile
  , following
  ) where

import Control.Exception (IOException, try)
import qualified Paths_thena

import Thena.Driver
  ( LoadError
  , Loaded (..)
  , Response (..)
  , Session
  , loadProofSource
  , loadRuleBases
  , loadSource
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
      (s', ProofLoaded {}) -> (s', [])
      (s', resp)           -> (s', [Unloadable path resp])

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
  (s', _, trouble) <- loadRuleFiles s [path]
  pure (s', trouble)

-- | Read every named rule base and install the whole ordered list, or none.
--
-- **All the files are read before any of them is installed**, which is what
-- makes 'Thena.Driver.loadRuleBases'\' all-or-nothing promise reach as far as
-- the disk: a second path that does not exist leaves the first uninstalled too.
loadRuleFiles :: Session -> [FilePath] -> IO (Session, [Response], [Trouble])
loadRuleFiles s paths = do
  reads' <- mapM (\p -> fmap ((,) p) (try (readFile p))) paths
  pure $ case [ (p, e) | (p, Left e) <- reads' ] of
    (p, e) : _ -> (s, [], [Unreadable p e])
    [] ->
      let contents = [ (p, c) | (p, Right c) <- reads' ]
          (s', resp) = loadRuleBases s contents
          -- The path a refusal is about. 'RuleFileRefused' names its own;
          -- 'BasesIllTyped' is about the whole ordered list at once (MS5 phase
          -- 66c), so it is filed under the first file read.
          about = case paths of { p : _ -> p ; [] -> "" }
       in case resp of
            -- A refusal is trouble and not output: the whole load was
            -- abandoned, so there is nothing to report as having happened.
            RuleFileRefused p _ -> (s, [], [Unloadable p resp])
            -- **The same bargain one step later** (MS5 phase 66c): the files
            -- all read and parsed, and the program they make does not type
            -- check, so nothing was installed and nothing happened to report.
            BasesIllTyped _     -> (s, [], [Unloadable about resp])
            _                   -> (s', [resp], [])

-- | Read a file and run it: the session after, **what its lines said**, and
-- **what went wrong**, kept apart because the two callers want different halves.
--
-- A loaded line\'s own output is real output — a file is a script of command
-- lines (§9), so @:infer@ in a file answers what @:infer@ answers.
loadFile :: Session -> FilePath -> IO (Session, [Response], [Trouble])
loadFile s path = do
  contents <- try (readFile path)
  pure $ case contents of
    Left e  -> (s, [], [Unreadable path e])
    Right c ->
      let l  = loadSource s c
          s' = loadedSession l
       in (s', loadedResponses l, map (Stopped path) (maybe [] pure (loadedError l)))

-- | Read a proof module and elaborate it (MS4 phase 43).
--
-- Simpler than 'loadFile' because a module is not a sequence of lines: the
-- whole file is one program, so there is one response and no line to name when
-- it stops. What went wrong is in that response, which renders like any other.
loadProofFile :: Session -> FilePath -> IO (Session, [Response], [Trouble])
loadProofFile s path = do
  contents <- try (readFile path)
  pure $ case contents of
    Left e  -> (s, [], [Unreadable path e])
    Right c -> let (s', resp) = loadProofSource s c in (s', [resp], [])

-- | **The three responses the driver cannot act on itself**: each named a file,
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
  _                    -> Nothing
