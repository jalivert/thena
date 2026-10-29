-- | **A batch type-checker: the files named, loaded in order, nothing
-- interactive.**
--
-- His instruction, 2026-10-29: /"a simple binary that acts like a
-- type-checker\/compiler. I just point it at a sequence of surface modules, it
-- loads the instral prelude by default, and it type checks as if that's the
-- sequence in TUI for @:load@."/ The sequence may mix kinds —
-- @surface-1 rules-1 surface-2 rules-2@ — and the order is the order written.
--
-- **It is the library's loaders and nothing else.** 'Thena.Files' does the
-- reading, "Thena.Render" does the printing, and the kind of each file is
-- 'Thena.Driver.kindOf' — the same function @:load@ asks, so a file cannot be
-- taken one way here and another way in the REPL. **Deliberately not
-- "Thena.Repl"**: that module is deprecated and will be deleted, and it may not
-- gain a second caller that is not a test.
--
-- **Where this is NOT a sequence of @:load@ commands, and it is one place.** A
-- load of rule bases /replaces/ the ordered list — his ruling of 2026-08-25,
-- /"if I want to shuffle them, I just run load again and that replaces the
-- entire thing"/ — so a second rule file typed at the REPL drops the first and
-- the shipped base with it. That would make his own interleaved sequence mean
-- something he did not ask for, so **a rule file here is appended to the list
-- and the shipped base stays at its head**, which is what the example corpus
-- does for the same reason. The written order is still the search order (§8),
-- so a base named later is searched later.
--
-- **The exit status is the answer.** Zero when every file was accepted;
-- non-zero as soon as one is not, and nothing after it is loaded — the files
-- after a failure are being checked against a session that does not have what
-- they asked for.
module Main (main) where

import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure)
import System.IO (hFlush, hPutStrLn, stderr, stdout)

import Thena.Driver (LoadKind (..), Response (..), Session, kindOf)
import Thena.Files
  ( loadFile
  , loadProofFile
  , loadRuleFiles
  , rulesPath
  , startingSession
  )
import Thena.Render (renderResponse, renderTrouble)

main :: IO ()
main = do
  args <- getArgs
  case filter (/= "--") args of
    []    -> usage >> exitFailure
    paths -> do
      -- **A broken prelude is fatal here, where the REPL starts anyway.** The
      -- REPL's bargain is that a session saying something beats one that
      -- refuses to open; a checker that answers "accepted" without the prelude
      -- is answering a different question than the one asked.
      (s, trouble) <- startingSession
      mapM_ putStrLn (concatMap (renderTrouble s) trouble)
      if not (null trouble)
        then complain "the shipped prelude or rule base did not load" >> exitFailure
        else do
          standard <- rulesPath
          ok <- walk s [standard] paths
          if ok then pure () else exitFailure

-- | Load one file, print what it said, and go on while it was accepted.
--
-- The accumulated rule-base list is carried rather than recomputed: a rule file
-- reinstalls the whole list, so the list is what has to be remembered.
walk :: Session -> [FilePath] -> [FilePath] -> IO Bool
walk _ _ [] = pure True
walk s bases (path : more) = case kindOf path of
  LoadRules -> do
    let bases' = bases ++ [path]
    (s', out, trouble) <- loadRuleFiles s bases'
    step s' bases' out trouble (any accepted out)
  LoadProof -> do
    (s', out, trouble) <- loadProofFile s path
    step s' bases out trouble (any accepted out)
  LoadScript -> do
    -- A script is a sequence of command lines and says so itself: a line that
    -- stopped it arrives as 'Thena.Files.Stopped', which is trouble.
    (s', out, trouble) <- loadFile s path
    step s' bases out trouble True
  where
    step s' bases' out trouble kept = do
      mapM_ putStrLn (concatMap (renderResponse s') out)
      mapM_ putStrLn (concatMap (renderTrouble s') trouble)
      if kept && null trouble
        then walk s' bases' more
        else complain (path ++ ": not accepted") >> pure False

    -- | The response a load gives when it took the file. A proof module's
    -- failure is in its own response rather than in trouble, which is why this
    -- is asked at all.
    accepted r = case r of
      ProofLoaded {} -> True
      BasesLoaded _  -> True
      _              -> False

-- | A word of our own, on @stderr@ and after what the load had to say.
--
-- **The flush is why this exists**: the diagnosis goes to @stdout@ and this
-- goes to @stderr@, and without it the verdict arrives above the reason it is
-- about whenever the two are read together.
complain :: String -> IO ()
complain what = hFlush stdout >> hPutStrLn stderr what

usage :: IO ()
usage = do
  me <- getProgName
  mapM_ (hPutStrLn stderr)
    [ "usage: " ++ me ++ " ‹file› …"
    , ""
    , "Type-checks the files in the order given, as :load would, after the"
    , "shipped rule base and prelude.  The extension says what a file is:"
    , ""
    , "  ‹name›.thena.rules    a rule base, appended to the search order"
    , "  ‹name›.thena.script   a script of command lines"
    , "  anything else         a surface proof module"
    , ""
    , "Exits non-zero at the first file that is not accepted."
    ]
