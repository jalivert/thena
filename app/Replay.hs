module Main (main) where

import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

import Tui.Replay (replayFiles)

-- | Replay one or more saved scripts and print what a terminal would have
-- shown, @:load@ing each in turn against a session booted the way the
-- terminal boots one. Linked against `thena:tui` and nothing else, same as
-- `thena-tui` itself.
main :: IO ()
main = do
  paths <- getArgs
  case paths of
    [] -> do
      hPutStrLn stderr "usage: thena-replay SCRIPT..."
      exitFailure
    _ -> replayFiles paths
