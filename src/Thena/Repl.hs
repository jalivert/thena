-- | The terminal frontend.
--
-- The only module in the project that reads a key or writes to the screen
-- (§2.1, §12 invariant 4). Everything it learns, it learns by calling
-- "Thena.Driver".
--
-- Phase 0 only; rewritten at phase 4 (§7.8).
module Thena.Repl (repl) where

import System.Console.Haskeline
  ( InputT
  , defaultSettings
  , getInputLine
  , outputStrLn
  , runInputT
  )

import Thena.Driver (Response (..), Session, command, newSession)

-- | Run the read-eval-print loop until @:quit@ or end of input.
repl :: IO ()
repl = runInputT defaultSettings (loop newSession)

loop :: Session -> InputT IO ()
loop s = do
  input <- getInputLine "thena> "
  case input of
    Nothing   -> pure ()          -- end of input: Ctrl-D
    Just line ->
      case command s line of
        (_, Quit)          -> pure ()
        (s', Echoed shown) -> outputStrLn shown >> loop s'
