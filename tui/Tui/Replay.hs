-- | **A script replayed through the frontend boundary alone** (`~5w5gx`).
--
-- `Thena.Repl`'s own header already rules it deleted; `transcriptFrom` and
-- `transcriptIO` are its replay harness and neither is on `thena:view`'s
-- reexport list, so nothing outside `thena` can call them. This is their
-- successor's first cut: `turn` is `renderResponse s' resp` where
-- @(s', resp) = oneLine s line@, and both halves are already reexported, so a
-- non-interactive replay is buildable almost entirely from the boundary
-- alone.
--
-- **No prompt line.** `Thena.Repl.prompt` reads the cursor's focus straight
-- from `Thena.Engine`, which is not on the boundary, and the one thing this
-- tool checks — did the script still replay clean — needs no prompt to answer
-- it. Resurface the gap only if `Thena.Repl` is actually being retired and the
-- existing @.golden@ files need matching without regenerating them.
module Tui.Replay (replayFiles) where

import Control.Monad (foldM)

import Thena.Driver (Session, oneLine)
import Thena.Files (Trouble, following, startingSession)
import Thena.Render (renderResponse, renderTrouble)

-- | Boot a session the way the terminal does, then @:load@ each file in
-- order, printing what a terminal would have shown for it. A script named
-- after an earlier one in the list — 08 after 01, 02, 03 and 07, say — sees
-- what the earlier ones declared, same as typing @:load@ at a real prompt.
replayFiles :: [FilePath] -> IO ()
replayFiles paths = do
  (s0, startupTrouble) <- startingSession
  printTrouble s0 startupTrouble
  _ <- foldM loadOne s0 paths
  pure ()

loadOne :: Session -> FilePath -> IO Session
loadOne s path = do
  let (s1, resp) = oneLine s (":load " ++ path)
  printLines (renderResponse s1 resp)
  case following s1 resp of
    Nothing  -> pure s1
    Just act -> do
      (s2, responses, trouble) <- act
      printLines (concatMap (renderResponse s2) responses)
      printTrouble s2 trouble
      pure s2

printLines :: [String] -> IO ()
printLines = mapM_ putStrLn

printTrouble :: Session -> [Trouble] -> IO ()
printTrouble s = printLines . concatMap (renderTrouble s)
