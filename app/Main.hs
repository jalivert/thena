module Main (main) where

import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

import Thena.Protocol.Socket (runSocketServer)
import Thena.Repl (repl, startingSession)

-- | The terminal REPL, or the same session on a socket.
--
-- **Both are clients of the same server** (MS7 phase 113): the REPL speaks
-- messages in process and this speaks them over a WebSocket, and nothing below
-- the transport can tell which. @--socket@ is what a browser connects to, and
-- what the editor will be built against.
main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> repl
    ["--socket"] -> socket 9000
    ["--socket", p] | [(n, "")] <- reads p -> socket n
    _ -> do
      hPutStrLn stderr "usage: thena [--socket [PORT]]"
      exitFailure
  where
    socket port = do
      -- The same starting session the REPL gets: the standard base, then the
      -- prelude, in that order (@Thena.Repl.startingSession@).
      (sess, problems) <- startingSession
      mapM_ (hPutStrLn stderr) problems
      hPutStrLn stderr ("thena listening on 127.0.0.1:" <> show port)
      runSocketServer port sess
