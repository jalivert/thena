module Main (main) where

import Thena.Repl (repl)

-- | The terminal REPL.
--
-- **One binary, and the frontend calls the library directly** (MS7 phase 122).
-- There was a @--socket@ here, serving the same session over a WebSocket to a
-- browser; his ruling of 2026-09-27 removed the wire, so a frontend is linked
-- rather than connected. See @discussion\/tight-integration.md@.
main :: IO ()
main = repl
