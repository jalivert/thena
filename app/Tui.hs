module Main (main) where

import Tui.App (runTui)

-- | The TUI, linked against `thena:tui` and nothing else.
--
-- **This binary is the whole of the boundary claim.** `thena-tui` never
-- depends on `thena` or `thena:view` directly — only on `thena:tui`, whose
-- own library depends on `thena:view`. Nothing here can reach `Thena.Engine`
-- even by accident.
main :: IO ()
main = runTui
