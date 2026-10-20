-- | The TUI's own test suite — his ruling, 2026-10-20: /"Yes, tui gets a test
-- suite. That won't hurt anything."/
--
-- **Narrowed to the pure drawing, and that narrowing is deliberate.** This
-- track verifies the TUI under a real pty, because a screenshot of a wrong
-- frame is worth more than a paragraph about what should render — and that
-- stays the authority on layout, keymaps, panes and themes. But
-- 'Tui.Render.renderDisplay' is a function from a 'Shape' to a widget, and
-- whether it puts a bracket in the right place is decidable with no terminal
-- at all. `~6crg8` is the item; `~r3fp9` is what it costs not to have had
-- this, a wrong function position that stood from the day the case was
-- written and that only the engine track's own corpus found.
--
-- **The reference is 'Thena.Render', not our judgement** — `~kq45n` and
-- `.jalivert/DESIGN-PRINCIPLES.md`, /"A pane draws a term the way the engine
-- prints it"/. 'Thena.View.Core.Shape' carries no parentheses, so every
-- drawer supplies its own; two drawers that disagree about where mean one
-- term reads as two different terms depending on the pane it is in.
module Main (main) where

import Test.Tasty (TestTree, defaultMain, testGroup)

import DrawingTests (drawingTests)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "tui" [drawingTests]
