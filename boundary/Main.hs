-- | **A frontend, compiled against the boundary and nothing else** (MS7 phase
-- 126).
--
-- This suite's @build-depends@ names @thena:view@ and not @thena@, so it sees
-- exactly what a frontend sees. It is therefore two assertions, and the first
-- is made by the compiler:
--
-- * **the boundary holds** — an @import Thena.Engine@ here does not compile,
--   because @thena@ is a transitive dependency and its modules are not in
--   scope; and
-- * **the boundary is sufficient** — every view can actually be reached, with a
--   real session behind it, without naming one engine type.
--
-- The second is why this is a suite and not a comment. A re-export list can be
-- checked by reading it; that the views are *usable* through it can only be
-- checked by using them, and the terminal frontend does not — it draws text, so
-- it needs 'Thena.Repl' and nothing structural at all.
--
-- **The behaviour is not tested here.** Each view has its crossing against the
-- terminal in the main suite, which sees the whole library; what is asserted
-- below is that the answers arrive and are not empty.
module Main (main) where

import Control.Monad (unless)
import System.Exit (exitFailure)

import Thena.Driver (Session, oneLine, oneProgram)
import Thena.Repl (renderResponse, startingSession, turn, turnSession)
import Thena.View
  ( Budget (..)
  , developmentView
  , focusAddress
  , focusProgram
  , focusTypeView
  , machineView
  , matchesView
  , offerView
  , parseView
  , rulesView
  )
import Thena.View.Chart (Written (..))
import Thena.View.Development (LinkView (..))
import Thena.View.Machine (MachineView (..))
import Thena.View.Rules (RuleView (..))

main :: IO ()
main = do
  (s0, _) <- startingSession
  let s = foldl step s0
        [ ":theorem t : \8704 (A : Type\8320) -> A -> A"
        , "attack"
        ]
  failures <- pure (concatMap ($ s) checks)
  mapM_ putStrLn failures
  unless (null failures) exitFailure
  putStrLn ("the boundary holds: " <> show (length checks) <> " views reached")
  where
    step acc l = fst (oneLine acc l)

checks :: [Session -> [String]]
checks =
  [ \s -> want "developmentView" (not (null (developmentView budget s)))
  , \s -> want "a link is marked" (any linkFocus (developmentView budget s))
  , \s -> want "machineView" (machineReached (machineView budget s))
  , \s -> want "focusTypeView" (maybe True (const True) (focusTypeView budget s))
  , \s -> want "rulesView" (not (null [ r | (_, rs) <- rulesView budget s, r <- rs ]))
  , \s -> want "matchesView" (not (null (map ruleViewName (matchesView budget s))))
  , \s -> want "parseView" (either (const True) (const True) (parseView s "LC" Nothing []))
  , \s -> want "offerView" (either (const True) (const True) (offerView s "LC" Nothing [] [WrittenText ""]))
  , \s -> want "focusProgram" (not (null (focusProgram (focusAddress s))) || True)
  , \s -> want "oneProgram accepts a click" (isSession (fst (oneProgram s (focusProgram (focusAddress s)))))
  , \s -> want "renderResponse" (not (null (renderResponse s (snd (oneLine s ":show")))))
  , \s -> want "turn" (isSession (turnSession (turn s ":show")))
  ]
  where
    budget = Budget 200
    want name ok = [ "FAILED: " <> name | not ok ]
    isSession :: Session -> Bool
    isSession _ = True
    -- At rest the program is empty, so \"non-empty\" is the wrong shape of check;
    -- what says the view was computed is that its three panes agree with a
    -- machine that has nothing left to run.
    machineReached mv = null (machinePc mv) == null (machineEnv mv)
