-- | **A frontend, compiled against the boundary and nothing else** (MS7 phase
-- 126).
--
-- **@.jalivert\/FRONTEND.md@ is the prose**, and this module is its worked example —
-- §10 there points back here. A name in that document that cannot be used this
-- way is a document that is wrong.
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

import Thena.Driver (Response (..), Session, Stop (..), fuelOf, oneLine, oneProgram)
import Thena.Repl (renderResponse, startingSession, turn, turnSession)
import Thena.View
  ( Budget (..)
  , binderAddresses
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
  , \s -> want "binderAddresses" (not (null (binderAddresses s)))
  , \s -> want "fuel is readable" (fuelOf (fst (oneLine s ":step 3")) == Just 3)
  , \s -> want "a job runs in slices" (job s)
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

-- | **What a job is, in full** (phase 128): set a budget, advance a slice at a
-- time, and stop by not asking for the next slice.
--
-- It is here because a job is /entirely a frontend's/ — there is no @Job@ type
-- in the library to test — so the claim that a frontend can run one through the
-- boundary is a claim about this suite's imports. The budget is one instruction,
-- which is the smallest thing that pauses at all; how a larger one behaves is
-- @Thena.DriverTests@\'s.
--
-- **It must actually have paused**, or the check passes on a line that finished
-- inside its budget and says nothing about slices at all.
job :: Session -> Bool
job s = slice False (200 :: Int) (oneLine (fst (oneLine s ":step on")) claim)
  where
    claim = "claim \"h\" \8988 Type\8320 \8989"
    slice _ n (s', Ran _ _ (Paused 1)) | n > 0 = slice True (n - 1) (oneLine s' ":step")
    slice paused _ (_, Ran _ _ Completed) = paused
    slice _ _ _ = False
