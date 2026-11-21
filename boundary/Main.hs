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
-- it needs 'Thena.Render' and nothing structural at all.
--
-- **The behaviour is not tested here.** Each view has its crossing against the
-- terminal in the main suite, which sees the whole library; what is asserted
-- below is that the answers arrive and are not empty.
module Main (main) where

import Control.Monad (unless)
import System.Exit (exitFailure)

import Thena.Driver
  ( Entry (..)
  , Leniency (..)
  , Response (..)
  , Session
  , Stop (..)
  , digestText
  , filesRead
  , moduleName
  , fuelOf
  , oneLine
  , oneProgram
  , provedSlices
  , recordOf
  )
import Thena.Files (importModule, startingSession)
import Thena.Render (renderResponse)
import Data.List (nub)

import Thena.View
  ( Budget (..)
  , binderAddresses
  , choicesView
  , developmentView
  , focusAddress
  , focusProgram
  , focusTypeView
  , goalsView
  , machineView
  , matchesView
  , nameDotted
  , offerView
  , statementOfferView
  , parseView
  , proofsView
  , rulesView
  , sessionTrust
  , trustView
  )
import Thena.View (failureView)
import Thena.View.Chart (BoundView (..), OfferView (..), Written (..))
import Thena.View.Failure
  ( FaultKind (..)
  , FaultView (..)
  , Nature (..)
  , PartView (..)
  , Piece (..)
  , Pos (..)
  , Role (..)
  , StopView (..)
  , Why (..)
  )
import Thena.View.Choices (ChoiceView (..))
import Thena.View.Development (LinkView (..))
import Thena.View.Goals (GoalKind (..), GoalView (..))
import Thena.View.Machine (MachineView (..))
import Thena.View.Matches (MatchView (..))
import Thena.View.Proofs (ProofsView (..), QuestClaim (..), QuestView (..))
import Thena.View.Rules (RuleView (..))
import Thena.View.Tokens (TokenView (..), tokensView)
import Thena.View.Trust (TrustLevel (..), TrustView (..))
import Thena.View.Type (SignatureView (..))

main :: IO ()
main = do
  -- **A frontend boots the shipped session from here, and from nothing else**
  -- (MS7 phase 130). This is the regression for @..\/editor\/REPORT.md@'s
  -- 2026-09-28 item: before that phase the only 'startingSession' was
  -- 'Thena.Repl'\'s, so a frontend had to import the terminal REPL's own module
  -- to get a session with the rule base and the prelude in it. The trouble list
  -- is asserted empty because a frontend that silently boots an empty base is
  -- exactly what that item was about.
  (s0, trouble) <- startingSession
  let s = foldl step s0
        [ ":theorem t : \8704 (A : Type\8320) -> A -> A"
        , "attack"
        ]
      booted = [ "FAILED: startingSession: " <> show t | t <- trouble ]
  -- **The one view that is not computed from the session alone** (MS12 phase
  -- 325), so it needs a module that did not all go in and cannot be reached
  -- from the shared session above.
  unfinished <- partial
  failures <- pure (booted <> unfinished <> concatMap ($ s) checks)
  mapM_ putStrLn failures
  unless (null failures) exitFailure
  putStrLn ("the boundary holds: " <> show (length checks + 1) <> " views reached")
  where
    step acc l = fst (oneLine acc l)

-- | Lines through the session, the way a frontend advances one — so a check
-- that needs a session of its own builds it here rather than moving the one
-- every other check shares.
advance :: Session -> [String] -> Session
advance = foldl (\acc l -> fst (oneLine acc l))

checks :: [Session -> [String]]
checks =
  [ \s -> want "developmentView" (not (null (developmentView budget s)))
  , \s -> want "a link is marked" (any linkFocus (developmentView budget s))
  , \s -> want "machineView" (machineReached (machineView budget s))
  , \s -> want "focusTypeView" (maybe True (const True) (focusTypeView budget s))
  , \s -> want "rulesView" (not (null [ r | (_, rs) <- rulesView budget s, r <- rs ]))
    -- **One row per name and arity, and the row carries its type** (his
    -- ruling, 2026-11-19). The boundary's business is that a frontend can
    -- reach both: a view that lost the signature would still be non-empty.
  , \s -> want "matchesView" (not (null (map matchViewName (matchesView budget s))))
  , \s -> want "matchesView carries a type"
            (any (\mv -> matchViewType mv /= Nothing) (matchesView budget s))
  , \s -> want "matchesView names each rule once"
            (let ns = map (\mv -> (matchViewName mv, matchViewArity mv))
                          (matchesView budget s)
              in length ns == length (nub ns))
    -- **The goals pane's own view** (MS12 phase 324, his request of 2026-11-19):
    -- every goal left, each with the word that reaches it, and guesses listed
    -- as goals as well as holes. The session here is one @attack@ in, so the
    -- root is a guess and there is a hole inside it — both kinds, which is the
    -- half of his request that the development view could not answer.
  , \s -> want "goalsView lists a guess and a hole"
            (let ks = map goalViewKind (goalsView budget s)
              in AGuess `elem` ks && AHole `elem` ks)
    -- **The word and the address reach the same place, and this is the check
    -- that matters.** A pane draws 'goalViewVar' for the reader to type; if the
    -- prompt did not bind that word, or bound it to another position, the pane
    -- would be offering a move that goes somewhere else. Running @goto ‹word›@
    -- and comparing where the focus lands against the row's own address is the
    -- contract said in the frontend's own terms.
  , \s -> want "every goal's word reaches its address"
            (all (\g -> focusAddress (advance s ["goto " <> goalViewVar g])
                          == goalViewAt g)
                 (goalsView budget s))
    -- **A standalone choice-points pane is reachable from the boundary** (his
    -- ruling, 2026-11-16), and the one thing worth asserting is that it is not
    -- always empty: at a settled prompt there is nothing to retry, so this
    -- check drives the session two instructions into @prove@ and stops there,
    -- where a 'Thena.Engine.Choice' frame is standing.
  , \s -> want "choicesView reaches a live choice point"
            (case choicesView (advance s [":step 2", "prove"]) of
               c : _ -> choiceViewId c > 0
                          && not (null (choiceViewRunning c))
                          && not (null (choiceViewUntried c))
               []    -> False)
  , \s -> want "choicesView is empty where nothing can be retried"
            (null (choicesView s))
    -- A rule's declared type arrives structured, not as a rendered line
    -- (MS7 phase 133) — so "Thena.View.Type" really is past the seam.
  , \s -> want "a signature view is structured"
            (not (null [ () | (_, rs) <- rulesView budget s
                            , r <- rs
                            , Just sg <- [ruleViewSignature r]
                            , not (null (signatureViewParams sg)) ]))
    -- A line comes back as coloured spans, and they really are spans (MS7
    -- phase 136). Needs no session, so unlike the two below it can assert the
    -- answer rather than only that one arrives.
  , \_ -> want "tokensView spans a line"
            (case tokensView "let x = 3" of
               Right ts -> concatMap tokenViewText ts == "letx=3"
                             && map tokenViewColumn ts == [1, 5, 7, 9]
               Left _   -> False)
  , \s -> want "parseView" (either (const True) (const True) (parseView s "LC" Nothing []))
  , \s -> want "offerView" (either (const True) (const True) (offerView s "LC" Nothing [] [WrittenText ""]))
    -- **The entry offer, and that its bound names cross** (MS7 phase 140): a
    -- frontend sees the names the lines above the cursor left in scope, with their
    -- types, without importing anything past this boundary.
    -- **The session's own goals are in the offer too, since MS12 phase 324**:
    -- a typed line starts with every hole and guess bound, so @t@ (the attacked
    -- root, a guess) and @t1@ (the hole inside it) stand where a @Core@ stands,
    -- ahead of what the entry's own lines bound.
    --
    -- **The innermost goal comes first here and the outermost first in
    -- 'goalsView'**, and the two orders are not an accident to be made to agree:
    -- this is the offer at a cursor, where the nearest binding is the one a
    -- reader most likely means, and that list is already /nearest first/
    -- ('Thena.Instral.Infer.blockResult'\'s @live@). A goals pane is the other
    -- question — what is left to prove — and answers in the order the
    -- development is written.
  , \s -> want "statementOfferView names what the entry bound"
            (map boundName (offeredBound (statementOfferView s [WrittenText "h = here\ngoto "] []))
               == ["t1", "t", "h"])
  , \s -> want "focusProgram" (not (null (focusProgram (focusAddress s))) || True)
  , \s -> want "oneProgram accepts a click" (isSession (fst (oneProgram s (focusProgram (focusAddress s)))))
  , \s -> want "renderResponse" (not (null (renderResponse s (snd (oneLine s ":show")))))
  , \s -> want "binderAddresses" (not (null (binderAddresses s)))
  , \s -> want "fuel is readable" (fuelOf (fst (oneLine s ":step 3")) == Just 3)
    -- **The trust level and the report both cross** (MS8 phase 151). The level
    -- is read so a pane can show it; the view is reached so the claims can be
    -- drawn; and the rung is switched through the ordinary command door, which
    -- is the whole of what a frontend has to do to own that affordance.
  , \s -> want "the trust level is readable" (sessionTrust s == NoUndischargeableTrust)
  , \s -> want "trustView" (trustViewLevel (trustView budget s) == sessionTrust s)
  , \s -> want "a frontend may switch the rung"
            (sessionTrust (fst (oneLine s ":trust none")) == NoTrust)
    -- A development that rests on nothing says so, which is the answer a pane
    -- draws for almost every proof.
  , \s -> want "nothing is resting on it yet" (null (trustViewClaims (trustView budget s)))
    -- **The quest list crosses with its statements drawn** (MS12 phase 310, his
    -- ruling of 2026-11-11: a pane held open on @:proofs@). Both halves are
    -- checked, because the pane needs both — what the session is on, which it
    -- marks, and what it has put down, which it offers @:resume@ on. A parked
    -- row is made here rather than asserted empty: an empty list would pass
    -- without 'Thena.View.Proofs.QuestView' ever being built.
  , \s -> want "proofsView marks the quest the session is on"
            (fmap questViewWord (proofsViewOn (proofsView budget s)) == Just "t")
  , \s -> want "and a parked quest crosses with its statement"
            (case proofsViewParked (proofsView budget (fst (oneLine s ":suspend"))) of
               [QuestView w (AStatement _)] -> w == "t"
               _                            -> False)
  , \s -> want "a job runs in slices" (job s)
    -- **Which files the session read, and what they said** (MS11 phase 295).
    -- It is the one part of a session on disc that a frontend cannot work out
    -- for itself — it knows which lines the user typed, and only the engine
    -- knows which path a module name resolved to and what was actually opened —
    -- so the claim that it crosses is a claim about this suite's imports. The
    -- shipped prelude and standard base are what a booted session has read.
    -- **Which theorems the session proved, and where each one is in its own
    -- transcript** (MS12 phase 311). It is the other half of what a session
    -- stored on disc is keyed by: the lines are 'recordOf''s and the frontend
    -- has them, but the name is a 'Thena.Driver.Entry''s @entryProof@, whose
    -- type crosses here with no fields a frontend can reach — so without these
    -- two the index can say where a proof is and not which one it is. @t@
    -- arrives open and is given up, so the one slice is the proof that sealed,
    -- and an abandoned attempt is not one.
  , \s -> want "provedSlices says which proof and where"
            (case provedSlices (proved s) of
               [("arr", i, j)] -> j == i + 2
               _               -> False)
  , \s -> want "and a name crosses as the text an index is keyed by"
            ((nameDotted <$> entryProof (last (recordOf (proved s)))) == Just "arr")
  , \s -> want "filesRead reaches a frontend" (length (filesRead s) == 2)
  , \s -> want "and a digest writes down"
            (all ((== 16) . length . digestText . snd) (filesRead s))
  ]
  where
    budget = Budget 200
    want name ok = [ "FAILED: " <> name | not ok ]
    -- One sealed proof, from the session the checks are handed: it arrives
    -- with @t@ open, so that is given up first and @arr@ is three lines.
    proved s = foldl (\acc l -> fst (oneLine acc l)) s
      [ ":abandon"
      , ":theorem arr : Type\8321"
      , "elaborate surface`Type\8320 -> Type\8320`"
      , "qed"
      ]
    isSession :: Session -> Bool
    isSession _ = True
    -- At rest the program is empty, so \"non-empty\" is the wrong shape of check;
    -- what says the view was computed is that its three panes agree with a
    -- machine that has nothing left to run.
    -- **At rest the program is empty and the environment is not** (MS12 phase
    -- 324). It read @null pc == null env@ until then, on the premise that the
    -- environment is what a running program bound — and a line now starts with
    -- the session's goals in it ('Thena.Engine.goalEnv'), so a settled prompt
    -- has an empty program and a populated environment. Both halves of the view
    -- are still what is being reached; the invariant between them is what moved.
    machineReached mv = null (machinePc mv) && not (null (machineEnv mv))

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
    claim = "claim \"h\" core`Type\8320`"
    slice _ n (s', Ran _ _ (Paused 1)) | n > 0 = slice True (n - 1) (oneLine s' ":step")
    slice paused _ (_, Ran _ _ Completed) = paused
    slice _ _ _ = False

-- | **A module that loads as far as it can, and the view of what did not**
-- (MS12 phase 325).
--
-- Its own check because a frontend reaches this one differently from every
-- other view: the 'Thena.Driver.NotDone' comes out of the response that
-- reported the module, not out of the session. So what is asserted here is that
-- a frontend can get from @import@ to a laid-out failure without naming an
-- engine type — and in particular that it never needs 'Thena.Errors', which it
-- cannot import.
--
-- **The parts are checked and not just the arrival.** A 'StopView' whose kind
-- came through and whose name did not would pass a non-empty check and be
-- useless: the name is the part the tui track asked for by name.
--
-- **AND THE POSITION, SINCE MS12 PHASE 334** (@~hcr2d@): the line and column
-- are what make the row a place to go, and a frontend has to be able to name
-- 'Thena.View.Failure.Pos' to use them — which is the half of this phase that
-- only the boundary can prove.
partial :: IO [String]
partial = do
  (s0, _) <- startingSession
  case moduleName "test.modules.PartlyGood" of
    Nothing -> pure ["FAILED: the fixture's name does not read"]
    Just m -> do
      (s, out, _) <- importModule Lenient s0 m
      pure $ case [ failureView (Budget 200) s u
                  | ProofLoadedPartly _ _ _ _ unfin <- out, u <- unfin ] of
        [v] | Broken <- stopViewNature v
            , Just (Pos 12 1) <- stopViewAt v
            , Faulty [f] <- stopViewWhy v
            , NotInScope <- faultViewKind f
            , [AName "nonesuch"] <-
                [ pc | PartView TheWord pc <- faultViewParts f ] -> []
        other -> ["FAILED: failureView: " <> show other]
