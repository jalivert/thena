-- | **Which panes are on screen and where** — `~fxc89`'s two operations, held
-- to their results.
--
-- **This is not what `~6crg8` excluded.** His ruling of 2026-10-20 narrowed
-- this suite to the pure drawing and said the pty stays the authority on
-- /layout/ — by which it meant what a terminal decides: how wide a pane is,
-- where its bar falls, whether a column is flush. None of that is here.
-- 'Tui.Layout' is a map from six numbers to panes and two functions over it;
-- whether @:pane goals open 1@ swaps goals with globals or closes one of them
-- is decidable with no terminal at all, and it is the half of `~fxc89` that
-- will rot silently if nothing holds it. **The screen it produces is still
-- measured under a pty**, which is what that ruling protects.
module LayoutTests (layoutTests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))

import Tui.Layout
  ( Pane (..)
  , Strip (..)
  , allPanes
  , closePane
  , closeStrip
  , columnsOf
  , defaultLayout
  , defaultStrip
  , layoutFrom
  , layoutPairs
  , paneBarEntries
  , openPane
  , openStrip
  , paneAt
  , paneByName
  , paneName
  , placedPanes
  , positionOf
  , positions
  , stripDefaultRows
  , stripMinRows
  , stripName
  , stripSized
  )

layoutTests :: TestTree
layoutTests =
  testGroup
    "layout"
    [ testCase "the default is the screen as it was before :pane existed" $
        columnsOf defaultLayout
          @?= ([Globals, Modules, Output], [ProofTerm, Goals, Machine])
    , testCase "the seventh pane starts closed" $
        positionOf Quests defaultLayout @?= Nothing
    , -- | **A position is an address, and closing does not renumber.** The
      -- panes below move up a row on screen because the column lists one
      -- fewer, but @output@ is still at 5 — so @:pane proofs open 3@ puts the
      -- new pane back between globals and output rather than under them.
      testCase "closing packs the column and leaves the addresses alone" $ do
        let after = closePane Modules defaultLayout
        fst (columnsOf after) @?= [Globals, Output]
        positionOf Output after @?= Just 5
        positionOf Modules after @?= Nothing
    , testCase "a closed pane opens back where it is sent" $ do
        let after = fst (openPane Quests 6 (closePane Machine defaultLayout))
        snd (columnsOf after) @?= [ProofTerm, Goals, Quests]
        positionOf Quests after @?= Just 6
    , -- | **The swap**: goals is on screen at 4, globals holds 1, so they
      -- trade. Refusing instead would mean no two panes could ever change
      -- places without a free position to stage through.
      testCase "opening a placed pane onto a taken position swaps the two" $ do
        let (after, shut) = openPane Goals 1 defaultLayout
        shut @?= Nothing
        positionOf Goals after @?= Just 1
        positionOf Globals after @?= Just 4
        length (placedPanes after) @?= 6
    , -- | **The one case that closes something.** The pane being opened is
      -- not on screen, so the occupant has nowhere to be moved to — and the
      -- caller says so rather than leaving him to notice.
      testCase "opening a closed pane onto a taken position closes the occupant" $ do
        let (after, shut) = openPane Quests 5 defaultLayout
        shut @?= Just Output
        positionOf Quests after @?= Just 5
        positionOf Output after @?= Nothing
        length (placedPanes after) @?= 6
    , testCase "a pane sent where it already is stays put" $ do
        let (after, shut) = openPane Globals 1 defaultLayout
        after @?= defaultLayout
        shut @?= Nothing
    , -- | A move across columns, which is the case the width clamp reads the
      -- layout for: machine is clamped against the column it is in now.
      testCase "a pane moved to the other column leaves the one it was in" $ do
        let after = fst (openPane Machine 5 (closePane Output defaultLayout))
        columnsOf after @?= ([Globals, Modules, Machine], [ProofTerm, Goals])
    , -- | A swap across the columns: modules leaves 3 for 2, and the pane that
      -- held 2 takes 3 — so neither position is vacated and no pane is placed
      -- twice.
      testCase "no pane is ever placed twice" $ do
        let after = fst (openPane Modules 2 defaultLayout)
            placed = placedPanes after
        assertBool "one position each" (length placed == 6)
        assertBool "modules once" (length (filter (== Modules) placed) == 1)
        positionOf Modules after @?= Just 2
        paneAt 3 after @?= Just ProofTerm
    , testCase "a position outside one to six changes nothing" $
        fst (openPane Quests 7 defaultLayout) @?= defaultLayout
    , testCase "every pane has a name and every name a pane" $ do
        positions @?= [1 .. 6]
        map (paneByName . paneName) allPanes @?= map Just allPanes
    , -- | **`~vqsd8`, his ruling of 2026-11-13** — the layout goes in the
      -- dotfile, so it has to survive being written down and read back.
      -- 'Tui.Config' writes 'layoutPairs' and parses into 'layoutFrom'; if
      -- these two stop being inverse, his screen comes back wrong after a
      -- restart and nothing else would say so.
      testCase "a layout survives the round trip the dotfile puts it through" $ do
        layoutFrom (layoutPairs defaultLayout) @?= defaultLayout
        let moved = fst (openPane Quests 5 (closePane Globals defaultLayout))
        layoutFrom (layoutPairs moved) @?= moved
        layoutFrom (layoutPairs (closePane Output moved)) @?= closePane Output moved
    , -- | **An empty screen round-trips too**, which the @panes=@ line writes
      -- as nothing at all — close all six and the document has the window, so
      -- this is a layout he can really be in when he quits.
      testCase "every pane closed is a layout and not a missing one" $ do
        let shut = foldr closePane defaultLayout allPanes
        placedPanes shut @?= []
        layoutFrom (layoutPairs shut) @?= shut
    , -- | **A hand-edited dotfile cannot make a layout the commands could
      -- not** — which is why 'layoutFrom' replays 'openPane' instead of
      -- wrapping the map. Out-of-range positions are dropped and a pane named
      -- twice lands once.
      testCase "a nonsense pane list is read as far as it makes sense" $ do
        layoutFrom [(7, Globals), (0, Modules), (-1, Output)] @?= layoutFrom []
        let twice = layoutFrom [(1, Globals), (4, Globals)]
        placedPanes twice @?= [Globals]
        positionOf Globals twice @?= Just 4
    , -- | **`~7tfhd`, his instruction of 2026-11-13** — the bar lists every
      -- pane the TUI has. **Placed ones in position order, then the closed
      -- ones**, which is the sketch he picked: ascending numbers read as a
      -- sequence where 'allPanes' order would scatter them.
      testCase "the bar lists the placed panes in position order, then the closed" $
        paneBarEntries defaultLayout @?=
          [ (Globals, Just 1)
          , (ProofTerm, Just 2)
          , (Modules, Just 3)
          , (Goals, Just 4)
          , (Output, Just 5)
          , (Machine, Just 6)
          , (Quests, Nothing)
          , (ChoicePoints, Nothing)
          , (Matches, Nothing)
          ]
    , -- | **A closed pane has no position and none is remembered** — unlike a
      -- width (`~vqsd8`), because a position is what @:pane@ states every time.
      testCase "closing a pane takes its number away and leaves it in the list" $ do
        let after = closePane Modules defaultLayout
        paneBarEntries after @?=
          [ (Globals, Just 1)
          , (ProofTerm, Just 2)
          , (Goals, Just 4)
          , (Output, Just 5)
          , (Machine, Just 6)
          , (Modules, Nothing)
          , (Quests, Nothing)
          , (ChoicePoints, Nothing)
          , (Matches, Nothing)
          ]
    , -- | **Every pane closed still lists every pane** — which is the case his
      -- ruling of the same day made reachable and the reason this bar exists:
      -- /"the user closed them, the user wants them closed."/
      testCase "a screen with no panes still names all nine" $ do
        let shut = foldr closePane defaultLayout allPanes
        paneBarEntries shut @?= [(p, Nothing) | p <- allPanes]
        length (paneBarEntries shut) @?= 9
    , -- | **The suggestion strip is not in the layout at all** — `~w2tk2`
      -- slice 1, and this is the test that keeps it that way. It has no
      -- position, so it is in neither column, in neither 'paneBarEntries'
      -- list, and in nothing the six numbers address; 'Tui.App' appends it to
      -- the bar itself. If it ever acquires a 'Pane' constructor this fails,
      -- which is the point.
      testCase "the strip is in no position and in neither column" $ do
        length allPanes @?= 9
        paneByName stripName @?= Nothing
        assertBool "named unlike every pane" (stripName `notElem` map paneName allPanes)
    , -- | **Closed, and nothing he has on screen moves until he says so.**
      testCase "the strip starts closed, at the height the finished pane wants" $ do
        stripOpen defaultStrip @?= False
        stripRows defaultStrip @?= stripDefaultRows
        assertBool "tall enough to be worth drawing" (stripDefaultRows > stripMinRows)
    , testCase "opening and closing the strip leaves its height alone" $ do
        let pulled = stripSized 14 defaultStrip
        stripRows (openStrip pulled) @?= 14
        stripRows (closeStrip (openStrip pulled)) @?= 14
        stripOpen (closeStrip (openStrip pulled)) @?= False
    , -- | **The floor is here and the ceiling is not** — 'stripSized' knows
      -- 'stripMinRows' and nothing about the terminal, which is
      -- 'Tui.App.maxStripRows'' job. A dotfile edited by hand goes through
      -- this same function, so a nonsense height is a short strip and never
      -- a strip with no rows.
      testCase "a strip can never be pulled below its floor" $ do
        stripRows (stripSized 0 defaultStrip) @?= stripMinRows
        stripRows (stripSized (-40) defaultStrip) @?= stripMinRows
        stripRows (stripSized stripMinRows defaultStrip) @?= stripMinRows
        stripRows (stripSized 99 defaultStrip) @?= 99
    ]
