{-# LANGUAGE OverloadedStrings #-}
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

import Graphics.Text.Width (safeWcwidth)
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
  , stripTitle
  , spinnerFrames
  , stripSized
  , Grid (..)
  , stripCellWidth
  , stripGrid
  , stripHintBudget
  , stripBodyRows
  , stripHintRows
  , stripHintUsed
  , stripReplyRows
  , stripSlotKeys
  )
import qualified Data.Text as Text

import Tui.Hint (HintModel (..), matchingModels, modelRow)
import Tui.Jev (jevNucleus, jevPickLimit)

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
    , -- | **The spinner beside the title, and only while a ranking is out** —
      -- HIS instruction, 2026-11-21, on `~swxcf`. The cells hold Jev's own
      -- picks and nothing else, so the pane is empty between the keystroke
      -- and the answer; the spinner is what tells him that gap is a wait.
      testCase "the title spins only while something is on its way" $ do
        stripTitle Nothing @?= stripName
        assertBool "the frame is beside the name" (stripTitle (Just 0) /= stripName)
        length (stripTitle (Just 0)) @?= length stripName + 2
    , -- | **The frame index is never bounds-checked by the caller** — it only
      -- ever counts up, so the table has to wrap for it.
      testCase "a frame index past the table wraps instead of failing" $ do
        stripTitle (Just (length spinnerFrames)) @?= stripTitle (Just 0)
        stripTitle (Just (3 * length spinnerFrames + 4)) @?= stripTitle (Just 4)
        assertBool "more than one frame to show" (length spinnerFrames > 1)
    , -- | **Every spinner glyph is one column wide, and that is `~8ztt3`'s
      -- rule applied before the fact**: a two-column glyph the TUI has not
      -- declared to vty shifts every cell to its right, which is how the ✅
      -- beside the prelude moved the next pane's accent bar. Braille is
      -- narrow, so there is nothing to declare.
      testCase "no spinner frame is a wide glyph" $
        assertBool "all one column" (all ((== 1) . safeWcwidth) spinnerFrames)
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
    , -- | **The grid is a function of the strip's size, which is HIS
      -- instruction of 2026-11-19** — /"it could also change depending on how
      -- wide the double-pane (main + suggestions) is"/. So 3×4 and 4×3 are
      -- two readings of one curve and neither is a constant to be picked.
      --
      -- **His measured geometry is the case to hold**: a 99-column script
      -- pane, three columns of cells, and at the strip's default height three
      -- grid rows — so **nine options**, which is what he will see.
      testCase "at his measured geometry the grid is three wide" $ do
        let g = stripGrid 96 (stripBodyRows stripDefaultRows) 0
        gridCols g @?= 3
        gridSlots g @?= length stripSlotKeys
    , -- | **A wider double-pane offers more suggestions, and a taller strip
      -- does too** — which makes slice 1's drag a control over the slate and
      -- not only over how much of it is on screen.
      testCase "more width is more columns, more height is more slots" $ do
        gridCols (stripGrid 52 (stripBodyRows stripDefaultRows) 0) @?= 2
        gridCols (stripGrid 140 (stripBodyRows stripDefaultRows) 0) @?= 5
        assertBool "a taller strip offers more"
          (gridSlots (stripGrid 30 9 4) > gridSlots (stripGrid 30 6 4))
    , -- | **An option with no key and a key with no option are both
      -- unreachable, and that is the invariant of the whole slice.** The
      -- slate is sized by the grid and the grid is bounded by the keys, so
      -- every cell drawn can be pressed and every key bound has a cell.
      testCase "the slate never outruns the keys there are" $ do
        let keys = length stripSlotKeys
        gridSlots (stripGrid 400 40 stripHintRows) @?= keys
        assertBool "never more than the keys" $
          and [ gridSlots (stripGrid w r stripHintRows) <= keys
              | w <- [1, 20, 52, 96, 140, 400], r <- [stripMinRows, 8, 14, 40] ]
        assertBool "never none" $
          and [ gridSlots (stripGrid w r stripHintRows) >= 1
              | w <- [1, 20, 52, 96, 140, 400], r <- [stripMinRows, 8, 14, 40] ]
    , -- | **The rows the slots NEED, not the rows they are allowed.** A strip
      -- pulled tall enough for fifteen cells still draws four rows of ten,
      -- and the room left over goes to the hint rather than to blank cells.
      testCase "a tall strip draws the rows its slots need and no more" $ do
        let g = stripGrid 96 40 stripHintRows
        gridSlots g @?= length stripSlotKeys
        gridRows g @?= 4
    , -- | **The hint and the reply keep their rows whatever the grid does** —
      -- his /"I want like bottom half or three lines-worth to always be free
      -- for an LLM suggestion"/ plus /"one row at the bottom, for a reply"/.
      -- The heading is the fifth row this leaves out, and it is inside the
      -- grid's budget because it is drawn in the strip's own rows.
      testCase "the reserve is kept out of the grid's budget at every height" $ do
        stripHintRows + stripReplyRows @?= 4
        assertBool "the grid never eats the reserve" $
          and [ gridRows (stripGrid 96 r reserved) <= max 1 (r - reserved)
              | r <- [stripMinRows .. 40]
              , let reserved = stripHintUsed r 1 + stripReplyRows ]
    , -- | **AN EMPTY REGION TAKES NO ROW, AND THAT IS `~8cr56`** — his
      -- report of 2026-11-19, /"Why do I only get 2 suggestions?"/ At his
      -- own geometry — a strip of eight rows, so seven of body, one cell
      -- wide — the reserve for a hint that did not exist plus a heading row
      -- left two cells. **Seven now**, and four once something is actually
      -- in the hint.
      testCase "with nothing in the hint the grid has the whole body" $ do
        gridSlots (stripGrid 51 (stripBodyRows 8) 0) @?= 7
        gridSlots (stripGrid 51 (stripBodyRows 8) (stripHintRows + stripReplyRows)) @?= 3
    , -- | **The reserve is a FLOOR and a long hint takes rows off the grid**
      -- — `~w2tk2` slice 4, which is what his /"always be free"/ asks for:
      -- three rows are the hint's whether it fills them or not, and a hint
      -- that needs more is not truncated to fit a grid.
      testCase "no hint and a short hint both take the floor" $ do
        stripHintUsed stripDefaultRows 0 @?= stripHintRows
        stripHintUsed stripDefaultRows 1 @?= stripHintRows
        stripHintUsed stripDefaultRows stripHintRows @?= stripHintRows
    , -- | **The grid is the region that gives way**, which is his /"I just
      -- don't want them to take **all** the vertical space"/ read in the
      -- other direction. A two-column strip is the case that shows it: at
      -- three columns the ten keys are the binding constraint and the grid
      -- has rows to spare.
      testCase "a hint past its floor takes the rows it needs, off the grid" $ do
        stripHintUsed 10 6 @?= 6
        assertBool "a longer hint is fewer options" $
          gridSlots (stripGrid 52 10 (6 + stripReplyRows))
            < gridSlots (stripGrid 52 10 (stripHintRows + stripReplyRows))
    , -- | **The grid keeps one row, always.** A strip that showed a hint and
      -- no options at all would have stopped being the pane the F-keys are
      -- bound to, so the hint's growth stops one row short of that.
      testCase "a hint can never take the grid's last row" $ do
        assertBool "a row of cells survives any hint" $
          and [ gridRows (stripGrid 96 r (stripHintUsed r n + stripReplyRows)) >= 1
              | r <- [stripMinRows .. 40], n <- [0, 1, 3, 7, 40, 400] ]
        assertBool "the budget leaves a grid row and the reply row" $
          and [ stripHintBudget r <= max stripHintRows (r - 1 - stripReplyRows)
              | r <- [stripMinRows .. 40] ]
    , -- | **The floor wins in a strip too short to pay for it**, which is
      -- the one place the region overflows: his /"always"/ is the rule and
      -- the drag slice 1 built is the remedy.
      testCase "the floor holds even where the strip cannot afford it" $ do
        stripHintBudget stripMinRows @?= stripHintRows
        stripHintUsed stripMinRows 9 @?= stripHintRows
    , -- | **THE BODY IS A ROW SHORTER THAN THE STRIP, AND THE ROW THE
      -- ARITHMETIC USED TO INVENT WAS THE REPLY ROW** — `~w2tk2` slice 4,
      -- measured under a pty: at a strip of fourteen the body drew thirteen
      -- rows and the fourteenth region fell past the viewport's last line.
      -- See 'stripBodyRows'.
      testCase "the body is one row shorter than the strip, floored at one" $ do
        stripBodyRows 14 @?= 13
        stripBodyRows stripDefaultRows @?= stripDefaultRows - 1
        stripBodyRows 1 @?= 1
        stripBodyRows 0 @?= 1
    , -- | **At the default height all four regions fit the body exactly** —
      -- a heading, his three rows of cells, the hint's floor and the reply
      -- row, in the eight rows a nine-row strip gives its body. **This is
      -- the case that holds 'stripDefaultRows' to its claim**: it was eight
      -- and the reply row was off the screen.
      testCase "at the default height a hint and the grid fit the body exactly" $ do
        let body = stripBodyRows stripDefaultRows
            g = stripGrid 96 body (stripHintRows + stripReplyRows)
        gridRows g @?= 4
        gridSlots g @?= length stripSlotKeys
        gridRows g + stripHintRows + stripReplyRows @?= body
    , testCase "a cell is wide enough for the key field and a typical label" $
        assertBool "" (stripCellWidth >= 3 + 2 + 18)
    , -- | **The filter is what makes `:models` usable at all** — 479 rows
      -- is a list you scroll past rather than read. Matches an id or a
      -- name, case ignored; **empty is every row**, which is what bare
      -- `:models` passes.
      testCase "the model filter matches id or name, case ignored" $ do
        map (Text.unpack . mdId) (matchingModels "haiku" catalogue) @?= ["anthropic/claude-haiku-5.5"]
        map (Text.unpack . mdId) (matchingModels "HAIKU" catalogue) @?= ["anthropic/claude-haiku-5.5"]
        map (Text.unpack . mdId) (matchingModels "openai" catalogue) @?= ["openai/gpt-5"]
        length (matchingModels "" catalogue) @?= 3
        map (Text.unpack . mdId) (matchingModels "nothing-like-this" catalogue) @?= []
    , -- | **A row is the id first**, because the id is what `:model` takes
      -- and what the dotfile stores; the context window and the price are
      -- what distinguishes two rows of one family.
      testCase "a model row leads with the id and carries context and price" $ do
        fst (modelRow (catalogue !! 0)) @?= "anthropic/claude-haiku-5.5"
        snd (modelRow (catalogue !! 0)) @?= "1000k   $0.0000001/tok"
        snd (modelRow (catalogue !! 2)) @?= "8k"
    , -- | **THE ONE THAT IS THE DEFECT** — `~swxcf`. A 'Choice' answers a
      -- probability for every option it was sent, so a flat answer over 255
      -- candidates used to count as 255 picks and the pane drew the whole
      -- engine list in Jev's order. **An answer that singles out nothing
      -- may not claim more cells than he allowed.**
      testCase "a flat answer over 255 candidates is held to his twelve" $ do
        jevNucleus (replicate 255 (1 / 255)) @?= jevPickLimit
        jevNucleus (replicate 191 (1 / 191)) @?= jevPickLimit
    , -- | **A confident answer is one cell, which is his own stated ideal
      -- for this pane** — one suggestion, and the whisper already on the
      -- line.
      testCase "a confident answer suggests exactly one candidate" $
        jevNucleus [0.95, 0.02, 0.01, 0.01, 0.01] @?= 1
    , -- | A hedged answer fills as many cells as it hedges across: 0.5 and
      -- 0.3 do not reach the cut, 0.12 carries it past.
      testCase "a hedged answer suggests as many as the hedge covers" $
        jevNucleus [0.5, 0.3, 0.12, 0.05, 0.03] @?= 3
    , -- | **An answer with no mass in it has named nobody.** Neither an
      -- empty map nor an all-zero one may put a row on a cell — the
      -- alternative is the top of an arbitrary order wearing Jev's colour.
      testCase "no mass means no suggestion at all" $ do
        jevNucleus [] @?= 0
        jevNucleus [0, 0, 0] @?= 0
    , -- | **The cut is on the shape of the answer, not on its scale or its
      -- order.** A 'Choice' normalises within its own option set, so the
      -- count must not change if the probabilities arrive unnormalised, and
      -- it must not depend on the caller having sorted them.
      testCase "the cut reads the shape and not the scale or the order" $ do
        jevNucleus [0.02, 0.95, 0.01, 0.01, 0.01] @?= 1
        jevNucleus [9.5, 0.2, 0.1, 0.1, 0.1] @?= 1
        jevNucleus [3.0, 1.2, 0.3, 0.1] @?= 2
    ]

-- | Three rows of OpenRouter's shape, enough to tell a filter from a sort:
-- two of one family so a substring hits one and not both, one from another
-- provider, and one with no price at all (a free endpoint has none).
catalogue :: [HintModel]
catalogue =
  [ HintModel "anthropic/claude-haiku-5.5" "Anthropic: Claude Haiku 5.5" 1000000 (Just "0.0000001")
  , HintModel "openai/gpt-5" "OpenAI: GPT-5" 400000 (Just "0.00000125")
  , HintModel "someone/tiny-free" "Someone: Tiny (free)" 8192 Nothing
  ]
