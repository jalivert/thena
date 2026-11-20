-- | **Which panes are on screen, and where** — `~fxc89`, his instruction of
-- 2026-11-12: /"I wonder if we ought to introduce some feature of the TUI that
-- allows us to manage them… Let's say we work with 6 positions like we have
-- now, each one given a number… So we can do @:pane modules open 1@ or
-- @:pane usage close@ and so."/
--
-- **Six positions, two columns of three, numbered across**:
--
-- > 1 2
-- > 3 4
-- > 5 6
--
-- so the odd ones are the left column and the even ones the right. The
-- numbering is row-major and the layout is column-major; 'columnsOf' is the
-- whole of that translation and nothing else in the TUI does it.
--
-- **This module is pure and knows nothing about brick**, which is what lets
-- `thena-tui-test` hold the two operations to their results without a terminal
-- — and they are the half of `~fxc89` worth testing, the drawing being the
-- pty's business as always.
--
-- **A position is an address and not a rectangle held open.** Close the pane at
-- 3 and the panes below it move up a row on screen, because 'columnsOf' lists
-- only what is placed; but @output@ is still at 5, so
-- @:pane proofs open 3@ puts the new pane back between them. Renumbering on a
-- close would mean every address he had learned moved under him.
module Tui.Layout
  ( Pane (..)
  , allPanes
  , paneName
  , paneByName
  , Position
  , positions
  , Layout
  , defaultLayout
  , paneAt
  , positionOf
  , placedPanes
  , columnsOf
  , openPane
  , closePane
  , layoutPairs
  , layoutFrom
  , paneBarEntries
  , Strip (..)
  , stripName
  , stripTitle
  , spinnerFrames
  , defaultStrip
  , stripMinRows
  , stripDefaultRows
  , openStrip
  , closeStrip
  , stripSized
  , stripBodyRows
  , Grid (..)
  , stripGrid
  , stripSlotKeys
  , stripCellWidth
  , stripHintRows
  , stripHintBudget
  , stripHintUsed
  , stripReplyRows
  , stripSeparatorRows
  , stripHintGapRows
  ) where

import qualified Data.Map.Strict as Map

-- | The panes a position can hold, **and nothing else of the screen** — the
-- document is not one of these, which is the point: it takes whatever the
-- panes leave, so it has no width of its own and no position either.
--
-- **The names are the ones they already go by** — his instruction: /"I think
-- we can use the ones they already go by."/ They were the titles drawn at the
-- head of each pane before they were a vocabulary, so nothing he reads on
-- screen had to change to make this command typeable.
data Pane
  = Globals
  | Modules
  | Output
  | ProofTerm
  | Goals
  | Machine
  | Quests
    -- ^ **the parked proofs, and the import standing in a @yield@** —
    -- `~76zrr`. **Called @Quests@ here and drawn as @proofs@ on screen, on
    -- purpose**: the engine's word for both of the things this pane lists is a
    -- quest, because a module's load that stopped is not a proof and nothing
    -- will ever certify it, while the words he asked in were /"a pane with
    -- parked proofs"/. 'paneName' is the one place the two meet.
  | ChoicePoints
    -- ^ **the live backtracking choice points** — `~396c8`, his request of
    -- 2026-11-13: /"we don't have a pane for backtracking choice-points…
    -- something that would show me all of the choice-points that could be
    -- revisited and paths taken from them."/ Blocked on `~sx324` until the
    -- engine answered it on 2026-11-16 with @Thena.View.choicesView@; drawn
    -- as @choices@, the same word @:choices@ already uses. **Not called
    -- @Choices@** — 'Thena.Driver' already has a 'Response' constructor of
    -- that name, and the two would collide unqualified everywhere a frontend
    -- imports both wholesale, as this one does.
  | Matches
    -- ^ **which rules apply at the focus, the same list @:matches@ already
    -- prints** — his ask, 2026-11-16, read back at cold-start as uncertain
    -- whether he had asked it at all. No blocked read this time:
    -- @Thena.View.matchesView :: Budget -> Session -> [RuleView]@ had been
    -- on the boundary since MS7 and was simply never drawn anywhere.
    -- **Since MS12 phase 323 the signature is
    -- @Budget -> Session -> [MatchView]@, one row per rule-arity rather
    -- than per clause** — pulled in 2026-11-19, see `~w2tk2`'s board.
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Every pane there is, placed or not. **The width map is built over this and
-- not over what is on screen**, so a pane that is closed and opened again comes
-- back the width it was pulled to.
allPanes :: [Pane]
allPanes = [minBound .. maxBound]

-- | What a pane is called — on screen, in @:pane@, and in the completion. One
-- function, so the title and the word he types cannot drift apart.
paneName :: Pane -> String
paneName p = case p of
  Globals -> "globals"
  Modules -> "modules"
  Output -> "output"
  ProofTerm -> "proofterm"
  Goals -> "goals"
  Machine -> "machine"
  Quests -> "proofs"
  ChoicePoints -> "choices"
  Matches -> "matches"

paneByName :: String -> Maybe Pane
paneByName w = lookup w [(paneName p, p) | p <- allPanes]

-- | One of 'positions'. **Not an index into anything** — see the module note:
-- it is the pane's address, and a pane keeps it until he moves the pane.
type Position = Int

-- | @[1 .. 6]@. **Six because three panes to a column is what the vertical
-- room allows**: a column of four on a forty-row terminal gives each pane ten
-- rows, which is a heading and eight names.
positions :: [Position]
positions = [1 .. 6]

-- | Which pane is at which position. **A pane appears at most once** — every
-- operation here removes it from where it was before placing it, so there is no
-- state in which one pane is drawn in two columns.
newtype Layout = Layout (Map.Map Position Pane)
  deriving (Eq, Show)

-- | **Exactly the screen as it was before this command existed**, so nothing
-- moves until he types @:pane@. 'Quests', 'ChoicePoints' and 'Matches' are
-- the seventh, eighth and ninth panes and all three start closed;
-- `~76zrr`/`:pane proofs open 6` fetches the first,
-- `~396c8`/`:pane choices open ‹n›` the second, and
-- `:pane matches open ‹n›` the third.
defaultLayout :: Layout
defaultLayout =
  Layout
    (Map.fromList
       [ (1, Globals)
       , (3, Modules)
       , (5, Output)
       , (2, ProofTerm)
       , (4, Goals)
       , (6, Machine)
       ])

paneAt :: Position -> Layout -> Maybe Pane
paneAt n (Layout m) = Map.lookup n m

positionOf :: Pane -> Layout -> Maybe Position
positionOf p (Layout m) =
  case [n | (n, q) <- Map.toAscList m, q == p] of
    n : _ -> Just n
    [] -> Nothing

-- | Every pane on screen, in position order.
placedPanes :: Layout -> [Pane]
placedPanes (Layout m) = Map.elems m

-- | **The two columns, each in position order** — odd positions left, even
-- right. A column holds only the panes actually placed in it, so a closed
-- position is one fewer row rather than a gap of backdrop.
columnsOf :: Layout -> ([Pane], [Pane])
columnsOf (Layout m) =
  ( [p | (n, p) <- Map.toAscList m, odd n]
  , [p | (n, p) <- Map.toAscList m, even n]
  )

-- | **Put a pane at a position, and say what that cost.**
--
-- The second component is the pane that was closed to make room, if any, so the
-- caller can tell him rather than leave him to notice. There are three cases
-- and only the third closes anything:
--
--   * the position is free — the pane moves there from wherever it was;
--   * the position is taken and the pane being opened is already on screen —
--     **the two swap**. @:pane goals open 1@ with @globals@ at 1 and @goals@ at
--     4 leaves goals at 1 and globals at 4. Refusing instead would mean no two
--     panes could ever trade places without a free position to stage through;
--   * the position is taken and the pane being opened is closed — the occupant
--     has nowhere to go, so **it is closed**, and it is named in the answer.
--
-- A pane opened onto the position it already holds is left alone.
openPane :: Pane -> Position -> Layout -> (Layout, Maybe Pane)
openPane p n layout@(Layout m)
  | n `notElem` positions = (layout, Nothing)
  | otherwise = case Map.lookup n m of
      Just q | q == p -> (layout, Nothing)
      Just q -> case positionOf p layout of
        Just was -> (Layout (Map.insert was q (Map.insert n p m)), Nothing)
        Nothing -> (Layout (Map.insert n p m), Just q)
      Nothing -> (Layout (Map.insert n p (without p m)), Nothing)

-- | Take a pane off the screen. **Its width is not forgotten** — that map is
-- keyed by pane and built over 'allPanes', so re-opening restores the width he
-- pulled it to.
closePane :: Pane -> Layout -> Layout
closePane p (Layout m) = Layout (without p m)

without :: Pane -> Map.Map Position Pane -> Map.Map Position Pane
without p = Map.filter (/= p)

-- | **Every placed pane and where it is, in position order** — `~vqsd8`, so
-- 'Tui.Config' can write a layout down without 'Layout' stopping being opaque.
--
-- **The inverse of 'layoutFrom' on anything 'layoutFrom' accepts**, which is
-- what makes a round trip through the dotfile mean something.
layoutPairs :: Layout -> [(Position, Pane)]
layoutPairs (Layout m) = Map.toAscList m

-- | **A layout read back from somewhere outside** — `~vqsd8`, the dotfile.
--
-- **Built by replaying 'openPane' over an empty layout rather than by wrapping
-- the map**, which is the whole point: every invariant 'openPane' keeps is kept
-- here for free, and a file that has been edited by hand cannot produce a
-- layout the commands could not. A position outside one to six is dropped, and
-- a pane named twice ends up at the last position given rather than at both.
--
-- **It never fails.** A frontend's own preference file is not worth refusing to
-- start over — same judgement as 'Tui.Config.loadConfig', which falls back
-- silently — so the worst a nonsense list can do is place fewer panes than it
-- meant to.
layoutFrom :: [(Position, Pane)] -> Layout
layoutFrom = foldl place (Layout Map.empty)
  where
    place layout (n, p) = fst (openPane p n layout)

-- | **Every pane the TUI has, with its position where it has one** — `~7tfhd`,
-- his instruction of 2026-11-13: /"some smaller UI element that lists all the
-- available panes, like all that the TUI has, opened ones are rendered a bit
-- differently to closed ones, and they show the position they are rendered at
-- (the number)."/
--
-- **Placed panes first in position order, then the closed ones.** Decided by
-- the mockup he picked rather than asked as a question, because it was in the
-- sketch he chose: @globals 1  proofterm 2  modules 3  goals 4  output 5
-- machine 6  proofs@. Ascending numbers read as a sequence; 'allPanes' order
-- would scatter them.
--
-- **A closed pane's position is 'Nothing' and is not remembered anywhere.**
-- 'closePane' drops it from the map and keeps nothing, which is right: a width
-- is remembered because he pulls one and expects it back (`~vqsd8`), while a
-- position is what @:pane ‹name› open ‹n›@ states every time it is used.
--
-- **The closed ones keep 'allPanes' order among themselves**, which is stable
-- across opens and closes — so a pane he closes does not make the others jump
-- about in the bar.
paneBarEntries :: Layout -> [(Pane, Maybe Position)]
paneBarEntries layout =
  [(p, Just n) | (n, p) <- layoutPairs layout]
    <> [(p, Nothing) | p <- allPanes, positionOf p layout == Nothing]

-- * The suggestion strip — `~w2tk2`

-- | **The suggestion strip: where it is, and how tall** — `~w2tk2` slice 1,
-- the pane that replaces the completion dropdown. A strip under the prompt,
-- the width of the script column; **his term for the pair is the
-- "double-pane"**.
--
-- **It is deliberately NOT a 'Pane', and that is the whole of why this type
-- exists.** A 'Pane' is a thing a 'Position' holds: it is addressed by one of
-- six numbers, it is sized in /columns/, and it is laid out in one of two
-- columns to the right of the document. The strip is none of those. It has
-- exactly one place it can be — under the prompt, which is the design's own
-- argument for it (/"eyes moving down is easier than eyes moving
-- sideways"/) — it is sized in /rows/, and its width is not its own but the
-- document column's. Adding it to 'Pane' would have made
-- @:pane suggestions open 3@ a sentence the type accepts and the screen
-- cannot honour, and would have given it a width in the pane-width map that
-- nothing ever reads.
--
-- **So what it shares with a pane is only what it genuinely shares**: it is
-- named in the pane bar, it is opened and closed by @:pane@, it is pulled by
-- its accent bar, and it is remembered in the dotfile.
data Strip = Strip
  { stripOpen :: Bool
    -- ^ whether it is on screen at all. **Closed is the default** — see
    -- 'defaultStrip'.
  , stripRows :: Int
    -- ^ **how many screen rows its viewport is given — the title row not
    -- counted**, the same reckoning a pane's width uses, which measures the
    -- pane and not its accent bar. The one row of breathing space a pane's
    -- body is padded with is inside this, so the rows of text visible are
    -- one fewer, exactly as in every other pane.
    --
    -- Never below 'stripMinRows'; **the ceiling is not here** — how tall it
    -- may be depends on what the document is left, which depends on the
    -- terminal, which this module does not know and will not read.
  }
  deriving (Eq, Show)

-- | What the strip is called — in @:pane@, in the pane bar, and in its own
-- title. **One function, for the reason 'paneName' is one function**: the
-- word on screen and the word he types cannot drift apart.
--
-- **His word, and the discussion settled on it**: /"let's just leave it at
-- 'suggestion pane' for now"/. Singular @suggestions@ rather than
-- @suggestion-pane@ because every other pane is named by what it holds.
stripName :: String
stripName = "suggestions"

-- | **The strip's title, with a turning spinner beside it while a ranking is
-- out** — HIS instruction, 2026-11-20, on `~swxcf`: /"You could show some ascii
-- spinner next to the \"suggestions\" when we are waiting for the Jev's
-- suggestions… Ideally it would move, like there are unicode characters that
-- can be used for that."/
--
-- The pane's cells only ever hold Jev's own picks, so between a keystroke and
-- Jev's answer there is nothing to draw; the spinner is what says the emptiness
-- is a wait and not an answer. 'Nothing' is the ordinary title and the only
-- thing drawn when no request is out.
--
-- **The frame is an index and the caller keeps it**, which is why this is a
-- function of one: the animation's clock belongs to the event loop and the
-- glyph table belongs here, beside the name it is drawn next to.
stripTitle :: Maybe Int -> String
stripTitle Nothing = stripName
stripTitle (Just frame) = stripName <> " " <> [spinnerFrames !! (frame `mod` length spinnerFrames)]

-- | **The spinner's glyphs, and every one of them is one column wide.** Braille
-- patterns (U+2800…) are narrow in vty's own width table and in a terminal, so
-- unlike ✅ or ⚠️ they need no entry in 'Tui.Panes.wideGlyphs' and cannot shift
-- the pane to their right — `~8ztt3` is the defect that rule comes from.
--
-- Ten frames, read as one dot travelling round a 2×3 cell.
spinnerFrames :: [Char]
spinnerFrames = "\10251\10265\10297\10296\10300\10292\10278\10279\10247\10255"

-- | **Closed, and that is deliberate for slice 1.** Nothing he has on screen
-- today moves until he types @:pane suggestions open@: the strip takes its
-- rows from the document, and a half-built pane that shrinks the document on
-- launch would be charging him for a thing he has not asked to see yet.
defaultStrip :: Strip
defaultStrip = Strip { stripOpen = False, stripRows = stripDefaultRows }

-- | Fewer rows than this and the strip holds nothing worth drawing: a
-- heading and two offers under it.
stripMinRows :: Int
stripMinRows = 3

-- | **Nine rows, which is what the finished strip needs and not a number
-- chosen for slice 1.** The design puts a grid of three or four rows in the
-- upper half, the LLM hint in the lower half, and a reply row under that —
-- so the strip he will eventually pull is about this tall, and opening it at
-- its eventual height is what makes slice 1 a test of the premise rather
-- than of a smaller thing.
--
-- **Eight until slice 4, and the extra row is the reply row he never saw.**
-- Measured under a pty, 2026-11-19: at eight the body drew a heading, three
-- rows of cells and the three hint rows, and the reply row was **below the
-- viewport's last line** — reserved in the arithmetic and absent from the
-- screen, which nothing could see while the reserve was blank. See
-- 'stripBodyRows' for why the body is a row shorter than the strip. **Nine
-- is the height at which his own measured geometry still holds**: three
-- columns of three, the hint's floor, and a reply row that is actually
-- drawn — @1 + 3 + 3 + 1@ in the eight rows a nine-row strip gives its body.
--
-- **His own dotfile holds a @suggestion-rows@ of its own and this default
-- will not reach it.** At eight he now sees two rows of cells rather than
-- three, with the reply row present; one pull of the accent bar is the
-- difference.
stripDefaultRows :: Int
stripDefaultRows = 9

-- | **The rows the strip's body can actually draw**, which is one fewer than
-- the strip's own height — `~w2tk2` slice 4, and it is a measurement rather
-- than an argument.
--
-- **Where the row goes.** 'Tui.App' gives the strip @stripRows + 1@ rows; of
-- those the pane's title takes one, leaving @stripRows@ for the viewport,
-- and the body inside it is wrapped in a @padAll 1@ whose top row is the
-- first thing the viewport shows. The bottom row of that padding falls past
-- the viewport's last line and is never drawn, which is why the body gets
-- @stripRows - 1@ and not @stripRows - 2@.
--
-- **Measured under a pty, 2026-11-19**, at a strip pulled to fourteen: the
-- title on one row, one row of padding, then **thirteen** rows of body. The
-- arithmetic had been handing 'stripGrid' the strip's own height, so every
-- region was budgeted one row that did not exist — and the row the overflow
-- fell on was the last one, the reply row.
--
-- **Floored at one.** A strip at 'stripMinRows' is a sliver and its body is
-- still a body; nothing downstream is prepared for a region of no rows.
stripBodyRows :: Int -> Int
stripBodyRows rows = max 1 (rows - 1)

openStrip :: Strip -> Strip
openStrip s = s { stripOpen = True }

closeStrip :: Strip -> Strip
closeStrip s = s { stripOpen = False }

-- | The strip at a height, floored at 'stripMinRows'. **No snap, unlike a
-- pane's width** — @paneWidthStep@ exists because a column is a fine unit
-- and "about the same width" should mean the same width; a row is already
-- coarse, and a strip snapped to every fourth row could not be put where he
-- means.
--
-- **The ceiling is not here.** How tall the strip may be depends on what the
-- document is left, which depends on the terminal, which this module does
-- not know and will not read.
stripSized :: Int -> Strip -> Strip
stripSized n s = s { stripRows = max stripMinRows n }

-- * The grid of numbered options — `~w2tk2` slice 2

-- | **The F-keys a slot can be taken by, in order** — `~w2tk2` slice 2, and
-- **this list is the one place the keymap's size is decided.**
--
-- **F1 to F10, and the two absences are each for their own reason.**
--
--   * **F11 never reaches the TUI on his machine**, measured 2026-11-19 by
--     reading the bytes his own terminal sends: every other F-key arrived as
--     the sequence vty names and F11 sent nothing at all. It is macOS, not
--     his terminal — /Show Desktop/ owns it (System Settings → Keyboard →
--     Keyboard Shortcuts → Mission Control). **Freeing it is one entry in
--     this list and no other change.**
--   * **F12 is the live-script command bar's, and that is HIS ruling of
--     2026-11-19**: /"we take F2 for suggestions, replacing its original
--     functionality with some other shortcut or command."/ F2 was the bar's
--     and would have put a hole in the middle of the grid. **The move costs
--     nothing**: Ctrl+X was always the bar's second way in, deliberately, so
--     /"a terminal that rewrites function keys should not be able to strand
--     someone in a mode whose only exit is the bar"/ — and F12 is the one
--     F-key no grid cell will ever reach for.
--
-- **Ctrl+digit is not an option and that is measured, not assumed.** vty does
-- not name the CSI-u encoding, so `ESC[49;5u` is typed into the line
-- verbatim (`~xmd5b`'s path); and the legacy encoding for Ctrl+1 is the bare
-- digit, which he must be able to type. **So the keymap is F-keys or
-- nothing.**
stripSlotKeys :: [Int]
stripSlotKeys = [1 .. 10]

-- | **The narrowest a cell may be**: the key field (@F10@ and two spaces),
-- then a label.
--
-- **Labels run to about twenty characters** — @constructor-recursive-arguments@
-- is the long tail and @intro-arm-binders@ is typical — so this is the key
-- field plus a typical label plus a column of air between cells.
stripCellWidth :: Int
stripCellWidth = 26

-- | **Rows kept for the LLM's hint, whatever the grid is doing** — his
-- instruction: /"I want like bottom half or three lines-worth to always be
-- free for an LLM suggestion"/. Three is the /"three lines-worth"/ reading,
-- which is the one that does not take half the strip away from the grid.
--
-- **Reserved at slice 2, filled at slice 4.** Blank rows first rather than a
-- grid that grows into them and has to be shrunk later: the geometry is the
-- thing slice 2 was establishing, and a reserve that only appears once
-- there is something to put in it is a reserve that was never tested.
--
-- **THIS IS A FLOOR AND NOT A CAP — `~w2tk2` slice 4**, which is the reading
-- his /"always be free"/ asks for: three rows are the hint's whether it uses
-- them or not, and a hint that needs more takes more. 'stripHintUsed' is the
-- whole of that rule and 'stripHintBudget' is where it stops.
stripHintRows :: Int
stripHintRows = 3

-- | **The most rows the hint may take in a strip this tall** — `~w2tk2`
-- slice 4.
--
-- **The grid keeps one row, always.** The hint grows by taking rows off the
-- grid, and the row it may not take is the last one: a strip showing a hint
-- and no options at all would have stopped being the pane the F-keys are
-- bound to. One grid row and the reply row are what the hint is not allowed
-- to have.
--
-- **It is never below 'stripHintRows', even in a strip too short to pay
-- for it.** At 'stripMinRows' the arithmetic wants fewer than three, and
-- the floor is what his /"always"/ means — the overflow clips, and the
-- remedy is the drag slice 1 built: pull the strip taller and both regions
-- grow.
stripHintBudget :: Int -> Int
stripHintBudget rows =
  max stripHintRows (rows - 1 - stripReplyRows - stripSeparatorRows - stripHintGapRows)

-- | **The rows the hint region actually occupies**, given how tall the strip
-- is and how many lines the hint wrapped to — `~w2tk2` slice 4.
--
-- **Takes the line count rather than the text**, so the arithmetic is here
-- and the wrapping is in 'Tui.Panes.stripHintLines', which is the one place
-- that knows how a row of this pane breaks. The drawing and the keymap read
-- the same two functions in the same order, which is how `~w2tk2` slice 3a's
-- defect — a key on a cell the grid never drew — stays fixed when the grid's
-- size starts depending on the hint as well as on the strip.
--
-- **No hint is @0@ lines and still three rows.** The region does not appear
-- and disappear: a grid that reflowed every time the model spoke would move
-- every key he had just learned.
stripHintUsed :: Int -> Int -> Int
stripHintUsed rows needed = min (stripHintBudget rows) (max stripHintRows needed)

-- | **One row at the bottom to reply to the LLM in** — his instruction,
-- /"there needs to be a room for one row at the bottom, for a reply from the
-- user"/. Built at slice 5; reserved here for the reason 'stripHintRows' is.
stripReplyRows :: Int
stripReplyRows = 1

-- | **One blank row between the grid and the LLM's half of the pane** — HIS
-- instruction, 2026-11-19: /"Leave one line's space between the Jev's
-- suggestions and the space for LLM."/
--
-- **Reserved rather than left to chance.** The space appears on its own
-- whenever the grid has fewer cells than it has room for — the slack falls
-- between them — but a grid that filled every row it was given would have
-- run straight into the hint, which is the case this row exists for. So the
-- grid is sized one row shorter and the gap is there at every height.
stripSeparatorRows :: Int
stripSeparatorRows = 1

-- | **One blank row between the model's answer and the row he types in** —
-- HIS instruction, 2026-11-19: /"Give me one empty line between the AI reply
-- and my AI prompt. That one will stay empty."/
--
-- **Reserved only while there is an answer**, unlike
-- 'stripSeparatorRows'. With no hint on screen there is nothing for it to
-- separate the ask row from, and the air above that row is already the
-- whole of the pane's slack — reserving it unconditionally would spend a row
-- to separate a row from nothing, which is the shape `~8cr56` was reported
-- for.
stripHintGapRows :: Int
stripHintGapRows = 1

-- | **The grid the strip's size implies** — `~w2tk2` slice 2.
--
-- **The shape is NOT a constant, which is his own instruction** of
-- 2026-11-19: /"It could also change depending on how wide the double-pane
-- (main + suggestions) is."/ So 3×4 and 4×3 are two points on a curve
-- rather than a choice to be made once, and the 99-column measurement his
-- discussion records is one reading of it.
data Grid = Grid
  { gridCols :: Int
    -- ^ how many cells across — the width divided by 'stripCellWidth'.
  , gridRows :: Int
    -- ^ how many rows the slots actually need, which is never more than the
    -- allowance and is usually fewer.
  , gridSlots :: Int
    -- ^ **how many options there are, which is the grid's own capacity** —
    -- never more than 'stripSlotKeys' has keys for. **An option with no key
    -- and a key with no option are both states this makes unreachable**: the
    -- slate is sized by the grid, and the grid is sized by the strip.
  }
  deriving (Eq, Show)

-- | The grid for a strip this wide and this tall. Width is the room the
-- /content/ has, not the pane's own — the caller takes the accent bar and
-- the padding off first.
--
-- **Three consequences worth stating, because each is a thing he will see:**
--
--   * **A wider double-pane offers more suggestions.** Pulling the pane
--     columns in gives the document more width, which gives the strip more
--     cells across.
--   * **A taller strip offers more suggestions**, up to ten — which makes
--     the drag of slice 1 a control over the slate and not only over how
--     much is on screen.
--   * **A hint offers fewer**, because @reserved@ is what the hint and the
--     reply row actually took — `~w2tk2` slice 4. The grid is the region
--     that gives way, which is his /"I just don't want them to take **all**
--     the vertical space"/ read in the other direction. **With no hint it is
--     zero and the grid has the whole body** (`~8cr56`).
--   * **At his measured geometry — a 99-column script pane — there are
--     three columns and three grid rows, so NINE options**, and F10 has no
--     slot to take. That is not a gap: the keys bound are exactly the cells
--     drawn, so nothing is advertised that cannot be pressed.
stripGrid :: Int -> Int -> Int -> Grid
stripGrid width rows reserved =
  Grid { gridCols = cols, gridRows = used, gridSlots = slots }
  where
    cols = max 1 (width `div` stripCellWidth)
    -- | **Every row the grid does not get is the caller's third argument,
    -- and with nothing to reserve for it is zero** — `~8cr56`, his report of
    -- 2026-11-19: /"Why do I only get 2 suggestions?"/ He had seven body
    -- rows and five of them were spent on a hint that did not exist, a reply
    -- row with nothing in it and a heading duplicating the pane's own title.
    -- **A region that is empty takes no row.**
    allowance = max 1 (rows - reserved)
    slots = min (length stripSlotKeys) (cols * allowance)
    -- | **The rows the slots need, not the rows they are allowed.** A strip
    -- pulled tall enough for twelve cells still draws four rows of ten, and
    -- the room left over goes to the hint.
    used = max 1 ((slots + cols - 1) `div` cols)
