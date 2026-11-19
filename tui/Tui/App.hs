-- | The TUI's entry point.
--
-- **Four panes, no borders** — a wide REPL on the left, proof-term/goals/
-- machine stacked narrower on the right (geometry from `MS7-CLI`, his
-- instruction: the layout only, never its code). Separation is a dark
-- panel fill plus one neon accent as a left edge, never a border glyph and
-- never a full-pane fill — his correction, 2026-09-29, after the first
-- pass used pale tints across the whole pane. **A real border was tried
-- for `.jalivert/TUI.md` #8 and withdrawn the same session** — what he
-- actually wanted was the panes not touching the screen's own edge, the
-- backdrop visible around the outside, not a drawn box around each pane.
-- That's a one-cell stage-colored margin along the top and the left (see
-- `draw`: `padTop` and `padLeft` only — his ruling of 2026-11-16, the
-- bottom row and the right column belong to the panes now), on top of the
-- gap the panes already had between each other — the
-- accent-edge-plus-title scheme itself is unchanged.
--
-- **Views are pulled, not pushed** — `developmentView`/`machineView` are
-- recomputed from `stSession` on every draw, never stored.
--
-- **The completion dropdown is one thing, not two** — `Thena.View.
-- statementOfferView`, called on every keystroke (TIER-A.md's own
-- instruction: the grammar rebuilds cheaply and caches engine-side, so
-- there is nothing to cache here), answers both an ordinary instral line
-- *and* a tagged term literal embedded in one, because its own recovery
-- path already merges the two into the same 'OfferView' before this ever
-- sees it. So what shipped fourth session as "the `:load` dropdown" and
-- what CLAUDE.md's bookkeeping still lists as two separate slices — the
-- statement dropdown and the tagged-literal dropdown — turned out to be
-- one piece of drawing code with one buffer-tracking model
-- ('splitWritten' below), not two.
--
-- **Not yet built**: a standalone tagged literal typed with no statement
-- around it at all reaches the same path (the lexer doesn't care), but a
-- *:*-command's own argument grammar does not exist engine-side yet
-- (TIER-A.md, "what we are doing next") — so a colon line gets no
-- completion beyond `:load`'s own. Tier B — a speculative run behind the
-- offer, showing what typechecking or running would do before Enter — is
-- next, not this session's. Clicking a proof-term/goal line to move the
-- cursor there is still agreed to stay, not yet wired (needs per-line
-- extents).
--
-- Drives the engine through `Thena.Driver` and `Thena.Files`/`Thena.Render`
-- for bootstrap and status text only — panes render through `Thena.View.*`.
-- Never `Thena.Repl`: off `thena:view` entirely since MS7 phase 130.
module Tui.App (runTui) where

import Brick
import Brick.Widgets.Edit
  ( Editor
  , editAttr
  , editFocusedAttr
  , getCursorPosition
  , getEditContents
  , handleEditorEvent
  , renderEditor
  )
import qualified Brick.Widgets.Edit as E
import Brick.Widgets.Center (centerLayer)
import Brick.BChan (BChan, newBChan, writeBChan)
import Control.Concurrent (forkIO, threadDelay)
import Control.Exception (SomeException, try)
import Control.Monad (void, when)
import Control.Monad.IO.Class (liftIO)
import Data.Char (isSpace)
import Data.List (intercalate, intersperse, isPrefixOf, isSuffixOf, sort, sortOn)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Maybe (isJust, isNothing, listToMaybe)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Zipper as Zip
import Data.Time.Clock (UTCTime, diffUTCTime, getCurrentTime)
import qualified Graphics.Vty as V
import Graphics.Vty.Platform.Unix (mkVty)
import Graphics.Vty.UnicodeWidthTable.Install (installUnicodeWidthTable)
import Graphics.Vty.UnicodeWidthTable.Types
  ( UnicodeWidthTable (..)
  , WidthTableRange (..)
  )
import Lens.Micro ((^.), Lens', lens)
import System.Directory (doesDirectoryExist, doesFileExist, listDirectory)
import System.FilePath (dropTrailingPathSeparator, takeDirectory, takeFileName, (</>))
import System.IO (hFlush, hPutStr, readFile', stdout)

import Thena.Driver
  ( Leniency (..)
  , Partly (..)
  , Response (..)
  , commandSummary
  , Unfinished (..)
  , Session
  , Stop (..)
  , digestOf
  , digestText
  , LoadKind (..)
  , exportedByModule
  , filesRead
  , declaredByModule
  , kindOf
  , moduleImportsOf
  , moduleOfFile
  , modulePartly
  , moduleText
  , modulesLoaded
  , oneLine
  , provedSlices
  , submittedLines
  )
import Thena.Files (following, preludePath, rulesPath, startingSession)
import Thena.Render (renderResponse, renderTrouble)
import Thena.View
  ( choicesView
  , developmentView
  , focusAddress
  , machineView
  , matchesView
  , nameDotted
  , proofsView
  , statementOfferView
  )
import Thena.View.Choices (ChoiceView (..))
import Thena.View.Rules (RuleView (..))
import Thena.View.Proofs
  ( ProofsView (..)
  , QuestClaim (..)
  , QuestView (..)
  )
import Thena.View.Chart
  ( OfferView (..)
  , ProductionView (..)
  , RecoveryView (..)
  , SymbolView (..)
  , Written (..)
  )
import Thena.View.Core (Budget (..))

import Tui.Render
  ( Fold (..)
  , developmentText
  , displayText
  , foldAttr
  , goalTexts
  , renderDevelopment
  , renderDisplay
  , renderGoals
  , renderMachineView
  , spliceAttr
  )
import Tui.Config (Config (..), loadConfig, saveConfig)
import Tui.Layout
  ( Grid (..)
  , Layout
  , Pane (..)
  , Position
  , Strip (..)
  , allPanes
  , closePane
  , closeStrip
  , columnsOf
  , openPane
  , openStrip
  , paneBarEntries
  , paneAt
  , paneByName
  , paneName
  , placedPanes
  , positionOf
  , positions
  , stripCellWidth
  , stripGrid
  , stripHintRows
  , stripHintUsed
  , stripMinRows
  , stripName
  , stripReplyRows
  , stripHintBudget
  , stripHintGapRows
  , stripSeparatorRows
  , stripSized
  , stripSlotKeys
  , stripBodyRows
  )
import Tui.Panes
  ( BarSpot (..)
  , FileKind (..)
  , ModuleEntry (..)
  , ModuleMark (..)
  , PaneRow (..)
  , globalRows
  , hintRegionWidget
  , wideGlyphs
  , moduleRows
  , offerGridWidget
  , stripHintLines
  , outputRows
  , paneBarWidget
  , paneRowWidget
  , paneWrap
  )
import Tui.Database
  ( Stored (..)
  , clockName
  , databaseDir
  , freshStored
  , loadIndex
  , readTranscript
  , saveIndex
  , storedNamed
  , writeTranscript
  )
import Tui.Hint
  ( HintConfig (..)
  , HintModel (..)
  , askHint
  , fetchModels
  , hintPlaceholder
  , hintPromptPath
  , loadHintConfig
  , loadHintPrompt
  , matchingModels
  , modelRow
  , resetHintPrompt
  )
import Tui.Jev (JevConfig, JevState (..), jevLog, jevNucleus, loadJevConfig, rankCandidates)
import Tui.Theme (Theme (..), neonPinkDark, themeByName, themes)

-- | **One constructor for all seven panes, carrying which one** — `~fxc89`.
-- They were seven constructors of their own until the layout became something
-- he arranges, at which point every function that walks the panes
-- ('resizablePanes', 'barRightOf', 'maxPaneWidth', 'draw''s own columns) wanted
-- a 'Tui.Layout.Pane' rather than a 'Name' to key on. Going through
-- 'Tui.Layout.Pane' keeps the layout in a module with no brick in it, which is
-- what `thena-tui-test` can reach.
data Name
  = Input
  | ScriptBar
  | HistoryVP
  | PaneVP Pane
  | GlobalGroup String
    -- ^ **one namespace's heading in the globals pane, by its label** —
    -- `~6n5qb`. The label and not an index: the groups are rebuilt from the
    -- session on every frame and a module loaded mid-session reorders them, so
    -- a click carrying a position would fold whichever group had moved into it.
  | ModuleRow String
    -- ^ **one module's row in the modules pane, by the name it is spelled
    -- with** — `~nf5tx`. A row of its own rather than arithmetic off the pane's
    -- 'Location': brick dispatches a click to the last extent reported under
    -- the pointer and a row inside the viewport is reported after the pane, so
    -- the row wins and the pane's accent-bar drag is untouched — that bar is
    -- outside the viewport.
  | StripVP
    -- ^ **the suggestion strip's own viewport and clickable extent** —
    -- `~w2tk2` slice 1. Not @PaneVP@ with a tenth 'Tui.Layout.Pane' in it:
    -- see 'Tui.Layout.Strip' for why the strip is not one, and note that
    -- every function keyed on 'PaneVP' — 'resizablePanes', 'barRightOf',
    -- 'paneWidthOf' — asks a question about /columns/ that has no answer
    -- here.
  | StripReply
    -- ^ **the reply row's own clickable extent and editor name** —
    -- `~w2tk2` slice 5. A click here is what opens it; see 'stStripReply'.
  | LoadPopup
  | OfferPopup
  | PickerVP
  deriving (Eq, Ord, Show)

-- | One committed line of a live script, and **the whole session it
-- produced** — not a delta, not an undo count.
--
-- **`:undo` is deliberately not used to rewind a script, and this was
-- measured rather than assumed** (his spec's Priority 0: *"simply doing
-- `:undo` might be enough (make sure of that)"*). It is not enough.
-- `Snapshot` excludes `globals` on purpose — §7.7, the environment only ever
-- grows — so an `:undo` past a @data@ or a @qed@ rewinds the development and
-- leaves the declaration standing. Checked directly through 'oneLine':
-- declare @Nat@, declare @Foo@, `:undo`, and @:show Foo@ still prints @Foo@.
-- A document rewound that way would be describing a session that does not
-- exist.
--
-- A 'Session' is an immutable value and 'oneLine' is pure, so holding one per
-- line costs only what actually differs between them, and rewinding is
-- indexing rather than replaying. The same check from the stored session
-- reports @nothing named Foo has been declared@, which is the truth the
-- document needs. **It also means a script is editable along its whole
-- length** — the `qed` wall that bounds `:undo` is simply not in this path.
data ScriptLine = ScriptLine
  { slText    :: String
    -- ^ exactly what will be written to the @.thena.script@.
  , slSession :: Maybe Session
    -- ^ the session after this line ran; **unchanged from the line before
    -- when the engine refused it**, which is what lets a refused line stay
    -- in the document without lying about the state beneath it.
    --
    -- **'Nothing' is a line of the document that has not been run in this
    -- session** — @~22qjj@. It is text and nothing else: opened from a
    -- `.thena.script` on disc, or left below the caret by a reload. The
    -- engine's own record only ever holds lines that were submitted, so there
    -- is nowhere else for these to live; `Session` is opaque and `flattened`
    -- is not exported, which is the design saying the same thing.
    --
    -- **The sessions form a prefix**: lines @[0, F)@ have run and @[F, n)@
    -- have not, for the frontier @F@ 'scriptFrontier' reads off. Every
    -- rebuild in this module is written to keep that true — it is what makes
    -- "the session above this line" a lookup rather than a search.
  , slRan     :: Maybe String
    -- ^ **the text that produced 'slSession'**, so that a line which has been
    -- edited since it ran can be told from one that has not — `~htff2`, his
    -- requirement of 2026-11-18: an edit he walks away from stays as he left
    -- it, the line goes dim because it is no longer evaluated, and the
    -- cascading re-run takes the new text.
    --
    -- **It is the text and not a flag**, so the question /is this line stale/
    -- is a comparison and cannot drift: typing a character and deleting it
    -- again leaves the line equal to what ran, and it is not stale, with
    -- nothing to reset. 'Nothing' for a line that has never run, which is
    -- never stale either — there is no session under it to disagree with.
  , slOutput  :: [String]
  , slOk      :: Bool
  }

-- | **A tail re-run in flight, off the keypress** — `~twdbp`, his ruling of
-- 2026-11-18: report progress on a background thread rather than freeze the
-- terminal for the run, which measured 9.6s–25.2s on his own machine with
-- nothing on screen to say so. 'Nothing' in 'stRerun' is the ordinary state;
-- a document-editing key is refused while this is 'Just' ('handleEventForKeys'),
-- so only one re-run is ever in flight and nothing races it.
data RerunState = RerunState
  { rrGen     :: Int
    -- ^ bumped every time a re-run starts. A posted 'RerunStep' whose
    -- generation disagrees is a straggler nothing is waiting on any more —
    -- the same role 'stJevGen' plays for a ranking answer.
  , rrAt      :: Int
    -- ^ the document index the batch starts at. Everything before it in
    -- 'stScript' is untouched for as long as this is 'Just'.
  , rrPending :: [ScriptLine]
    -- ^ the batch's lines exactly as they stood the instant the re-run
    -- started — already dim, a 'Nothing' session, their own text. A posted
    -- step's completed prefix replaces a prefix of this; the rest keeps
    -- showing as it did, which is what makes a line nothing has reached yet
    -- indistinguishable from one that was always going to wait.
  , rrUnrun   :: [ScriptLine]
    -- ^ whatever came after the batch — never touched by this re-run,
    -- appended back unchanged at every step.
  , rrFinish  :: [ScriptLine] -> EventM Name St ()
    -- ^ what the call site already did with 'foldRun''s result before this
    -- existed — 'reseated', 'loadScriptAt', or a plain splice. Runs once,
    -- when the whole batch has an answer.
  , rrShow    :: Bool
    -- ^ **the half-second threshold has passed and it is worth saying so**
    -- — his requirement of 2026-11-18. 'False' throughout a re-run that
    -- finishes quickly, which never draws the foot note or the '>' marker
    -- at all.
  }

-- | A fresh line nothing has run yet, for text with no existing 'ScriptLine'
-- to start from — the same shape 'unran' leaves one in.
freshPending :: String -> ScriptLine
freshPending t = ScriptLine t Nothing Nothing [] True

-- | One completed round: the line that was run (absent for the startup
-- trouble dump and the `:theme`/`:fold` pseudo-commands, which never echoed
-- what was typed even before this) and the output lines it produced.
data Turn = Turn
  { turnPrompt :: Maybe String
  , turnOutput :: [String]
  , turnSession :: Session
    -- ^ **the session this turn left behind** — `~hxzjq`, his instruction of
    -- 2026-11-19: /"ctr + l, when removing a command that change the
    -- machine-state\/proof-state, does not revert to a previous snapshot. It
    -- should."/
    --
    -- **The session AFTER the turn's line ran, not before it.** Taking @n@
    -- turns off the transcript then restores the session of the turn that is
    -- now last, which is the state the screen is left showing — and with
    -- every turn gone it is the launch session, which is why 'stSession0'
    -- exists. Storing the state before each line would answer the same
    -- question with an off-by-one and no gain.
    --
    -- **A 'Session' is an immutable value and the turns share their
    -- structure**, so a transcript of a hundred turns holds a hundred
    -- references and not a hundred copies.
  }

-- | The live `:load` completion dropdown — his request 2026-09-29: appears
-- the moment the line matches `:load `, updates on every keystroke, an
-- arrow key moves 'ldSelected' rather than the text cursor. 'Nothing' means
-- no dropdown at all (wrong prefix, no directory, or nothing left to
-- suggest), not an empty one — 'draw' never has to render a dropdown with
-- zero rows.
data LoadDropdown = LoadDropdown
  { ldEntries  :: [String]
  , ldSelected :: Maybe Int
  }

-- | One row of the completion dropdown, drawn from a 'SymbolView'.
--
-- **Only a literal is text to type** — a scan class or a nonterminal names a
-- *kind* of thing that may stand here ('Operand:Core', '‹name›'), not
-- characters an accept could insert, so 'rowInsert' is 'Nothing' for those
-- and the row is shown but never lands under 'odSelected'.
data OfferRow = OfferRow
  { rowLabel  :: String
  , rowInsert :: Maybe String
  }
  deriving (Eq)

-- | The live completion dropdown driven by 'Thena.View.statementOfferView'
-- — recomputed on every keystroke a line that isn't a colon command
-- produces, same as the module header says.
data OfferDropdown = OfferDropdown
  { odRows       :: [OfferRow]
    -- ^ every candidate, alphabetised within its own group (tokens before
    -- productions — see 'buildOfferDropdown') — the popup scrolls
    -- ('OfferPopup') rather than capping the list and stranding the rest
    -- behind an unreachable "+N more".
  , odSelected   :: Maybe Int
    -- ^ an index into 'odRows', but only ever one whose 'rowInsert' is
    -- 'Just' — see 'offerMoveDown'/'offerMoveUp'.
  , odWordStart  :: Int
    -- ^ the column an accepted row replaces from. The recovered unit's own
    -- start when recovered; the cursor's own column otherwise, since the
    -- ordinary path only ever offers something to insert, never something
    -- partially typed to replace.
  , odReplaceLen :: Int
    -- ^ how many characters after 'odWordStart' an accept removes — the
    -- recovered text's own length when recovered; one placeholder character
    -- when the cursor sits on a box ('offeredReplaces'); zero otherwise.
  , odJevPicked :: Int
    -- ^ how many leading 'odRows' are Jev's own picks, floated to the top
    -- of the whole list by 'floatJevPicks' — crossing "tokens before
    -- productions" on purpose, his call, 2026-10-29: *"Jev's top three
    -- pick can be anything Jev wants."* Zero on a freshly built dropdown
    -- (every keystroke) until an answer actually lands; 'offerRowToPopup'
    -- reads it to colour exactly that many rows and no more.
  }

-- | **What the engine is offering for the line as it stands, and nothing at
-- all about whether a popup is on screen** — `~3gn2r`, his correction of
-- 2026-11-19: /"the suggestion pane is not supposed to hide and appear the
-- suggestions together with the dropdown, they are always supposed to be
-- there when available."/
--
-- **It exists because the strip read 'stOfferDropdown', and that field means
-- two things at once**: what the engine offers, and whether the completion
-- popup is up. The second is what 'submitted' clears on every Enter and what
-- Esc's second press clears — so the strip went blank for reasons that were
-- about an element that is switched off. **Concretely**: submit @:show Nat@
-- and the strip is empty with every op in the language available; type one
-- character and nine options appear, with nothing about the session changed
-- between the two frames.
--
-- **The dropdown is a slate plus a highlight; the strip is the slate with no
-- highlight at all.** So this carries the rows and the accept geometry and no
-- selection — there is nothing in the strip to select, which is his design
-- and not an omission ('draw''s grid lights no cell).
--
-- **Filtered to rows with something to insert**, which is the filter
-- 'stripSlateOf' used to apply itself: a row that cannot be accepted has no
-- business occupying a numbered slot. Since `~bkzw9` the engine's offers are
-- all insertable, so it is a guard and not a policy.
data Slate = Slate
  { slateRows :: [OfferRow]
    -- ^ every insertable candidate, in the order 'buildOfferDropdown' puts
    -- them in (tokens before productions), Jev's picks floated to the top
    -- once an answer has landed ('applyJevRanking').
  , slateStart :: Int
    -- ^ the column an accepted row replaces from — 'odWordStart's own
    -- arithmetic, since it is literally that value.
  , slateReplaceLen :: Int
    -- ^ how many characters after 'slateStart' an accept removes —
    -- 'odReplaceLen'.
  , slateJevPicked :: Int
    -- ^ how many leading 'slateRows' are Jev's own picks. **Nothing draws it
    -- yet** — the strip lights no cell — and it is carried so that the
    -- strip's order and the dropdown's can never explain themselves
    -- differently.
  }

-- | **Nothing is offered here**: a `:load` path line, whose offers are a
-- directory listing and 'stDropdown''s own business, or a line the statement
-- grammar answers nothing for.
emptySlate :: Slate
emptySlate = Slate [] 0 0 0

-- | **The stored sessions, as a thing you move a highlight through** — `~xf2hv`,
-- his instruction, 2026-11-12: /"the session selection shouldn't be done by
-- `:script sessions` printing a static list and the user having to re-type its
-- identifier. That should be some dialog with a selectable sessions."/
--
-- **It is the TUI's first modal, and the reason is selection and not typing.**
-- 'scriptSave' says in its own haddock that the command bar retired the modal
-- his spec once wanted — and that still holds, because what the bar gives you
-- is somewhere to *type*. A list you pick a row out of is the other thing: the
-- bar has one row to draw and no way to highlight one of nine sessions in it.
--
-- **The rows are the index's own order, and 'pkSelected' opens on the last of
-- them.** That order is not "newest first" — it is least-recently-touched
-- first: 'persist' writes the index as @[everything else] <> [this session]@,
-- so every save moves its own entry to the end. The last row is therefore the
-- session you were in most recently, which is the one a picker should open on,
-- and the rows above it are a history in the order you left them.
data Picker = Picker
  { pkFor      :: PickerFor
    -- ^ never empty: with nothing to select the command that would open the
    -- dialog says so in the transcript instead of opening one onto an empty
    -- list.
  , pkSelected :: Int
    -- ^ an index into 'pkFor''s rows, always in range — 'pickerMove' clamps
    -- rather than wrapping, so Up at the top and Down at the bottom are
    -- no-ops and the highlight cannot be lost off either edge.
  }

-- | **What a picker is picking** — one dialog, two lists.
--
-- `~w2tk2` slice 6 added the second, and **his instruction was that it be
-- the first one again**: /"make it navigable by arrow keys, like session and
-- selectable by enter."/ So the widget, the keys, the scrolling, the clamp
-- and the box are shared outright rather than reimplemented beside each
-- other — what differs is the rows, the title, and what Enter does with the
-- row it is on, and those are the three functions below.
data PickerFor
  = PickSession [Stored]
  | PickModel [HintModel]

-- | How many rows there are, whichever list it is — the one number the keys
-- clamp against.
pickerCount :: Picker -> Int
pickerCount pk = case pkFor pk of
  PickSession rows -> length rows
  PickModel rows -> length rows

-- | **A pane being pulled wider or narrower by its accent bar** — `~gs8tj`,
-- his request of 2026-11-12: /"can you make the panes resizeable by
-- mouse-pulling on the 'accent bar'? Each one independently, but make it
-- 'snapping' to some 'steps'."/
--
-- **Latched on the press and read until the release.** The pane under the
-- pointer changes as a drag proceeds — and so does the pane's own left edge,
-- since widening the widest pane of a column moves that column left — so
-- neither can be used to work out how far the pointer has travelled. What
-- does not move is the column the press landed on and the width the pane had
-- then; every frame of the drag is computed from those two numbers.
data Drag = Drag
  { dragPane  :: Pane
  , dragFrom  :: Int
    -- ^ the absolute screen column the press landed on.
  , dragWidth :: Int
    -- ^ the pane's width at the moment of the press.
  , dragWhole :: Bool
    -- ^ **Option was held at the press, so the whole column moves as one** —
    -- `~t927j`, his instruction of 2026-11-13. Latched here with the rest of
    -- the drag rather than read off each motion report: a modifier that
    -- stopped arriving part-way through a drag would split one gesture into
    -- two, and the press is the moment he decided which gesture this is.
  }

-- | **The suggestion strip being pulled taller or shorter by its accent
-- bar** — `~w2tk2` slice 1, and slice 5's /"we just let the user resize the
-- pane upwards taking space from the main prompt\/script"/ is the gesture
-- this is.
--
-- **Latched on the press, for the same reason 'Drag' is**: the strip's own
-- top edge moves as it grows, so neither it nor the widget under the pointer
-- can say how far the pointer has travelled. What does not move is the row
-- the press landed on and the height the strip had then.
--
-- **A row and not a column, which is the whole difference from 'Drag'.**
-- Pulling the bar /up/ grows the strip, because the bar travels up with the
-- strip's own top edge — so the edge follows the pointer, the same property
-- 'resizeTo' has sideways.
data StripDrag = StripDrag
  { sdFrom :: Int
    -- ^ the absolute screen row the press landed on.
  , sdRows :: Int
    -- ^ the strip's content height at the moment of the press.
  }

data St = St
  { stTurns       :: [Turn]  -- ^ forward chronological — oldest first, an
                              -- append-only document, his correction 2026-09-29
  , stInput       :: Editor Text Name
  , stSession     :: Session
  , stSession0    :: Session
    -- ^ **the session as the TUI launched with it** — `~hxzjq`. What
    -- @:clear@ restores when it takes the last turn off the transcript and
    -- there is no earlier one to go back to. Never written after 'runTui'
    -- builds the state: a reload replaces the whole 'St'.
  , stTheme       :: Theme
  , stFoldOn      :: Bool
  , stDropdown    :: Maybe LoadDropdown
  , stOfferDropdown :: Maybe OfferDropdown  -- ^ mutually exclusive with
                                              -- 'stDropdown' by construction
                                              -- (a colon line never reaches
                                              -- 'refreshOfferDropdown'; a
                                              -- non-colon line never reaches
                                              -- ':load''s), never enforced
                                              -- as an invariant beyond that
  , stSlate :: Slate
    -- ^ **the suggestion strip's own source, and never the dropdown's
    -- state** — `~3gn2r`. Recomputed from the session and the line wherever
    -- 'stOfferDropdown' is ('refreshOfferDropdown'), and also at every place
    -- the dropdown is deliberately closed while the offers themselves have
    -- not gone anywhere: 'submitted' on every Enter, 'closeDropdowns' on a
    -- mode switch. **It is never cleared by a dismissal**, which is the whole
    -- of what the item asked for.
  , stInputExtent :: Maybe (Extent Name)  -- ^ looked up post-render, one
                                             -- frame behind — 'Brick.Main'
                                             -- has no way to ask for an
                                             -- extent mid-'draw'
  , stStripWidth :: Maybe Int
    -- ^ **how wide the suggestion strip's content was in the last frame
    -- drawn** — `~w2tk2` slice 3a, same post-render lag as 'stInputExtent'
    -- and for the same reason. The grid's shape is a function of this
    -- ('Tui.Layout.stripGrid'), and the keymap has to know the same shape the
    -- drawing worked out, or an F-key lands on a cell that is not there.
    -- 'Nothing' before the first frame and while the strip is closed.
  , stPaneExtent :: Maybe (Extent Name)  -- ^ same lag, the repl pane's own
                                             -- viewport bounds, needed to
                                             -- decide whether the dropdown
                                             -- has room below the caret
  , stArrowsReleased :: Bool
    -- ^ **Esc's first step gave Up/Down back to the document.** 'stDismissed'
    -- cannot carry this: the two-step Esc (his `.jalivert/TUI.md` #14) clears
    -- the *highlight* first and only hides the *list* on the second press, so
    -- between the two the dropdown is open with nothing selected — which is
    -- also exactly the state a fresh dropdown is in under `:preselect off`.
    -- Without a flag the two are indistinguishable, and 'navigateCompletion'
    -- has to choose one behaviour for both: either Up re-grabs the keys after
    -- an Esc (his report, 2026-10-20) or `:preselect off` can never reach a
    -- row by keyboard at all. Cleared by any edit, same lifetime as
    -- 'stDismissed'.
  , stDismissed :: Maybe String
    -- ^ Esc hid the dropdowns while the input read this (his
    -- `.jalivert/TUI.md` #14) — 'Nothing' while they show. Refresh keeps
    -- them hidden while the line is unchanged, and any edit brings them
    -- back.
  , stRecoveredSpan :: Maybe (Int, Int)
    -- ^ what 'renderInputContent' underlines — his `.jalivert/TUI.md` #7, a
    -- visible cue that the line (or the literal under the cursor) will not
    -- run as written. Computed alongside 'stOfferDropdown' in
    -- 'refreshOfferDropdown', 'Nothing' wherever that is (a `:` line, or
    -- nothing offered) — see 'recoveredSpan'.
  , stAutoSelect :: Bool
    -- ^ `:preselect on|off` (his `.jalivert/TUI.md` #23) — whether a freshly
    -- shown dropdown highlights its first candidate on its own. 'True' is
    -- the standing behaviour (his `.jalivert/TUI.md` #9); this only lets him
    -- turn it off and back on, not a change of default.
  , stWhisperOn :: Bool
    -- ^ `:whisper on|off` (his `.jalivert/TUI.md` #23) — whether
    -- 'ghostAt' ever shows anything. 'True' is the standing behaviour
    -- (`.jalivert/TUI.md` #17/#21); same as 'stAutoSelect', a toggle on top
    -- of the default, not a new one.
  , stConfirmQuit :: Bool
    -- ^ `:confirm-quit on|off`, his instruction of 2026-11-18 — whether
    -- quitting with a script session that was never saved, or saved and
    -- then changed, is caught and asked about first. 'True' is the default;
    -- same shape as 'stAutoSelect' and 'stWhisperOn', a toggle on top of it.
  , stQuitArmed :: Bool
    -- ^ **the one warning has already fired, so the next quit attempt goes
    -- through.** Set when 'maybeQuit' holds a quit back; cleared by
    -- 'afterScriptEdit', so any further edit re-arms the check rather than
    -- leaving a stale "quit again" live over new, different unsaved work.
  , stHistory :: [String]
    -- ^ every line actually submitted, oldest first — 'recordHistory'
    -- appends, blank lines and an immediate repeat of the last entry
    -- excluded. In-memory only, this session's own; not the dotfile
    -- 'Tui.Config' persists, and not asked for.
  , stHistoryPos :: Maybe Int
    -- ^ 'Nothing' while editing live; 'Just i' while Up/Down is browsing
    -- 'stHistory', @i@ the index currently loaded into 'stInput'. His
    -- ruling on the dropdown/history conflict, 2026-09-30: Up/Down still
    -- browses an open dropdown first exactly as it always has
    -- ('navigateCompletion'); history only takes the keys once nothing is
    -- left to navigate there (Esc, or nothing offered).
  , stScriptMode :: Bool
    -- ^ live-script mode (`~5vtt3`), entered with `:script`. The repl pane
    -- stops being an append-only transcript and becomes the script itself:
    -- what you type *is* the document, and the caret moves into it.
  , stScript :: [ScriptLine]
    -- ^ the committed script, oldest first. Survives toggling the mode off
    -- and back on — discarding someone's script on a stray keypress is a bad
    -- failure mode, so leaving the mode only hides it.
  , stRerun :: Maybe RerunState
    -- ^ **a tail re-run in flight off the keypress** — `~twdbp`, see
    -- 'RerunState'. 'Nothing' almost always; see 'rerunTail'.
  , stRerunGen :: Int
    -- ^ the last generation handed to a re-run, bumped by 'rerunTail' every
    -- time one starts — same role 'stJevGen' plays for a ranking request.
  , stShipped :: [FilePath]
    -- ^ Thena's own prelude and standard base, as absolute paths, read once
    -- at boot. **The modules pane needs them to tell his files from ours**
    -- (`~t7wc8`) and 'draw' cannot ask: 'preludePath' is IO. The staleness
    -- check asks the same question at reload time and does its own call,
    -- which is fine there and would not be in a redraw.
  , stScriptBase :: Maybe Session
    -- ^ **the session live-script mode started from, and it is a fresh one**
    -- — his ruling: entering the mode does not inherit the ordinary REPL's
    -- session. 'Nothing' until the mode is first entered, since booting one
    -- is IO. Rewinding to line 0 means rewinding to this.
  , stScriptPos :: Maybe Int
    -- ^ 'Nothing' while composing a new line past the end; @'Just' i@ while
    -- the caret stands *on* committed line @i@, whose text is loaded into
    -- 'stInput' for editing in place. **Not 'stHistoryPos' wearing a
    -- different name**: history recalls text and never touches the entry it
    -- came from, where this edits the document and rewinds the session with
    -- it.
  , stScriptDraft :: String
    -- ^ the new-line text Up interrupted, same job as 'stHistoryDraft'.
  , stScriptBar :: Maybe (Editor Text Name)
    -- ^ the command bar, his own design call: **nothing typed in the
    -- document is ever a command**, so a command needs somewhere else to be
    -- typed. Summoned (F12, or Ctrl+X), one line, closes on Enter or Esc.
    -- 'Nothing' when it is not showing — a permanent input row at the pane's
    -- foot reads as a second REPL, which is exactly the confusion it exists
    -- to prevent.
  , stScriptNote :: Maybe String
    -- ^ what the bar last had to say — a refusal, or a saved path. Shown at
    -- the pane's foot until the next thing happens.
  , stStored :: Maybe Stored
    -- ^ **the index entry the live document is persisted under** — `~22qjj`,
    -- the project database. 'Nothing' before live-script mode has ever been
    -- entered, since there is no document to persist and no reason to write a
    -- file into somebody's project for a session they have not started.
    --
    -- **It holds the entry rather than the whole index**: every save re-reads
    -- the index, replaces this one entry and writes it back, so two TUIs open
    -- on the same project do not drop each other's sessions, and there is no
    -- second copy of the index to keep true.
  , stGlobalsClosed :: Set.Set String
    -- ^ **the globals pane's namespaces that are folded** — `~6n5qb`, his
    -- instruction of 2026-11-12, and clicking a heading toggles one.
    --
    -- **It holds what is CLOSED, where 'stModulesOpen' holds what is open**,
    -- and the two are opposite because their defaults are. A module's
    -- unfinished list starts folded — there is usually nothing in it — while a
    -- namespace starts unfolded, because the pane exists to show what is in
    -- scope and must not open saying nothing is. **In both cases the set holds
    -- the deviation from the default**, so an empty set is the pane as it was
    -- before this feature.
    --
    -- **Nothing prunes it.** A label left here after its module is gone costs a
    -- string, and means the group is still folded if that module comes back.
  , stModulesOpen :: Set.Set String
    -- ^ **the modules whose unfinished list is unfolded** — `~nf5tx`, his
    -- instruction of 2026-11-13, and clicking the row toggles one. A set and
    -- not a single selection: he can have two broken modules open at once, and
    -- nothing here is a cursor.
    --
    -- **A module that stops being partial simply stops being drawn unfolded.**
    -- Nothing prunes this set — a name left in it after the module loads whole
    -- costs a string and means the fold is still open if it breaks again.
  , stLayout :: Layout
    -- ^ **which panes are on screen and at which of the six positions** —
    -- `~fxc89`, his instruction of 2026-11-12. 'Tui.Layout.defaultLayout' is
    -- the screen exactly as it was before the command existed, so nothing
    -- moves until he types @:pane@.
    --
    -- **It is not persisted, and that is `~vqsd8`'s question rather than a
    -- separate one.** That item is the pane *widths* not surviving a restart
    -- and it names three places they could live; a position is the same
    -- question about the same panes and takes the same answer whenever he
    -- gives it.
  , stDefaultWidths :: Map.Map Pane Int
    -- ^ **the widths 'appStart' derived from the terminal, kept so that a
    -- width he CHOSE can be told from one he merely got** — `~vqsd8`.
    -- 'configOf' writes only the difference, which is what stops an untouched
    -- pane being frozen at the first terminal's arithmetic.
    --
    -- **Not a second source of truth for drawing.** Nothing reads this but
    -- 'configOf'; 'stPaneWidths' is still the only map the clamp and the
    -- drawing consult.
  , stPaneWidths :: Map.Map Pane Int
    -- ^ **how wide each pane is, in columns** — `~gs8tj`. Keyed by the pane
    -- and filled over every pane there is, closed ones included, so a pane
    -- closed and opened again comes back the width he pulled it to.
    -- Filled at startup from the terminal's own width ('defaultPaneWidth')
    -- and then only ever by a drag, so a pane he has pulled to a width keeps
    -- it; a pane he has not is the width it always was.
    --
    -- **Absolute columns rather than a percentage, and that is the point of
    -- the feature**: a percentage is a rule about the screen, and what he
    -- asked for is a width he chose. 'draw' shrinks them proportionally if
    -- the terminal is too narrow to honour them, and does not write that back.
  , stDrag :: Maybe Drag
    -- ^ a resize in progress — see 'Drag'. 'Nothing' between drags, which is
    -- almost always.
  , stStrip :: Strip
    -- ^ **the suggestion strip: whether it is on screen, and how tall** —
    -- `~w2tk2` slice 1. Persisted, like the layout and the widths.
  , stStripDrag :: Maybe StripDrag
    -- ^ the strip being pulled taller or shorter — see 'StripDrag'. **A
    -- field of its own and not 'stDrag'**: a 'Drag' latches a pane and a
    -- /column/, and the strip has neither; the two gestures also cannot be
    -- in flight at once, which is an invariant the separate fields make
    -- plain rather than one a shared field would have to keep.
  , stDropdownOn :: Bool
    -- ^ **whether the completion dropdown appears and takes keys at all** —
    -- `~492hq`, his sequencing ruling of 2026-11-19: /"The dropdown will be
    -- disabled pretty much immediately as we start working. It will however
    -- not be deleted right away."/ @:dropdown on|off@, persisted, the same
    -- shape as 'stAutoSelect' and 'stWhisperOn'.
    --
    -- **Off means it stops appearing and stops taking keys, and nothing
    -- more.** Its rows are still built, 'stOfferDropdown' is still the
    -- strip's own source, @:preselect@ still toggles, and every attr and
    -- test it has stays — which is exactly the state his ruling asks for
    -- between \"disabled\" and the deletion he has not authorised.
  , stJevOn :: Bool
    -- ^ **whether Jev is asked at all** — `~zttnz`, his instruction of
    -- 2026-11-19. @:jev on|off@, persisted, the same shape as
    -- 'stDropdownOn'.
    --
    -- **Off means no request is ever sent** — not sent and discarded, not
    -- sent: 'scheduleJevRanking' returns at once, so nothing of his quota is
    -- spent and nothing can arrive late and renumber a cell.
    --
    -- **And the suggestion pane falls back to its own candidates in
    -- alphabetical order**, which is the one state where it shows a row Jev
    -- did not name. His rule — /"We don't show suggestions that are not from
    -- Jev"/ — is about the pane when Jev is answering; a switch that turned
    -- the pane off along with Jev would have been a different instruction
    -- from the one he gave.
  , stHint :: Maybe String
    -- ^ **what the suggestion strip's hint region is saying** — `~w2tk2`
    -- slice 4, his /"when it sees that the user is clearly taking the wrong
    -- turn in a proof (chosing to do induction on the wrong value), it could
    -- just give a hint"/.
    --
    -- **Nothing behind it yet, and that is the slice.** @:hint ‹text›@ puts
    -- a string here and @:hint@ alone takes it away, so the geometry — the
    -- region's floor, a long hint taking rows off the grid, the keymap
    -- agreeing with the grid that shrank — is real and measurable before any
    -- model exists to write one. Slice 6 replaces the command and not this
    -- field.
    --
    -- **Not persisted, unlike the four toggles above it.** A hint is
    -- content, not a preference: a sentence about the proof he was in last
    -- week has no business arriving with the dotfile.
    --
    -- **Nothing clears it but @:hint@** — not an Enter, not an Esc, not a
    -- mode switch. That is `~3gn2r`'s rule applied to the other half of the
    -- strip: a region that blanked itself whenever the dropdown would have
    -- closed would be empty in exactly the frames he is reading it.
  , stStripReply :: Maybe (Editor Text Name)
    -- ^ **the reply row's own editor, and the strip owns every key while it
    -- holds one** — `~w2tk2` slice 5, his instruction on who owns the
    -- keyboard: the suggestion strip, not the document. 'Nothing' until the
    -- row is clicked (it is drawn only while 'stHint' is 'Just', so there is
    -- never a row to click without one); 'handleStripReplyEvent' then takes
    -- every key the way 'handleBarEvent' already does for the command bar.
    --
    -- **What becomes of a submitted reply is slice 6's, not this one's** —
    -- there is no model on the other end yet to hand it to. Enter and Esc
    -- both close the row unused until there is; that is a stub, not a
    -- ruling, and it is the one thing slice 6 replaces here.
    --
    -- **Cleared along with whatever would otherwise orphan it**: a @:hint@
    -- that clears the hint, and a @:pane suggestions close@, both take the
    -- reply row's keyboard claim away with them. Without that a key typed
    -- after either would vanish into an editor nothing on screen names any
    -- more — the dead-key shape his `~sshbb` report already found once.
  , stPicker :: Maybe Picker
    -- ^ **the session picker, and while it is open it owns the keyboard** —
    -- see 'Picker' and 'handlePickerEvent'. It is the one widget in the TUI
    -- that is modal, and it is modal because Up, Down and Enter already mean
    -- three other things in each of the keyboards underneath it.
  , stEscRun :: Maybe String
    -- ^ **The only thing standing between a Shift+Enter and a corrupted
    -- proof line.** vty decodes neither of the two standard encodings and
    -- hands the bytes over as a 'V.KEsc' followed by the rest as literal
    -- characters — measured, not assumed, with a vty event dump under the
    -- pty: @ESC [ 13;2u@ (kitty) and @ESC [ 27;2;13~@ (xterm
    -- @modifyOtherKeys@, his own terminal) both arrive that way.
    --
    -- @'Just' p@ means an Esc was just handled and @p@ is the literal text
    -- seen since, still a prefix of one of those two sequences, held back
    -- rather than typed. A prefix that completes is swallowed whole; one
    -- that diverges is typed, in order, as though it had never been held.
    -- 'Nothing' is the ordinary state, where every character goes straight
    -- through.
    --
    -- **Anchored on the Esc, which is what makes it exact**: ordinary typing
    -- never follows an Esc with @[13;2u@, so nothing a user means to type is
    -- ever delayed by more than the one keystroke that diverges.
  , stHistoryDraft :: String
    -- ^ the live line 'historyBack' interrupted, restored by
    -- 'historyForward' on the way back past the newest entry — the same
    -- "what you were typing before you went looking" a shell keeps.
    -- Meaningless while 'stHistoryPos' is 'Nothing'.
  , stJevConfig :: Maybe JevConfig
    -- ^ loaded once at startup from @TYPESAFE_API_KEY@ — 'Nothing' turns
    -- the whole feature off, see 'Tui.Jev.loadJevConfig'. Never reloaded
    -- mid-session; there is no command that would need it to be.
  , stJevChan :: BChan AppEvent
    -- ^ so 'refreshOfferDropdown' can hand a background request somewhere
    -- to report back to — 'EventM' itself has no access to the channel
    -- 'runTui' gave 'customMain'.
  , stJevGen :: Int
    -- ^ bumped every time a ranking request is sent. 'applyJevRanking'
    -- drops an answer whose generation doesn't match — the candidate set
    -- it scored is not the one on screen any more, so it isn't a stale
    -- reordering of the same list, it's an answer to a question nobody is
    -- asking.
  , stModel :: Text
    -- ^ **the OpenRouter model id the hint region asks** — `~w2tk2` slice
    -- 6. Persisted ('Tui.Config.cfgModel'); set by @:model ‹id›@ or by Enter
    -- in the @:models@ picker.
  , stHintConfig :: Maybe HintConfig
    -- ^ loaded once at startup from @OPENROUTER_API_KEY@, the same shape as
    -- 'stJevConfig'. **Carries 'stModel' as it stood at startup**, so a
    -- @:model@ since then is read from 'stModel' at ask time rather than
    -- from here.
  , stModels :: Maybe [HintModel]
    -- ^ OpenRouter's catalogue once it has been fetched, and 'Nothing'
    -- until the first @:models@. **Held for the session**: 479 rows is
    -- about 900 KB and the list does not change while he is proving.
  , stHintAsking :: Bool
    -- ^ **a request is out** — HIS, 2026-11-19: /"there needs to be some
    -- visual que of when a new request is sent to the API"/. It is what the
    -- strip's label reads off, and it is also the guard that keeps Enter
    -- from firing a second ask on top of the first.
  , stHintAsked :: Int
    -- ^ how many asks this session, drawn beside the label — his /"I need
    -- to know how often it is asked"/. A count and not a log line, because
    -- the question is answered by glancing at the pane.
  , stJevPending :: Int
    -- ^ bumped every time a dropdown change schedules a ranking. A
    -- 'JevDue' timer whose generation doesn't match was superseded by a
    -- later keystroke while it slept, so 'handleJevDue' drops it and only
    -- the trailing edge of a burst ever reaches 'fireJevForCurrentDropdown'.
  }

stInputL :: Lens' St (Editor Text Name)
stInputL = lens stInput (\st i -> st { stInput = i })

emptyInput :: Editor Text Name
emptyInput = E.editorText Input (Just 1) Text.empty

runTui :: IO ()
runTui = do
  (s0, trouble) <- startingSession
  cfg <- loadConfig
  jevCfg <- loadJevConfig
  hintCfg <- loadHintConfig (Text.pack (cfgModel cfg))
  shipped <- shippedPaths
  chan <- newBChan 16
  let theme0 = maybe neonPinkDark id (themeByName (cfgTheme cfg))
      autoSelect0 = cfgAutoSelect cfg
  let st0 = St
        { stTurns       = case concatMap (renderTrouble s0) trouble of
            []  -> []
            out -> [Turn Nothing out s0]
        , stInput       = emptyInput
        , stSession     = s0
        , stSession0    = s0
        , stTheme       = theme0
        , stFoldOn      = True
        , stDropdown    = Nothing
        -- The input opens with its dropdown already up (his
        -- `.jalivert/TUI.md` #14): the empty line offers the full rule
        -- list, first row lit — the same state deleting back to empty
        -- reaches.
        , stOfferDropdown = buildOfferDropdown autoSelect0 0 (statementOfferView s0 [] [])
        -- The strip's own source, from the same view — `~3gn2r`. Built here
        -- rather than left empty for the first keystroke to fill, because
        -- the strip is open on launch for anyone whose dotfile had it open.
        , stSlate       = slateFromView 0 (statementOfferView s0 [] [])
        , stDismissed   = Nothing
        , stRecoveredSpan = Nothing
        , stAutoSelect  = autoSelect0
        , stWhisperOn   = cfgWhisperOn cfg
        , stConfirmQuit = cfgConfirmQuit cfg
        , stQuitArmed   = False
        , stHistory     = []
        , stHistoryPos  = Nothing
        , stHistoryDraft = ""
        , stScriptMode  = False
        , stScript      = []
        , stRerun       = Nothing
        , stRerunGen    = 0
        , stShipped     = shipped
        , stScriptBase  = Nothing
        , stScriptPos   = Nothing
        , stScriptDraft = ""
        , stScriptBar   = Nothing
        , stScriptNote  = Nothing
        , stStored      = Nothing
        , stGlobalsClosed = Set.empty
        , stModulesOpen = Set.empty
        , stLayout      = cfgLayout cfg
        , stDefaultWidths = Map.empty
          -- **The stored widths start here and 'appStart' fills the gaps**,
          -- because the terminal's width is not known until there is a vty.
        , stPaneWidths  = Map.fromList (cfgWidths cfg)
        , stDrag        = Nothing
        , stStrip       = cfgStrip cfg
        , stStripDrag   = Nothing
        , stDropdownOn  = cfgDropdownOn cfg
        , stJevOn       = cfgJevOn cfg
        , stPicker      = Nothing
        , stEscRun      = Nothing
        , stInputExtent = Nothing
        , stStripWidth  = Nothing
        , stHint        = Nothing
        , stStripReply  = Nothing
        , stPaneExtent  = Nothing
        , stArrowsReleased = False
        , stJevConfig   = jevCfg
        , stJevChan     = chan
        , stJevGen      = 0
        , stJevPending  = 0
        , stModel       = Text.pack (cfgModel cfg)
        , stHintConfig  = hintCfg
        , stModels      = Nothing
        , stHintAsking  = False
        , stHintAsked   = 0
        }
  -- One synthetic event after startup: extents only exist once something
  -- has rendered, so the launch dropdown cannot position on the very first
  -- frame — this tick runs the outer wrapper (which records them) without
  -- touching anything, and the second frame lays out against real
  -- measurements. A single delayed write, then the thread is done; if the
  -- first draw somehow hasn't happened yet, the tick is a harmless no-op
  -- and the dropdown arrives on the first keystroke as before.
  _ <- forkIO (threadDelay 200000 >> writeBChan chan Tick)
  declareWideGlyphs
  vty <- mkVty V.defaultConfig
  _ <- customMain vty (mkVty V.defaultConfig) (Just chan) app st0
  resetCursorStyle

-- | **Tell vty that the mark glyphs are two columns wide, because it thinks
-- they are one and the terminal does not** — `~8ztt3`, from his report of
-- 2026-11-13: /"the new symbol for ✅ next to the prelude moves the accent bar
-- of the next pane to the right."/
--
-- **Why, in one line, with the whole of it on 'Tui.Panes.wideGlyphs'**: vty's
-- built-in table calls those glyphs one column, a terminal spends two on them,
-- and the difference shoves the rest of the row — the neighbouring pane's
-- accent bar included.
--
-- **So vty is told.** 'V.installUnicodeWidthTable' takes a run-length table and
-- vty allocates it across the whole code-point space, **falling back to its
-- built-in table for every code point a range does not cover** — so three
-- ranges change three characters and nothing else. It must run before
-- 'mkVty', which installs the user's own table if one is configured and
-- **skips its own install when a table is already there**, catching everything;
-- so this cannot stop the TUI from starting.
--
-- **It declares what his terminal demonstrably does.** The misalignment he
-- reported is only possible if his terminal draws ✅ in two cells, so 2 is the
-- measured value here and not a guess at one. A terminal that drew them in one
-- cell would be misaligned by this — see `.claude/CLOSEOUT.md`.
--
-- **'Tui.Panes.wideGlyphs' is the list, and it lives beside the glyphs it is
-- about** so that adding a mark and declaring its width cannot come apart.
declareWideGlyphs :: IO ()
declareWideGlyphs =
  void (try @SomeException (installUnicodeWidthTable table))
  where
    table = UnicodeWidthTable (map wide wideGlyphs)
    wide cp = WidthTableRange (fromIntegral cp) 1 2

-- | The custom event channel carries the synthetic post-startup tick
-- (handled by doing nothing — the outer wrapper around every event still
-- records the fresh extents), a Jev debounce timer coming due, tagged with
-- the pending generation it was scheduled for ('stJevPending',
-- 'handleJevDue'), a Jev ranking answer, tagged with the
-- generation it was asked for ('stJevGen', 'applyJevRanking'), and a step
-- of a tail re-run coming due off 'rerunTail''s background thread: the
-- generation it was started under, the batch's result so far, whether the
-- half-second threshold has passed, and whether this is the final step.
data AppEvent
  = Tick
  | JevDue Int
  | JevRanked Int (Either String (Map.Map Text Double))
  | RerunStep Int [ScriptLine] Bool Bool
  -- | **The model's answer to one ask** — `~w2tk2` slice 6. **No
  -- generation tag, unlike 'JevRanked'**, and that is not an oversight: Jev
  -- fires on a keystroke, so an earlier answer can land after a later one
  -- and has to be dropped. A hint is fired by Enter and only ever by Enter
  -- ('stHintAsking' refuses a second while one is out), so there is never
  -- more than one in flight and nothing to put in order.
  | HintAnswered (Either String Text)
  -- | OpenRouter's catalogue, with the filter the `:models` that asked for
  -- it carried — so the picker opens on the rows he asked for rather than
  -- on all 479 and a second command.
  | ModelsListed Text (Either String [HintModel])

app :: App St AppEvent Name
app = App
  { appDraw         = draw
  , appChooseCursor = showFirstCursor
  , appHandleEvent  = handleEvent
  , appStartEvent   = appStart
  , appAttrMap      = attrs . stTheme
  }

-- | Two terminal-mode requests made once, at startup: mouse reporting
-- ("no matter where the focus is" — his words, 2026-09-29, which needs
-- mouse mode on at the terminal, not just clickable widgets) and a
-- blinking caret — his `.jalivert/TUI.md` item 9, "why is it still and
-- solid?" Checked directly in vty's own source before writing anything:
-- vty never emits a cursor-*style* request, only show/hide/position, so
-- whatever style the caret has is purely inherited from the terminal's own
-- last-set state — easy to end up "steady" if some other program left it
-- that way and never reset it. Asking explicitly (DECSCUSR, @ESC[1 q@)
-- makes this program's own preference the one that actually applies;
-- 'resetCursorStyle' undoes it on the way out so thena-tui doesn't leave
-- the terminal modified for whatever runs next. Not independently verified
-- against a real terminal — worth confirming.
appStart :: EventM Name St ()
appStart = do
  vty <- getVtyHandle
  liftIO (V.setMode (V.outputIface vty) V.Mouse True)
  liftIO requestBlinkingCursor
  -- | **The six pane widths, from the terminal's real width** — `~gs8tj`.
  -- Here rather than in 'runTui' because this runs with a vty in hand and
  -- before the first frame is drawn, so nothing ever renders against an
  -- unfilled map.
  (w, _) <- liftIO (V.displayBounds (V.outputIface vty))
  st <- get
  -- | **A width restored from the dotfile wins; every other pane takes the
  -- terminal's** — `~vqsd8`. 'Map.union' is left-biased, and 'stPaneWidths'
  -- holds exactly what the dotfile had at this point, so this is the whole of
  -- the layering. **The clamp still applies on every frame**, which is what
  -- keeps a 60-column pane restored into an 80-column terminal sane.
  let derived = Map.fromList [(p, defaultPaneWidth w) | p <- allPanes]
  put st
    { stPaneWidths = Map.union (stPaneWidths st) derived
    , stDefaultWidths = derived
    }

-- | The panes a drag can resize: **the ones on screen, which is now a
-- question about 'stLayout' rather than a constant** — `~fxc89`. A closed pane
-- reports no extent, so it could not be hit in any case; reading the layout
-- is what keeps the clamp and the hit test agreeing with the drawing when he
-- moves a pane to the other column.
resizablePanes :: St -> [Name]
resizablePanes = map PaneVP . placedPanes . stLayout

-- | **@:pane ‹name› open ‹n›@ and @:pane ‹name› close@** — `~fxc89`, his
-- instruction of 2026-11-12 and his own two examples.
--
-- 'Nothing' for a line that is not a @:pane@ line at all, so the caller falls
-- through to whatever it did before; 'Just' with the layout unchanged and a
-- complaint for a @:pane@ line that does not parse, because a line that starts
-- with the word is his and must not be handed to the engine or written into a
-- document as a proof step.
--
-- **One function for both keyboards.** The REPL and live-script mode's command
-- bar each dispatch their own commands, and a command built twice is a command
-- that will eventually behave two ways.
paneCommand :: [String] -> Layout -> Strip -> Maybe (Layout, Strip, String)
paneCommand ws layout strip = case ws of
  -- | **The suggestion strip, which has no position** — `~w2tk2` slice 1.
  -- Three arms of its own rather than a 'Tui.Layout.Pane' that ignores its
  -- argument: the strip has exactly one place it can be, so @open@ takes
  -- nothing and @open ‹3›@ is a sentence to refuse rather than to honour by
  -- dropping half of it.
  [":pane", name, "open"] | name == stripName ->
    Just (layout, openStrip strip, stripName <> " open under the prompt")
  [":pane", name, "close"] | name == stripName ->
    Just (layout, closeStrip strip, stripName <> " closed")
  [":pane", name, "open", _] | name == stripName ->
    Just
      ( layout
      , strip
      , stripName <> " has no position — it sits under the prompt, the width "
          <> "of the script column, so \":pane " <> stripName <> " open\" is "
          <> "the whole of it"
      )
  [":pane", name, "close"] ->
    withPane name (\p -> (closePane p layout, paneName p <> " closed"))
  [":pane", name, "open", n] -> withPane name $ \p -> case readPosition n of
    Nothing ->
      ( layout
      , n <> " is not a position — they are 1 to 6, two columns of three "
          <> "numbered across"
      )
    Just pos -> placed p pos
  (":pane" : _) -> Just (layout, strip, paneUsage)
  _ -> Nothing
  where
    withPane name k = Just $ case paneByName name of
      Just p -> let (l, said) = k p in (l, strip, said)
      Nothing ->
        ( layout
        , strip
        , "no pane called " <> name <> " — " <> intercalate ", " paneWords
        )
    -- | **What a move cost is said, not left to be noticed.** A swap moves the
    -- pane that was there, and opening a closed pane onto a taken position
    -- closes the occupant; both are read back off the layouts rather than
    -- reported by 'openPane', which keeps that function about the placement.
    placed p pos =
      ( after
      , intercalate ", "
          ( (paneName p <> " at " <> show pos)
              : [ paneName q <> " at " <> show w
                | Just q <- [paneAt pos layout]
                , q /= p
                , Just w <- [positionOf q after]
                ]
              <> [paneName q <> " closed" | Just q <- [shut]]
          )
      )
      where (after, shut) = openPane p pos layout

-- | **Every pane @:pane@ knows, the positionless one last** — `~w2tk2`.
-- Last and not sorted in, so a word that behaves differently from the other
-- nine is not hidden in the middle of them.
paneWords :: [String]
paneWords = map paneName allPanes <> [stripName]

paneUsage :: String
paneUsage =
  ":pane ‹name› open ‹1-6›, :pane ‹name› close, :pane " <> stripName
    <> " open|close — "
    <> intercalate ", " paneWords

readPosition :: String -> Maybe Position
readPosition w = case reads w of
  [(n, "")] | n `elem` positions -> Just n
  _ -> Nothing

-- | The words @:pane@ offers where the caret stands, or 'Nothing' off a
-- @:pane@ line. **Read by the dropdown and by Tab through 'dropdownRows'**, so
-- the key and the list cannot offer different things.
paneVocabulary :: String -> Maybe [String]
paneVocabulary line
  | not (paneCommandPrefix `isPrefixOf` line) = Nothing
  | otherwise = Just (vocab slot)
  where
    ws = words line
    -- | A line ending in a space is one word further on than its words say.
    slot = if not (null line) && last line /= ' ' then length ws - 1 else length ws
    vocab 1 = paneWords
    vocab 2 = ["open", "close"]
    -- | **No positions offered after @:pane suggestions open@** — `~w2tk2`.
    -- The strip has none, and a completion that offers six numbers the very
    -- next word will refuse is the dropdown telling him something untrue.
    vocab 3 | ws !! 2 == "open", ws !! 1 /= stripName = map show positions
    vocab _ = []

paneCommandPrefix :: String
paneCommandPrefix = ":pane "

-- | **What a pane is wide before anybody drags it: a quarter of the screen,
-- which is what `~z5dmq` chose.** It was two nested percentages before
-- (52% for the pair of columns, then half of that each); this is the same
-- arithmetic done once, in columns, so that a dragged width and a default
-- width are the same kind of number.
defaultPaneWidth :: Int -> Int
defaultPaneWidth screen = max minPaneWidth (((screen - 2) * 52 `div` 100 - 1) `div` 2)

-- | **A drag snaps to a multiple of this** — his instruction: /"make it
-- 'snapping' to some 'steps' not like infinite precision (pixel-perfect)
-- that doesn't make sense anyway. Let it snap on like 10 pixels or
-- something."/ The unit here is a terminal cell and not a pixel, so ten of
-- them would be a fifth of a pane; four is a step you can see happen and
-- still lands a pane where you meant it.
--
-- **The snap is to an absolute multiple, not to a multiple of the distance
-- dragged**, so two panes pulled to "about the same" width are the same
-- width rather than four columns apart.
paneWidthStep :: Int
paneWidthStep = 4

-- | Narrower than this and a pane holds nothing worth drawing: @modules  1@
-- is twelve columns with no room for a module under it.
minPaneWidth :: Int
minPaneWidth = 12

-- | **What the document keeps, whatever the panes are doing.** A drag cannot
-- take the screen away from the thing being edited.
docMinWidth :: Int
docMinWidth = 24

-- | The same floor downwards — `~w2tk2`, the suggestion strip being the
-- first thing that can take /rows/ off the document. **A title, the input
-- line, and six rows of transcript above it**: below that the pane is no
-- longer somewhere a proof is being read.
docMinHeight :: Int
docMinHeight = 8

-- | How tall the strip may be pulled on a terminal of this many rows —
-- `~w2tk2`.
--
-- **The five rows taken off are 'draw''s own and are counted there, not
-- guessed**: the outer top margin, the pane bar, the blank row under it, the
-- spacer row between the document and the strip, and the strip's own title.
maxStripRows :: Int -> Int
maxStripRows screen = max stripMinRows (screen - 5 - docMinHeight)

requestBlinkingCursor :: IO ()
requestBlinkingCursor = hPutStr stdout "\ESC[1 q" >> hFlush stdout

resetCursorStyle :: IO ()
resetCursorStyle = hPutStr stdout "\ESC[0 q" >> hFlush stdout

-- | One dark panel fill, one neon accent per pane (edge and title text,
-- never a fill), plus the fold/splice attrs the reading-flow feature uses.
-- 'V.linearColor', always — 'V.rgbColor' quantizes to 256 colors at
-- construction in vty 6 and is why the first pass came out as two
-- indistinguishable pale blobs instead of four panes (`.claude/LOG.md`,
-- 2026-09-29).
attrs :: Theme -> AttrMap
attrs th = attrMap (surface (themeStage th) (themeInk th))
  [ (attrName "panel",          surface (themePanel th) (themeInk th))
  , (attrName "edge.repl",      surface (themePanel th) (themeRepl th))
  -- Live-script mode's pane wears the repl's own accent — it *is* the repl
  -- pane in another mode, not a fifth pane, so a second colour would say
  -- something untrue about the layout.
  , (attrName "edge.script",    surface (themePanel th) (themeRepl th))
  , (attrName "title.script",   surface (themePanel th) (themeRepl th))
  -- The caret's own row marker, his suggested '⟩'. The accent, because it
  -- answers "where am I in the document" and nothing else on screen does.
  , (attrName "script.marker",  ink (themeRepl th))
  -- A line the engine refused, and its complaint. Dim rather than loud:
  -- the line is still in the document and still yours to fix, which is not
  -- an alarm.
  , (attrName "script.refused", ink (themeDim th))
  -- **A line below an edit, still there and no longer true of anything** —
  -- his ruling of 2026-11-11, that the tail survives an edit and says so by
  -- colour rather than by vanishing. The same dim ink a refusal wears, and
  -- deliberately: both are "this line is in your document and is not
  -- carrying the session", which is one fact with two causes. It is a
  -- separate attribute so a theme can part them later without touching the
  -- drawing.
  -- **A surface, not an ink**: 'ink' leaves the background at 'V.defAttr',
  -- which brick resolves against the map's default — the *stage* colour, not
  -- the panel the pane is filled with. On a short run of output that is a
  -- near-black seam nobody notices; on a stale document line, which is as
  -- wide as the line is long, it is a black band behind every character.
  -- Measured under the pty: @bg:0;0;0@ where the line above reads
  -- @bg:16;10;14@.
  , (attrName "script.stale",   surface (themePanel th) (themeDim th))
  -- **The command bar is a surface, not a line of text** — his report,
  -- 2026-10-20: *"it is just almost invisible."* Measured under a pty, the
  -- whole of it on screen was a single @:@ in the pane's last row: the bar
  -- drew its marker and an empty editor, and an empty editor on the panel
  -- fill in the panel's own ink is nothing at all. It takes the dropdown's
  -- background for the same reason a dropdown has one — it floats over the
  -- document rather than belonging to it — and it is filled to the pane's
  -- width so the surface is what you see, not the three characters in it.
  , (attrName "script.bar",     surface (themePopup th) (themePopupInk th))
  , (attrName "script.bar.mark", surface (themePopup th) (themeRepl th))
  , (attrName "edge.proofterm", surface (themePanel th) (themeProof th))
  , (attrName "edge.goals",     surface (themePanel th) (themeGoals th))
  , (attrName "edge.machine",   surface (themePanel th) (themeMachine th))
  , (attrName "title.repl",     surface (themePanel th) (themeRepl th))
  , (attrName "title.proofterm", surface (themePanel th) (themeProof th))
  , (attrName "title.goals",    surface (themePanel th) (themeGoals th))
  , (attrName "title.machine",  surface (themePanel th) (themeMachine th))
  -- | **The second column** — `~z5dmq`. Same scheme, three more accents: the
  -- edge and the title carry a pane's colour and nothing else does.
  , (attrName "edge.globals",   surface (themePanel th) (themeGlobals th))
  , (attrName "edge.modules",   surface (themePanel th) (themeModules th))
  , (attrName "edge.output",    surface (themePanel th) (themeOutput th))
  , (attrName "edge.choices",   surface (themePanel th) (themeChoices th))
  , (attrName "edge.matches",   surface (themePanel th) (themeMatches th))
  , (attrName "title.globals",  surface (themePanel th) (themeGlobals th))
  , (attrName "title.modules",  surface (themePanel th) (themeModules th))
  , (attrName "title.output",   surface (themePanel th) (themeOutput th))
  , (attrName "title.choices",  surface (themePanel th) (themeChoices th))
  , (attrName "title.matches",  surface (themePanel th) (themeMatches th))
  -- | **The suggestion strip** — `~w2tk2` slice 1. Same scheme as every
  -- other pane and no special case: the edge and the title carry the accent,
  -- both paired with 'themePanel' so neither punches the hole `~bv2wj` was.
  , (attrName ("edge." <> stripName),  surface (themePanel th) (themeSuggest th))
  , (attrName ("title." <> stripName), surface (themePanel th) (themeSuggest th))
  -- | **A grid cell's key, in the strip's own accent** — `~w2tk2` slice 2.
  -- The thing a cell is asking him to press, and the only part of the strip
  -- that is not ordinary text.
  --
  -- **An accent ink on the panel, not a filled block.** A fill is what
  -- `panebar.open` and `dropdown.selected` are, and both of those mean
  -- /this one/ — which is exactly the reading this pane must not have: there
  -- is no selected cell, so ten filled blocks would be ten rows all claiming
  -- to be chosen. **Paired with 'themePanel' explicitly**, `~bv2wj`'s
  -- lesson, or it punches a hole in the pane's own fill.
  , (attrName "strip.key",      surface (themePanel th) (themeSuggest th))
  -- | **The hint region's text** — `~w2tk2` slice 4.
  --
  -- **Ordinary ink, which is the same ink a cell's label carries**, and the
  -- difference between a hint and an option is left to shape: a grid cell is
  -- @F3@ and a terse name, a hint is a sentence with air above it. **The
  -- alternative was 'themeDim'**, whose own haddock calls it the colour for
  -- /hints/ — and it is wrong here for the one reason that matters: he asked
  -- for half this pane to be kept free for the model, and a region reserved
  -- that hard is not secondary text.
  --
  -- **It is an attr of its own so that retuning it is one line** rather than
  -- a hunt through 'draw' — his to move, the same standing 'themeSuggest'
  -- has. **Paired with 'themePanel'**, `~bv2wj` again, and here it matters
  -- for the blank rows too: the region draws its padding in this attr, so an
  -- unpaired one would have punched a three-row hole in the panel whenever
  -- the hint was short.
  , (attrName "strip.hint",     surface (themePanel th) (themeInk th))
  -- | **`strip.jev` IS GONE WITH THE MARK IT PAINTED — HIS WORD,
  -- 2026-11-19**: /"turn off the green color under Jev's suggestions."/ See
  -- 'Tui.Panes.offerGridWidget' for why his two instructions about it do not
  -- conflict — `~zt4jk` asked for the colour while the grid still mixed
  -- Jev's rows with the engine's, and exclusion made every cell Jev's the
  -- same day. **The entry is removed rather than left unused**: an attr
  -- nothing draws is a theme key he can retune to no effect.
  -- | **The reply row's unanswered state** — `~w2tk2` slice 6: the label
  -- that names the region and the dim sentence that fires it. HIS, on the
  -- sentence: /"it by default has a dim line with text like \"give me a
  -- hand\""/, and dim is the whole signal — it reads as something offered
  -- rather than as text that is already there. 'themeDim' is the colour
  -- whose own haddock calls it /hints/, which is finally what this is.
  -- **Paired with 'themePanel'**, `~bv2wj`.
  , (attrName "strip.dim",      surface (themePanel th) (themeDim th))
  -- | A list pane's group heading and its small print. **Both dim, and the
  -- same dim**: a heading is not a thing in the list and neither is a module's
  -- file, so what separates them from the entries is weight, not hue — the
  -- accents are the panes' and a fourth colour inside a pane would compete
  -- with them.
  --
  -- **Both name their background explicitly, and that is `~bv2wj`** — his
  -- report of 2026-11-18: /"lines like `modules  3` and `shipped with thena  2`
  -- lost their background color. The bg is black, when it should be pane's
  -- background color."/ They were plain 'ink', which sets a foreground and
  -- leaves the background at 'V.defAttr' — the terminal's own, not
  -- 'themePanel'. An attr that has to sit on the panel's colour pairs the two
  -- itself, the way `panebar.closed` just below already did.
  --
  -- **Why 'ink' punches a hole rather than inheriting: a pane's body IS filled
  -- with 'themePanel', and an entry carrying no attr at all inherits that
  -- fill.** What does not inherit is an explicit 'withAttr' whose background is
  -- 'Default' — vty merges the named attr over the inherited one and
  -- /"terminal default"/ replaces the fill instead of deferring to it.
  -- Measured under a pty: with 'ink', a heading read `bg=000000` sitting in a
  -- band of `bg=100a0e`.
  --
  -- **Every `title.*` had the same hole and all ten were fixed with these two**
  -- — his report named two headings, but the cause is one and the pane titles
  -- showed it just as plainly. The test is now structural: a `title.X` sits on
  -- the panel exactly as its `edge.X` sibling already did, so the two cannot
  -- drift.
  , (attrName "pane.heading",   surface (themePanel th) (themeDim th))
  , (attrName "pane.detail",    surface (themePanel th) (themeDim th))
  , (attrName "dim",            ink (themeDim th))
  -- | **The pane bar, `~7tfhd`** — an open pane against a closed one. His
  -- instruction was that the two be /"rendered a bit differently"/, and the
  -- difference is weight rather than hue, for the same reason a pane's heading
  -- is: the accents belong to the panes themselves, and a bar in a colour of
  -- its own would compete with every one of them at once.
  --
  -- **An open pane is ordinary text, not an accent.** It is the resting state
  -- of the screen and should not ask to be read; a closed pane is the one that
  -- is saying something unusual, and dim is how this TUI says /"present but not
  -- in play"/ everywhere else — a stale script line, a pane's heading.
  --
  -- **Both are filled blocks as of his instruction of 2026-11-13** — /"a pink
  -- accent background around the text (get the contrast right)"/ — so the
  -- difference between an open pane and a closed one is now the fill itself and
  -- not only the ink.
  --
  -- **The contrast was computed, not eyeballed, and that was the instruction.**
  -- An open chip is 'themeStage' on 'themePaneBar': in neon-pink-dark that is
  -- **6.4:1**, where 'themeInk' on the same pink is 2.8:1 and fails for text.
  -- A closed chip is 'themeDim' on 'themePanel', **3.8:1** — below AA and
  -- deliberately so: a closed pane is a recessed label and this is the same
  -- dim-on-panel pairing `pane.heading` and `pane.detail` already ship.
  , (attrName "panebar.open",   surface (themePaneBar th) (themeStage th))
  , (attrName "panebar.closed", surface (themePanel th) (themeDim th))
  -- A placeholder box, in the input line, in a dimmer ink than ordinary
  -- text — his `.jalivert/TUI.md`-adjacent report, 2026-09-29: the caret
  -- itself went dark standing on one. Root cause: the glyph is a solid
  -- FULL BLOCK, drawn at full 'themeInk' brightness by default, so the
  -- terminal's own reverse-video caret — already an inverted full cell —
  -- had nothing to invert *against*, reading as a dark cell instead of a
  -- visible caret. A dimmer ink still marks the box as a box without
  -- fighting the caret over the brightest color in the theme.
  , (attrName "placeholder",    ink (themeDim th))
  -- The recovered-span underline (his `.jalivert/TUI.md` #7), and its own
  -- combination with a placeholder box inside a broken literal. **Two
  -- named attrs, not one nested inside the other** — nesting
  -- 'withAttr "recovered"' around 'withAttr "placeholder"' was the first
  -- attempt, and it looked right until a box landed inside a recovered
  -- span: the inner call's 'ctxAttrName' *replaces* the outer's rather
  -- than composing with it (confirmed by reading 'withAttr's own
  -- definition — it is a plain field set, `ctxAttrNameL .~ an`, not a
  -- stack), so the outer "recovered" was silently discarded on every box
  -- and only the ordinary text around it ever showed the underline. Fixed
  -- by naming the combination outright rather than trying to compose two
  -- unrelated attrs through nesting.
  --
  -- **In the repl's own accent, not plain ink** — his request, 2026-09-30:
  -- vty's 'V.Attr' has no underline-color field separate from the text's
  -- own foreground (checked directly, not assumed — 'attrStyle'/
  -- 'attrForeColor'/'attrBackColor'/'attrURL' is the whole record), so a
  -- distinct, noticeable underline means coloring the *text* underneath it
  -- — the terminal draws the stroke in whatever color the character
  -- already is. 'themeRepl' picked as the most saturated accent in the
  -- palette, both combinations, so a box inside a recovered span reads as
  -- unmistakably part of the same broken run as the text around it.
  , (attrName "recovered",             V.withStyle (ink (themeRepl th)) V.underline)
  , (attrName "placeholder.recovered", V.withStyle (ink (themeRepl th)) V.underline)
  , (attrName "accent.output",  ink (themeSoft th))
  , (attrName "dropdown",          surface (themePopup th) (themePopupInk th))
  , (attrName "dropdown.jevpick",  surface (themeJevPick th) (themeStage th))
  -- A real background swap for the selected row, not a foreground tint
  -- beside an arrow — his `.jalivert/TUI.md` #20: the arrow was the only
  -- thing marking a row selected, which read as weak. The repl accent as a
  -- solid bar, panel-dark text on top of it, same "selected" contrast an
  -- ordinary list widget uses.
  , (attrName "dropdown.selected", surface (themeRepl th) (themePanel th))
  -- | **Small print *on* the popup surface, which is why it is not "dim".**
  -- The picker's title, its key hints and the highlighted session's handle
  -- are secondary text inside a floating box, and 'attrName "dim"' is an ink
  -- with no background of its own — brick resolves that against the map's
  -- default, the stage, so it would draw a black band across a box filled
  -- with 'themePopup'. The same mistake 'script.stale' was measured making.
  , (attrName "dropdown.faint",    surface (themePopup th) (themeDim th))
  -- The input line's own editor: 'renderEditor' wraps its output in
  -- Brick's 'edit'/'editFocused' attributes, which fall back to the
  -- terminal default (black) unless named here. The input is the last line
  -- of the repl pane's own document, so it takes the pane's fill, not a
  -- background of its own.
  , (editAttr,        surface (themePanel th) (themeInk th))
  , (editFocusedAttr, surface (themePanel th) (themeInk th))
  , (foldAttr,   V.withStyle (surface (themeFold th) (themeInk th)) V.italic)
  , (spliceAttr, V.withStyle (surface (themeSplice th) (themeInk th)) V.bold)
  ]
  where
    surface bgC fgC = V.withBackColor (V.withForeColor V.defAttr fgC) bgC
    ink fgC = V.withForeColor V.defAttr fgC

-- | **The first layer in this list is the topmost one, confirmed
-- empirically** — not documented anywhere obvious, and the opposite of
-- what seemed like the safer guess. Got this backwards on the first attempt
-- at the dropdown below: appending it after the base layer put it fully
-- behind the panes, invisible, no error, just never on screen. Verified
-- with a hardcoded marker widget before trusting the fix.
draw :: St -> [Widget Name]
draw st =
  pickerLayer st
    <> popups
    -- **The outer margin runs along the top and the left only** — his
    -- ruling of 2026-11-16: the bottom row and the right column belong to
    -- the panes, so content reaches the screen's own bottom-right corner.
    <> [padTop (Pad 1) (padLeft (Pad 1) (vBox [paneBar, str " ", hBox [docColumn, gapH, paneColumns]]))]
  where
    budget = Budget 200
    s = activeSession st

    -- | **Every pane, which are open, and where** — `~7tfhd`. Above
    -- everything and the full width of the screen, his ruling of 2026-11-13,
    -- **with a blank row under it** — /"It needs breathing space bellow it to
    -- separate it from the main pane."/ The row is a 'str' in the 'vBox' rather
    -- than padding on the bar, so it costs the document exactly one line and
    -- nothing has to reason about a pad that does not reduce a child's width
    -- (brick's trap, and the reason `padLeft` is avoided elsewhere here);
    -- 'Tui.Layout.paneBarEntries' decides the order and
    -- 'Tui.Panes.paneBarWidget' how the line reads, so neither is decided here.
    -- **The strip is last in the bar, always** — `~w2tk2`. The nine
    -- positioned panes come in position order and then the closed ones, which
    -- is an order that changes as he moves them; the strip's place never
    -- changes, so it sits at the end where it will not travel.
    paneBar =
      paneBarWidget
        ( [(paneName p, maybe BarClosed BarAt pos) | (p, pos) <- paneBarEntries (stLayout st)]
            <> [(stripName, if stripOpen (stStrip st) then BarUnder else BarClosed)]
        )

    -- | **Neither dropdown is drawn while the picker is open**, and the
    -- state behind them is untouched: a completion popup hanging over a
    -- modal is two things claiming the same keys on screen when only one of
    -- them has them. Esc out of the picker and whatever was open comes back
    -- exactly as it was, because nothing was dismissed to get it off screen.
    popups
      | isJust (stPicker st) = []
      | otherwise = dropdownLayer st <> offerDropdownLayer st
    links = developmentView budget s
    machine = machineView budget s
    fold = if stFoldOn st then Fold (focusAddress s) else NoFold

    -- | A one-cell stage-colored strip between panes, his correction,
    -- 2026-09-29 — panes touched directly before this, `MS7-CLI`'s own
    -- convention is a thin stage gap both ways. Left at the ambient (base)
    -- attr rather than any pane's "panel" attr, same as the stage itself.
    gapH = hLimit 1 (fill ' ')

    -- | An append-only document, not a fixed-position input row — his
    -- correction, 2026-09-29: the prompt used to be pinned to the pane's
    -- bottom row regardless of how much history existed, "like a second-class
    -- element." It's now the last line of the same scrollable content as
    -- everything above it, and travels down with it. Starting with the
    -- plain version, his own call: let it reach the pane's actual bottom and
    -- scroll from there like a normal terminal, not a pre-built holding-point
    -- short of that — add one later only if this doesn't feel right.
    replColumn
      | stScriptMode st =
          withAttr (attrName "panel") $
            paneWith "script" HistoryVP
              (padAll 1 (vBox (renderScript st editorWidget)))
              (scriptFoot st)
      | otherwise =
          withAttr (attrName "panel") $
            pane "repl" HistoryVP
              (padAll 1 (vBox (renderTurns (stTurns st) <> [inputLine])))

    -- | **The document and the suggestion strip under it — his
    -- "double-pane"** (`~w2tk2` slice 1). One 'vBox', which is the whole of
    -- why the strip needs no width of its own: it is as wide as the document
    -- column, and the document column is whatever the panes leave.
    --
    -- **The strip is height-limited and the document is not**, so the
    -- document is the greedy child and the strip takes exactly what it has
    -- been pulled to — slice 5's /"we just let the user resize the pane
    -- upwards taking space from the main prompt\/script"/, which is his own
    -- first choice over a mode switch.
    --
    -- **One spacer row between them, the same 'gapRow' a pane column uses
    -- between its panes.** The pair is two panes and the gap is what says so.
    docColumn
      | stripOpen (stStrip st) =
          vBox [replColumn, gapRow, vLimit (stripRows (stStrip st) + 1) suggestionStrip]
      | otherwise = replColumn

    -- | **The suggestion strip** — `~w2tk2` slice 1, and it is drawn through
    -- the same 'pane' the other nine go through: the accent edge, the title
    -- strip, the viewport. Nothing about it is special-cased in the drawing,
    -- which is what makes it a pane rather than a widget pretending to be one.
    suggestionStrip =
      withAttr (attrName "panel") $
        pane stripName StripVP (padAll 1 stripBody)

    -- | **The strip's contents: a counted heading, then the grid, then the
    -- rows kept for the hint and the reply** — `~w2tk2` slice 2.
    --
    -- **A 'Widget' that reads its own width**, because the grid's shape is a
    -- function of it — his instruction of 2026-11-19, /"it could also change
    -- depending on how wide the double-pane (main + suggestions) is"/. Three
    -- columns at his measured geometry, two in a narrow window, five in a
    -- wide one; 'Tui.Layout.stripGrid' is the whole of that arithmetic and
    -- nothing here repeats it.
    --
    -- **The hint region is drawn from 'stHint', and the reply row with it** —
    -- `~w2tk2` slice 4 draws the first, slice 5 fills the second. The
    -- region's height is 'Tui.Layout.stripHintUsed' and the grid is sized
    -- from the same number, so a hint that outgrows its floor takes rows off
    -- the grid rather than off the pane. **'stripHintRowsFor' is literally
    -- the function the keymap calls** — not a second copy of the arithmetic —
    -- with the live width where the keymap passes 'stStripWidth''s.
    --
    -- **NEITHER REGION TAKES A ROW WHEN THERE IS NOTHING IN IT, AND THERE IS
    -- NO HEADING AT ALL** — `~8cr56`, his report of 2026-11-19: /"Why do I
    -- only get 2 suggestions?"/ Three things made that number, all of them
    -- ours: his strip has seven body rows, the hint and reply rows were
    -- reserved whether or not anything was in them, and a heading row said
    -- @offers 2 of 318@ beneath a pane whose own title already says
    -- @suggestions@. **The heading is gone** — /"Why does it help the user to
    -- know 318?"/, and it does not: the cells are numbered and the numbers
    -- are the information — **and the reserve now follows the content.**
    -- Seven cells at his geometry where there were two.
    --
    -- **What it costs, stated rather than hidden: a hint arriving reflows the
    -- grid**, so a key he has just learned can move. That is the trade the
    -- question chose, and the alternative is the two cells he objected to.
    --
    -- **THE HINT DRAWS WHETHER OR NOT THERE ARE OPTIONS**, which is the
    -- answer slice 4 gives his §15 question 7 (/"does the strip ever hold a
    -- hint with no options at all"/): yes. A slate is empty mid-proof
    -- whenever nothing applies, which is one of the moments a hint is worth
    -- most, and his own property 3 says offers and hints are the same kind of
    -- content from two sources. **With neither, the strip is one blank row** —
    -- the call the output pane already makes for an empty pane.
    stripBody = Widget Fixed Fixed $ do
      ctx <- getContext
      let width = ctx ^. availWidthL
          hintRows = stripHintRowsFor st width
          grid =
            stripGrid
              width
              (stripBodyRows (stripRows (stStrip st)))
              (stripReserveOf st width)
          cellW = max stripCellWidth (width `div` gridCols grid)
          shown = take (gridSlots grid) (map rowLabel stripSlate)
          offers
            | null stripSlate = []
            | otherwise = [offerGridWidget cellW (gridCols grid) shown]
          -- **The reply row is drawn whenever the strip is open, and the
          -- hint's own rows only when there is a hint** — `~w2tk2` slice 6
          -- moved the first of those. Slice 4 drew the row only beside a
          -- hint, which was right while a hint could only arrive from
          -- `:hint`; it is wrong now that **the row is how a hint is asked
          -- for in the first place** — a row that is not on screen cannot
          -- be clicked, and his design has no other door. `~8cr56`'s rule
          -- is kept where it still applies: the hint's three rows cost
          -- nothing until something is in them.
          llm =
            concat
              [ [hintRegionWidget width hintRows (stHint st) | isJust (stHint st)]
              -- | **The line he asked for, and it stays empty** — HIS,
              -- 2026-11-19: /"Give me one empty line between the AI reply and
              -- my AI prompt. That one will stay empty."/ Drawn in the hint's
              -- own surface rather than left bare, so the LLM's half of the
              -- pane reads as one block down to the row he types in
              -- (`~bv2wj`: an attr-less row would punch the panel's fill).
              , [ withAttr (attrName "strip.hint") (vLimit stripHintGapRows (fill ' '))
                | isJust (stHint st)
                ]
              , [stripReplyWidget]
              ]
          -- | **THE ROW HE TYPES IN IS THE PANE'S LAST LINE, AND THE GAP
          -- ABOVE IT IS HIS** — HIS, 2026-11-19: /"I told you that the
          -- prompt for the AI is supposed to be on the bottom line at the
          -- bottom of the pane"/ and /"Leave one line's space between the
          -- Jev's suggestions and the space for LLM."/
          --
          -- **It is counted, not filled.** A greedy 'fill' would be the
          -- obvious way to push the bottom group down and it is the wrong
          -- one here: this body renders inside a *vertical* viewport, which
          -- offers its content unbounded height, so a greedy row claims all
          -- of it — the trap 'stripReplyWidget' already names for its own
          -- blank row. So the slack is worked out against
          -- 'Tui.Layout.stripBodyRows' and emitted as that many bounded
          -- rows.
          --
          -- **Never fewer than 'stripSeparatorRows'.** The grid is sized a
          -- row shorter than it could be ('stripReserveOf'), so a grid
          -- drawing every row it was given still leaves his one line; the
          -- 'max' is there so the gap survives a geometry too short to pay
          -- for it, the same way 'stripHintBudget' keeps the hint's floor.
          drawnRows = length offers * ((length shown + gridCols grid - 1) `div` max 1 (gridCols grid))
          slack =
            max stripSeparatorRows
              (stripBodyRows (stripRows (stStrip st)) - drawnRows - hintUsed - stripReplyRows)
          hintUsed = if isJust (stHint st) then hintRows + stripHintGapRows else 0
          gap = [vLimit slack (fill ' ')]
      render (vBox (offers <> gap <> llm))

    -- | **The reply row — `~w2tk2` slice 5.** Blank and clickable while
    -- 'stStripReply' is 'Nothing'; the click that opens it is
    -- 'handlePaneClick''s @MouseDown StripReply@ case. Drawn in the same
    -- @strip.hint@ surface as the region above it, which is what pairs the
    -- two — the hint and the reply to it are one region reading top to
    -- bottom, not two.
    --
    -- **The mark borrows @strip.key@, the grid's own F-key colour**, rather
    -- than a new attr: both are "how you act on this pane," and a theme that
    -- retunes one already means the other. 'overrideAttr' on
    -- 'editFocusedAttr' is 'scriptFoot''s own fix for the same thing — an
    -- editor paints its focused background from that attr, and without the
    -- override it was the input's own colour rather than the strip's.
    -- **'vLimit 1' around both branches, and it is load-bearing.** 'fill'
    -- is 'Greedy' in both directions, so without it a blank row claimed
    -- the viewport's whole remaining height — the same trap 'scriptFoot'
    -- already names for the command bar's own row. **And it is why the
    -- unopened row is 'fill' and not 'str " "'**: a single-character
    -- widget's own reported extent is one column wide, so the row was
    -- clickable only in its first column — measured under a pty, a click
    -- three columns in did nothing at all until this was 'fill'.
    stripReplyWidget =
      clickable StripReply $ withAttr (attrName "strip.hint") $ vLimit 1 $
        hBox
          ( [withAttr (attrName "strip.key") (str (hintLabel st <> "  "))]
              <> case stStripReply st of
                -- **The dim sentence, and clicking it is what fires the
                -- ask** — his design. It is not a hint about a feature; it
                -- is the feature's only control.
                Nothing -> [withAttr (attrName "strip.dim") (str (Text.unpack hintPlaceholder))]
                -- **Open and still empty: the sentence is a ghost behind
                -- the cursor, and Tab is what makes it real** — his ruling
                -- of 2026-11-19. Enter sends it either way, so the ghost is
                -- never a lie about what would go out; Tab is there for
                -- when he wants to edit it rather than send it.
                --
                -- **The editor is held to the width of its own text** so
                -- the ghost can sit after it. 'renderEditor' is greedy
                -- across the row otherwise and would cover the whole line,
                -- leaving nowhere for the ghost to be drawn; one column
                -- past the text is where the cursor goes.
                Just ed ->
                  [ withAttr (attrName "strip.key") (str "❯ ")
                  , hLimit (Text.length (typedReply ed) + 1)
                      ( overrideAttr editFocusedAttr (attrName "strip.hint")
                          (renderEditor (vBox . map (str . Text.unpack)) True ed)
                      )
                  ]
                    <> [ withAttr (attrName "strip.dim") (str (Text.unpack hintPlaceholder))
                       | Text.null (typedReply ed)
                       ]
              <> [fill ' ']
          )

    -- | **The slate: what the grid is drawn from and what an F-key takes** —
    -- `~w2tk2` slice 2. 'stripSlateOf' is the whole of it, so the drawing and
    -- the keymap read the same list and a key can never land on a cell that
    -- is not there.
    stripSlate = stripSlateOf st

    -- | 'Input' reported here, on the editor itself, not the "❯ " ahead of
    -- it — so 'stInputExtent's own upper-left is column 0 of the *text*,
    -- and every text offset ('pathStartOff', the cursor, anything later)
    -- adds onto a real screen column directly, no prompt width to remember.
    -- | The whisper of what the highlighted row would land (his
    -- `.jalivert/TUI.md` #17, at the caret rather than only the line's end
    -- since #21): dimmed, inserted right where the caret stands, skipping
    -- over whatever real characters past it the accept would consume (a
    -- box, typically). Real text on either side of that point renders
    -- unchanged, so Brick's own cursor placement — a column count into the
    -- *unmodified* zipper — stays correct without knowing any of this
    -- happened; see 'ghostAt'/'offerGhost'.
    inputLine = str "❯ " <+> editorWidget
    -- | The same editor without the prompt glyph. **Script mode has no
    -- prompt**: the caret is standing in a document, and a '❯' in front of
    -- the line you are editing would be a prompt drawn into the text it is
    -- not part of — and would land in no saved file, which is the tell.
    -- | **Focused only while the command bar is closed.** 'showFirstCursor'
    -- takes the first cursor any widget reports in draw order, and the
    -- document is drawn before the pane's foot — so with both editors
    -- rendered focused, the caret stayed in the document while every key
    -- went to the bar. Measured under a pty, his report of 2026-10-20: the
    -- bar opened, the cursor did not move, and the mode read as a dead key.
    -- | **Unfocused while the picker is open, for the same reason as the
    -- bar.** 'showFirstCursor' takes the first cursor any widget reports in
    -- draw order, so an editor still rendered focused under a modal leaves
    -- the caret blinking in a document that is not taking keys.
    editorWidget = reportExtent Input (renderEditor (\ts -> renderInputContent ts col ghost skip (stRecoveredSpan st)) (isNothing (stScriptBar st) && isNothing (stPicker st) && isNothing (stStripReply st)) (stInput st))
      where
        -- | `:whisper off` (his `.jalivert/TUI.md` #23) silences this
        -- outright rather than 'ghostAt' itself carrying the flag — the
        -- accept-span math it returns alongside the text isn't wanted by
        -- anything else, so there's nothing to lose by short-circuiting here.
        -- | **The whisper is whatever is in slot 1 once the strip is
        -- open** — his ruling, `~w2tk2` slice 2: /"perhaps the concept of
        -- the whisper would be tied to the option number 1"/. With the
        -- strip closed it is still the dropdown's selected row, which is
        -- the old behaviour and stays while the dropdown does.
        --
        -- **This is what dissolves part one §4 rather than fixing it.** The
        -- whisper was stale because the selection was pinned to a candidate
        -- by label, so Jev's answer arriving a moment later left the guess
        -- whispered underneath its picks. Slot 1 is a position, so a slate
        -- Jev reorders moves the whisper by construction and there is no
        -- highlight to travel under him.
        (ghost, skip) = if stWhisperOn st then whisper else ("", 0)
        whisper
          | stripOpen (stStrip st)
          , Just ins <- rowInsert =<< listToMaybe (stripSlateOf st)
          = maybe ("", 0) id (ghostOfInsert col (slateStart (stSlate st)) (slateReplaceLen (stSlate st)) ins)
          | otherwise = ghostAt line col (stDropdown st) (liveOffers st)
        line = concatMap Text.unpack (getEditContents (stInput st))
        (_, col) = getCursorPosition (stInput st)

    -- | **Six panes in two columns of three, all six the same width** — his
    -- request of 2026-11-11, `~z5dmq`: /"They should form a new column left to
    -- the three panes already there. Those get slimmer, they have been wasting
    -- space anyway. And these new ones are the same width as the old ones after
    -- you make them slimmer."/
    --
    -- **A quarter each, so the document keeps about half the screen.** The
    -- three panes that existed had 38% between them and the document 62%;
    -- two columns of 25% leave it 48%. The document is the one thing here
    -- whose content has no choice about its width — a proof-script line in
    -- `examples/Products.thena.script` runs past 200 characters — where a list
    -- of names or of module paths is narrow by nature. **Measured under a pty
    -- before it was chosen**, which is what `~z5dmq` asked for.
    -- | **Both columns inside one limit, and that is what makes them equal.**
    -- 'hLimitPercent' is a percentage of what is left where it stands, so two
    -- 25%s side by side are not 25% each: measured under a pty, the second
    -- came out at 25% of the remaining 75% and the three old panes lost a
    -- third of their width to the three new ones. Limiting the pair to half
    -- the screen and then halving that gives six panes of one width.
    -- | **Each of the six panes is as wide as it has been pulled** —
    -- `~gs8tj`, his request of 2026-11-12, and `~z5dmq`'s two nested
    -- percentages are gone with it. Three consequences, all of them his
    -- choice of /"each one independently"/ over one width per column:
    --
    --   * a column is as wide as its widest pane, and the narrower ones leave
    --     backdrop to their right — a column is no longer a rectangle;
    --   * the second column's own position depends only on its own widths, so
    --     pulling a pane of the first column never moves the second;
    --   * the document takes whatever is left, which is why it is the one
    --     thing here with no width of its own.
    --
    -- **The clamp reads the terminal's width and does not write it back.** A
    -- window too narrow to honour six chosen widths shrinks them in
    -- proportion for as long as it is narrow; widen it again and the widths
    -- he chose are still the widths he chose.
    -- | **Which panes, and in which column, is 'stLayout''s to say** —
    -- `~fxc89`. Both columns can be empty now: close all six and the document
    -- has the window, which is the other thing the command buys.
    paneColumns = Widget Fixed Greedy $ do
      ctx <- getContext
      let spare = max (2 * minPaneWidth) (ctx ^. availWidthL - docMinWidth - 1)
          (first', second') = columnsOf (stLayout st)
          wide ns = maximum (minPaneWidth : map storedWidth ns)
          (w1, w2) = (wide first', wide second')
          scale x
            | w1 + w2 <= spare = x
            | otherwise = max minPaneWidth (x * spare `div` (w1 + w2))
          width n = max minPaneWidth (scale (storedWidth n))
          -- | **A column is flush on the right and ragged on the LEFT, which
          -- is the whole of `~rr8bx`'s fix.** A 'vBox' left-aligns a child
          -- narrower than the box, so before this the three panes of a column
          -- shared one left edge — and therefore one bar column, three bars
          -- drawn on top of each other — while their right edges were ragged.
          -- Two things went wrong with that and he found both. **Pulling any
          -- bar of a column moved all three bars**, because the column's left
          -- edge is the layout's and not the pane's. And **widening one pane
          -- took width off the other two**: the column grows, so its left edge
          -- moves left, and a pane left-aligned against it keeps its own width
          -- while its right edge travels left with the box — his report of
          -- 2026-11-12, /"it adds or removes space from the pane on the
          -- right-hand side, not the one where the bar is"/. Padding each pane
          -- on the left instead pins every right edge to the column's, so a
          -- pane's own bar is the only thing its width moves.
          drawn cw n = hLimit cw . padLeft Max . hLimit (width n)
          -- | **An empty column draws nothing at all, not an empty box** —
          -- `~fxc89` made that a state he can reach, @:pane@-ing all three of
          -- a column away. 'maximum' over no panes has no answer and 'vBox'
          -- over no widgets has no height, so both are short-circuited here
          -- rather than guarded further down.
          column [] = emptyWidget
          column ns =
            vBox (intersperse gapRow [drawn (colWidth ns) n (paneOf n) | n <- ns])
            where colWidth = maximum . map width
          -- | **The stage gap belongs to the second column, not to the pair.**
          -- With that column closed there is nothing to its right to be
          -- separated from, and a gap drawn anyway is a column of backdrop the
          -- document could have had.
          gapIf ns = if null ns then emptyWidget else gapH
      render (hBox [column first', gapIf second', column second'])

    storedWidth = paneWidthOf st

    -- | **A spacer row of one column, not a greedy fill.** The row this
    -- replaced was @vLimit 1 (fill ' ')@, as wide as it was allowed to be,
    -- and a greedy row inside a column of chosen widths makes the column
    -- greedy too — the second column then has nowhere left to be drawn.
    gapRow = str " "

    -- | Which pane is which, so that the layout above is the column structure
    -- and nothing else. **The title is 'paneName' and not a literal**, which
    -- is what keeps the word on screen and the word @:pane@ takes the same
    -- word — the attribute names ("edge.globals" and the rest) are built from
    -- it too, so a theme keeps its accent per pane wherever the pane is moved.
    paneOf p = withAttr (attrName "panel") $ case p of
      Globals ->
        pane' (paneBody (map (fmap GlobalGroup)
                          (globalRows (Set.toList (stGlobalsClosed st)) (globalGroups st))))
      Modules -> pane' (paneBody (map (fmap ModuleRow) (moduleRows (moduleEntries st) (fileEntries st))))
      Output -> pane' (paneBody (outputRows focusText focusOut))
      ProofTerm -> pane' (padAll 1 (renderDevelopment fold links))
      Goals -> pane' (padAll 1 (renderGoals fold links))
      -- | **The parked proofs, and the import standing in a `yield`** —
      -- `~76zrr`, his request of 2026-11-12: /"Right, I need a pane with
      -- parked proofs!"/
      Quests -> pane' (paneBody' (proofWidgets (proofsView budget s)))
      -- | **The live choice points** — `~396c8`, his request of 2026-11-13:
      -- /"we don't have a pane for backtracking choice-points … something
      -- that would show me all of the choice-points that could be
      -- revisited and paths taken from them."/ Blocked on `~sx324` until
      -- 'Thena.View.choicesView' answered it on 2026-11-16. **No 'Budget'**:
      -- a 'ChoiceView' holds no term.
      ChoicePoints -> pane' (paneBody (choiceRows (choicesView s)))
      -- | **Which rules apply at the focus** — the same list @:matches@
      -- already prints, through 'matchesView' rather than through
      -- 'Thena.Render': never blocked, simply never drawn until now.
      Matches -> pane' (paneBody (matchRows (matchesView budget s)))
      -- | **The machine's lines wrap like a list pane's row**, same
      -- reason and the same settings ('paneWrap'): the engine elides a
      -- value against its own 'Budget', which knows nothing about how
      -- wide a quarter of this screen is.
      Machine -> pane' (padAll 1 (vBox (map (strWrapWith paneWrap) (renderMachineView machine))))
      where
        pane' = pane (paneName p) (PaneVP p)

    (focusText, focusOut) = lineInFocus st

    -- | A list pane's body. **One blank row when there is nothing**, because a
    -- viewport over an empty 'vBox' has no height to scroll and the pane's
    -- fill would stop at its title — and an empty output pane is the ordinary
    -- state of the output pane, not an error.
    paneBody rows = paneBody' (map paneRowWidget rows)

    -- | The same, for a pane whose rows are not all text — the proofs pane
    -- draws a theorem's statement through 'renderDisplay', which is a widget
    -- and not a 'Tui.Panes.PaneRow'.
    paneBody' ws = padAll 1 (vBox (if null ws then [str " "] else ws))

    -- | **The proofs pane's rows** — `~76zrr`. The live quest and the parked
    -- ones, each as its heading, the word @:resume@ takes, and what the quest
    -- is.
    --
    -- **Nothing here is an operation, and that is the engine's design showing
    -- through**: 'Thena.View.Proofs' carries no action, because a parked proof
    -- is picked up by submitting @:resume ‹word›@ — the same line a user types
    -- — and unparking is a step and never automatic, his ruling of 2026-11-11.
    -- So this pane says what there is and leaves the gesture to the prompt.
    --
    -- **'proofsViewOn' is a field and not the head of the list**, so which
    -- quest is live is the engine's answer rather than this pane's guess; it
    -- is drawn under its own heading for the same reason.
    proofWidgets pv =
      concat
        [ [paneRowWidget (Heading "on" Nothing)] <> questWidgets q
        | Just q <- [proofsViewOn pv]
        ]
        <> concat
             [ paneRowWidget (Heading "parked" (Just (length ps))) : concatMap questWidgets ps
             | let ps = proofsViewParked pv
             , not (null ps)
             ]

    -- | **The choice-points pane's rows** — `~396c8`. One group per live
    -- choice point, nearest first (the order 'choicesView' already hands
    -- back and the order @retry@ with no argument walks): a heading naming
    -- the identifier @retry@ takes and the alternative running now, counted
    -- by how many are left to try, then one entry per untried alternative,
    -- in dispatch order. **Never empty where this is drawn**: 'choicesView'
    -- excludes an exhausted frame, so 'choiceViewUntried' always has at
    -- least one name.
    choiceRows cvs =
      concat
        [ Heading (show (choiceViewId cv) <> "  " <> choiceViewRunning cv) (Just (length untried))
            : map Entry untried
        | cv <- cvs
        , let untried = choiceViewUntried cv
        ]

    -- | **The matches pane's rows.** Which rules apply at the focus, in
    -- dispatch order — 'matchesView' is a look and running it never moves
    -- the session. **One entry each, the exact line @:matches@ prints**:
    -- a rule's name then its params, each already spelled and already a
    -- `:matches`-style placeholder (a bare variable keeps its corners,
    -- anything else is shown as written) — 'RuleView' hands both over
    -- pre-formatted, so there is no printer policy left for this pane to
    -- choose. 'thena-boundary' crosses this exact formula against
    -- @:matches@ itself.
    matchRows rvs =
      [Heading "matches" (Just (length rvs)) | not (null rvs)]
        <> [Entry (unwords (ruleViewName rv : ruleViewParams rv)) | rv <- rvs]

    -- | One quest: the word, then what it is. **A statement is drawn at the
    -- root address and with no fold** — a parked quest's claim is not a
    -- subterm of the development the session is standing in, so there is
    -- nothing for the reading-flow fold to be relative to.
    questWidgets q =
      paneRowWidget (Entry (questViewWord q))
        : case questViewClaim q of
            -- | **The indent is an 'hBox' and not a 'padLeft'**, measured
            -- under a pty: 'padLeft' does not take its four columns off the
            -- width the term is flowed against, so a statement wider than the
            -- pane broke at the wrong place and lost the characters past the
            -- edge — @∀ (a : Nat) (b : Nat) (c : Nat) -> Eq {0} Nat …@ drew as
            -- @(a : Nat) -> (b : Nat) -> (@ and then @{0} Nat …@, with
            -- @c : Nat) -> Eq@ simply gone. An 'hBox' hands the flow a box of
            -- what is left, so every continuation line sits inside the indent
            -- too.
            AStatement d -> [str "    " <+> renderDisplay NoFold d]
            AnImportStanding header ->
              [paneRowWidget (Detail ("standing in a yield: " <> header))]

    -- | The accent edge, a title strip, then the content — never a full
    -- fill, per his correction. 'clickable' so a scroll-wheel event over
    -- this pane resolves to its own 'Name', not the row under it.
    --
    -- **A real border was tried here for `.jalivert/TUI.md` #8 and
    -- withdrawn the same session** — his own correction: what he actually
    -- wanted was the panes not touching the *screen's* edge, backdrop
    -- visible around the outside, not a drawn box around each one. The
    -- accent-edge-plus-title scheme stays exactly as it was; only 'draw's
    -- own outer margin is new, and since his ruling of 2026-11-16 it runs
    -- along the top and the left only.
    --
    -- **The edge is a glyph, not a solid cell** — his correction,
    -- 2026-09-29: a full-cell fill read as too thick, and a cell can't be
    -- fractional, so it's a left three-eighths block ('▎', same glyph
    -- `MS7-CLI` used for this) in the accent color against the panel
    -- background, still 'hLimit 1' wide.
    --
    -- **The edge bar sits outside the 'viewport', not inside it**, same
    -- reasoning as the title below. **And so does the title, as of this
    -- session** — `.jalivert/TUI.md`'s item 2: it used to be the first
    -- line of the 'vBox' that went *inside* the viewport, so it scrolled
    -- away with the content the moment the repl pane held enough turns to
    -- scroll at all. Only 'content' is inside the viewport now; the title
    -- is a fixed one-line header above it, sized by the outer 'vBox' like
    -- any other widget, the same move already made once for the edge bar's
    -- own infinite-height crash.
    pane key vp content = paneWith key vp content []

    -- | The same pane, plus fixed rows pinned below the viewport — the
    -- command bar and its note. **Below the viewport, not inside it**, for
    -- the reason the title is: anything inside scrolls away with the content,
    -- and a bar you are typing into must not.
    paneWith key vp content foot =
      clickable vp $
        hBox
          [ withAttr (attrName ("edge." <> key)) (hLimit 1 (fill '▎'))
          , vBox
              ( [ withAttr (attrName ("title." <> key)) (padLeftRight 1 (str key))
                , viewport vp Vertical content
                ]
                  <> foot
              )
          ]

-- | One turn, prompt (if any) then output, then a blank row — one empty
-- line between turns, his call, so each turn visibly ends before the next
-- begins. The most recent turn's output gets a thin accent bar to its left,
-- his request 2026-09-29 (thinner than a pane's own '▎' edge, so '▏',
-- one-eighth block, distinct glyph). The bar column is always reserved,
-- blank on every other turn, so a turn's text doesn't visibly shift
-- left/right as a newer one takes over the accent.
renderTurns :: [Turn] -> [Widget n]
renderTurns turns = zipWith renderTurn [1 :: Int ..] turns
  where
    lastIx = length turns
    renderTurn ix t =
      vBox (promptLine <> map (outputLine (ix == lastIx)) (turnOutput t) <> [str " "])
      where
        promptLine = case turnPrompt t of
          Nothing -> []
          Just line -> [str "❯ " <+> str line]
    -- | **The repl pane's output wraps too, and that is slightly past what he
    -- asked for.** His report named the output pane, but what it named is a
    -- message he could not read, and the engine's answer to a line is the same
    -- text in both places — `:show And.elim` is twelve lines of type either
    -- way. A prompt line and a document line are deliberately NOT wrapped:
    -- those are lines you put a caret in, and one that occupied two screen
    -- rows would have the editor's own single-row line jumping under it.
    outputLine accented l = marker <+> str " " <+> strWrapWith paneWrap l
      where
        marker = if accented then withAttr (attrName "accent.output") (str "▏") else str " "

-- | The script as a document: every committed line, with the live editor
-- standing wherever the caret is rather than pinned anywhere.
--
-- **The output of a line that worked is not shown.** The three panes to the
-- right already say what the session looks like at the caret, continuously,
-- and a document that interleaved responses would be a transcript again —
-- which is the thing this mode exists not to be. **A line the engine refused
-- does show its complaint**, dimmed beneath it, because that is the one case
-- the panes cannot express: the line is in the document, it changed nothing,
-- and it is yours to fix.
--
-- **A line below an in-place edit is drawn dim and is still drawn** — his
-- ruling of 2026-11-11 ('scriptStaleFrom'). It was run against a session the
-- line above no longer produces, so it is telling you about a state nothing
-- holds; the dim says exactly that, and the Enter that follows decides
-- whether it is re-run or cut. Before that ruling the lines were gone from
-- the screen and from memory on the first keystroke.
renderScript :: St -> Widget Name -> [Widget Name]
renderScript st inputLine =
  concat (zipWith row [0 ..] (stScript st)) <> tail'
  where
    -- | **The line a re-run is on right now, once it is worth saying** —
    -- `~twdbp`, his requirement of 2026-11-18 that a '>' stand beside it so
    -- position is not only available when a line happens to flip dim.
    -- 'Nothing' until the half-second threshold passes ('rrShow'), same as
    -- 'rerunNote' at the pane's foot — the two always appear together.
    rerunRow = case stRerun st of
      Just rs
        | rrShow rs
        , let done = scriptFrontier st - rrAt rs
        , done < length (rrPending rs) ->
            Just (rrAt rs + done)
      _ -> Nothing
    -- | **The caret's own row stops rendering as a live editor while a
    -- re-run is in flight** — `~twdbp`. Editing is suspended for the run's
    -- length ('handleEventForKeys' refuses the keys that would reach it
    -- anyway), so there is nothing here to edit; it falls through to 'dim',
    -- which is what a batch's lines already are the instant the run starts.
    row i sl
      | stScriptPos st == Just i, isNothing (stRerun st) = [marker <+> inputLine] <> refusal sl
      | dim i = [marker <+> withAttr (attrName "script.stale") (str (slText sl))] <> refusal sl
      | otherwise = [marker <+> str (slText sl)] <> refusal sl
      where
        marker
          | rerunRow == Just i = withAttr (attrName "script.marker") (str "> ")
          | stScriptPos st == Just i = withAttr (attrName "script.marker") (str "⟩ ")
          | otherwise = str "  "
    -- | **One dim, two causes** — the design's own words. A line is drawn
    -- dim when it has not run in this session (below the frontier, which is
    -- every line of a freshly opened proof-script) or when it stands at or
    -- below an edited line, whose session nothing is going to produce again.
    --
    -- **The edited line is itself dim, and that is `~htff2`** — his
    -- requirement of 2026-11-18, /"it will turn dim too, so that the user can
    -- see that this line is actually not evaluated"/. While the caret is on it
    -- the editor draws it and this is not asked; the moment the caret leaves,
    -- it is a line of the document holding text that never ran.
    dim i = i >= scriptFrontier st || case scriptStaleFrom st of
      Just j -> i >= j
      Nothing -> False
    refusal sl
      | slOk sl = []
      | otherwise =
          [ withAttr (attrName "script.refused") (strWrapWith paneWrap ("  " <> l)) | l <- slOutput sl ]
    -- | The composing line sits past the end, which is where a document's
    -- cursor is when you have not walked back into it.
    tail' = if isNothing (stScriptPos st) then [str "  " <+> inputLine] else []

-- | What is pinned below the script pane's viewport: the command bar while it
-- is open, otherwise whatever it last had to say, otherwise nothing.
scriptFoot :: St -> [Widget Name]
scriptFoot st = case stScriptBar st of
  Just bar ->
    -- 'vLimit 1' is load-bearing: 'fill' fills both axes, so without it the
    -- bar grew to the pane's whole remaining height and took the caret to
    -- the top of that block — row 21 of 39, measured. One row, filled right.
    [ vLimit 1 $
        withAttr (attrName "script.bar") $
          hBox
            -- **'❯', not ':'** — his report, 2026-10-20: the bar opened with
            -- a ':' in front of it and he read it as a colon already typed
            -- for him, so `:theorem foo : T` went in as `theorem foo : T`
            -- and came back *1:12: unexpected :*. The glyph has to be the
            -- ordinary prompt, because **the bar is not a colon-command
            -- slot**: its fallback is 'insertScriptLine', so most of what
            -- is typed here is a plain script line (`intro`, `succ zero`,
            -- a rule's name) with no colon at all. Pre-inserting a real ':'
            -- — the other way to make the old glyph honest — would mean
            -- deleting it for every one of those.
            [ withAttr (attrName "script.bar.mark") (str " ❯ ")
            -- The editor paints 'editFocusedAttr', which is the *panel*
            -- fill — so without this override the bar's surface stopped at
            -- its marker and the rest of the row read as document again.
            , overrideAttr editFocusedAttr (attrName "script.bar")
                (renderEditor (vBox . map (str . Text.unpack)) True bar)
            , fill ' '
            ]
    ]
  Nothing -> case rerunNote st of
    Just note -> [withAttr (attrName "script.marker") (str (" " <> note))]
    Nothing -> case stScriptNote st of
      Just note -> [withAttr (attrName "script.refused") (str (" " <> note))]
      -- | **A line's own output used to be drawn here, four lines of it, and
      -- it is the output pane's now** — `~wx6m3`, his request of 2026-11-11:
      -- /"That stuff that you show me at the bottom of the screen when I do
      -- `:show o` in a script-mode? That goes into a new pane also."/ The foot
      -- had room for four lines and cut `:show` on a proved theorem off
      -- mid-term; a pane has room, so the cap went with the move instead of
      -- travelling with it. 'lineInFocus' is what the pane reads, and it keeps
      -- the one thing the foot got right: it follows the caret, so nothing
      -- anywhere needs a taxonomy of which commands are queries.
      Nothing -> []

-- | **"re-running line N of X", and only once the run has gone on long
-- enough to say so** — `~twdbp`, his requirement of 2026-11-18: /"the entire
-- re-run takes longer than half a second... some visual signal that stuff is
-- happening."/ 'Nothing' throughout a re-run that finishes inside that
-- window, which draws nothing at all — the same silence a fast re-run has
-- always drawn.
rerunNote :: St -> Maybe String
rerunNote st = case stRerun st of
  Just rs | rrShow rs ->
    let done = scriptFrontier st - rrAt rs
     in Just ("re-running line " <> show (done + 1) <> " of " <> show (length (rrPending rs)))
  _ -> Nothing

-- | **What is in scope, grouped by where it came from** — `~5d35q`, and the
-- session it reads is 'activeSession', which is his ruling of 2026-11-12:
-- /"what's in scope where the caret is in live mode and what's in scope just
-- now in normal mode."/ Walking the document up walks this pane back with it,
-- the same way the proof-term and goals panes already follow the caret.
--
-- **Two things it cannot say yet, and both are `~6bckq` in
-- `.jalivert/REPORT.md` rather than an oversight here.**
--
-- 1. **A declaration made at the prompt is not in it.** Nothing on the
--    boundary enumerates one: `modulesLoaded`/`exportedByModule` only ever
--    answer for a module and a prompt declaration belongs to none. Measured
--    2026-11-12 against `lib:thena` — after
--    @data Nat : Type0 where { zero : Nat ; succ : Nat -> Nat }@ at the
--    prompt, `modulesLoaded` is still @[Prelude]@ and nothing names
--    @Nat.zero@. **A theorem is the one prompt-made thing that does cross**,
--    through `provedSlices`, which is why it is the first group.
-- 2. **A name is written in full, not as it would be written here.**
--    @Nat.zero@ reads as @zero@ once @open Nat@ is in force, and the function
--    that knows that — 'Thena.Core.Term.spelledIn' — is not on the boundary:
--    'Thena.View.spellingOf' hands out a 'Spelling' and nothing out here can
--    consume one. So the dotted form is what is drawn, which is right about
--    what is in scope and silent about how to type it.
globalGroups :: St -> [(String, [String])]
globalGroups st =
  ("proved in this session", [n | (n, _, _) <- provedSlices s])
    : [ (moduleText m, map nameDotted (exportedByModule m s)) | m <- modulesLoaded s ]
  where
    s = activeSession st

-- | **Every module that is in, newest first, and the file it was read from** —
-- `~t7wc8`. The prelude has no file of its own in this list, arriving with the
-- session rather than through an @import@, and is shown without one.
--
-- **It is the import tree and not a list** — `~84j24`, his request of
-- 2026-11-11, because leniency reaches all the way down and /"the module you
-- typed may be ✅ while something three levels beneath it is ⚠️"/. A module
-- nothing else imported is a root at depth 0; its own imports follow it, in
-- the order they were written, at depth 1, and so on down.
-- 'Thena.Driver.moduleImportsOf' is the only place the shape he wrote
-- survives — the closure is flattened into dependency order before it is
-- walked, which is what 'modulesLoaded' answers with.
--
-- **Every path is drawn, so a module two modules import is two rows** — his
-- ruling of 2026-11-18, taken against the measurement: /"my reason for the
-- pane was to see the dependency structure. That means only (a) is
-- acceptable."/ See 'Tui.Panes.meDepth' for the two renderings he turned down.
--
-- **The walk needs no cycle guard, because a cycle never reaches a loaded
-- session.** The engine refuses one by name before anything loads — @trouble@
-- answers `ImportCycle` with the chain in it (MS11 phase 274), the same walk
-- for a file's import and for the prompt's, and @thena-test@ holds both. So
-- the edges among 'modulesLoaded' are a DAG: the walk terminates, and every
-- loaded module is reachable from some module with nothing importing it, which
-- is why the roots cannot miss one. **Measured rather than assumed, under a
-- pty on 2026-11-18**: @import test.modules.LoopA@, whose pair import each
-- other, leaves the pane with the prelude in it and nothing else.
moduleEntries :: St -> [ModuleEntry]
moduleEntries st = concat [walk 0 m | m <- modulesLoaded s, m `notElem` imported]
  where
    s = activeSession st
    -- | **A root is a module nobody imports**, which is one he named at the
    -- prompt or in a script: the engine does not say which act pulled a module
    -- in, and /nothing imports it/ is the same answer for everything except a
    -- module he asked for twice — once directly and once through a parent —
    -- which the engine no-ops anyway and which is in under its parent either
    -- way.
    imported = concat [moduleImportsOf m s | m <- modulesLoaded s]
    walk depth m =
      entryFor depth m : concat [walk (depth + 1) i | i <- moduleImportsOf m s]
    entryFor depth m =
      ModuleEntry
        { meName = moduleText m
        , meFile = listToMaybe [p | (p, _) <- filesRead s, moduleOfFile p == Just m]
        , meMark = mark
        , meOpen = mark /= AllIn && Set.member (moduleText m) (stModulesOpen st)
        , meUnfinished = maybe [] (map flatten . partlyUnfinished) partly
        , meDepth = depth
        }
      where
        partly = modulePartly m s
        mark = marked partly m
    -- | **The three marks, and which one is `~nf5tx`'s ❌.** `moduleWhole` is
    -- `moduleLoaded` with no `Partly`, and everything in this list is loaded —
    -- so the question here is only whether there is a `Partly` and, if there
    -- is, whether *anything* got in under it. Measured under a pty on
    -- 2026-11-13: a module whose every item fails is still a loaded module,
    -- with an empty namespace, which is the state ❌ is for.
    marked partly m = case partly of
      Nothing -> AllIn
      Just _ | null (declaredByModule m s) -> NoneIn
      Just _ -> SomeIn
    -- | **The engine's own renderer, and that crossing is `~8btbp`.** An
    -- 'Unfinished' carries its reason as a 'Response', and
    -- 'Thena.Render.renderResponse' is the only thing that renders one —
    -- `Thena.Driver`'s own haddock says as much: /"a frontend showing a ⚠️ node
    -- wants to say what it says at the prompt, and renderResponse is already
    -- that renderer."/ There is no `Thena.View` for an unfinished item, so the
    -- pane rule — panes render through the views, `Thena.Render` being
    -- status-line text — has no other path here. It is in `.claude/CLOSEOUT.md`.
    flatten u =
      ( case unfinishedDeclares u of
          [] -> "an item"
          xs -> intercalate ", " xs
      , renderResponse s (unfinishedWhy u)
      )

-- | **Every file the session read, sorted into what it is** — the other half
-- of `~t7wc8`.
--
-- **The engine says what kind a path is, through 'Thena.Driver.kindOf'**, and
-- that is the point: the extensions are the engine's and a suffix test written
-- here would be this frontend keeping its own copy of them. What it cannot say
-- is /imported versus consulted/ — `moduleImports`/`moduleConsults` take a
-- module's items rather than a session — but a @LoadRules@ file in here was
-- consulted, which is the half of the distinction that is visible.
-- **Thena's own two files are told apart by 'stShipped'** so that his corpus is
-- never listed under our prelude.
fileEntries :: St -> [(FileKind, FilePath)]
fileEntries st = [(sortOf p, p) | (p, _) <- filesRead s]
  where
    s = activeSession st
    sortOf p
      | p `elem` stShipped st = AShippedFile
      | kindOf p == LoadRules = ARuleBase
      | Just m <- moduleOfFile p, m `elem` modulesLoaded s = AModuleFile
      | otherwise = AnotherFile

-- | **The line the output pane is about, and what it answered** — `~wx6m3`.
--
-- **In script mode it is the caret's line, and the last committed line when
-- the caret has moved past the end.** That second case is the one that makes
-- the pane work: submitting @:show Bit.o@ leaves the caret composing a new
-- line, so a pane that only ever drew the caret's own line would go empty at
-- exactly the moment the answer arrived. In the ordinary REPL it is the last
-- turn, whose output the transcript also shows — uncapped here, which is the
-- point.
-- | What the output pane is showing, as something comparable across one
-- event — 'handleEvent' snaps the pane back to the bottom when this changes
-- (`~3fs3f`). **The turn count rides along with the text** because an answer
-- can be replaced by an identical one: `:show And.elim` twice in a row is the
-- same two lines, and only the count says a second answer arrived.
outputShown :: St -> (Int, (Maybe String, [String]))
outputShown st = (length (stTurns st), lineInFocus st)

lineInFocus :: St -> (Maybe String, [String])
lineInFocus st
  | stScriptMode st = case caretLine of
      Just sl -> (Just (slText sl), slOutput sl)
      Nothing -> case reverse (stScript st) of
        (sl : _) -> (Just (slText sl), slOutput sl)
        [] -> (Nothing, [])
  | otherwise = case reverse (stTurns st) of
      (t : _) -> (turnPrompt t, turnOutput t)
      [] -> (Nothing, [])
  where
    caretLine = stScriptPos st >>= \i -> nthOf i (stScript st)

-- | The `:load` dropdown, as its own layer positioned by the caret's actual
-- screen coordinates from the *previous* render — 'Brick.Main.lookupExtent'
-- only works post-render, so this is one frame behind by construction, the
-- standard Brick technique for a caret-anchored popup.
--
-- **Flips above the caret past 80% of the pane's depth, below it otherwise**
-- — his rule, 2026-09-29, since the prompt can now be anywhere in the pane
-- (it used to always sit at the fixed bottom row, where "above" was the only
-- option that fit). 80% is a starting point he named, not measured; nothing
-- here should read it as final.
dropdownLayer :: St -> [Widget Name]
dropdownLayer st = case (stDropdown st, loadPathPrefix line) of
  (Just ld, Just prefix) ->
    popupAt st (pathStartOff line + segOff prefix) (length (ldEntries ld)) LoadPopup
      (zipWith (loadRow (ldSelected ld)) [0 :: Int ..] (ldEntries ld))
  _ -> []
  where line = concatMap Text.unpack (getEditContents (stInput st))

-- | One directory entry as a row: the base name to look at, while the full
-- path stays beside it in 'ldEntries' for Tab and Enter to act on — the
-- typed directory is already on the input line, so repeating it in every
-- row is noise (his `.jalivert/TUI.md` #2). Values may trail a slash
-- ('loadDropdownEntries'), which is not part of the name.
loadRow :: Maybe Int -> Int -> String -> PopupRow
loadRow selected i name = PopupRow (takeFileName (dropTrailingPathSeparator name)) (Just i == selected) False False

-- | The completion dropdown, positioned the same way — see 'popupAt'.
offerDropdownLayer :: St -> [Widget Name]
offerDropdownLayer st = case liveOffers st of
  Just od | not (null (odRows od)) ->
    popupAt st (odWordStart od) (length (odRows od)) OfferPopup
      (zipWith (offerRowToPopup (odSelected od) (odJevPicked od)) [0 :: Int ..] (odRows od))
  _ -> []

-- | **The completion dropdown as the keyboard and the screen see it:
-- 'Nothing' under @:dropdown off@** — `~492hq`, his sequencing ruling of
-- 2026-11-19.
--
-- **One function and not a flag tested at each binding, which is the whole
-- reason it exists.** The dropdown is consulted in six places — Enter, Tab
-- and Esc in both keyboards, the arrows, the whisper and the drawing — and
-- /disabled/ has to mean the same thing in all six or the switch leaves a
-- key that still accepts a row nobody can see.
--
-- **'stOfferDropdown' itself is untouched and is still built on every
-- keystroke.** That is what @disabled, not deleted@ comes to: the rows are
-- the suggestion strip's own source ('draw''s @stripLabels@), Jev still
-- ranks them, @:preselect@ still sets a selection in them, and nothing of
-- the dropdown's code, attrs or tests has moved.
--
-- **The whisper goes with it, deliberately.** @offerGhost@ renders the
-- selected row's untyped remainder, and a whisper driven by a list that is
-- not on screen is the staleness part one §4 of
-- @discussion/the-dropdown-is-the-wrong-element.md@ is about, with the one
-- thing that explained it removed.
--
-- **The @:load@ path dropdown is NOT gated.** It is a different element with
-- a different job, and nothing in this design replaces it.
liveOffers :: St -> Maybe OfferDropdown
liveOffers st = if stDropdownOn st then stOfferDropdown st else Nothing

-- | **The suggestion pane's cells, and they are Jev's or there are none** —
-- `~w2tk2` slices 2 and 3b.
--
-- **Read by the drawing and by the keymap, which is the point of its being a
-- function.** 'draw' cuts it to the grid's capacity and the F-keys index
-- into it; if the two computed it separately a key could land on a cell that
-- was not drawn.
--
-- **NOTHING IN THIS PANE IS ANYTHING BUT JEV'S — HIS INSTRUCTION,
-- 2026-11-19, said five times and spelled out the last time**: /"the
-- suggestion pane's 12 suggestions (or 11 because I don't know if we can
-- capture F11) are all from Jev. **We don't show suggestions that are not
-- from Jev**."/
--
-- So this is the **scored prefix** of 'stSlate' and never the whole of it.
-- 'slateJevPicked' is how many leading rows Jev's answer named
-- ('jevOrderRows' sorts them to the front in Jev's own order), so taking
-- that many is exactly /the ones Jev suggested/ and nothing else can reach a
-- cell.
--
-- **'stSlate' itself stays whole, and that is not a loophole.** It is the
-- candidate pool the next request is built from — Jev has to be asked about
-- something — so the pool is the engine's full offer list and what the pane
-- shows is this prefix of it.
--
-- **With no answer in hand the pane is empty, and that is the instruction
-- applied rather than a gap.** 'slateJevPicked' is zero before the first
-- answer lands, so the strip shows nothing for the ~300ms a request takes,
-- and shows nothing at all where Jev cannot be reached (no key, no network).
-- The question we had raised about what to show in that window
-- (@discussion/the-dropdown-is-the-wrong-element.md@ §15 q1) is answered by
-- his rule: nothing that is not from Jev.
--
-- **Filtered to rows with something to insert.** A row that cannot be
-- accepted has no business occupying a numbered slot — his design has no
-- unselectable rows in it, every cell being reachable by its own key.
--
-- **Empty with the strip closed**, so no F-key does anything for a pane that
-- is not on screen.
--
-- **`:jev off` is the one state that shows a row Jev did not name** —
-- `~zttnz`, his instruction of 2026-11-19: /"when Jev is disabled, the
-- twelve or 11 or however many options are simply alphabetically sorted"/.
-- The rows sorted are **this pane's own candidates** — what the statement
-- grammar offers for the line, which is the only list whose rows carry an
-- insertion — and not @matchesView@, which is the rules that apply at the
-- focus and has no insertion to give a cell.
stripSlateOf :: St -> [OfferRow]
stripSlateOf st
  | not (stripOpen (stStrip st)) = []
  | not (stJevOn st) = sortOn rowLabel (slateRows (stSlate st))
  | otherwise = take (slateJevPicked (stSlate st)) (slateRows (stSlate st))

-- | **The grid as the keymap can know it** — `~w2tk2` slice 3a.
--
-- **The drawing works the same arithmetic out from the width it is handed,
-- and this works it out from the width the last frame reported.** Two
-- sources, one function ('Tui.Layout.stripGrid'), which is what keeps the
-- keys and the cells the same set: the alternative is the keymap capping at
-- 'Tui.Layout.stripSlotKeys' and the grid capping at its slots, and those
-- two numbers are not equal — at his geometry they are ten and nine.
--
-- **The one frame it can be wrong about is the frame after a resize**, where
-- the width it holds is the width before it. A narrower window for one frame
-- means an F-key could take a candidate that frame no longer draws; the
-- screen itself is never wrong, because 'draw' uses the live width. The
-- strip's own drag does not have this exposure at all — a drag changes
-- 'Tui.Layout.stripRows', which is read from state by both.
--
-- **An empty grid before the first frame.** With no width reported there is
-- no grid to speak of, so no key takes anything until something has been
-- drawn — which is a frame earlier than anyone can press one.
--
-- **The hint is now one of the grid's inputs** — `~w2tk2` slice 4 — so this
-- reads 'stripHintRowsFor' where 'draw' reads the same two functions off the
-- live width. A hint long enough to take a row off the grid takes the keys
-- on that row with it, which is the whole point of 3a stated for a second
-- source of shrinking.
stripGridFor :: St -> Maybe Grid
stripGridFor st =
  (\w -> stripGrid w (stripBodyRows (stripRows (stStrip st))) (stripReserveOf st w))
    <$> stStripWidth st

-- | **The rows the grid does not get** — `~8cr56`. The hint's own height
-- plus the reply row when there is a hint, and **zero when there is not**:
-- his /"Why do I only get 2 suggestions?"/ was five of seven body rows held
-- for regions with nothing in them.
--
-- **The reply row goes with the hint and not with the strip.** It is a row
-- to answer a hint in, so a strip that is not saying anything has nothing to
-- answer; reserving it unconditionally was reserving a row for a
-- conversation that had not started.
stripReserveOf :: St -> Int -> Int
stripReserveOf st w = stripSeparatorRows + hint + stripReplyRows
  where
    -- **The hint's rows and the blank one under them go together**, so that
    -- an answer arriving never pushes the ask row off the bottom and the
    -- line he asked for is there whenever there is an answer to separate.
    hint = if isJust (stHint st) then stripHintRowsFor st w + stripHintGapRows else 0

-- | **How tall the hint region is at a given content width** — `~w2tk2`
-- slice 4.
--
-- **The keymap's copy of what 'draw' works out**, and the two are the same
-- two calls in the same order ('Tui.Panes.stripHintLines' for the lines,
-- 'Tui.Layout.stripHintUsed' for the height) rather than two pieces of
-- arithmetic that happen to agree today. The width is the argument because
-- that is the one thing the two sides do not share: 'draw' has the live one
-- and this has 'stStripWidth''s, one frame behind.
stripHintRowsFor :: St -> Int -> Int
stripHintRowsFor st w =
  stripHintUsed
    (stripBodyRows (stripRows (stStrip st)))
    (maybe 0 (length . stripHintLines w) (stHint st))

-- | **What is actually on a cell, and therefore what an F-key may take** —
-- `~w2tk2` slice 3a, the cap his property 2 asks for: /"it should not list
-- tens or hundreds of options"/.
--
-- **The slate is longer than this and deliberately so.** The heading says
-- @offers  9 of 318@ — how many he can press and how many the engine
-- offered, which are two different facts and the second is the one that
-- tells him the grid is a selection and not the whole list. So the cap is on
-- the cells and the keys, never on the count.
--
-- **Capped by today's ranking, which is the order the slate is already in**:
-- Jev's picks floated to the top ('floatJevRows') and the engine's own
-- tokens-before-productions order below them. Taking the grid's worth off
-- the front is therefore taking the best of them, for whatever ranking there
-- is on the day.
stripShownOf :: St -> [OfferRow]
stripShownOf st = case stripGridFor st of
  Nothing -> []
  Just grid -> take (gridSlots grid) (stripSlateOf st)

-- | **The slate for the line as it stands, from the session and the line and
-- nothing else** — `~3gn2r`. Pure, so every place that changes either of
-- those two can put a fresh one in state without an 'EventM'.
--
-- **Built through 'buildOfferDropdown' rather than beside it.** The strip's
-- order is then the dropdown's order by construction, instead of two lists
-- that have to be kept agreeing; the selection it builds is thrown away, so
-- 'False' goes in for @:preselect@ whatever 'stAutoSelect' says — the strip
-- has no highlight to preselect.
--
-- **A `:load` path line is 'emptySlate'**, the one case 'refreshOfferDropdown'
-- also declines: the path's own candidates are a directory listing and
-- 'stDropdown' owns them, so asking the statement grammar would be asking
-- the wrong question a second time.
slateFor :: St -> Slate
slateFor st
  | isJust (loadPathPrefix line) = emptySlate
  | otherwise = slateFromView col (statementOfferView (activeSession st) before after)
  where
    line = concatMap Text.unpack (getEditContents (stInput st))
    (_, col) = getCursorPosition (stInput st)
    (before, after) = splitWritten line col

-- | 'slateFor' once the view is in hand — also the launch slate's own path,
-- where 'runTui' has a 'Session' and no 'St' to ask yet.
slateFromView :: Int -> OfferView -> Slate
slateFromView col ov = slateOfDropdown (buildOfferDropdown False col ov)

-- | **The slate a built dropdown carries inside it** — the rows it can
-- accept and the span an accept replaces, with the highlight dropped.
--
-- **'refreshOfferDropdown' goes through this rather than through
-- 'slateFromView'**, so one keystroke runs one 'statementOfferView' and one
-- 'buildOfferDropdown' exactly as it did before `~3gn2r`: the strip's list
-- and the popup's list are not two computations that could disagree, they
-- are one value read two ways.
slateOfDropdown :: Maybe OfferDropdown -> Slate
slateOfDropdown Nothing = emptySlate
slateOfDropdown (Just od) = Slate
  { slateRows = filter (isJust . rowInsert) (odRows od)
  , slateStart = odWordStart od
  , slateReplaceLen = odReplaceLen od
  , slateJevPicked = odJevPicked od
  }

offerRowToPopup :: Maybe Int -> Int -> Int -> OfferRow -> PopupRow
offerRowToPopup selected jevPicked i (OfferRow label ins) =
  PopupRow label (Just i == selected) (isNothing ins) (i < jevPicked)

-- * The session picker

-- | The picker, centred over the whole layout — see 'Picker'.
--
-- **Centred rather than anchored to the input line.** Every other floating
-- thing here hangs off the caret ('popupAt') because it is about the text
-- under it; this one is about the project, so there is no column it belongs
-- beside, and the middle of the screen is where a modal is looked for.
pickerLayer :: St -> [Widget Name]
pickerLayer st = case stPicker st of
  Nothing -> []
  Just pk -> [centerLayer (renderPicker pk)]

-- | **The dropdown's own surface, its own selected-row swap, its own
-- scrolling** — a session picker that looked like a fifth kind of floating
-- box would be a new visual language for the same gesture. The box hugs its
-- widest line, title and foot included, so nothing sticks out one side (his
-- `.jalivert/TUI.md` #4, #6, #7).
renderPicker :: Picker -> Widget Name
renderPicker pk = Widget Fixed Fixed $ do
  ctx <- getContext
  render (pickerBox (ctx ^. availWidthL) pk)

-- | The box, against a known width. **The width is the terminal's own**, read
-- from the render context rather than fixed: a row here ends in a path, which
-- is both the longest field and the one that identifies a session opened from
-- a file, and a constant cap ellided it on a 120-column screen with forty
-- columns going spare. Measured under a pty, 2026-11-12, before and after:
-- @from examples\/Stlc08PreservationBy…@ against the whole path.
pickerBox :: Int -> Picker -> Widget Name
pickerBox avail pk@(Picker for selected) =
  withAttr (attrName "dropdown") $
    hLimit boxWidth $
      vBox
        ( [ faint titleText, blank ]
            <> [ vLimit visibleH (viewport PickerVP Vertical (vBox (zipWith row [0 ..] texts))) ]
            <> [ blank
               , faint keysText
               -- | **The handle, for the one row that is lit.** The rows
               -- themselves do not carry it: a slug is what you *type* and
               -- the whole point of this dialog is that you no longer have
               -- to. It stays on screen anyway, because `:script resume
               -- ‹slug›` is still there for anyone who would rather type it,
               -- and nothing else in the TUI shows a slug now.
               , faint handleText
               ]
        )
  where
    -- | The box keeps a column of backdrop on either side of itself, the same
    -- one cell the whole layout keeps against the screen's edge ('draw''s own
    -- 'padAll' 1) — a modal flush against the terminal's edge reads as part
    -- of the furniture rather than as something floating over it.
    cap = max 24 (avail - 2 - 2 * dropdownMarkerWidth)
    texts = map (capText cap) (pickerTexts for)
    titleText = pickerTitle for
    keysText = pickerKeys for
    handleText = pickerHandle pk
    boxWidth = maximum (0 : map length (texts <> [titleText, keysText, handleText])) + 2 * dropdownMarkerWidth
    visibleH = popupVisibleH (pickerCount pk)
    blank = str (replicate boxWidth ' ')
    faint t = withAttr (attrName "dropdown.faint") (str (padTo boxWidth (dropdownMargin <> t)))
    row i t = mark (styled (str (padTo boxWidth (dropdownMargin <> t))))
      where
        styled = if i == selected then withAttr (attrName "dropdown.selected") else id
        mark = if i == (selected :: Int) then visible else id

-- | A session as one row of the picker: **what it is called, where its caret
-- stood, and where its lines came from** — and no slug, see 'renderPicker'.
--
-- The three are padded into columns across the whole list rather than run
-- together, so the dates line up under each other and the eye can scan one
-- column at a time. @from@ is last because it is the one field that is
-- usually absent (a typed session came from nowhere) and the only one long
-- enough to ellide.
pickerTexts :: PickerFor -> [String]
pickerTexts (PickSession rows) =
  [ padTo nameW (stName s) <> "   " <> padTo placeW (place s) <> from s | s <- rows ]
  where
    place s = show (stCaret s) <> "/" <> show (stLines s) <> " lines"
    from s = maybe "" ("   from " <>) (stFrom s)
    nameW = maximum (0 : map (length . stName) rows)
    placeW = maximum (0 : map (length . place) rows)
-- | **A model as its id, then its context window and price** — padded into
-- the same two columns down the list, for the reason the session rows are:
-- the eye scans one column at a time. 'Tui.Hint.modelRow' decides what the
-- two fields are; this only lines them up.
pickerTexts (PickModel rows) =
  [ padTo idW i <> "   " <> extra | (i, extra) <- cells ]
  where
    cells = map modelRow rows
    idW = maximum (0 : map (length . fst) cells)

pickerTitle :: PickerFor -> String
pickerTitle (PickSession _) = "stored sessions in " <> databaseDir
-- | **Says the count, because this list is long enough that the filter is
-- the feature.** `:models` on its own is 479 rows; `:models claude` is the
-- handful he meant, and the title is where he can see which of the two he
-- is looking at.
pickerTitle (PickModel rows) = show (length rows) <> " models at openrouter"

pickerKeys :: PickerFor -> String
pickerKeys (PickSession _) = "↑↓ move · Enter resume · Esc cancel"
pickerKeys (PickModel _) = "↑↓ move · Enter use this model · Esc cancel"

-- | **The typed form of the row that is lit** — the same reasoning the
-- session picker's own foot carries: the row does not show the handle
-- because the whole point of the dialog is that you no longer type it, and
-- it stays on the foot anyway because the typed door is still open.
pickerHandle :: Picker -> String
pickerHandle pk = case pkFor pk of
  PickSession rows -> maybe "" ((":script resume " <>) . stSlug) (at rows)
  PickModel rows -> maybe "" ((":model " <>) . Text.unpack . mdId) (at rows)
  where
    at :: [a] -> Maybe a
    at = listToMaybe . drop (pkSelected pk)


-- | One row of any dropdown, before it becomes a 'Widget' — shared by
-- ':load''s directory listing and the completion dropdown so both scroll
-- and pad exactly the same way, see 'renderPopup'.
data PopupRow = PopupRow
  { prText     :: String
  , prSelected :: Bool
  , prDim      :: Bool  -- ^ drawn muted rather than as a landing spot.
                          --
                          -- **Unreachable since `~bkzw9`, and kept on
                          -- purpose.** It was how a hint row (a nonterminal
                          -- or a token class) was shown; those rows are no
                          -- longer built, so nothing sets this 'True' today.
                          -- The mechanism stays because `~5f3k6` — where
                          -- that information goes instead — is open, and a
                          -- muted row is one of the answers still on the
                          -- table.
  , prJevPick  :: Bool  -- ^ one of Jev's own top three, floated to the
                          -- head of the list ('floatJevPicks') — drawn in
                          -- 'themeJevPick' so it reads as Jev's say-so and
                          -- not the engine's. 'False' for every row of the
                          -- ':load' dropdown, which never asks Jev anything.
  }

-- | **A dropdown with room to breathe, symmetric all round** — his
-- `.jalivert/TUI.md` items 4 and 7, then #6: no padding to the right (a row
-- used to end exactly at its own last letter), no minimum size (":load
-- examples" against a short match looked "starved"), then the opposite —
-- the 24-column floor that followed padded short rows far past their text
-- on the right only. Both were the same defect (a box that won't sit
-- symmetric round its content), so one shape: every row is the marker, the
-- text, and as much air right as the marker takes left, and the box hugs
-- the longest row — no floor, so nothing can stick out one side.
-- Past 'popupMaxRows' the list scrolls ('viewport' plus 'visible' on the
-- selected row, the same mechanism Brick's own editor/list widgets use, so
-- the selected row is always the one that scrolls into view — never lost
-- off either edge).
--
-- **Long rows ellide, values untouched.** Past 'popupTextCap' a row shows
-- an ellipsis; Tab and Enter act on the full text by row index, so
-- truncating display corrupts no accept.
--
-- **The breathing row lives on the far side only** ('padSide'): below the
-- content when the popup hangs under the input, above it when it flips
-- over — never the input side, or the content would drift from the line it
-- belongs to. Minimum-height fillers are the same far-side blanks
-- ('popupFarBlanks'), so a short list still stands 'popupMinRows' tall.
renderPopup :: Name -> PadSide -> [PopupRow] -> Widget Name
renderPopup vp padSide rows =
  withAttr (attrName "dropdown") $
    hLimit boxWidth $
      vBox (topPad <> [vLimit visibleH (viewport vp Vertical (vBox (map renderRow shown)))] <> bottomPad)
  where
    shown = map (truncateRow popupTextCap) rows
    maxText = maximum (0 : map (length . prText) shown)
    boxWidth = maxText + 2 * dropdownMarkerWidth
    visibleH = popupVisibleH (length rows)
    farBlanks = replicate (popupFarBlanks (length rows)) (str (replicate boxWidth ' '))
    (topPad, bottomPad) = case padSide of
      PadTop    -> (farBlanks, [])
      PadBottom -> ([], farBlanks)
    renderRow r = mark (styled (str (padTo boxWidth (dropdownMargin <> prText r))))
      where
        styled
          | prSelected r = withAttr (attrName "dropdown.selected")
          | prJevPick r  = withAttr (attrName "dropdown.jevpick")
          | prDim r      = withAttr (attrName "dim")
          | otherwise    = id
        mark = if prSelected r then visible else id

-- | Which side of the content the breathing row goes — always the far side
-- from the input line, decided once in 'popupAt' from the same flip that
-- positions the box, so padding and placement cannot disagree.
data PadSide = PadTop | PadBottom

padTo :: Int -> String -> String
padTo n s = s <> replicate (max 0 (n - length s)) ' '

-- | A row over the cap shows an ellipsis rather than running past the
-- pane — display only, the row's value keeps its full text.
truncateRow :: Int -> PopupRow -> PopupRow
truncateRow cap r = r { prText = capText cap (prText r) }

-- | Text past a cap, with an ellipsis standing for the rest.
capText :: Int -> String -> String
capText cap s
  | length s > cap = take (cap - 1) s <> "…"
  | otherwise = s

popupMinRows, popupMaxRows :: Int
popupMinRows  = 3
popupMaxRows  = 10

-- | The box never runs past this, marker and air included — his call, a
-- number to tune by eye rather than derive. Retuned 60 → 40: at 60 an
-- unfiltered list ballooned the box to triple its visible rows' width.
popupMaxWidth :: Int
popupMaxWidth = 40

-- | The text a row may hold before it ellides: the cap minus the marker on
-- one side and its matching air on the other.
popupTextCap :: Int
popupTextCap = popupMaxWidth - 2 * dropdownMarkerWidth

-- | What the viewport shows of a list: the rows, up to the scroll cap.
popupVisibleH :: Int -> Int
popupVisibleH n = min (max n 0) popupMaxRows

-- | Breathing blanks on the far side: at least the one pad row, more while
-- the list is short of 'popupMinRows'.
popupFarBlanks :: Int -> Int
popupFarBlanks n = max 1 (popupMinRows - n)

-- | The whole box, content plus far-side blanks — what 'popupAt'
-- positions against above the line, so a flipped box lands its content
-- against the input rather than a row short.
popupTotalH :: Int -> Int
popupTotalH n = popupVisibleH n + popupFarBlanks n

-- | Position a popup at a given column of the input's own text (column 0
-- is the text's own left edge, per 'stInputExtent's own doc) — the math
-- 'dropdownLayer' always used, factored out so two popups position
-- themselves identically rather than drifting from two copies. Flips above
-- the input past 80% of the pane's depth, below it otherwise — his rule,
-- 2026-09-29; see the historical note this carries forward from
-- 'dropdownLayer's original home.
--
-- Builds the content itself from the rows, so the flip that positions the
-- box also sides its breathing row ('PadTop'/'PadBottom') and sizes
-- against the whole rendered height ('popupTotalH') — one decider, never a
-- pad here and a height there disagreeing.
--
-- **Above the line the rows run bottom-to-top** (his `.jalivert/TUI.md`
-- #16): what was first sits closest to the input either way — direction
-- and distance to the active line matter, so a flipped box is not the same
-- list merely translated. Navigation swaps to match (see the arrow-key
-- clauses): Down always travels visually down.
--
-- **One row of air from the input, his `.jalivert/TUI.md` #15** — below it
-- the box opens a row lower, above it a row higher. Distance, not a drawn
-- widget: below shows empty pane, above the document behind.
popupAt :: St -> Int -> Int -> Name -> [PopupRow] -> [Widget Name]
popupAt st col n vp rows = case stInputExtent st of
  Nothing -> []
  Just inputExt -> [translateBy (Location (popupCol, popupRow)) content]
    where
      above = popupAbove st
      content = renderPopup vp (if above then PadTop else PadBottom) (if above then reverse rows else rows)
      popupCol   = max 0 (locationColumn (extentUpperLeft inputExt) + col - dropdownMarkerWidth)
      inputRow   = locationRow (extentUpperLeft inputExt)
      popupRow = if above then inputRow - popupTotalH n - 1 else inputRow + 2

-- | Whether a popup at the input flips above it: past 80% of the pane's
-- depth, below it otherwise — his rule, 2026-09-29. One helper, called by
-- 'popupAt', the refresh paths and the arrow keys alike, so placement is
-- decided once and never recomputed ad hoc. Extents lag a frame behind by
-- construction, uniformly, like everything else positioned from them.
popupAbove :: St -> Bool
popupAbove st = case stInputExtent st of
  Nothing -> False
  Just inputExt ->
    let pane = case stPaneExtent st of
          Just p  -> p
          Nothing -> inputExt
        inputRow = locationRow (extentUpperLeft inputExt)
        paneRow = locationRow (extentUpperLeft pane)
        paneHeight = snd (extentSize pane)
        frac :: Double
        frac = if paneHeight <= 0 then 0 else fromIntegral (inputRow - paneRow) / fromIntegral paneHeight
     in frac > 0.8

-- | The left margin every dropdown row carries, selected or not — his
-- `.jalivert/TUI.md` #20: the arrow used to be the only mark of selection,
-- which read as weak next to a real background swap, so it's gone and
-- 'renderRow's own "dropdown.selected" attr covers the whole row instead.
-- Kept as blank space rather than deleted outright, so the reserved margin
-- — 'dropdownMarkerWidth' — and everything positioned against it
-- ('dropdownLayer's own column math) stays exactly as it was.
dropdownMargin :: String
dropdownMargin = "  "

dropdownMarkerWidth :: Int
dropdownMarkerWidth = length dropdownMargin

-- | What accepting the highlighted row would write at the caret, dimmed,
-- and how many real characters right after the caret it stands in for
-- consuming — his `.jalivert/TUI.md` #17, generalized by #21: not only a
-- pure suffix when the caret sits at the end of the line, but wherever the
-- caret actually stands, since "walk into a box" (his own words) is exactly
-- what leaves it somewhere else.
--
-- **`:load`'s own dropdown keeps the simple, end-only form** — a path is
-- always typed forward, so the caret is always at the end while it shows,
-- and 'acceptLine' being a pure extension past what's typed is the same
-- check as before: the accepted line must keep everything already there,
-- or a rewrite behind the cursor would show as a fiction.
--
-- **The completion dropdown uses 'offerGhost's general form.** Mirrors the
-- two Enter/Tab branches' own math (`acceptOfferRow`), so the whisper and
-- the landing cannot disagree.
ghostAt :: String -> Int -> Maybe LoadDropdown -> Maybe OfferDropdown -> (String, Int)
ghostAt line col ld od = case ld of
  Just (LoadDropdown entries (Just i)) | i < length entries ->
    let new = replacePathPrefix line (entries !! i)
     in if col == length line && line `isPrefixOf` new && new /= line
          then (drop (length line) new, 0)
          else ("", 0)
  _ -> maybe ("", 0) id (od >>= offerGhost col)

-- | The general case 'ghostAt' needs: of the candidate's own insertion
-- text, how much has the caret already walked past? Zero standing right on
-- a box ('odWordStart' is the caret's own column then, 'offerAt's
-- 'offeredReplaces' path) — so the whole insertion shows, which is what
-- "insert at the caret" (his `.jalivert/TUI.md` #21) asks for exactly.
-- Positive mid-completion of a bare word ('odWordStart' is the word's
-- *start*, behind the caret) — so only the untyped remainder shows, the
-- familiar "ack" of "attack". Either way, real text before the caret is
-- untouched by this, which is the whole reason Brick's own cursor
-- placement (a column count into the *unmodified* zipper, 'Edit.hs's own
-- 'renderEditor') stays correct without knowing any of this happened —
-- only what comes after the caret ('skip', how many real characters the
-- accept consumes there) needs the render side to act on it at all.
offerGhost :: Int -> OfferDropdown -> Maybe (String, Int)
offerGhost col od = do
  i <- odSelected od
  ins <- rowInsert (odRows od !! i)
  ghostOfInsert col (odWordStart od) (odReplaceLen od) ins

-- | The same arithmetic, for an insertion the caller has already chosen —
-- `~w2tk2` slice 2, where the whisper's row is **slot 1 of the strip** and
-- not the dropdown's selection.
--
-- **Split out rather than parameterised by an index**, because the strip's
-- slate is a filtered list and an index into it is not an index into
-- 'odRows'. What both callers genuinely share is this: given the text an
-- accept would write, how much of it has the caret already walked past.
--
-- **It takes the two numbers and not a dropdown** — `~3gn2r`. The strip's
-- caller has a 'Slate' and may have no dropdown at all (after an Enter,
-- after Esc), and the arithmetic never wanted anything else from one.
ghostOfInsert :: Int -> Int -> Int -> String -> Maybe (String, Int)
ghostOfInsert col wordStart replaceLen ins =
  let typedLen = col - wordStart
   in if typedLen < 0 || typedLen > length ins
        then Nothing
        else Just (drop typedLen ins, max 0 (replaceLen - typedLen))

-- | A line, run against the session, and its 'Response' rendered as lines
-- via 'Thena.Render.renderResponse' — a status-line-shaped placeholder for
-- the REPL pane's own output; the side panes render through 'Thena.View'.
--
-- **A file-naming response is followed through 'Thena.Files.following'** —
-- the IO half 'oneLine' cannot do itself (§12 invariant 4): the driver only
-- names the file ('LoadRequested' and kin, which render as nothing), so this
-- reads it, renders what the load said against the loaded session, and
-- stores that session — the same two steps the terminal loop in
-- 'app/Repl.hs' takes.
--
-- **Two TUI-local pseudo-commands, intercepted before 'oneLine' ever sees
-- them**: `:theme <name>` and `:fold on|off`. Neither is instral syntax —
-- same standing as `:load`'s path completion, his ruling 2026-09-28:
-- *"it is not instral. Therefore special casing it in our TUI's repl is
-- ok."*
--
-- **Every branch, at the end, records where the input and the repl pane
-- itself now sit on screen** — 'stInputExtent'/'stPaneExtent', read back via
-- 'lookupExtent' after whatever the event did, for the *next* 'draw' to
-- position the dropdown against (see 'dropdownLayer'). This is the outer
-- wrapper every branch runs through, not a per-branch call, so nothing can
-- forget it.
handleEvent :: BrickEvent Name AppEvent -> EventM Name St ()
handleEvent ev = do
  focusBefore <- outputShown <$> get
  handleEventInner ev
  focusAfter <- outputShown <$> get
  -- | **The output pane shows the END of an answer, not its beginning** —
  -- `~3fs3f`, his instruction of 2026-11-12: /"needs to be scrolled to the
  -- bottom any time its contents are too much to show. It stays at the top of
  -- the output and that's not helping."/ A `:show` of a long type is a dozen
  -- lines in a pane a dozen rows tall, and the line that says what the answer
  -- *is* is the last one.
  --
  -- **Here, and only when the answer itself changed.** A viewport keeps its
  -- offset across redraws, so a pane snapped to the bottom stays there while
  -- he types; pinning it every frame instead ('visible' on the last row) would
  -- have taken the wheel away from this one pane, which already scrolls. So
  -- the rule is tail-the-output: a new answer lands at the bottom, and from
  -- there the wheel is his.
  --
  -- **The turn count is in the comparison because the text alone is not
  -- enough**: measured under a pty, re-running `:show And.elim` after scrolling
  -- up produced an answer identical to the one on screen, so a comparison of
  -- the text saw no change and the pane stayed where it had been dragged.
  when (focusAfter /= focusBefore) (vScrollToEnd (viewportScroll (PaneVP Output)))
  inputExt <- lookupExtent Input
  paneExt <- lookupExtent HistoryVP
  -- | **The strip's own width, for the grid the keymap has to agree with** —
  -- `~w2tk2` slice 3a. The extent is the viewport 'pane' reports, and the
  -- body is drawn inside a @padAll 1@, so the content has two columns fewer.
  stripExt <- lookupExtent StripVP
  st <- get
  put st
    { stInputExtent = inputExt
    , stPaneExtent = paneExt
    , stStripWidth = (\e -> max 0 (fst (extentSize e) - 2)) <$> stripExt
    }

-- | Three keyboards in one app, and which one an event reaches is decided
-- here rather than guarded at twenty branches: the command bar while it is
-- open, live-script mode's own keys while the mode is on, and otherwise the
-- ordinary REPL exactly as it always was.
handleEventInner :: BrickEvent Name AppEvent -> EventM Name St ()
handleEventInner ev = do
  held <- stEscRun <$> get
  case held of
    Nothing -> do
      handleEventFor ev
      armEscRun ev
    Just p -> continueEscRun p ev

handleEventFor :: BrickEvent Name AppEvent -> EventM Name St ()
handleEventFor ev = do
  resized <- handleResize ev
  if resized
    then pure ()
    else do
      folded <- handlePaneClick ev
      if folded then pure () else handleEventForKeys ev

-- | **Clicking a module's row unfolds what did not go in, and clicking it
-- again folds it away** — `~nf5tx`, his instruction of 2026-11-13.
--
-- Returns whether it took the event. **After 'handleResize' and before the
-- keyboards**: a press on a row is not a press on an accent bar — the bar is
-- outside the viewport the rows are in — so the two cannot both claim one
-- click, and the order here is only so that a drag in progress keeps the
-- events it needs.
--
-- **Only a row drawn with a name of its own can arrive here at all** — a
-- 'Tui.Panes.Tap' or a 'Tui.Panes.TapHeading'. In the modules pane that is a
-- ⚠️ or ❌ module and nothing else ('moduleRows' draws a whole module as a plain
-- entry with no name to click), so there is no "nothing to unfold" case to
-- answer; in the globals pane it is every namespace heading, which can always
-- be folded.
handlePaneClick :: BrickEvent Name AppEvent -> EventM Name St Bool
handlePaneClick ev = case ev of
  MouseDown (ModuleRow m) V.BLeft _ _ -> do
    st <- get
    put st { stModulesOpen = toggle m (stModulesOpen st) }
    pure True
  -- **Every namespace heading is clickable, so there is no inert row here** —
  -- `~6n5qb`, unlike 'ModuleRow' above, where only a module with something to
  -- unfold is drawn as a target at all.
  MouseDown (GlobalGroup label) V.BLeft _ _ -> do
    st <- get
    put st { stGlobalsClosed = toggle label (stGlobalsClosed st) }
    pure True
  -- | **A click on the reply row opens it** — `~w2tk2` slice 5. There is
  -- nothing to do if it is already open: a second click lands in the
  -- editor's own text, which brick's own cursor placement already handles,
  -- so this only ever fires the row's first click.
  MouseDown StripReply V.BLeft _ _ -> do
    st <- get
    case stStripReply st of
      Just _ -> pure True
      -- | **THE CLICK ONLY TAKES THE KEYBOARD; TAB IS WHAT MAKES THE
      -- SENTENCE REAL — HIS, 2026-11-19**: /"I don't want the click to turn
      -- it into a real prompt. I want the tab to do that. Like is usually
      -- the UX in editors and prompts."/
      --
      -- So the row opens **empty** and the sentence stays dim behind the
      -- cursor, which is the shape this TUI already uses at its own prompt:
      -- the whisper is dimmed and Tab accepts what is lit (his
      -- `.jalivert/TUI.md` #17). 'handleStripReplyEvent' has the Tab.
      Nothing -> do
        put st { stStripReply = Just (E.editorText StripReply (Just 1) Text.empty) }
        pure True
  _ -> pure False
  where
    toggle x set
      | Set.member x set = Set.delete x set
      | otherwise = Set.insert x set

-- | **A pane being pulled wider or narrower by its accent bar** — `~gs8tj`.
-- Returns whether it took the event, so that everything it does not take
-- reaches the keyboards below exactly as it did before.
--
-- **The bar follows the pointer, so pulling left widens.** A column is as
-- wide as its widest pane and the document takes what is left, so widening
-- the widest pane of a column moves that column's left edge — and the bar
-- with it — towards the pointer. Pulling right therefore narrows. The one
-- case where the bar does not move under the hand is a pane that is not its
-- column's widest: it still changes width, but the column's edge is somebody
-- else's.
--
-- **Both shapes of mouse event are handled, because brick sends both.**
-- Measured under a pty, 2026-11-12: a press inside a pane arrives as
-- 'MouseDown' with the column measured from that pane's own extent (the
-- panes are 'clickable'), and a press on the one-column stage gap between
-- panes belongs to no clickable extent and arrives raw, in absolute screen
-- coordinates. The same measurement is what established that a drag arrives
-- at all — vty asks for @ESC[?1002h@, button-event tracking, so motion with
-- the button held comes through as a run of 'MouseDown's at successive
-- columns.
handleResize :: BrickEvent Name AppEvent -> EventM Name St Bool
handleResize ev = case ev of
  -- | **A press inside a pane, which is the bar when its column is 0.** The
  -- event's own name says which pane, and that is the whole of the hit test —
  -- each pane's bar sits at its own left edge since `~rr8bx`, so the name is
  -- enough and the row never has to be consulted here.
  MouseDown n V.BLeft mods (Location (c, r)) -> do
    corner <- paneCorner n
    st <- get
    case (stStripDrag st, stDrag st, corner) of
      -- | **A strip drag in flight wins, and it is read in ROWS** —
      -- `~w2tk2`. The pointer leaves the strip the moment it is pulled up
      -- (the document is above it), so the motion reports arrive named for
      -- whatever is under the hand; what is needed from them is the absolute
      -- row, which is that widget's own top plus the event's.
      (Just sd, _, Just (_, t)) -> resizeStripTo sd (t + r) >> pure True
      (Just _, _, Nothing) -> pure True
      (_, Just d, Just (l, _)) -> resizeTo d (l + c) >> pure True
      (_, Just _, Nothing) -> pure True
      (Nothing, Nothing, Just (l, t))
        | c == 0, StripVP <- n -> startStripDrag (t + r) >> pure True
        | c == 0, PaneVP p <- n, n `elem` resizablePanes st ->
            startDrag p l (wholeColumn mods) >> pure True
      _ -> pure False
  -- | **A press on the stage gap, which belongs to no clickable widget and so
  -- arrives in absolute screen coordinates.** Taking it doubles a one-column
  -- target ('▎' is one column — his correction of 2026-09-29, a full cell read
  -- as too thick) and costs no other gesture, because nothing else is drawn
  -- there. Here the row is needed, and here it is reliable: an extent and a
  -- raw event are both absolute.
  VtyEvent (V.EvMouseDown c r V.BLeft mods) -> do
    st <- get
    case (stStripDrag st, stDrag st) of
      (Just sd, _) -> resizeStripTo sd r >> pure True
      (_, Just d) -> resizeTo d c >> pure True
      _ -> do
        hit <- barRightOf st c r
        -- | **The screen's own left margin, beside the strip, is the strip's
        -- bar too** — `~w2tk2`, the same doubling of a one-column target
        -- `~rr8bx` was reported as. The column left of the strip's edge is
        -- 'draw''s outer margin and belongs to no clickable extent, so
        -- nothing else is competing for it.
        onStrip <- stripBarRightOf c r
        case (hit, onStrip) of
          (Just p, _) -> startDrag p c (wholeColumn mods) >> pure True
          (Nothing, True) -> startStripDrag r >> pure True
          _ -> pure False
  MouseUp _ (Just V.BLeft) _ -> release
  VtyEvent (V.EvMouseUp _ _ (Just V.BLeft)) -> release
  _ -> pure False
  where
    startDrag p from whole = do
      st <- get
      put st { stDrag = Just (Drag p from (paneWidthOf st p) whole) }
    startStripDrag from = do
      st <- get
      put st { stStripDrag = Just (StripDrag from (stripRows (stStrip st))) }
    -- | **The width is persisted when the drag ENDS, not while it runs** —
    -- `~vqsd8`. A drag arrives as a run of mouse-downs (vty asks for
    -- @ESC[?1002h@), so saving in 'resizeTo' would rewrite the dotfile on every
    -- report of every pull. This is the one place both mouse-up shapes meet.
    release = do
      st <- get
      case (stDrag st, stStripDrag st) of
        (Nothing, Nothing) -> pure False
        _ -> do
          let st' = st { stDrag = Nothing, stStripDrag = Nothing }
          put st'
          liftIO (saveConfig (configOf st'))
          pure True

-- | A widget's upper-left corner, @(column, row)@. **Both halves from one
-- extent lookup**, because a horizontal drag needs the column and the strip's
-- vertical one needs the row, and two lookups of the same extent in one
-- frame could not disagree but would read as though they might.
paneCorner :: Name -> EventM Name St (Maybe (Int, Int))
paneCorner n = fmap (corner . extentUpperLeft) <$> lookupExtent n
  where corner loc = (locationColumn loc, locationRow loc)

-- | Whether @(col, row)@ is the column immediately left of the suggestion
-- strip's accent bar, within the strip's own rows — `~w2tk2`, the rectangle
-- test the margin press needs. 'False' with the strip closed, there being no
-- extent to be beside.
stripBarRightOf :: Int -> Int -> EventM Name St Bool
stripBarRightOf col row = do
  ext <- lookupExtent StripVP
  pure $ case ext of
    Just e
      | locationColumn (extentUpperLeft e) == col + 1
      , let top = locationRow (extentUpperLeft e)
      , row >= top
      , row < top + snd (extentSize e) -> True
    _ -> False

-- | The pane whose accent bar is in the column just right of @(col, row)@ —
-- the rectangle test the gap press needs, and the reason a pane's extent is
-- read whole rather than for its left edge alone.
barRightOf :: St -> Int -> Int -> EventM Name St (Maybe Pane)
barRightOf st col row = do
  found <- mapM beside (placedPanes (stLayout st))
  pure (listToMaybe [p | Just p <- found])
  where
    beside p = do
      ext <- lookupExtent (PaneVP p)
      pure $ case ext of
        Just e
          | locationColumn (extentUpperLeft e) == col + 1
          , let top = locationRow (extentUpperLeft e)
          , row >= top
          , row < top + snd (extentSize e) ->
              Just p
        _ -> Nothing

paneWidthOf :: St -> Pane -> Int
paneWidthOf st p = Map.findWithDefault minPaneWidth p (stPaneWidths st)

-- | **Option held at the press means the whole column moves as one** —
-- `~t927j`, his instruction of 2026-11-13: /"the whole column of panes snaps
-- together and moves as one line… this way I can resize the entire column at
-- the same time."/
--
-- **'V.MMeta' is what Option arrives as, and that is vty's own mapping, not a
-- guess**: @vty-unix@'s 'classifyMouseEvent' reads the SGR modifier field and
-- turns bit 8 — the meta bit — into 'V.MMeta', on the press and on every
-- motion report. 'V.MAlt' is taken as well because it costs nothing and
-- nothing else in the TUI binds either: a terminal that spells Option the
-- other way then works without a second finding.
--
-- **Whether his terminal sets the bit at all is the terminal's business and
-- not ours.** If Option-drag behaves as a plain drag on his, the bit is not
-- being sent, and the fix is a terminal setting rather than a line of this.
wholeColumn :: [V.Modifier] -> Bool
wholeColumn mods = V.MMeta `elem` mods || V.MAlt `elem` mods

-- | One frame of a drag: the pane's width is what it was at the press, plus
-- however far the pointer has travelled back towards the screen's left edge,
-- snapped and then held between 'minPaneWidth' and whatever leaves the
-- document 'docMinWidth'.
--
-- **With Option held, every pane of that column takes the same width** —
-- `~t927j`. "Snaps together" is his word and it is the literal behaviour: the
-- panes of a column are ragged on the left since `~rr8bx`, and this is the
-- gesture that puts them back on one edge, at a width he chooses in one pull.
-- It is one assignment and not three drags because the column is what he is
-- sizing — a column of three panes dragged one at a time to the same width is
-- three chances to land on three different multiples of four.
resizeTo :: Drag -> Int -> EventM Name St ()
resizeTo d col = do
  st <- get
  vty <- getVtyHandle
  (screen, _) <- liftIO (V.displayBounds (V.outputIface vty))
  let pulled = dragWidth d - (col - dragFrom d)
      capped = min (maxPaneWidth st (dragPane d) screen) (snapWidth pulled)
      -- | **The clamp is the dragged pane's and is right for all of them**:
      -- 'maxPaneWidth' asks what the other column and the document leave,
      -- which is one answer for the column rather than one per pane.
      moving
        | dragWhole d = columnOf st (dragPane d)
        | otherwise = [dragPane d]
  put st { stPaneWidths = foldr (\p -> Map.insert p capped) (stPaneWidths st) moving }

-- | One frame of a strip drag: the strip's height is what it was at the
-- press, plus however far the pointer has travelled back towards the
-- screen's top edge — so **pulling up grows it**, which is the gesture he
-- asked for in his own words, /"resize the pane upwards taking space from
-- the main prompt\/script"/.
--
-- **No snap**, unlike 'resizeTo': see 'Tui.Layout.stripSized'. A row is
-- already a coarse unit and a strip that could only land on every fourth row
-- could not be put where he means.
--
-- **Floored by 'Tui.Layout.stripSized' and capped by 'maxStripRows'**, which
-- is the vertical twin of 'docMinWidth': a drag cannot take the screen away
-- from the thing being edited.
resizeStripTo :: StripDrag -> Int -> EventM Name St ()
resizeStripTo sd row = do
  st <- get
  vty <- getVtyHandle
  (_, screen) <- liftIO (V.displayBounds (V.outputIface vty))
  let pulled = sdRows sd + (sdFrom sd - row)
  put st { stStrip = stripSized (min (maxStripRows screen) pulled) (stStrip st) }

-- | The panes sharing a column with this one, itself included — the column
-- the layout puts it in now, not the one it was built in.
columnOf :: St -> Pane -> [Pane]
columnOf st p = if p `elem` c1 then c1 else c2
  where (c1, c2) = columnsOf (stLayout st)

-- | To the nearest multiple of 'paneWidthStep', never below 'minPaneWidth' —
-- which is itself a multiple of it, so the floor is on the grid too.
snapWidth :: Int -> Int
snapWidth w = max minPaneWidth (((w + paneWidthStep `div` 2) `div` paneWidthStep) * paneWidthStep)

-- | How wide this pane may be pulled: what is left of the screen once the
-- other column's widest pane, the two stage gaps, the layout's own margins
-- and the document's minimum have had their share.
--
-- **It does not consider this pane's own neighbours**, and does not need to:
-- a pane narrower than one beside it costs the column nothing, and a column
-- too wide for the window is what 'draw''s proportional clamp is for.
maxPaneWidth :: St -> Pane -> Int -> Int
maxPaneWidth st p screen =
  max minPaneWidth (screen - 2 - 1 - 1 - docMinWidth - otherWide)
  where
    -- | **Which column is "the other one" is 'stLayout''s to say** — `~fxc89`.
    -- A pane he has moved across is clamped against the column it is in now,
    -- not the one it was built in.
    (c1, c2) = columnsOf (stLayout st)
    other = if p `elem` c1 then c2 else c1
    otherWide = maximum (minPaneWidth : map (paneWidthOf st) other)

-- | **A re-run in flight owns the document, so a key that would edit it is
-- refused until the run posts its finished step** — `~twdbp`. Only a
-- 'VtyEvent' is refused: 'AppEvent's still have to reach 'handleRerunStep',
-- and a mouse click still has to reach a pane fold or a drag, neither of
-- which touches 'stScript'. This is what keeps only one re-run ever in
-- flight — 'rerunTail' would otherwise have no way to stop a second one
-- starting on top of the first, each racing the other to splice the same
-- document.
handleEventForKeys :: BrickEvent Name AppEvent -> EventM Name St ()
handleEventForKeys ev = do
  st <- get
  case (stRerun st, ev) of
    (Just _, VtyEvent _) -> pure ()
    _ -> case (stPicker st, stScriptBar st, stStripReply st) of
      -- | **The picker is checked first, and that is what makes it modal** —
      -- the one widget here that takes the keyboard off whichever of the three
      -- keyboards below it was holding it. Up, Down and Enter mean something in
      -- each of them, so a picker that merely added bindings would be a fourth
      -- claim on the same three keys.
      (Just pk, _, _) -> handlePickerEvent pk ev
      (_, Just bar, _) -> handleBarEvent st bar ev
      -- | **The reply row, same tier as the bar — `~w2tk2` slice 5.** The two
      -- cannot be open at once in practice (one is the script document's,
      -- the other the strip's), but if they ever were, the bar's own command
      -- line is the one a stray key is more dangerous in, so it keeps its
      -- place ahead of this.
      (_, _, Just reply) -> handleStripReplyEvent st reply ev
      _
        | stScriptMode st -> handleScriptEvent ev
        | otherwise -> handleReplEvent ev

-- | **The byte runs vty hands over as literal text, and what each one means.**
-- vty decodes neither the kitty keyboard protocol's @CSI ‹key›;‹mods› u@ nor
-- xterm's @modifyOtherKeys@ @CSI 27;‹mods›;‹key› ~@, so a key spelled either
-- way arrives as an 'V.KEsc' followed by one 'V.KChar' per byte of the rest
-- — measured with a vty event dump under the pty, 2026-11-11. Recognising
-- them here is the only route such a key has into this frontend.
--
-- **One gesture, and it is a table anyway.** Both entries are Shift+Enter's
-- two encodings, both measured. The @(run, action)@ shape is kept past the
-- point where one gesture needs it because `~xmd5b` wants exactly it: a run
-- that is not in this table is typed into the line, so Ctrl+Enter still
-- deposits @[27;5;13~@ into a proof line, and closing that is an entry here
-- rather than a second mechanism. **It does not close `~xmd5b`** — that is
-- still his call.
--
-- **DO NOT PUT CMD+L BACK. IT WAS TRIED AND IT DOES NOT ARRIVE.** `~p6g53`:
-- @[108;9u@ (kitty protocol — @l@ is 108, modifier @1 + 8@ for super) and
-- @[27;9;108~@ (@modifyOtherKeys@) were both added and both verified to clear
-- a turn when fed to a pty. **On his own terminal nothing comes through at
-- all** — HIS, 2026-11-13: /"ctrl works, cmd doesn't"/ — because macOS
-- terminals bind Cmd themselves and never forward it to the program. The
-- entries were removed on his instruction, /"unbind cmd so that it doesn't
-- confuse us in the future"/: two recognisers for a key that cannot be
-- pressed are two things a later reader has to disprove.
escRuns :: [(String, EventM Name St ())]
escRuns =
  [ ("[13;2u",    shiftEnter)
  , ("[27;2;13~", shiftEnter)
  ]

-- | Esc has just been handled, so the characters that follow it /may/ be the
-- tail of a Shift+Enter. Start holding them back ('stEscRun').
--
-- **Esc's own meaning is untouched and the dismissal has already happened by
-- the time this runs.** Nothing can be known about what follows an Esc at the
-- moment the Esc arrives, so a Shift+Enter does dismiss an open dropdown as a
-- side effect. That is the whole of the cost, and it is the right trade: the
-- alternative is delaying every Esc by a keystroke, which would break the one
-- key the mode uses to get out of things.
armEscRun :: BrickEvent Name e -> EventM Name St ()
armEscRun (VtyEvent (V.EvKey V.KEsc [])) = do
  st <- get
  put st { stEscRun = Just "" }
armEscRun _ = pure ()

-- | A character arriving while a sequence is being held: extend it, and
--
--   * a complete sequence **IS the Shift+Enter, and it is now dispatched
--     rather than only swallowed** — `~bmk98`, his instruction of 2026-11-13.
--     vty cannot decode these two sequences, but this function already
--     recognises them exactly, so the gesture was always available here and
--     was being thrown away. The line is still left as it was: inserting a
--     line does not touch the caret's own text;
--   * a still-possible prefix keeps being held, invisibly, for one more key;
--   * anything else is **typed, in order** — the held characters and then
--     this one — so a user who presses Esc and then genuinely types @[1@ has
--     lost nothing but the frame it took to know that.
--
-- A non-character event (an arrow, Enter, a resize) also ends the run: the
-- held text is typed first, then the event is handled, because the text was
-- typed before the key was pressed.
continueEscRun :: String -> BrickEvent Name AppEvent -> EventM Name St ()
continueEscRun p ev = do
  st <- get
  case ev of
    VtyEvent (V.EvKey (V.KChar c) []) | p' <- p ++ [c], any ((p' `isPrefixOf`) . fst) escRuns ->
      case lookup p' escRuns of
        Just act -> put st { stEscRun = Nothing } >> act
        Nothing  -> put st { stEscRun = Just p' }
    _ -> do
      put st { stEscRun = Nothing }
      mapM_ (\c -> handleEventFor (VtyEvent (V.EvKey (V.KChar c) []))) p
      handleEventFor ev

-- | **What Shift+Enter does** — `~bmk98`, his instruction of 2026-11-13:
-- /"It should serve as a way to insert a line in between two already existing
-- lines in script mode. That way I can actually edit something that I might
-- have done wrong."/
--
-- **Script mode only.** In the ordinary REPL there is no document to insert
-- into, so the sequence is swallowed exactly as it was before.
shiftEnter :: EventM Name St ()
shiftEnter = do
  st <- get
  if stScriptMode st then scriptOpenLine else pure ()

-- | **An empty line below the caret, with the caret seated on it** — the
-- other half of `~bmk98`.
--
-- **It is 'insertScriptLine''s rebuild with no text and an explicit seat.**
-- Inserting through the command bar hands over a line already written;
-- Shift+Enter is for a line he has not written yet, so the one thing it must
-- not do is 'reseated''s un-park — that would drop him on the composing line
-- at the end of the document, which is the one place the new line is not.
--
-- **An empty line costs nothing while it waits to be written.** `oneLine`
-- answers @Blank@ for it, so the tail re-runs against a session the blank left
-- exactly as it found it, and a blank he changes his mind about is removed by
-- the Backspace that backs out of it (`~282h8`) or by Enter on the empty line.
--
-- **On the composing line it appends and seats**, there being no "between" to
-- insert into there. That is the honest reading rather than a refusal: the
-- gesture means /give me a line here/, and at the end of the document here is
-- the end.
scriptOpenLine :: EventM Name St ()
scriptOpenLine = do
  st <- get
  let at = maybe (length (stScript st)) (+ 1) (stScriptPos st)
  case scriptSessionBefore st at of
    Nothing -> pure ()
    Just s -> do
      let (ran, unrun) = tailFrom st at
      rerunTail at s ("" : ran) unrun $ \rebuilt -> do
        st' <- get
        let doc = take at (stScript st') ++ rebuilt ++ unrun
        loadScriptAt st' { stScript = doc } at (stScriptDraft st')

-- | The command bar owns every key while it is open. Enter submits it, Esc
-- closes it unused, everything else edits its one line — no completion, no
-- history, nothing shared with the document's own editor.
handleBarEvent :: St -> Editor Text Name -> BrickEvent Name AppEvent -> EventM Name St ()
handleBarEvent st bar ev = case ev of
  VtyEvent (V.EvKey V.KEnter []) ->
    scriptBarSubmit st (concatMap Text.unpack (getEditContents bar))
  VtyEvent (V.EvKey V.KEsc []) -> closeScriptBar
  _ -> do
    bar' <- nestEventM' bar (handleEditorEvent ev)
    put st { stScriptBar = Just bar' }

-- | **The reply row owns every key while it is open** — `~w2tk2` slice 5,
-- his ruling on who holds the keyboard: the strip, not the document.
--
-- **Enter and Esc both close it unused.** Esc is the ordinary "never mind";
-- Enter is a stub and says so at the call site — there is no model on the
-- other end to hand a submitted reply to yet, so until slice 6 exists the
-- two keys do the same thing rather than one of them pretending to send
-- something nowhere.
handleStripReplyEvent :: St -> Editor Text Name -> BrickEvent Name AppEvent -> EventM Name St ()
handleStripReplyEvent st reply ev = case ev of
  -- | **Enter asks** — `~w2tk2` slice 6 and his ruling of 2026-11-19. Esc
  -- is still the ordinary never-mind; the two keys did the same thing in
  -- slice 5 only because there was no model on the other end yet.
  VtyEvent (V.EvKey V.KEnter []) -> askHintNow
  VtyEvent (V.EvKey V.KEsc [])   -> closeStripReply
  -- | **TAB MAKES THE GHOST REAL — HIS, 2026-11-19**: /"I want the tab to
  -- do that. Like is usually the UX in editors and prompts."/ The same key
  -- that accepts the whisper at the main prompt, so there is one gesture
  -- for /take what is dimmed/ in the whole TUI rather than two.
  --
  -- **Only while the row is empty**, because that is when there is a ghost
  -- on screen to accept. With text in the row Tab has nothing to take, and
  -- inserting the sentence into the middle of what he is writing is the one
  -- thing it must not do.
  VtyEvent (V.EvKey (V.KChar '\t') []) | Text.null (typedReply reply) -> do
    put st { stStripReply = Just (openStripReply hintPlaceholder) }
  VtyEvent (V.EvKey (V.KChar '\t') []) -> pure ()
  -- | **A CLICK ANYWHERE ELSE GIVES THE KEYBOARD BACK — HIS, 2026-11-19**:
  -- /"when I click the AI pane, I can't click back to the repl. That's
  -- wrong too."/ He was right and it was a trap: this row claims every
  -- event while it is open, so a click on the prompt went into the row's
  -- own editor and Esc was the only way out, which nothing on screen said.
  --
  -- **Any mouse press reaching here is already outside the row.**
  -- 'handlePaneClick' runs ahead of this dispatch and takes the row's own
  -- click, the accent-bar drags and the pane folds, returning 'True' for
  -- each; so there is no gesture to tell apart here, and none to protect.
  --
  -- **The click is then handled, not just swallowed.** Releasing the
  -- keyboard and dropping the press would cost him a second click to do
  -- what he meant by the first — so the event is re-dispatched down the
  -- path it would have taken had the row never been open.
  MouseDown _ V.BLeft _ _ -> releaseAndPass
  VtyEvent (V.EvMouseDown _ _ V.BLeft _) -> releaseAndPass
  _ -> do
    reply' <- nestEventM' reply (handleEditorEvent ev)
    put st { stStripReply = Just reply' }
  where
    releaseAndPass = do
      closeStripReply
      st' <- get
      if stScriptMode st' then handleScriptEvent ev else handleReplEvent ev

closeStripReply :: EventM Name St ()
closeStripReply = do
  st <- get
  put st { stStripReply = Nothing }

-- | **The reply row has nothing left to answer once the strip it lives in
-- closes** — `~w2tk2` slice 5. Carried into both @:pane@ handlers so
-- @:pane suggestions close@ never leaves a key claim behind it: without
-- this, a key typed afterwards would vanish into an editor nothing on
-- screen names any more, the dead-key shape `~sshbb` already found once.
closeReplyIfStripClosed :: Strip -> St -> St
closeReplyIfStripClosed strip' st'
  | stripOpen strip' = st'
  | otherwise = st' { stStripReply = Nothing }

-- | **WITHDRAWN IN SLICE 6, AND IT IS KEPT AS A NOTE RATHER THAN A
-- FUNCTION.** Slice 5 closed the reply row whenever the hint it replied to
-- was cleared, because the row was drawn only beside a hint and would
-- otherwise have been a key claim with nothing on screen to name it.
--
-- **Slice 6 makes the row permanent while the strip is open** — it is how a
-- hint is asked for, so it cannot depend on one existing — and the rule
-- stops applying: there is nothing to orphan. @:hint@ with no argument now
-- clears the text above the row and leaves the row alone.
-- 'closeReplyIfStripClosed' is still needed and still does its job.

-- | The session picker's keys, and they are the three a list dialog has
-- everywhere: Up and Down move the highlight, Enter takes the session it is
-- on, Esc leaves without taking one. Home\/End and PageUp\/PageDown come
-- along because the list scrolls past ten rows and a long one is tedious to
-- walk a row at a time.
--
-- **The highlight clamps and does not wrap.** Up on the first row and Down on
-- the last do nothing: this is a list of nine things you are looking at, not
-- a carousel, and wrapping would move the eye to the far end of the box on a
-- keystroke that read as "one more".
--
-- **A background Jev answer is still let through.** It belongs to the
-- completion dropdown underneath, which is intact and merely not drawn, and
-- dropping it would leave that dropdown holding a ranking request it never
-- gets an answer to.
handlePickerEvent :: Picker -> BrickEvent Name AppEvent -> EventM Name St ()
handlePickerEvent pk ev = case ev of
  VtyEvent (V.EvKey V.KUp [])       -> moveBy (-1)
  VtyEvent (V.EvKey V.KDown [])     -> moveBy 1
  VtyEvent (V.EvKey V.KPageUp [])   -> moveBy (-popupMaxRows)
  VtyEvent (V.EvKey V.KPageDown []) -> moveBy popupMaxRows
  VtyEvent (V.EvKey V.KHome [])     -> moveTo 0
  VtyEvent (V.EvKey V.KEnd [])      -> moveTo (pickerCount pk - 1)
  -- The wheel moves the highlight rather than scrolling the box under it:
  -- there is one thing to choose here, so a scroll that left the selection
  -- behind would be scrolling away from the only state the dialog has.
  MouseDown _ V.BScrollUp _ _       -> moveBy (-1)
  MouseDown _ V.BScrollDown _ _     -> moveBy 1
  VtyEvent (V.EvKey V.KEnter [])    -> pickerTake pk
  VtyEvent (V.EvKey V.KEsc [])      -> closePicker
  AppEvent _                        -> handleReplEvent ev
  _                                 -> pure ()
  where
    moveBy d = moveTo (pkSelected pk + d)
    moveTo i = do
      st <- get
      put st { stPicker = Just pk { pkSelected = max 0 (min (pickerCount pk - 1) i) } }

closePicker :: EventM Name St ()
closePicker = do
  st <- get
  put st { stPicker = Nothing }

-- | **`:script sessions` opens the picker** — `~xf2hv`, his instruction of 2026-11-12,
-- and what it replaces is a printed listing whose slugs you then re-typed
-- into `:script resume`.
--
-- **With nothing stored it says so and opens nothing.** A dialog whose only
-- content is "there is nothing here" is a dialog you have to dismiss to be
-- told something a line of text could have told you.
--
-- **The index is re-read on every open**, like every other read of it: two
-- TUIs on one project are expected, and the picker showing a session that was
-- started after this one booted is the whole reason to go through the file.
openSessionPicker :: St -> EventM Name St ()
openSessionPicker st = do
  index <- liftIO loadIndex
  case index of
    [] -> sayEither st noStoredSaid
    rows -> do
      sayEither st (storedCountSaid (length rows))
      st' <- get
      put st' { stPicker = Just (Picker (PickSession rows) (length rows - 1)) }

-- | Enter on a row: the same path `:script resume ‹slug›` takes, from the
-- entry in hand rather than from a handle that had to be matched — so the
-- staleness check, the caret and the note are one piece of code and cannot
-- come to differ between the two doors.
pickerTake :: Picker -> EventM Name St ()
pickerTake pk = case pkFor pk of
  PickSession rows -> case listToMaybe (drop (pkSelected pk) rows) of
    Nothing -> closePicker
    Just stored -> do
      st <- get
      let st' = st { stPicker = Nothing }
      held <- liftIO (readTranscript (stSlug stored))
      case held of
        Nothing -> sayEither st' (transcriptGoneSaid stored)
        Just texts -> resumeStored st' stored texts
  -- | **Enter on a model row is `:model ‹id›`**, down to the same function,
  -- so the dialog and the typed command cannot come to mean different
  -- things — the rule 'pickerTake''s session arm already follows.
  PickModel rows -> case listToMaybe (drop (pkSelected pk) rows) of
    Nothing -> closePicker
    Just m -> do
      st <- get
      said <- setModel st { stPicker = Nothing } (mdId m)
      st' <- get
      sayEither st' said

-- | **Says one line in whichever of the two places is on screen** — the
-- repl's transcript, or live-script mode's pane foot. The picker is reachable
-- from both and has nowhere of its own to put a refusal.
sayEither :: St -> String -> EventM Name St ()
sayEither st said
  | stScriptMode st = put st { stScriptNote = Just said }
  | otherwise = appendTurn st Nothing [said]

noStoredSaid :: String
noStoredSaid = "no stored sessions yet — one is started the first time a line is committed in :script"

storedCountSaid :: Int -> String
storedCountSaid 1 = "1 stored session in " <> databaseDir
storedCountSaid n = show n <> " stored sessions in " <> databaseDir

transcriptGoneSaid :: Stored -> String
transcriptGoneSaid stored =
  "the transcript for " <> stSlug stored <> " is gone from " <> databaseDir

-- | Live-script mode's own keys. **Enter, Up, Down and forward-delete mean
-- something different here**; everything else — ordinary typing, Tab, the
-- completion dropdown, Option+Backspace — falls through to the REPL's own
-- handler, because editing the text of a line is editing text either way.
--
-- **F12 or Ctrl+X summons the command bar, and Esc deliberately does not.**
-- Esc was tried first, on the reasoning that it is the one key every terminal
-- delivers identically — and it was wrong, measured under a pty: Esc already
-- means "dismiss", in two steps (his `.jalivert/TUI.md` #14), and how many
-- steps are pending depends on what the dropdown is showing. One Esc too many
-- silently opened the bar, which then ate the next Enter, so a line looked
-- submitted and was not. **Esc keeps exactly its old meaning here**; the bar
-- gets keys that mean nothing else.
--
-- **It was F2 until his ruling of 2026-11-19 gave F2 to the suggestion
-- strip's second slot** (`~w2tk2`); F12 arrives as @ESC[24~@ and decodes to
-- 'V.KFun' 12, read off his own keyboard rather than assumed. Ctrl+X is the
-- second way in, because a terminal that rewrites function keys should not be
-- able to strand someone in a mode whose only exit is the bar — which is
-- also why the F-key could be moved at no cost.
-- | **Editing a committed line makes every line below it stale, the instant it
-- is edited — and leaves them standing.** His ruling of 2026-10-21 (@~sv5v8@)
-- said the lines were *dropped* on that keystroke; **his ruling of 2026-11-11
-- overruled the timing** and this is it: the half that survives is that the tail
-- is invalid at once, which is what the paragraph below argues. What is gone is
-- that invalid and deleted were the same event. The tail now lives — dim, and
-- marked stale by 'scriptStaleFrom' — until the Enter that decides it: plain Enter
-- re-runs it (@~bxmsc@), Option+Enter cuts it. See
-- @.jalivert/DESIGN-PRINCIPLES.md@, /A reload re-runs the transcript/.
--
-- The lines after line @i@ were
-- produced by running against the session line @i@ left behind; change line
-- @i@ at all and they describe a session nothing is going to produce, so
-- leaving them on screen is the document telling a lie until Enter. His own
-- argument, and the symmetry he drew with it: it has to hold for inserting a
-- character as much as for deleting one, because both make the tail stale.
--
-- **This is the whole of it, and it needs no list of which keys are edits.**
-- An edit is "the text under the caret changed while the caret stayed on the
-- same committed line", which is observable after the fact, so the rule is a
-- before/after comparison around the ordinary dispatch rather than a clause
-- per key. Enter, Up, Down and Backspace-at-column-0 all change the text too
-- and all move 'stScriptPos' off @i@ while doing it, which is exactly what
-- distinguishes them: they are commits and navigation, not edits. Accepting a
-- completion into a parked line is not distinguished, and should not be — it
-- rewrites the line like any other keystroke.
handleScriptEvent :: BrickEvent Name AppEvent -> EventM Name St ()
handleScriptEvent ev = do
  dispatchScriptEvent ev
  keepTheEdit

-- | **Whatever the caret's line says now is what the document says** —
-- `~htff2`, his requirement of 2026-11-18. The editor holds the line being
-- typed; this writes it straight back into 'stScript', so the document and the
-- editor cannot disagree and there is no copy of the line anywhere to be
-- restored from.
--
-- **This is what fixed the edit that undid itself.** His report: /"when I go
-- edit a line and then I do not hit enter to submit it and go a line above or
-- below, it actually reverts my edit back to the original line. Not good."/ It
-- did, and it was by design — 'loadScriptAt' seats the stored 'slText' under
-- the caret, so a move used to read the old text back over the new one.
-- **His ruling: the edit stays as he left it**, the line goes dim because it
-- is no longer evaluated, and the cascading re-run takes the new text. Writing
-- through on every keystroke is what makes that true of every way out of the
-- line — an arrow, a click, the bar, leaving the mode — rather than of the
-- ones somebody remembered to list.
--
-- **Nothing is removed and nothing is moved.** 'stScriptPos' stays where it
-- is, and 'slSession' is untouched: the line still carries the state it
-- produced, which is what lets 'scriptStaleFrom' say the two disagree and what
-- lets a re-run start from the session above. **The dropdown is left alone**
-- too — somebody is typing mid-keystroke, and closing it here would make the
-- completion box flicker shut on every edit of an older line.
keepTheEdit :: EventM Name St ()
keepTheEdit = do
  st <- get
  case stScriptPos st of
    Nothing -> pure ()
    Just i -> case nthOf i (stScript st) of
      Nothing -> pure ()
      Just sl
        | slText sl == typed -> pure ()
        | otherwise ->
            put st
              { stScript = take i (stScript st) <> [sl { slText = typed }] <> drop (i + 1) (stScript st)
              -- | **Only the lines that have run can go stale**, so the count
              -- stops at the frontier: in a proof-script opened from disc the
              -- lines below it are text that has not run against anything and
              -- an Enter does not reach them.
              , stScriptNote =
                  let below = scriptFrontier st - (i + 1)
                   in if below <= 0 || slRan sl == Just typed
                        -- Editing the newest line has nothing below it, so it
                        -- says nothing.
                        then Nothing
                        else
                          Just
                            ( show below
                                <> (if below == 1 then " line" else " lines")
                                <> " below went stale — Enter re-runs them, Option+Enter cuts them"
                            )
              }
        where
          typed = concatMap Text.unpack (getEditContents (stInput st))

dispatchScriptEvent :: BrickEvent Name AppEvent -> EventM Name St ()
dispatchScriptEvent (VtyEvent (V.EvKey V.KEnter [])) = do
  st <- get
  case (stDropdown st, liveOffers st) of
    (Just (LoadDropdown entries (Just i)), _) | i < length entries ->
      acceptLoadRow st entries i
    (_, Just od) | Just i <- odSelected od, Just ins <- rowInsert (odRows od !! i) ->
      acceptOfferRow st od ins
    _ -> scriptSubmit
-- | **Shift+Enter: discard everything below the caret's line and run just
-- that line** — his feature, 2026-10-20, beside plain Enter rather than
-- replacing it. Enter rewinds and *re-runs* the tail, which is what the
-- spec asked for and is what you want when an edit near the top should
-- carry through a long script. This is the other intent: the tail is wrong
-- now, cut it.
--
-- **Cmd+Enter was the other candidate and it cannot be built.** macOS
-- terminals do not transmit Cmd to the program — it is a terminal-level
-- modifier — so vty never receives it and no binding could fire.
--
-- **Shift+Enter does not reach this vty either, and that is measured, not
-- assumed.** Both standard encodings were fed through the pty and neither
-- decodes: kitty's @ESC [ 13;2u@ and xterm @modifyOtherKeys@' @ESC [
-- 27;2;13~@ both arrive as *literal text* and get typed into the line —
-- the caret's line read @bbb[13;2u@ afterwards. So the 'V.MShift' clause
-- below is unreachable on this vty today; it is kept because it costs
-- nothing and is already correct if vty gains the kitty protocol.
-- **The bytes no longer reach the line**: they are swallowed by
-- 'stEscRun', which is not a workaround for the missing binding but a
-- refusal to let a keypress write punctuation into a proof.
--
-- **Option+Enter is the one that works** — it arrives as @ESC CR@ and
-- decodes to 'V.KEnter' with 'V.MMeta', verified under the pty. **And
-- `:script cut` in the command bar does the same thing with no modifier
-- at all**, so no terminal can strand the feature — the same belt-and-
-- braces F12 and Ctrl+X already have.
-- | **Backspace with nothing to its left wraps to the end of the line
-- above** — his feature, 2026-10-20. In a document the caret should not
-- stop dead at column 0 when there is a line above it to back into, and
-- the keypress is otherwise wasted: there is nothing there to delete.
--
-- **It moves the caret and does not join the lines.** Backspace at the
-- start of a line joins in an ordinary editor, but a script's lines are
-- each a submitted REPL instruction with a 'Session' of its own, so
-- gluing two of them together would mean running something neither line
-- says. Removing a line is @:script drop@ or clearing it and pressing
-- Enter; this is navigation.
--
-- 'scriptUp' is exactly the operation already: it steps the caret back one
-- line and 'loadScriptAt' seats it at the end of the text it loads, which
-- is where backing into a line should leave you. At line 0 it is a no-op,
-- the same stop-rather-than-wrap the whole mode uses. **Option+Backspace
-- keeps its word-delete** — that arrives with 'V.MMeta' and never matches
-- this clause.
--
-- **A line he has EMPTIED is removed when he backs out of it** — his report,
-- 2026-11-13: /"I start deleting with backspace and I go one character after
-- another, reaching the beginning of the current line. It correctly teleports
-- me to the end of the line above but the line bellow is still there. I think
-- that the intuitive way would be to observe that I have literally deleted it
-- and when I am teleported, it should remove it."/
--
-- **It does not contradict his ruling of 2026-11-11 that arrowing off a line
-- leaves it alone** ('scriptStaleFrom'), and the difference is the key rather
-- than the state. Up and Down say /go elsewhere/; Backspace says /delete/, and
-- it is the only key that does both. He pressed a delete key once per character
-- and then once more — at that last press the line itself is the only thing
-- left to delete, so taking it is what the keystroke already meant.
--
-- **The line still having text keeps today's pure navigation**, which is his
-- own feature of 2026-10-20: backing into the line above when there is nothing
-- under the caret to delete.
dispatchScriptEvent ev@(VtyEvent (V.EvKey V.KBS [])) = do
  st <- get
  let (_, col) = getCursorPosition (stInput st)
      line = concatMap Text.unpack (getEditContents (stInput st))
  case stScriptPos st of
    Just i | col == 0, all isSpace line -> scriptBackOut i
    _ | col == 0 -> scriptUp
    _ -> handleReplEvent ev
-- **Shift+Enter inserts a line** — `~bmk98`, his instruction of 2026-11-13,
-- taking this spelling off the cut. **Option+Enter keeps the cut and is the
-- one that arrives**, so nothing of his 2026-10-20 gesture is lost: the two
-- were one gesture under two spellings and this is the spare one.
--
-- **This clause is still the unreachable one** — vty decodes neither encoding
-- — and it is kept correct for the day vty gains the kitty protocol. **The
-- binding that actually fires is 'continueEscRun''s**, which recognises the
-- bytes itself.
dispatchScriptEvent (VtyEvent (V.EvKey V.KEnter [V.MShift])) = scriptOpenLine
dispatchScriptEvent (VtyEvent (V.EvKey V.KEnter [V.MMeta]))  = scriptCutAndRun
-- | **F12 or Ctrl+X summons the command bar. It used to be F2, and F2 is now
-- the suggestion strip's second slot — HIS RULING, 2026-11-19**: /"we take F2
-- for suggestions, replacing its original functionality with some other
-- shortcut or command."/
--
-- **The move costs nothing, which is why F12 and not a new command.** Ctrl+X
-- was built as the bar's second way in precisely so a terminal that rewrites
-- function keys could not strand anyone, so the bar never depended on an
-- F-key alone; and F12 is the one F-key no grid cell will ever reach for —
-- 'Tui.Layout.stripSlotKeys' stops at ten.
dispatchScriptEvent (VtyEvent (V.EvKey (V.KFun 12) [])) = openScriptBar
dispatchScriptEvent (VtyEvent (V.EvKey (V.KChar 'x') [V.MCtrl])) = openScriptBar
-- | **Live-script mode does not need a clause for the clear keys.** It falls
-- through to the repl's, and 'clearOneTurn' asks 'stScriptMode' itself — see
-- its haddock for why the guard lives there and not at each binding.
dispatchScriptEvent ev = handleReplEvent ev

handleReplEvent :: BrickEvent Name AppEvent -> EventM Name St ()
handleReplEvent (VtyEvent (V.EvKey V.KEnter [])) = do
  st <- get
  case (stDropdown st, liveOffers st) of
    -- | Enter accepts the highlighted candidate into the input instead of
    -- submitting — his spec: "Enter selects it" — and Tab does the same
    -- (his `.jalivert/TUI.md` #10, VS Code's rule). Only fires with a
    -- highlight to act on; with the dropdown merely open and nothing
    -- selected, Enter still runs the line as typed.
    (Just (LoadDropdown entries (Just i)), _) | i < length entries ->
      acceptLoadRow st entries i
    -- | Same spec, the offer dropdown's own candidate.
    (_, Just od) | Just i <- odSelected od, Just ins <- rowInsert (odRows od !! i) ->
      acceptOfferRow st od ins
    _ -> do
      let line = concatMap Text.unpack (getEditContents (stInput st))
          -- | Folds this submission into 'stHistory' before dispatch, so
          -- every branch below (TUI-local or engine-bound alike) starts
          -- from a state that already has it — a submitted line is a
          -- submitted line, `:theme` included, his ask: "commands/instral
          -- programs I submitted."
          st0 = recordHistory line st
      case words line of
        [":theme", name] | Just th <- themeByName name -> do
          let st' = st0 { stTheme = th }
          liftIO (saveConfig (configOf st'))
          appendTurn st' Nothing ["theme: " <> name]
        [":fold", mode] | mode `elem` ["on", "off"] ->
          appendTurn st0 { stFoldOn = mode == "on" } Nothing ["fold: " <> mode]
        -- | **@:pane@ — which panes are on screen and where** — `~fxc89`.
        -- TUI-local like `:theme` and `:fold`: the engine has no panes, so
        -- this never reaches it.
        paneLine@(":pane" : _)
          | Just (layout', strip', said) <- paneCommand paneLine (stLayout st0) (stStrip st0) -> do
              let st' = closeReplyIfStripClosed strip' st0 { stLayout = layout', stStrip = strip' }
              liftIO (saveConfig (configOf st'))
              appendTurn st' Nothing [said]
        -- | `:script` enters live-script mode (`~5vtt3`). TUI-local like the
        -- rest of this block, and the only way *in* — leaving again is the
        -- command bar's `:script`, because once the mode is on, what you type
        -- is the document and never a command.
        [":script"] -> enterScriptMode st0
        -- | **`:script ‹path›` opens a proof-script into the mode** —
        -- `~22qjj`. One gesture rather than two, and the path completes as
        -- it is typed, `":script "` being in 'pathCommands'. The bar's
        -- `:script open ‹path›` is the same call for when the mode is
        -- already on.
        -- | **`:script sessions` opens the picker** — his instruction,
        -- 2026-11-12. It used to print the index and leave you to re-type a
        -- slug into the command below; it now puts the sessions on screen as
        -- rows you move a highlight through, 'openSessionPicker'.
        --
        -- **Which is also why it is in the bar now.** The old reason both
        -- database commands lived in the repl and not in live-script mode's
        -- bar was that each of them answers with a list, and the bar has one
        -- row to say a list in. A dialog has as many rows as it likes, so
        -- that reason is gone and script mode can reach its own sessions
        -- without leaving the mode first.
        [":script", "sessions"] -> openSessionPicker st0
        [":script", "resume", handle] -> do
          index <- liftIO loadIndex
          case storedNamed handle index of
            Left why -> appendTurn st0 Nothing [why]
            Right stored -> do
              held <- liftIO (readTranscript (stSlug stored))
              case held of
                Nothing -> appendTurn st0 Nothing [transcriptGoneSaid stored]
                Just texts -> resumeStored st0 stored texts
        -- | **The slug left off, said as that and not as a missing file.**
        -- The branch below reads anything after `:script` as a path, so
        -- without this one a forgotten slug answers /no such file: resume/.
        [":script", "resume"] ->
          appendTurn st0 Nothing
            [":script resume ‹slug› takes a stored session up where its caret was"
            , "  :script sessions picks one from a list instead"]
        -- | **A path argument is the whole of the rest of the line, spaces
        -- and all** — `~td887`. `:script` takes exactly one path, so there is
        -- nothing for a space to separate, and matching @[":script", path]@
        -- meant a path with a space in it missed every branch and reached the
        -- engine, which answered /no such command: :script/. His own project
        -- directory has a space in it, so every absolute path into it was in
        -- that case. **The engine's own path arguments are split on spaces on
        -- purpose and that is untouched** — @:consult@ takes a list of them,
        -- where this takes one.
        (":script" : rest@(_ : _)) -> do
          let path = unwords rest
          ok <- openScriptFile st0 path 0
          if ok then pure () else appendTurn st0 Nothing ["no such file: " <> path]
        -- | Two more TUI-local toggles, his `.jalivert/TUI.md` #23 — same
        -- standing as `:theme`/`:fold` (not instral, so special-casing them
        -- here is his own ruling already covers this). Disabling either is
        -- not "Esc" — it's a standing preference until turned back on, which
        -- is exactly why it needed its own command rather than a keybinding.
        --
        -- **These two, plus the theme, persist to 'Tui.Config''s dotfile**
        -- (his ask, 2026-09-30) — `:fold` doesn't, scope as asked.
        [":preselect", mode] | mode `elem` ["on", "off"] -> do
          let st' = st0 { stAutoSelect = mode == "on" }
          liftIO (saveConfig (configOf st'))
          appendTurn st' Nothing ["preselect: " <> mode]
        [":whisper", mode] | mode `elem` ["on", "off"] -> do
          let st' = st0 { stWhisperOn = mode == "on" }
          liftIO (saveConfig (configOf st'))
          appendTurn st' Nothing ["whisper: " <> mode]
        -- | **`:dropdown on|off`** — `~492hq`, his sequencing ruling of
        -- 2026-11-19. Same standing as the three above: a preference, not an
        -- Esc, persisted to the dotfile. See 'stDropdownOn' for what \"off\"
        -- does and does not touch.
        [":dropdown", mode] | mode `elem` ["on", "off"] -> do
          let st' = st0 { stDropdownOn = mode == "on" }
          liftIO (saveConfig (configOf st'))
          appendTurn st' Nothing ["dropdown: " <> mode]
        -- | **`:jev on|off`** — `~zttnz`. See 'stJevOn' for what off means
        -- on screen and for his quota.
        [":jev", mode] | mode `elem` ["on", "off"] -> do
          let st' = st0 { stJevOn = mode == "on" }
          liftIO (saveConfig (configOf st'))
          appendTurn st' Nothing ["jev: " <> mode]
        -- | **`:hint ‹text›` and `:hint`** — `~w2tk2` slice 4, and it is a
        -- **stub on purpose**: the hint region has to be drawable, and its
        -- geometry measurable, before the model that would write one
        -- exists. Slice 6 replaces this command with the model's own
        -- channel and the field under it does not move.
        --
        -- **Not persisted**, unlike the four toggles above: see 'stHint'.
        -- **`:hint` with nothing after it clears**, which is why this takes
        -- the tail rather than requiring an argument — an empty hint and no
        -- hint are the same state and spelling them differently would have
        -- invented a third.
        (":hint" : rest) -> do
          let st' = st0 { stHint = hintFrom rest }
          appendTurn st' Nothing [hintSaid (hintFrom rest)]
        -- | **`:model` and `:model ‹id›`** — `~w2tk2` slice 6.
        [":model"] -> appendTurn st0 Nothing ["model: " <> Text.unpack (stModel st0)]
        [":model", m] -> do
          said <- setModel st0 (Text.pack m)
          st' <- get
          appendTurn st' Nothing [said]
        -- | **`:models` and `:models ‹filter›`** — the picker.
        (":models" : rest) -> openModelPicker st0 (Text.pack (unwords rest))
        -- | **`:hint-prompt` and `:hint-prompt reset`** — `~3p9g2`. The
        -- file is his, so 'Tui.Hint.loadHintPrompt' will not overwrite one
        -- that is already there; **this is how a better default shipped
        -- later reaches him**, and taking it is his keystroke.
        [":hint-prompt"] -> do
          path <- liftIO hintPromptPath
          appendTurn st0 Nothing ["the prompt the model is sent is " <> path]
        [":hint-prompt", "reset"] -> do
          path <- liftIO resetHintPrompt
          appendTurn st0 Nothing [path <> " is back to the one that ships"]
        -- | **`:confirm-quit on|off`**, his instruction of 2026-11-18 — same
        -- standing as the two above. See 'maybeQuit'.
        [":confirm-quit", mode] | mode `elem` ["on", "off"] -> do
          let st' = st0 { stConfirmQuit = mode == "on" }
          liftIO (saveConfig (configOf st'))
          appendTurn st' Nothing ["confirm-quit: " <> mode]
        -- | **`:clear` and `:clear ‹n›`** — `~p6g53`. TUI-local for the
        -- plainest possible reason: the engine has no transcript. It holds a
        -- session and answers lines; what is still on screen from an earlier
        -- line is this frontend's alone, which is also why `:clear` is not in
        -- `Thena.Driver`'s table and why no other frontend would want it
        -- there. 'dropTurns' says what it does and does not touch.
        [":clear"] -> clearTurns 1 st0
        [":clear", n] | Just k <- readCount n -> clearTurns k st0
        (":clear" : _) -> appendTurn st0 Nothing clearUsage
        -- | `:help` runs through the engine as usual (below) — its table is
        -- `Thena.Driver`'s, and stays that way, since it's the one command
        -- the engine and every other frontend share. `:preselect`/`:whisper`
        -- never reach `Thena.Driver` at all (intercepted above), so its own
        -- `:help` can't know they exist; 'tuiHelpLines' is appended here
        -- instead of touching the engine's table for two commands that are
        -- only ever true from inside this frontend.
        [":help"] -> runEngineLine st0 line tuiHelpLines
        _ -> runEngineLine st0 line []
-- | **An F-key takes the option in its slot** — `~w2tk2` slice 2, his
-- proposal: /"perhaps they are all numbered … and the user can just hit … F1
-- through F12"/.
--
-- **One clause for every key, because the slot is the key's own number.**
-- 'Tui.Layout.stripSlotKeys' is the list and this guard is the only place it
-- is consulted for dispatch, so freeing F11 is an entry in that list and no
-- change here.
--
-- **Nothing happens when there is no such slot**, and the two cases are the
-- same case: the strip is closed, or the grid is smaller than this key's
-- number. 'stripShownOf' is empty in the first and short in the second, and
-- 'nthOf' answers 'Nothing' either way — so a key is never swallowed on
-- behalf of a cell that is not on screen.
--
-- **It is cut to the grid's capacity, which is 'stripShownOf' and not
-- 'stripSlateOf'** — `~w2tk2` slice 3a. It read the uncapped slate until
-- then, and the two numbers are not the same: measured under a pty on
-- 2026-11-19 at a three-cell strip, **F4 inserted @app-function@**, the
-- fourth candidate, which was drawn on no cell at all.
--
-- **This clause is in the repl's handler and live-script mode falls through
-- to it**, so the gesture is one gesture in both keyboards — which is the
-- whole reason F2 had to leave the command bar.
--
-- **It asks the slate and not the dropdown** — `~3gn2r`. Requiring a
-- 'stOfferDropdown' here meant every F-key was dead after an Enter and after
-- Esc's second press, in exactly the frames where the strip was blank for the
-- same reason.
handleReplEvent (VtyEvent (V.EvKey (V.KFun k) []))
  | k `elem` stripSlotKeys = do
      st <- get
      case nthOf (k - 1) (stripShownOf st) of
        Just row | Just ins <- rowInsert row -> acceptSlateRow st ins
        _ -> pure ()
handleReplEvent (VtyEvent (V.EvKey V.KEsc [])) = do
  st <- get
  case (stDropdown st, liveOffers st) of
    -- | Esc walks an open dropdown back in two steps (his `.jalivert/TUI.md`
    -- #14): first the highlight, then the list itself, which stays hidden
    -- until an edit brings it back ('stDismissed'). With nothing open, Esc
    -- is simply a no-op — it used to fall through to 'halt' and quit the
    -- whole TUI, which is not "Esc's ordinary meaning" for a line editor
    -- and was never asked for. Quitting is still `:quit`.
    (Just ld@(LoadDropdown _ (Just _)), _) ->
      put st { stDropdown = Just ld { ldSelected = Nothing }, stArrowsReleased = True }
    (_, Just od@(OfferDropdown _ (Just _) _ _ _)) ->
      put st { stOfferDropdown = Just od { odSelected = Nothing }, stArrowsReleased = True }
    (Just _, _) -> do
      let line = concatMap Text.unpack (getEditContents (stInput st))
      put st { stDropdown = Nothing, stDismissed = Just line }
    (_, Just _) -> do
      let line = concatMap Text.unpack (getEditContents (stInput st))
      put st { stOfferDropdown = Nothing, stDismissed = Just line }
    _ -> pure ()
-- | Ctrl+D quits on an empty line, EOF the way a terminal means it
-- (his `.jalivert/TUI.md` #12) — with text to delete it falls through to
-- the editor instead, which binds it as delete-char-forward, so no editing
-- key is lost to the quit. Note the shape vty gives it: 'd' with 'MCtrl',
-- not a bare 'EOT' character.
handleReplEvent ev@(VtyEvent (V.EvKey (V.KChar 'd') [V.MCtrl])) = do
  st <- get
  let line = concatMap Text.unpack (getEditContents (stInput st))
  if null line
    then maybeQuit st
    else Brick.zoom stInputL (handleEditorEvent ev)
      >> followInput >> refreshDropdown >> refreshOfferDropdown
-- | Down travels visually down in both placements — toward the input below
-- it, likewise toward the input above it, where the rows run reversed and
-- rising indices climb away. So above the line the two move-function pairs
-- swap: 'moveUp'/'offerMoveUp' step down-screen, 'moveDown'/'offerMoveDown'
-- step up-screen. From a cleared selection the same swap lands the visual
-- ends symmetrically (top on Down, bottom on Up) rather than list ends.
handleReplEvent ev@(VtyEvent (V.EvKey V.KDown [])) = do
  st <- get
  if popupAbove st
    then navigateCompletion moveUp offerMoveUp ev
    else navigateCompletion moveDown offerMoveDown ev
handleReplEvent ev@(VtyEvent (V.EvKey V.KUp [])) = do
  st <- get
  if popupAbove st
    then navigateCompletion moveDown offerMoveDown ev
    else navigateCompletion moveUp offerMoveUp ev
-- | Tab takes what's lit, VS Code's rule (his `.jalivert/TUI.md` #10) —
-- the same accepts Enter performs above, so the two keys cannot disagree.
-- With nothing highlighted, Tab keeps its old job: shell-completion on a
-- ':load' path (Esc-clear the highlight to get that back with the list
-- open), silence everywhere else.
handleReplEvent (VtyEvent (V.EvKey (V.KChar '\t') [])) = do
  st <- get
  case (stDropdown st, liveOffers st) of
    (Just (LoadDropdown entries (Just i)), _) | i < length entries ->
      acceptLoadRow st entries i
    (_, Just od) | Just i <- odSelected od, Just ins <- rowInsert (odRows od !! i) ->
      acceptOfferRow st od ins
    _ -> completeLoadPath
-- | "Walk into" a placeholder box and type to fill it — his own ask,
-- `.jalivert/LIVE-OFFERS.md`/`.jalivert/TUI.md`: the caret standing right
-- at a box, typing a character, used to just insert ahead of it — "it just
-- moves the placeholder behind the parameter name I just wrote." A
-- placeholder is one character in the buffer (see 'placeholderGlyph'), so
-- "standing at it" is simply "the character under the caret is the
-- glyph" — a local, buffer-only check, nothing to ask the engine.
-- Consumes exactly the one glyph and inserts the typed character in its
-- place, same edit 'acceptOfferEdit' already does for a dropdown accept
-- landing on a box ('offeredReplaces'). Only the *first* character of a
-- name types this way; once the glyph is gone, ordinary typing resumes
-- through the catch-all below.
handleReplEvent (VtyEvent (V.EvKey (V.KChar c) [])) = do
  st <- get
  let (_, col) = getCursorPosition (stInput st)
      line = concatMap Text.unpack (getEditContents (stInput st))
  if col < length line && line !! col == placeholderGlyph
    then do
      put st { stInput = E.applyEdit (acceptOfferEdit col 1 [c]) (stInput st) }
      followInput
      refreshDropdown
      refreshOfferDropdown
    else
      Brick.zoom stInputL (handleEditorEvent (VtyEvent (V.EvKey (V.KChar c) [])))
        >> followInput >> refreshDropdown >> refreshOfferDropdown
-- | Option+Backspace deletes a word backward. It arrives as 'KBS' with
-- 'MMeta' — Ghostty sends ESC DEL, and a non-printable always comes through
-- as Alt whether option-as-alt is set or not — which Brick's editor binds
-- nothing to ('C-w' falls through there too), so it is handled here, in the
-- zipper, before the catch-all: whitespace back, then the word itself,
-- readline's rubout.
-- | **Ctrl+L clears the last turn, and it is the only key that does** —
-- `~p6g53`, settled by him on 2026-11-13 after two others were tried and
-- measured. Neither alternative is coming back; both are recorded so that
-- nobody spends the round again.
--
-- **Option+L: withdrawn, his λ.** /"Option + l doesn't work, because I have it
-- mapped to print λ."/ A key that types a character he wants in his proofs is
-- not a key this frontend may claim, and in a proof assistant λ is about as
-- spoken-for as a character gets.
--
-- **Cmd+L: withdrawn, it does not arrive.** /"ctrl works, cmd doesn't"/ —
-- macOS terminals bind Cmd themselves. See 'escRuns' for the two encodings
-- that were tried and why they are gone.
--
-- **Ctrl+L means \"clear the screen\" in every terminal and here it means
-- \"clear one turn\", which is a real difference and is his, not a liberty
-- taken**: he asked for this key by name. The one-turn meaning is the whole
-- feature — what he described is Terminal.app's **Clear to Previous Mark**,
-- which is `Cmd+L` there, and that key cannot be had.
handleReplEvent (VtyEvent (V.EvKey (V.KChar 'l') [V.MCtrl])) = clearOneTurn
handleReplEvent (VtyEvent (V.EvKey V.KBS [V.MMeta])) = do
  st <- get
  put st { stInput = E.applyEdit killWordBack (stInput st) }
  followInput
  refreshDropdown
  refreshOfferDropdown
handleReplEvent (MouseDown n V.BScrollUp _ _) = vScrollBy (viewportScroll n) (-1)
handleReplEvent (MouseDown n V.BScrollDown _ _) = vScrollBy (viewportScroll n) 1
-- | Press-and-release gestures end here, all of them. A wheel tick arrives
-- as a press *and* a release (SGR 'M' then 'm'), and so does an ordinary
-- click — neither half carries editing intent, so neither reaches the
-- editor nor moves the viewport. Without these, the release half of every
-- wheel tick falls into the catch-all below, whose 'followInput' yanks the
-- pane back to the bottom: the pane fighting back on each scroll.
-- (Click-to-navigate on a dev-link/goal will claim 'MouseDown' with the
-- left button here once per-line extents land; until then clicks stay
-- inert rather than quietly yanking.)
handleReplEvent (MouseUp _ _ _) = pure ()
handleReplEvent (MouseDown _ _ _ _) = pure ()
-- | The startup tick ('runTui', the only 'Tick' there is) always did
-- nothing for the extents — the outer wrapper already recorded those by
-- the time this runs, which was the whole point of it — but it is also
-- the first and only chance to score the launch dropdown, which
-- 'refreshOfferDropdown' never built and so never would have scored on
-- its own ('fireJevForCurrentDropdown').
handleReplEvent (AppEvent Tick) = fireJevForCurrentOffers
handleReplEvent (AppEvent (JevDue gen)) = handleJevDue gen
handleReplEvent (AppEvent (JevRanked gen result)) = applyJevRanking gen result
handleReplEvent (AppEvent (HintAnswered result)) = applyHintAnswer result
handleReplEvent (AppEvent (ModelsListed filt result)) = do
  st <- get
  case result of
    Left err -> sayEither st ("models: openrouter could not be reached — " <> err)
    Right ms -> do
      put st { stModels = Just ms }
      st' <- get
      showModels st' filt ms
handleReplEvent (AppEvent (RerunStep gen soFar shown finished)) =
  handleRerunStep gen soFar shown finished
handleReplEvent ev =
  Brick.zoom stInputL (handleEditorEvent ev) >> followInput >> refreshDropdown >> refreshOfferDropdown

-- | What a highlighted ':load' row does on accept — shared by Enter and
-- Tab, so the two keys cannot disagree (his `.jalivert/TUI.md` #10, VS
-- Code's rule: Tab takes what's lit).
acceptLoadRow :: St -> [String] -> Int -> EventM Name St ()
acceptLoadRow st entries i = do
  let line = concatMap Text.unpack (getEditContents (stInput st))
      -- The value lands as is — directories already trail their slash
      -- from 'loadDropdownEntries'.
      line' = replacePathPrefix line (entries !! i)
  put st { stInput = E.editorText Input (Just 1) (Text.pack line') }
  refreshDropdown
  followInput

-- | What a highlighted offer row does on accept — shared the same way.
-- 'acceptOfferEdit' replaces exactly the recovered/replaced span, not the
-- whole line, so this is a zipper edit rather than a rebuilt editor (same
-- shape as 'killWordBack').
acceptOfferRow :: St -> OfferDropdown -> String -> EventM Name St ()
acceptOfferRow st od ins = do
  put st { stInput = E.applyEdit (acceptOfferEdit (odWordStart od) (odReplaceLen od) ins) (stInput st) }
  refreshOfferDropdown
  followInput

-- | **The same landing for a slot taken off the strip** — `~3gn2r`. The
-- geometry is the slate's ('slateStart', 'slateReplaceLen'), which is the
-- same arithmetic 'buildOfferDropdown' computed for the same line; what it
-- does not need is a dropdown to exist.
acceptSlateRow :: St -> String -> EventM Name St ()
acceptSlateRow st ins = do
  put st { stInput = E.applyEdit (acceptOfferEdit (slateStart (stSlate st)) (slateReplaceLen (stSlate st)) ins) (stInput st) }
  refreshOfferDropdown
  followInput

-- | Arrow-key navigation only takes over the keypress while a dropdown is
-- actually showing candidates — otherwise Up/Down recall submission
-- history instead (his ruling on the conflict, 2026-09-30: the dropdown
-- keeps first claim on the keys exactly as it always has; history only
-- gets them once nothing is left to navigate there — Esc, or nothing
-- offered). ':load''s own dropdown takes priority (mutually exclusive
-- with the offer dropdown by construction, so this only ever matters in
-- principle).
navigateCompletion
  :: (Maybe Int -> Int -> Int)
  -> ([Int] -> Maybe Int -> Maybe Int)
  -> BrickEvent Name AppEvent
  -> EventM Name St ()
navigateCompletion moveLoad moveOffer ev = do
  st <- get
  case (stDropdown st, liveOffers st) of
    -- | **Esc already handed these keys over, so do not take them back.**
    -- The comment above has always said history gets them "once nothing is
    -- left to navigate there — Esc, or nothing offered"; the Esc half was
    -- never implemented, because clearing the highlight leaves the rows in
    -- place and 'selectableIxs' still answers non-empty. His report,
    -- 2026-10-20: Esc to unselect, press Up, and the highlight reappeared on
    -- the *last* row — 'offerMoveUp' with no selection enters from the
    -- bottom — so the caret never moved and the list had scrolled instead.
    _ | stArrowsReleased st -> documentOrHistory ev
    (Just ld@(LoadDropdown entries sel), _) | not (null entries) ->
      let next = moveLoad sel (length entries)
       in if Just next == sel
            then documentOrHistory ev
            else put st { stDropdown = Just ld { ldSelected = Just next } }
    -- | Only a row with something to insert ('selectableIxs') is ever a
    -- landing spot — a hint row (a nonterminal or scan class) is shown but
    -- names a *kind* of thing, not text an accept could write.
    -- | **At the end of the list the key is passed on, not swallowed** —
    -- his report, 2026-10-20: *"when the top-most is highlighted, it is
    -- just stuck there… why isn't arrow up in the dropdown when it can't be
    -- non-captured and used by the next UI that would use it?"* The movers
    -- answer with the selection unchanged when there is nowhere to go, and
    -- that used to be written back as a no-op. Now it releases: Up off the
    -- top row walks the document (or recalls history), Down off the last
    -- row the same way. The dropdown keeps first claim only while it has
    -- somewhere left to move.
    (_, Just od) | not (null (selectableIxs (odRows od))) ->
      let next = moveOffer (selectableIxs (odRows od)) (odSelected od)
       in if next == odSelected od
            then documentOrHistory ev
            else put st { stOfferDropdown = Just od { odSelected = next } }
    -- | Nothing left to navigate — the dropdown's own bug fix (his
    -- `.jalivert/TUI.md` #19, an offer with nothing selectable used to
    -- fall through without refreshing either dropdown) plus the new case:
    -- the real key identity, not 'moveLoad'/'moveOffer' (which are
    -- pre-flipped for the popup's own screen direction, 'popupAbove' —
    -- history's "older"/"newer" means the same thing regardless of where
    -- the popup would have drawn). Anything that isn't literally Up or
    -- Down here falls to the plain editor binding same as before — this
    -- function is only ever called with one of the two, but the catch-all
    -- keeps the fallback honest without assuming that from outside.
    -- | In script mode the same two keys walk the *document* instead of
    -- recalling text — a different mechanism wearing the same UI shape, so it
    -- branches here rather than inside 'historyBack'.
    _ -> documentOrHistory ev

-- | Where Up and Down go once no dropdown is claiming them: the script
-- document in live-script mode, shell history in the ordinary REPL, and the
-- plain editor binding for anything that is neither key.
--
-- **The key's own identity decides, not the pre-flipped movers** that
-- 'navigateCompletion' is handed — those are flipped for the popup's screen
-- direction ('popupAbove'), and "older"/"newer" means the same thing
-- wherever the popup would have been drawn.
documentOrHistory :: BrickEvent Name AppEvent -> EventM Name St ()
documentOrHistory ev = do
  st <- get
  case ev of
    VtyEvent (V.EvKey V.KUp [])   | stScriptMode st -> scriptUp
    VtyEvent (V.EvKey V.KDown []) | stScriptMode st -> scriptDown
    VtyEvent (V.EvKey V.KUp [])   -> historyBack
    VtyEvent (V.EvKey V.KDown []) -> historyForward
    _ -> Brick.zoom stInputL (handleEditorEvent ev) >> followInput >> refreshDropdown >> refreshOfferDropdown

-- | Recalls one entry further back in 'stHistory' — the first press saves
-- the live buffer into 'stHistoryDraft' first, so 'historyForward' has
-- something to return to. Stops at the oldest entry rather than wrapping,
-- same as a shell.
historyBack :: EventM Name St ()
historyBack = do
  st <- get
  let hs = stHistory st
      line = concatMap Text.unpack (getEditContents (stInput st))
  case (hs, stHistoryPos st) of
    ([], _)                 -> pure ()
    (_, Nothing)             -> loadHistoryAt st (length hs - 1) line
    (_, Just i) | i > 0      -> loadHistoryAt st (i - 1) (stHistoryDraft st)
    _                        -> pure ()

-- | The other direction — stepping past the newest entry restores
-- whatever 'historyBack' interrupted and leaves browsing ('stHistoryPos')
-- rather than looping back to the oldest.
historyForward :: EventM Name St ()
historyForward = do
  st <- get
  case stHistoryPos st of
    Nothing -> pure ()
    Just i
      | i + 1 < length (stHistory st) -> loadHistoryAt st (i + 1) (stHistoryDraft st)
      | otherwise -> do
          put st
            { stInput = E.editorText Input (Just 1) (Text.pack (stHistoryDraft st))
            , stHistoryPos = Nothing
            , stHistoryDraft = ""
            }
          followInput >> refreshDropdown >> refreshOfferDropdown

-- | Loads @'stHistory' st !! i@ into the input and records 'draft' as
-- what 'historyForward' restores once browsing runs back past the newest
-- entry — shared by both directions so the draft is only ever captured
-- once per browsing session, at the moment 'historyBack' first leaves
-- live editing.
loadHistoryAt :: St -> Int -> String -> EventM Name St ()
loadHistoryAt st i draft = do
  put st
    { stInput = E.editorText Input (Just 1) (Text.pack (stHistory st !! i))
    , stHistoryPos = Just i
    , stHistoryDraft = draft
    }
  followInput
  refreshDropdown
  refreshOfferDropdown

moveDown :: Maybe Int -> Int -> Int
moveDown Nothing  _ = 0
moveDown (Just i) n = min (n - 1) (i + 1)

moveUp :: Maybe Int -> Int -> Int
moveUp Nothing  n = n - 1
moveUp (Just i) _ = max 0 (i - 1)

-- | The same up/down shape as 'moveDown'/'moveUp', over the sparse set of
-- selectable row indices rather than a dense @0..n-1@ range — a hint row in
-- the middle of the list is skipped over, never landed on.
offerMoveDown, offerMoveUp :: [Int] -> Maybe Int -> Maybe Int
offerMoveDown ixs cur = case cur of
  Nothing -> listToMaybe ixs
  Just i  -> case dropWhile (<= i) ixs of
    (n : _) -> Just n
    []      -> Just i
offerMoveUp ixs cur = case cur of
  Nothing -> listToMaybe (reverse ixs)
  Just i  -> case takeWhile (< i) ixs of
    [] -> Just i
    xs -> Just (last xs)

selectableIxs :: [OfferRow] -> [Int]
selectableIxs rows = [i | (i, r) <- zip [0 :: Int ..] rows, isJust (rowInsert r)]

-- | Appends one completed turn and scrolls the repl viewport to show it —
-- the document grows downward and the view always follows, same as any
-- terminal. Nothing did this before this session; 'HistoryVP' just stayed
-- wherever it started, which is exactly his bug report ("it doesn't scroll
-- so the end of the output is at the bottom... no terminal behaves like
-- that").
-- | The fallback path every line not caught by a TUI-local command takes:
-- run it through the engine, follow a load if it names one, append 'extra'
-- lines to whatever comes back. 'extra' is @[]@ for an ordinary line and
-- 'tuiHelpLines' for `:help` — the one place this frontend's own commands
-- get documented, since the engine's own `:help` table has no way to know
-- about a command that never reaches it.
runEngineLine :: St -> String -> [String] -> EventM Name St ()
runEngineLine st line extra = do
  let (s', resp) = oneLine (stSession st) line
  -- **The editor is an interactive prompt, so its acts are lenient** (MS12
  -- phase 315, @~mgqwb@): a module whose proofs are not all finished loads as
  -- far as it can and says what did not go in.
  case following Lenient s' resp of
    Just act | resp /= Quit -> do
      (sLoaded, responses, trouble) <- liftIO act
      let out =
            renderResponse s' resp
              ++ concatMap (renderResponse sLoaded) responses
              ++ concatMap (renderTrouble sLoaded) trouble
      appendTurn st { stSession = sLoaded } (Just line) (out ++ extra)
    _ -> do
      appendTurn st { stSession = s' } (Just line) (renderResponse s' resp ++ extra)
      if resp == Quit then get >>= maybeQuit else pure ()

-- | **Every door a quit can be requested through** — Ctrl+D on an empty
-- line and `:quit` from either the REPL or the script bar — comes here
-- rather than calling 'halt' itself, his instruction of 2026-11-18.
--
-- **"Unsaved" is never about losing the session.** The project database
-- already holds every committed line continuously ('persist'), restart or
-- no restart — see `~j3hx8`/`~73f2k`. What this catches is narrower: a
-- script document whose content a `.thena.script` file on disc does not
-- (yet, or any more) match, so a `:script save` would still write
-- something new. A REPL-only session, 'stScript' empty throughout, never
-- trips this at all.
--
-- **One warning, then it goes through** — 'stQuitArmed' is what remembers
-- that the warning already fired; 'afterScriptEdit' clears it on the next
-- edit, so a quit attempt long after, against different unsaved content,
-- asks again rather than riding on a stale confirmation.
maybeQuit :: St -> EventM Name St ()
maybeQuit st = do
  go <- liftIO (shouldQuitNow st)
  if go
    then halt
    else if stScriptMode st
      then put st { stQuitArmed = True, stScriptNote = Just quitNote }
      else appendTurn st { stQuitArmed = True } Nothing [quitNote]

-- | **The quit decision, pulled out so 'maybeQuit' and `:quit` typed
-- straight into the document (`scriptLocal`) answer it the same way** — one
-- rule, not two readings of it. See 'maybeQuit' for what each answer means.
shouldQuitNow :: St -> IO Bool
shouldQuitNow st
  | not (stConfirmQuit st) = pure True
  | stQuitArmed st = pure True
  | otherwise = not <$> scriptUnsaved st

quitNote :: String
quitNote = "unsaved script changes — quit again to discard, or :script save first"

-- | **Compares the document against disc, not a flag** — so this can never
-- drift from what ':script save' itself would do. 'Nothing' (never saved
-- anywhere) or any difference from what is on disc now counts as unsaved;
-- an empty document is never unsaved, there being nothing to lose.
scriptUnsaved :: St -> IO Bool
scriptUnsaved st
  | null (stScript st) = pure False
  | otherwise = case stStored st >>= stFrom of
      Nothing -> pure True
      Just path -> do
        onDisk <- try @SomeException (readFile path)
        pure $ case onDisk of
          Left _ -> True
          Right contents -> contents /= unlines (map slText (stScript st))

-- | **The TUI's own words, recognized directly in the document now — a
-- fresh line exactly the same as an edit to an old one.** His ruling,
-- 2026-11-18, on a proposal that treated the two differently: *"the real
-- split is what I am saying and not what you are saying at all."* One rule:
-- whatever a line's text is when it commits, this is checked first, and the
-- line's text in the document is exactly what was typed either way — a
-- recognized word is not kept out of a saved `.thena.script`, it just also
-- does something.
--
-- 'Nothing' for ordinary proof content, unchanged. A recognized word
-- answers the status text to show as this line's own output (what a
-- refused line's complaint already does) and, as a side effect, applies
-- itself to 'St' — the same handful of commands `scriptBarSubmit` already
-- knows, read off the same functions so the two can't drift apart.
--
-- **Deliberately not here**: the `:script save/sessions/cut/drop/reload/
-- open` family. Those manage the session itself, have their own argument
-- shapes, and are a separate question from "a standing TUI preference, run
-- from inside my own proof" — not folded in without being asked.
scriptLocal :: St -> String -> Maybe (EventM Name St String)
scriptLocal st text = case words text of
  [":theme", name] | Just th <- themeByName name -> Just $ do
    let st' = st { stTheme = th }
    liftIO (saveConfig (configOf st'))
    put st'
    pure ("theme: " <> name)
  [":fold", mode] | mode `elem` ["on", "off"] -> Just $ do
    put st { stFoldOn = mode == "on" }
    pure ("fold: " <> mode)
  paneLine@(":pane" : _)
    | Just (layout', strip', said) <- paneCommand paneLine (stLayout st) (stStrip st) -> Just $ do
        let st' = closeReplyIfStripClosed strip' st { stLayout = layout', stStrip = strip' }
        liftIO (saveConfig (configOf st'))
        put st'
        pure said
  [":preselect", mode] | mode `elem` ["on", "off"] -> Just $ do
    let st' = st { stAutoSelect = mode == "on" }
    liftIO (saveConfig (configOf st'))
    put st'
    pure ("preselect: " <> mode)
  [":whisper", mode] | mode `elem` ["on", "off"] -> Just $ do
    let st' = st { stWhisperOn = mode == "on" }
    liftIO (saveConfig (configOf st'))
    put st'
    pure ("whisper: " <> mode)
  [":dropdown", mode] | mode `elem` ["on", "off"] -> Just $ do
    let st' = st { stDropdownOn = mode == "on" }
    liftIO (saveConfig (configOf st'))
    put st'
    pure ("dropdown: " <> mode)
  [":jev", mode] | mode `elem` ["on", "off"] -> Just $ do
    let st' = st { stJevOn = mode == "on" }
    liftIO (saveConfig (configOf st'))
    put st'
    pure ("jev: " <> mode)
  -- | `:hint` runs from a script line too, his ruling `~g5wjz` — a
  -- TUI-local word is a TUI-local word wherever it is typed. **No
  -- 'saveConfig'**: 'stHint' is content and is not in the dotfile.
  (":hint" : rest) -> Just $ do
    put st { stHint = hintFrom rest }
    pure (hintSaid (hintFrom rest))
  -- | `:model` and `:models` run from a script line and from the bar too,
  -- his ruling `~g5wjz` — a TUI-local word is a TUI-local word wherever it
  -- is typed.
  [":model"] -> Just (pure ("model: " <> Text.unpack (stModel st)))
  [":model", m] -> Just (setModel st (Text.pack m))
  (":models" : rest) -> Just $ do
    openModelPicker st (Text.pack (unwords rest))
    pure ("models: " <> Text.unpack (stModel st) <> " is the one in use")
  [":hint-prompt"] -> Just (("the prompt the model is sent is " <>) <$> liftIO hintPromptPath)
  [":hint-prompt", "reset"] -> Just ((<> " is back to the one that ships") <$> liftIO resetHintPrompt)
  [":confirm-quit", mode] | mode `elem` ["on", "off"] -> Just $ do
    let st' = st { stConfirmQuit = mode == "on" }
    liftIO (saveConfig (configOf st'))
    put st'
    pure ("confirm-quit: " <> mode)
  (":clear" : _) -> Just (pure clearNotHere)
  [":quit"] -> Just $ do
    go <- liftIO (shouldQuitNow st)
    if go
      then halt >> pure "quit"
      else put st { stQuitArmed = True } >> pure quitNote
  _ -> Nothing

-- | **What `:hint`'s tail means** — `~w2tk2` slice 4. Nothing after the
-- word is no hint; anything else is the hint, spaces collapsed.
hintFrom :: [String] -> Maybe String
hintFrom rest = case unwords rest of
  "" -> Nothing
  t  -> Just t

-- | What the line says back, so the bar and a script line say the same thing.
hintSaid :: Maybe String -> String
hintSaid = maybe "hint: cleared" ("hint: " <>)

-- | **Where a committed line actually goes through** — the composing line
-- at the end, or an edit to an existing one with a tail below it
-- ('scriptSubmit', 'runTheEdit'). Both reduce to the same shape: one line
-- just typed, then 'ran' and 'unrun' carried through unchanged — so this is
-- the one place 'scriptLocal' needs wiring in, not two.
--
-- **Why the typed line is pulled out of the batch rather than left in it.**
-- 'rerunTail''s own fold runs on a forked thread (`~twdbp`) that cannot
-- touch 'St' at all — that is what lets a 500-line re-run not freeze the
-- terminal. A TUI-local action needs 'St', so it has to run here, on the
-- thread that already has it, before anything is handed to the fork. The
-- rest of the tail never depended on what the edited line did to the
-- session anyway — a TUI-local line is a no-op on it — so handing the fork
-- the same @s@ it would have gotten either way is exactly as correct as
-- running the line through the engine would have been.
commitTailFrom
  :: Int -> Session -> String -> [String] -> [ScriptLine]
  -> ([ScriptLine] -> EventM Name St ()) -> EventM Name St ()
commitTailFrom at s text ran unrun finish = do
  st <- get
  case scriptLocal st text of
    Nothing -> rerunTail at s (text : ran) unrun finish
    Just action -> do
      said <- action
      let sl = ScriptLine
            { slText = text, slSession = Just s, slRan = Just text
            , slOutput = [said], slOk = True
            }
      rerunTail at s ran unrun (\rest -> finish (sl : rest))

-- | `:preselect` and `:whisper`, in the same column layout
-- 'Thena.Render.renderHelp' uses for its own rows (two-space indent, a
-- 28-wide spelling column) so the appended block reads as part of the same
-- list, not a bolted-on afterthought.
tuiHelpLines :: [String]
tuiHelpLines =
  [ ""
  , "tui-local — never reaches the engine, so :help above doesn't list them:"
  , ""
  ] ++ concatMap (uncurry helpRow)
    [ (":theme ‹name›",     intercalate ", " (map themeName themes))
    , (":pane ‹name› open ‹n›", "put a pane at one of six positions, numbered across:")
    , ("",                  "  1 2 / 3 4 / 5 6, so odd is the left column and even the right")
    , ("",                  "  " <> intercalate ", " (map paneName allPanes))
    , (":pane ‹name› close", "take it off the screen — its width is remembered")
    , (":pane " <> stripName <> " open", "the suggestion strip, under the prompt and as wide as")
    , ("",                  "  the document — it has no position, and nothing else does")
    , ("",                  "  either. Pull its accent bar UP to make it taller;")
    , ("",                  "  the rows come off the document. :pane " <> stripName <> " close")
    , ("F1 … F10",          "take the option in that slot of the suggestion strip.")
    , ("",                  "  Nothing is selected or highlighted there and nothing can")
    , ("",                  "  be: a cell is reached by its own key and by no other way,")
    , ("",                  "  so Up and Down always belong to the document. A wider or")
    , ("",                  "  taller strip has more slots — pull it and see")
    , (":dropdown on|off",  "whether the completion dropdown appears and takes keys")
    , ("",                  "  at all. Off leaves :load's own path listing alone")
    , (":jev on|off",       "whether Jev is asked at all. The suggestion pane shows")
    , ("",                  "  Jev's own candidates and nothing else, so with jev off it")
    , ("",                  "  falls back to its candidates in alphabetical order")
    , (":hint ‹text›",      "put a line in the strip's hint region, the rows kept for")
    , ("",                  "  a model that watches — " <> show stripHintRows <> " of them at least, and a")
    , ("",                  "  longer hint takes rows off the grid. :hint alone clears it.")
    , ("",                  "  A stub: nothing writes one yet")
    , ("a click in a list pane", "folds a namespace in globals — ▾ is open, ▸ folded,")
    , ("",                  "  and the count stays either way; unfolds a ⚠️ or ❌ module's")
    , ("",                  "  row in modules. Anywhere along the row, not just the symbol")
    , (":preselect on|off", "highlight a fresh dropdown's first row on its own")
    , (":whisper on|off",   "show the untyped remainder of the selected candidate")
    , (":clear [n]",        "take the last line and its output off the transcript;")
    , ("",                  "  with n, the last n of them. Ctrl+L is :clear 1")
    , ("",                  "  The session goes back with them, to where the turn now")
    , ("",                  "  last left it — so the panes and the transcript agree")
    , (":script sessions",  "pick a stored session from a list and resume it")
    , ("",                  "  ↑↓ move, Enter resumes, Esc cancels. In the bar too")
    , (":script resume ‹slug›", "the same, by handle, with no list to walk")
    , (":script [path]",    "live-script mode: the pane becomes an editable document")
    , ("",                  "  with a path, that proof-script is opened into it as text:")
    , ("",                  "  its lines are dim until Down walks into them, one run per")
    , ("",                  "  keypress. :script open ‹path› in the bar does the same")
    , ("",                  "  in it: Up/Down walk the document, every other key edits")
    , ("",                  "  text. Editing a committed line makes the lines below it")
    , ("",                  "  stale, drawn dim, until an Enter decides them:")
    , ("",                  "  Enter runs this line and re-runs the lines below it,")
    , ("",                  "  Option+Enter runs this line and discards the lines below it.")
    , ("",                  "  F12 or Ctrl+X opens the command bar — :script leaves,")
    , ("",                  "  :script cut is Option+Enter with no modifier, :script reload")
    , ("",                  "  re-runs from the caret down (from the top, if the caret is")
    , ("",                  "  past the end) and says what changed on disc, :script drop")
    , ("",                  "  discards this line and the lines below it, :script save")
    , ("",                  "  writes back to the file the document was opened from, or")
    , ("",                  "  names it off the clock if there is none —")
    , ("",                  "  Wednesday-11-11-2026-at-22-15.thena.script. :script save")
    , ("",                  "  ‹name› writes a new one; naming a file that exists asks")
    , ("",                  "  once, and :script save! ‹name› replaces it")
    ]
  where
    width = 28
    helpRow spelling gloss
      | length spelling <= width =
          ["  " ++ spelling ++ replicate (width - length spelling) ' ' ++ "  " ++ gloss]
      | otherwise =
          ["  " ++ spelling, "  " ++ replicate width ' ' ++ "  " ++ gloss]

-- | Folds a just-submitted line into 'stHistory' — shell-style: skipped
-- when blank (holding Enter on nothing shouldn't pad history) or when
-- it's an exact repeat of the immediately preceding entry (resubmitting
-- the same line twice, e.g. re-running the last command, shouldn't
-- either). Always resets browsing back to live, submission being exactly
-- what a history session was for; the entry itself is what the *next*
-- 'historyBack' will now reach.
recordHistory :: String -> St -> St
recordHistory line st
  | all isSpace line = st { stHistoryPos = Nothing, stHistoryDraft = "" }
  | otherwise = st
      { stHistory = if lastOf (stHistory st) == Just line then stHistory st else stHistory st ++ [line]
      , stHistoryPos = Nothing
      , stHistoryDraft = ""
      }
  where
    lastOf [] = Nothing
    lastOf xs = Just (last xs)

-- * Live-script mode — `~5vtt3`

-- | **The session every pane draws against.** In the ordinary REPL that is
-- just 'stSession'; in script mode it is the session at the caret, so walking
-- up the document walks the proof-term, goals and machine panes back with it.
-- Standing on line @i@ shows the state /after/ @i@ ran — where you are in the
-- document, not what the line was about to see.
-- **A caret on a line that has not run shows the state that line is about to
-- see**, which under the prefix invariant means nothing has run at all and
-- the answer is the base — the state a freshly opened proof-script is in
-- before its first Down.
activeSession :: St -> Session
activeSession st
  | not (stScriptMode st) = stSession st
  | otherwise = case stScriptPos st of
      Just i
        | Just sl <- nthOf i (stScript st) ->
            maybe (fallback (scriptSessionBefore st i)) id (slSession sl)
      _ -> fallback (scriptTip st)
  where
    fallback = maybe (stSession st) id

nthOf :: Int -> [a] -> Maybe a
nthOf i xs
  | i < 0 = Nothing
  | otherwise = listToMaybe (drop i xs)

-- | **How many of the document's lines have run in this session** — the
-- frontier of 'slSession'. Read rather than stored: a second copy of it in
-- 'St' would be one more thing every rebuild has to remember.
scriptFrontier :: St -> Int
scriptFrontier st = length (takeWhile (isJust . slSession) (stScript st))

-- | **The first line of the document that no longer says what it ran with**,
-- and therefore the first that is stale — `~htff2`. 'Nothing' when every line
-- holds the text that produced its session.
--
-- **Read off the document rather than stored**, the same reasoning as
-- 'scriptFrontier': a copy in 'St' would be one more thing every rebuild has
-- to remember, and this one would have to be reset by hand the moment an edit
-- was typed back to what it was. It replaced a 'Maybe Int' field that was
-- exactly that.
--
-- **Everything at or below it is drawn dim.** The line itself was edited, so
-- its own session is from text that is gone; the lines under it ran against
-- that session.
scriptStaleFrom :: St -> Maybe Int
scriptStaleFrom st = listToMaybe [i | (i, sl) <- zip [0 ..] (stScript st), staleLine sl]

-- | **Whether a line's text has changed since it ran.** A line that never ran
-- is not stale: there is no session under it to disagree with, and it is dim
-- already for being past the frontier.
staleLine :: ScriptLine -> Bool
staleLine sl = case slRan sl of
  Just ran -> ran /= slText sl
  Nothing -> False

-- | The session a new line past the end of the script runs against: the last
-- line that has run, or the base.
scriptTip :: St -> Maybe Session
scriptTip st = scriptSessionBefore st (scriptFrontier st)

-- | The session line @i@ runs against — line 0's is the base the mode was
-- entered on. **This is the whole of the rewind**: no `:undo`, no replay, no
-- arithmetic over how many snapshots a line happened to push.
scriptSessionBefore :: St -> Int -> Maybe Session
scriptSessionBefore st i
  | i <= 0 = stScriptBase st
  | otherwise = case nthOf (i - 1) (stScript st) of
      -- An un-run line above can only happen when nothing has run at all,
      -- the sessions being a prefix, so the base is the right answer and
      -- there is nothing to search backwards for.
      Just sl -> maybe (stScriptBase st) Just (slSession sl)
      Nothing -> stScriptBase st

-- | The tail below line @i@, split where the frontier is: the part that has
-- run in this session, as text to re-run, and the part that has not, which
-- stays exactly as it is. **Every rebuild goes through this**, which is how
-- the prefix invariant survives an edit in the middle of an opened
-- proof-script: re-running stops at the frontier instead of running the rest
-- of the file as a side effect of one Enter.
tailFrom :: St -> Int -> ([String], [ScriptLine])
tailFrom st at =
  let (ran, unrun) = span (isJust . slSession) (drop at (stScript st))
   in (map slText ran, unrun)

-- | Run one line and keep everything it produced. The IO is 'following''s,
-- the same half 'runEngineLine' takes for the ordinary REPL — a `:load` names
-- a file and somebody has to read it.
-- **Lenient, the same as the prompt's own line** — MS12 phase 315. Live-script
-- mode *is* the prompt here: what he types is the document, so an @import@ of a
-- module whose proofs are not all finished must come in as far as it can on
-- this path too. The two paths taking different leniencies would mean the same
-- line behaved one way typed and another way replayed.
runScriptLine :: Session -> String -> IO ScriptLine
runScriptLine s line = do
  let (s', resp) = oneLine s line
  case following Lenient s' resp of
    Just act | resp /= Quit -> do
      (sLoaded, responses, trouble) <- act
      let out =
            renderResponse s' resp
              ++ concatMap (renderResponse sLoaded) responses
              ++ concatMap (renderTrouble sLoaded) trouble
      pure (ScriptLine line (Just sLoaded) (Just line) out (responseTook resp))
    _ -> pure (ScriptLine line (Just s') (Just line) (renderResponse s' resp) (responseTook resp))

-- | Whether a response means the line actually advanced the session.
--
-- **Display only** — the stored 'slSession' is correct either way, because a
-- refused line simply hands back the session it was given. This decides a
-- marker, nothing more, so an unlisted refusal shows its text without a
-- marker rather than corrupting anything. `IllTyped` is deliberately absent:
-- @:infer@ answering "this term has no type" is the command working.
responseTook :: Response -> Bool
responseTook resp = case resp of
  Rejected {}        -> False
  LineRefused {}     -> False
  Failed {}          -> False
  RuleFileRefused {} -> False
  EntryMistyped {}   -> False
  BasesIllTyped {}   -> False
  -- | **A program that ran and stopped badly did not do what its line said**,
  -- and in this mode that has to show. Found by pty, 2026-11-11: a trailing
  -- space on `open Nat` makes the name @"Nat "@, the act halts with
  -- *stuck: nothing is named Nat …*, and because a halt was not in this list
  -- the document drew the line as though it had worked — with the lines below
  -- it failing for no visible reason. The ordinary REPL never had the problem,
  -- since it prints every response either way.
  Ran _ _ stop       -> stopTook stop
  _                  -> True

-- | Whether an instral program's stop means its line took effect.
--
-- **The four that are not failures are the four that are not over**:
-- a completed program, a question waiting for an answer, a yield handing
-- control back, and a pause. Everything else is the engine declining to do
-- what the line asked.
stopTook :: Stop -> Bool
stopTook stop = case stop of
  Completed   -> True
  Waiting {}  -> True
  Yielded {}  -> True
  Paused {}   -> True
  Halted {}         -> False
  Refused {}        -> False
  BlockRefused {}   -> False
  BlockIllTyped {}  -> False
  Uncertified {}    -> False
  Untrusted {}      -> False

-- | `:script` from the ordinary REPL. **A fresh session, his ruling** — the
-- mode does not inherit what the REPL has been doing, because the REPL
-- echoes refused lines too and a script must not contain any.
enterScriptMode :: St -> EventM Name St ()
enterScriptMode st = do
  base <- case stScriptBase st of
    Just s -> pure (Just s)
    Nothing -> do
      (s, _) <- liftIO startingSession
      pure (Just s)
  -- The session the document will be persisted under, minted here and written
  -- the first time a line is committed ('persist').
  stored <- case stStored st of
    Just held -> pure (Just held)
    Nothing -> do
      index <- liftIO loadIndex
      Just <$> liftIO (freshStored index Nothing)
  put st
    { stScriptMode = True
    , stStored = stored
    , stScriptBase = base
    , stScriptPos = Nothing
    , stScriptBar = Nothing
    , stScriptNote = Nothing
    , stInput = emptyInput
    }
  closeDropdowns
  followInput

-- | **Write the live document to the project database** — `~22qjj`. The lines
-- go to the session's own proof-script and the index entry is rewritten with
-- where the caret stands, what the session has read, and what it has proved.
--
-- **Every committed line and every caret move, his instruction of 2026-11-06**:
-- *"it happens automatically line by line. That's never going to be an issue,
-- that's not too many writes anyway, nowadays editors write even more often."*
-- So it hangs off 'afterScriptEdit', which is already the one place every
-- commit and every move in the mode goes through.
--
-- **Nothing it does can fail loudly.** 'Tui.Database' swallows its own IO
-- trouble, and a document with no stored session yet — the ordinary REPL — is
-- simply not written.
persist :: EventM Name St ()
persist = do
  st <- get
  case stStored st of
    Nothing -> pure ()
    -- Nothing has been committed, so there is nothing to write — and no
    -- reason to put a `.thena` directory into somebody's project for a
    -- session they have not started.
    Just _ | null (stScript st) -> pure ()
    Just stored -> do
      let ran = scriptTip st
          entry =
            stored
              { stCaret = maybe (length (stScript st)) id (stScriptPos st)
              , stLines = length (stScript st)
              , stRead = maybe [] (\s -> [(p, digestText d) | (p, d) <- filesRead s]) ran
              -- **Filled since MS12 phase 311** — `provedSlices` answers the
              -- name and the engine's own indices, which `scriptProofs` puts
              -- back into the document's numbering. `~jnfkj` asked for this
              -- and it is answered.
              , stProofs = scriptProofs st
              }
      liftIO (writeTranscript (stSlug entry) (map slText (stScript st)))
      others <- liftIO loadIndex
      liftIO (saveIndex ([o | o <- others, stSlug o /= stSlug entry] <> [entry]))
      put st { stStored = Just entry }

-- | **Which theorems the document proves, and where each one is in it** —
-- the @proofs@ field of the index entry, and `~jnfkj`'s consumer.
--
-- 'Thena.Driver.provedSlices' (MS12 phase 311) answers the name in full and
-- the first and last line of each proof, **in the engine's numbering**, which
-- is not the document's — so the indices are translated here.
--
-- **Why a translation rather than the engine's numbers written down.**
-- 'provedSlices' indexes 'submittedLines', the lines the engine was handed;
-- the transcript this index sits beside is the document's lines, blanks and
-- comments included. The two agree line for line until one document line
-- hands over several, and one does: @:replay ‹path›@ submits the whole of the
-- file it names ('Thena.Files.script' folds it through 'oneLine'), so a
-- forty-line replay on line 3 leaves the engine forty lines ahead for
-- everything below it. **It is measured per line rather than assumed** — how
-- many lines the engine had been handed by the end of each document line is a
-- read of the session that line produced, and the line holding engine index
-- @k@ is the first whose count has passed it.
--
-- A slice that starts before the document did is dropped rather than clamped.
-- It belongs to the base session, so it is not a slice of this transcript —
-- which cannot happen while entering the mode boots a fresh session, and is
-- one line here rather than an invariant to remember.
scriptProofs :: St -> [(String, Int, Int)]
scriptProofs st = case scriptTip st of
  Nothing -> []
  Just tip ->
    [ (name, lineOf from, lineOf to)
    | (name, from, to) <- provedSlices tip
    , from >= base
    ]
  where
    base = maybe 0 (length . submittedLines) (stScriptBase st)
    ends = [maybe base (length . submittedLines) (slSession sl) | sl <- stScript st]
    lineOf k = length (takeWhile (<= k) ends)

-- | What became of a file a session read: unchanged, changed under it, or not
-- findable from here at all.
--
-- **Three outcomes and not two, and this is the part that bites if it is got
-- wrong** — §5 of @.jalivert/discussion/the-session-in-the-tui.md@. The paths
-- come back mixed: a file the user named is relative to the working directory,
-- while the prelude and the standard base are absolute, out of the data
-- directory. So starting the TUI in the wrong folder makes every file of the
-- user's corpus unreadable, and reporting that as *changed* would be a lie
-- about a file nobody touched.
data FileCheck = Unchanged | Changed | Missing
  deriving (Eq, Show)

-- | **Which of the files a session stands on have moved under it.** The whole
-- of the mechanism, and nothing is owed by the engine for it: `filesRead`
-- hands over a path and a `Digest` per file, `digestOf` hashes what is on disc
-- now, and `Digest` has `Eq`. The engine does no IO and the frontend owns the
-- project root, so there is deliberately no @FilePath -> IO Digest@ on the
-- boundary.
-- **Two moments, comparing different things, and one code path** — §5 of the
-- design. A partial reload is the same process and still holds the session's
-- own `Digest` values; taking a session up again is a new process, where the
-- `Digest` is gone and the sixteen hex digits in the index are what there is to
-- compare. So everything goes through 'checkStored' and the digest is text at
-- the point of comparison.
checkFilesRead :: Session -> IO [(FilePath, FileCheck)]
checkFilesRead s = checkStored [(p, digestText d) | (p, d) <- filesRead s]

-- | The same check against what the index wrote down.
checkStored :: [(FilePath, String)] -> IO [(FilePath, FileCheck)]
checkStored = mapM one
  where
    one (path, was) = do
      there <- doesFileExist path
      if not there
        then pure (path, Missing)
        else do
          -- Strict, for the reason 'Tui.Database.loadIndex' is: a lazy read
          -- holds its handle open, and this walks every file a session read.
          now <- readFile' path
          pure (path, if digestText (digestOf now) == was then Unchanged else Changed)

-- | The two files every session reads at boot, asked for by name rather than
-- guessed at from the shape of a path. **It is what lets the report tell
-- "Thena itself changed under this session" from "your file changed"** —
-- different sentences for different facts, which the design asks for and a
-- heuristic over absolute-vs-relative would only approximate.
shippedPaths :: IO [FilePath]
shippedPaths = sequence [preludePath, rulesPath]

-- | One line for the pane's foot, or 'Nothing' when nothing moved.
staleNote :: [FilePath] -> [(FilePath, FileCheck)] -> Maybe String
staleNote shipped checks = case clauses of
  [] -> Nothing
  cs -> Just (intercalate "; " cs)
  where
    yours = [p | (p, Changed) <- checks, p `notElem` shipped]
    thenas = [p | (p, Changed) <- checks, p `elem` shipped]
    missing = [p | (p, Missing) <- checks]
    clauses =
      [ plural (length yours) "file" <> " changed since these lines read " <> listUp yours
      | not (null yours)
      ]
        <> [ "thena's own " <> listUp (map takeFileName thenas) <> " changed under this session"
           | not (null thenas)
           ]
        <> [ plural (length missing) "file" <> " cannot be found from here — wrong folder? " <> listUp missing
           | not (null missing)
           ]
    plural k noun = show k <> " " <> noun <> (if k == 1 then "" else "s")
    listUp ps = case ps of
      [p] -> p
      (p : q : rest) -> p <> ", " <> q <> (if null rest then "" else ", …")
      [] -> ""

-- | **Open a proof-script from disc into the mode** — `~22qjj`, and the
-- design's *one code path at three speeds*
-- (@.jalivert/discussion/the-session-in-the-tui.md@ §8). Its lines become the
-- document as text; @upto@ of them are run before you get the keyboard, and
-- the caret is left on the last one that ran.
--
--   * **opening a `.thena.script`** is @upto = 0@: nothing runs, every line is
--     dim, and Down walks into it a line at a time.
--   * **resuming a stored session** will be @upto = its stored caret@, which
--     is the only difference between the two.
--   * **reloading** is the same call again on a document already open.
--
-- **It does not read the engine's record and cannot.** A record only ever
-- holds lines that were submitted, so the lines below the caret have nowhere
-- to live but here — `Session` is opaque and `flattened` is not exported,
-- which is the boundary saying the same thing.
--
-- **Every line of the file is kept, comments and blanks included.** Measured
-- against `lib:thena`: `oneLine` answers `Blank` for @""@, @"   "@ and
-- @"-- a comment"@ and renders nothing, so they cost a no-op apiece and the
-- file round-trips through `:script save` as it was written. Dropping them
-- would silently reformat somebody's proof.
-- **It answers whether it opened anything**, because a missing path is
-- reported differently depending on where the command was typed: the REPL has
-- turns, the command bar has the pane's foot.
openScriptFile :: St -> FilePath -> Int -> EventM Name St Bool
openScriptFile st path upto = do
  there <- liftIO (doesFileExist path)
  if not there
    then pure False
    else do
      src <- liftIO (readFile' path)
      index <- liftIO loadIndex
      -- **A session of its own, recording where the lines came from.** The
      -- file the user opened is never the file the document is written to:
      -- persisting happens on every keystroke, and auto-writing over somebody's
      -- corpus file is not what was agreed. `:script save` is still the way
      -- to put a document somewhere by name.
      stored <- liftIO (freshStored index (Just path))
      openDocument st stored (lines src) upto ("opened " <> path)
      pure True

-- | **The one way a document is opened**, whatever it came from: a path on
-- disc, a stored session's transcript, or a reload of either. The lines are
-- the document; the first @upto@ of them are run before the keyboard comes
-- back, and the caret is left on the last one that ran.
--
-- **Opening a file, resuming a session and reloading are one code path at
-- three speeds** — the design's own words, and this is where that is true
-- rather than merely intended.
openDocument :: St -> Stored -> [String] -> Int -> String -> EventM Name St ()
openDocument st stored texts upto said = do
  base <- case stScriptBase st of
    -- A base is a session nothing has advanced, so the one already in hand is
    -- the same session a new boot would produce, a second of prelude-reading
    -- later.
    Just s -> pure s
    Nothing -> fst <$> liftIO startingSession
  let (runNow, rest) = splitAt (max 0 (min upto (length texts))) texts
  ran <- liftIO (foldRun base runNow)
  let doc = ran ++ [ScriptLine t Nothing Nothing [] True | t <- rest]
      caret = max 0 (length ran - 1)
  put st
    { stScriptMode = True
    , stScriptBase = Just base
    , stScript = doc
    , stScriptPos = if null doc then Nothing else Just caret
    , stScriptDraft = ""
    , stScriptBar = Nothing
    , stStored = Just stored
    , stScriptNote =
        Just
          ( said <> " — " <> show (length doc) <> " lines, " <> show (length ran)
              <> " run; Down runs the next"
          )
    , stInput = case nthOf caret doc of
        Just sl -> E.editorText Input (Just 1) (Text.pack (slText sl))
        Nothing -> emptyInput
    }
  closeDropdowns
  followInput
  persist

-- | **`:script resume ‹slug›` — take up a stored session where it was left** —
-- `~22qjj`, and the reason the database stores a caret at all: resuming goes
-- there, which is his ruling, and *top or bottom?* was never the question.
--
-- **This is the second moment for the staleness check** and it compares
-- different things from a reload's: the process that wrote those digests is
-- gone, so what there is to compare is the sixteen hex digits in the index
-- against the files as they are now. The three outcomes are the same three.
resumeStored :: St -> Stored -> [String] -> EventM Name St ()
resumeStored st stored texts = do
  checks <- liftIO (checkStored (stRead stored))
  shipped <- liftIO shippedPaths
  let moved = maybe "" ("; " <>) (staleNote shipped checks)
  openDocument st stored texts (stCaret stored + 1) ("resumed " <> stName stored <> moved)

-- | **`:script reload` — re-run the document from the caret down** —
-- `~rctjq`, his question of 2026-11-11, and it is 'openScriptFile' at an index
-- rather than a second feature. The caret's line and everything below it drop
-- the session they produced and go back to being text; the lines above keep
-- theirs, and the walk down re-runs the rest.
--
-- **With the caret on line 0 — or composing past the end, where there is no
-- line to be at — it is the hard reload**, and the base session is booted
-- again so the prelude and the standard rule base are re-read. That is not a
-- special case bolted on: the session a reload runs from is the one above its
-- first line, and above line 0 there is no stored session, so one is made.
--
-- **IT RUNS THE STALENESS CHECK, AND THE REASON IS IN THE WORD "RELOAD"** —
-- §4 of the design. The kept prefix is not re-read, so line 10's session still
-- holds the modules as they were when line 10 ran; a partial reload above a
-- changed import would otherwise keep the stale one silently, which is the one
-- thing a reload is supposed to prevent. **This is a check on an action the
-- user just asked for and not filesystem watching**, which he refused
-- (`~qb6gc`).
scriptReload :: EventM Name St ()
scriptReload = do
  st <- get
  let n = length (stScript st)
      at = maybe 0 id (stScriptPos st)
  if n == 0
    then put st { stScriptBar = Nothing, stScriptNote = Just "nothing to reload" }
    else do
      checks <- liftIO (maybe (pure []) checkFilesRead (scriptSessionBefore st at))
      shipped <- liftIO shippedPaths
      base <- case at of
        0 -> Just . fst <$> liftIO startingSession
        _ -> pure (stScriptBase st)
      let doc = take at (stScript st) ++ map unran (drop at (stScript st))
          said =
            "reload: "
              <> show (n - at)
              <> (if n - at == 1 then " line" else " lines")
              <> " un-run — Down runs the next"
      put st
        { stScriptBase = base
        , stScript = doc
        , stScriptPos = Just at
        , stScriptBar = Nothing
        , stInput = E.editorText Input (Just 1) (Text.pack (maybe "" slText (nthOf at doc)))
        , stScriptNote = Just (maybe said ((said <> "; ") <>) (staleNote shipped checks))
        }
      afterScriptEdit

-- | A line of the document with the state it produced thrown away: the text
-- stays, and that is the whole of a reload.
unran :: ScriptLine -> ScriptLine
unran sl = sl { slSession = Nothing, slRan = Nothing, slOutput = [], slOk = True }

-- | Back to the ordinary REPL, whose 'stSession'/'stTurns' were never touched.
-- The script itself stays in memory, so toggling out to check something and
-- back in loses nothing.
leaveScriptMode :: EventM Name St ()
leaveScriptMode = do
  st <- get
  put st
    { stScriptMode = False
    , stScriptBar = Nothing
    , stScriptPos = Nothing
    , stInput = emptyInput
    }
  closeDropdowns
  followInput

-- | Shut both dropdowns and the recovery underline that is computed beside
-- them. **A dropdown belongs to a line someone is writing**, so crossing a
-- mode boundary closes it rather than rebuilding it for an empty line —
-- his report, 2026-10-20, and it was two visible defects at once.
--
-- Measured under a pty before the fix: @:script@ on a session with three
-- lines of transcript left the full rule chart on screen at rows 26-35, the
-- bottom of the pane, while the document's own caret stood at row 3. The
-- box was not merely unwanted, it was in the wrong place — 'popupAt' reads
-- 'stInputExtent', which lags one frame by construction, so the frame drawn
-- on the mode switch positions the box against the *repl* input line it has
-- just stopped drawing. Nothing redraws until the next keypress, so it sits
-- there, detached, until you touch something. Refreshing it here could only
-- ever re-open it at the stale coordinates; closing it is the fix.
--
-- **The slate is recomputed rather than cleared** — `~3gn2r`. The box is
-- closed because it would be drawn at stale coordinates; the offers have not
-- gone anywhere, and on a mode switch the active session has changed, so the
-- strip wants a fresh answer and not a blank one.
closeDropdowns :: EventM Name St ()
closeDropdowns = do
  st <- get
  put st
    { stDropdown = Nothing
    , stOfferDropdown = Nothing
    , stSlate = keepJevOrder (stSlate st) (slateFor st)
    , stRecoveredSpan = Nothing
    , stDismissed = Nothing
    , stArrowsReleased = False
    }

-- | **A rebuilt slate keeps the order the old one had when it offers the same
-- things** — `~7prxf`, his report of 2026-11-19: /"Why does the suggestion
-- list revert to abandon and along when I hit ctr + x? That is proper
-- dumb."/
--
-- **What was happening.** 'closeDropdowns' rebuilt the slate from the engine,
-- and the engine's order is tokens-before-productions — @abandon@, @along@,
-- @app-first-argument@. Jev's ranking lives in the *order* of 'slateRows'
-- ('floatJevRows'), nowhere else, so rebuilding threw it away. Ctrl+X does
-- not change the line, so there was nothing to rebuild for.
--
-- **The test is the candidate set and not the order**, which is the same
-- comparison 'refreshOfferDropdown' already makes before asking Jev again: if
-- the engine offers the same things, the slate in hand is that list already
-- ranked and is strictly better than a fresh one. A different set means the
-- line moved and the fresh slate is the right one — and Jev is asked again by
-- the path that moved it.
keepJevOrder :: Slate -> Slate -> Slate
keepJevOrder old new
  | slateJevPicked old > 0, sameSet = old { slateStart = slateStart new, slateReplaceLen = slateReplaceLen new }
  | otherwise = new
  where
    sameSet = sortOn key (slateRows old) == sortOn key (slateRows new)
    key r = (rowLabel r, rowInsert r)

-- | Enter in the document. Composing past the end appends; standing on line
-- @i@ **replaces** it — rewind to @i@, run what is written there now, then
-- re-run the stored tail.
--
-- **The tail is re-run rather than discarded**, which his own command-bar
-- design forced: the bar inserts a line at the caret, and an insert that
-- threw away everything below it would be useless. Each tail line is run
-- exactly as if retyped, so one that no longer works keeps its place and its
-- complaint and the rest carry on from whatever session it handed back — the
-- same thing that would happen at a prompt.
scriptSubmit :: EventM Name St ()
scriptSubmit = do
  st <- get
  let line = concatMap Text.unpack (getEditContents (stInput st))
  case stScriptPos st of
    _ | all isSpace line, isNothing (stScriptPos st) -> pure ()
    Nothing -> case scriptTip st of
      Nothing -> pure ()
      Just s -> case scriptLocal st line of
        Nothing -> do
          sl <- liftIO (runScriptLine s line)
          put st { stScript = stScript st ++ [sl], stInput = emptyInput, stScriptNote = Nothing }
          afterScriptEdit
        Just action -> do
          said <- action
          let sl = ScriptLine
                { slText = line, slSession = Just s, slRan = Just line
                , slOutput = [said], slOk = True
                }
          st' <- get
          put st' { stScript = stScript st' ++ [sl], stInput = emptyInput, stScriptNote = Nothing }
          afterScriptEdit
    -- | **Clearing a committed line and pressing Enter deletes it** — his
    -- report, 2026-10-20: *"it literally leaves an empty line there."* It
    -- did: the blank went through 'foldRun' as a line of its own, so the
    -- document kept a row that runs nothing and saves to the file as a
    -- stray newline. Emptying a line in a document means removing it, so
    -- the tail is spliced up and re-run from the session the line *before*
    -- it left behind — the same rebuild an edit does, one line shorter.
    --
    -- **@~sv5v8@ has made this unreachable and it is left standing on
    -- purpose.** Clearing a committed line is now an edit like any other,
    -- so the first Backspace severs the tail and un-parks the caret, and
    -- this branch can no longer be entered with 'stScriptPos' set. It is
    -- also the only splice left in the mode, which is half of @~c9rj9@ —
    -- his open question of whether dropping a line truncates or splices.
    -- Deleting it would answer that question by attrition, so it waits.
    Just i | all isSpace line -> case scriptSessionBefore st i of
      Nothing -> pure ()
      Just s -> do
        let (ran, unrun) = tailFrom st (i + 1)
        rerunTail i s ran unrun $ \rebuilt -> do
          st' <- get
          put (reseated st' i (take i (stScript st') ++ rebuilt ++ unrun))
          afterScriptEdit
    Just i -> case scriptSessionBefore st i of
      Nothing -> pure ()
      Just s -> do
        let (ran, unrun) = tailFrom st (i + 1)
        commitTailFrom i s line ran unrun $ \rebuilt -> do
          st' <- get
          put (reseated st' i (take i (stScript st') ++ rebuilt ++ unrun))
          afterScriptEdit

-- | The document after a commit on line @i@, and where the caret goes with
-- it.
--
-- **It un-parks to the composing line, as it always has, when every line of
-- the document has run.** That was the only possible answer while an edit
-- severed the tail: there was nothing below to stand on.
--
-- **It stays on line @i@ when lines below have not run** — an opened
-- proof-script, @~22qjj@. There is no composing line past the end of a
-- document whose last lines have never been submitted; un-parking there would
-- seat the caret below the frontier, which is the one position the prefix
-- invariant does not allow. **A splice is the one case where line @i@ is a
-- different line afterwards**, so the text is read back out of the new
-- document rather than carried over.
reseated :: St -> Int -> [ScriptLine] -> St
reseated st i doc = case (all (isJust . slSession) doc, nthOf i doc) of
  (False, Just sl) ->
    st
      { stScript = doc
      , stScriptPos = Just i
      , stInput = E.editorText Input (Just 1) (Text.pack (slText sl))
      , stScriptNote = Nothing
      }
  _ ->
    st
      { stScript = doc
      , stScriptPos = Nothing
      , stInput = E.editorText Input (Just 1) (Text.pack (stScriptDraft st))
      , stScriptDraft = ""
      , stScriptNote = Nothing
      }

-- | Shift+Enter's operation: **the caret's line is run and everything after
-- it is discarded.** On the composing line there is no tail, so it is an
-- ordinary submit; on a blank committed line there is nothing to run, so it
-- is 'scriptTruncate' — the same rule as everywhere else in the mode, that
-- an empty line is not a line.
scriptCutAndRun :: EventM Name St ()
scriptCutAndRun = do
  st <- get
  let line = concatMap Text.unpack (getEditContents (stInput st))
  case stScriptPos st of
    Nothing -> scriptSubmit
    Just _ | all isSpace line -> scriptTruncate
    Just i -> case scriptSessionBefore st i of
      Nothing -> pure ()
      Just s -> do
        rebuilt <- liftIO (foldRun s [line])
        put st
          { stScript = take i (stScript st) ++ rebuilt
          , stScriptPos = Nothing
          , stInput = E.editorText Input (Just 1) (Text.pack (stScriptDraft st))
          , stScriptDraft = ""
          , stScriptNote = Nothing
          }
        afterScriptEdit

-- | Run a list of lines in order from one session, keeping each line's own
-- result — the rebuild every edit and every insert goes through.
foldRun :: Session -> [String] -> IO [ScriptLine]
foldRun _ [] = pure []
foldRun s (l : ls) = do
  sl <- runScriptLine s l
  rest <- foldRun (maybe s id (slSession sl)) ls
  pure (sl : rest)

-- | **'foldRun', off the keypress** — `~twdbp`, his ruling of 2026-11-18 on
-- his own report that a 500-line re-run froze the terminal for 9.6 to 25.2
-- seconds with no sign anything was happening. Every call site that used to
-- do @rebuilt <- liftIO (foldRun s texts)@ and then splice the three pieces
-- together now does that splicing inside @finish@ instead, and hands it to
-- this.
--
-- @at@ is the document index the batch starts at — everything before it in
-- 'stScript' is never touched. @unrun@ is whatever was already sitting below
-- the batch, carried through to every step unchanged. @finish@ runs once,
-- when 'runRerunBatch' posts the whole batch's result — exactly what the
-- call site did with 'foldRun''s result before this existed.
--
-- **The whole batch goes dim here, synchronously, the instant this is
-- called** — not new: a line below an edit has always gone dim the moment
-- the edit landed (`~htff2`), not when something later gets around to
-- re-running it. What is new is everything after that moment, which is
-- 'runRerunBatch''s to report.
rerunTail
  :: Int
  -> Session
  -> [String]
  -> [ScriptLine]
  -> ([ScriptLine] -> EventM Name St ())
  -> EventM Name St ()
rerunTail at session texts unrun finish = do
  closeDropdowns
  st <- get
  let gen = stRerunGen st + 1
      pending = map freshPending texts
      chan = stJevChan st
  put st
    { stRerunGen = gen
    , stRerun = Just RerunState
        { rrGen = gen, rrAt = at, rrPending = pending, rrUnrun = unrun
        , rrFinish = finish, rrShow = False
        }
    , stScript = take at (stScript st) ++ pending ++ unrun
    }
  liftIO (void (forkIO (runRerunBatch chan gen session texts)))

-- | The background half of 'rerunTail'. **Two numbers, both his, both
-- 2026-11-18** — a step is posted no more than once every 50ms of wall
-- clock, so a batch that finishes faster than that posts nothing until its
-- one, final step (his reasoning: /"there is no reason to cause visual
-- flashing when reloading 50 lines would just take 20ms"/), and
-- 'postRerunStep' marks a step 'visible' only once the whole run has taken
-- half a second — his words, /"the entire re-run takes longer than half a
-- second... some visual signal that stuff is happening"/.
runRerunBatch :: BChan AppEvent -> Int -> Session -> [String] -> IO ()
runRerunBatch chan gen session texts = do
  start <- getCurrentTime
  go start start session texts []
  where
    go start lastPost s pending acc = case pending of
      [] -> pure ()
        -- unreachable: every recursive call below passes a non-empty list,
        -- guarded by the 'null ts' checks that fire before it would be.
      (t : ts) -> do
        sl <- runScriptLine s t
        let acc' = sl : acc
            s'   = maybe s id (slSession sl)
        if null ts
          then postRerunStep chan gen start True (reverse acc')
          else do
            now <- getCurrentTime
            if diffUTCTime now lastPost >= 0.05
              then do
                postRerunStep chan gen start False (reverse acc')
                go start now s' ts acc'
              else go start lastPost s' ts acc'

postRerunStep :: BChan AppEvent -> Int -> UTCTime -> Bool -> [ScriptLine] -> IO ()
postRerunStep chan gen start finished soFar = do
  now <- getCurrentTime
  writeBChan chan (RerunStep gen soFar (diffUTCTime now start >= 0.5) finished)

-- | A posted step from 'rerunTail''s background thread. **A generation that
-- does not match 'stRerun' is a straggler nothing is waiting on any more**
-- and is dropped — the same rule 'handleJevDue' applies to a superseded
-- timer.
--
-- A step that is not yet 'finished' only ever touches 'stScript' and
-- 'rrShow' — the splice is exactly 'rrPending''s own shape with a longer
-- completed prefix, which is what lets 'scriptFrontier' draw the
-- progression with no other state to keep true. The final step clears
-- 'stRerun' and hands the whole batch to 'rrFinish', which does the rest —
-- the caret, the note, 'afterScriptEdit' — exactly as the call site did
-- before any of this existed.
handleRerunStep :: Int -> [ScriptLine] -> Bool -> Bool -> EventM Name St ()
handleRerunStep gen soFar shown finished = do
  st <- get
  case stRerun st of
    Just rs | rrGen rs == gen ->
      if finished
        then do
          put st { stRerun = Nothing }
          rrFinish rs soFar
        else
          put st
            { stScript =
                take (rrAt rs) (stScript st)
                  ++ soFar
                  ++ drop (length soFar) (rrPending rs)
                  ++ rrUnrun rs
            , stRerun = Just rs { rrShow = shown }
            }
    _ -> pure ()

-- | **How every script-mode event that is not typing ends: the dropdown
-- closes.** Committing a line, walking the caret, dropping a line, inserting
-- one from the bar — none of them is someone writing a line, so none of them
-- should leave a completion box open. Typing does not come through here; it
-- goes to the editor branch of 'documentOrHistory' and refreshes as it always
-- has.
--
-- **This one definition is three of his reports, 2026-10-20, and they were
-- one bug.**
--
--   * *"why does it move the dropdown down a bit?"* — 'popupAt' positions
--     against 'stInputExtent', which lags a frame. A commit adds a line and
--     its output, so the box drew two rows above where the caret had just
--     moved to and snapped down on the next keypress. Measured: rows 11-20,
--     then 13-22. It cannot be mispositioned if it is not open, and by the
--     time typing opens it the input has not moved since the last frame.
--   * *"when I hit enter, that obviously needs to drop the lines below it…
--     I think you broke it"* then *"it's the weird combination… of by
--     default selected option in the dropdown and the option being just what
--     I typed on the line."* Exactly that: walking to a committed line
--     reopened the dropdown with a row preselected, so Enter **accepted the
--     completion** instead of reaching 'scriptSubmit' — and because the row
--     read the same as the line, the accept was invisible and the re-run
--     never happened. Enter was never broken; it was being eaten.
--   * And the dropdown standing open over a line nobody is writing to, which
--     is what he said about the command bar and is the same principle.
--
-- **It no longer has a staleness slot to clear, and that is `~htff2`.** There
-- was one, cleared here on every commit and every move, on the reasoning that
-- a move took the edit back — which is precisely the behaviour he rejected on
-- 2026-11-18. Staleness is now read off the document ('scriptStaleFrom'), so a
-- commit stops it by re-running the lines and a move stops nothing, because
-- there is nothing to stop: the edit is in the document and the line is dim
-- until something runs it.
afterScriptEdit :: EventM Name St ()
afterScriptEdit = do
  closeDropdowns
  followInput
  persist
  -- | **Any edit re-arms 'maybeQuit''s one-warning gate** — his 2026-11-18
  -- instruction's check is against the document as it now stands, so a
  -- quit held back once must ask again rather than letting a later,
  -- different bit of unsaved work ride through on an old confirmation.
  st <- get
  put st { stQuitArmed = False }

-- | **Back out of a line that has been emptied: remove it and seat the caret
-- at the end of the line above** — `~282h8`, his report of 2026-11-13.
--
-- **It is the splice `scriptSubmit` already does for a cleared line, reached by
-- the other gesture.** Clearing a committed line and pressing Enter has spliced
-- the tail up and re-run it since 2026-10-20; this makes the backspace that
-- walks off the front of the same emptied line mean the same thing, so the two
-- cannot disagree about what emptying a line does. **Nothing new is decided
-- about truncate-versus-splice** — `~c9rj9` is still his, and this adds no
-- third behaviour.
--
-- **At line 0 it is a no-op, which is what Backspace there already did.** There
-- is no line above to be seated on, and the mode stops rather than wraps
-- everywhere else ('scriptUp'). Removing the first line stays reachable by
-- clearing it and pressing Enter.
scriptBackOut :: Int -> EventM Name St ()
scriptBackOut i
  | i <= 0 = pure ()
  | otherwise = do
      st <- get
      case scriptSessionBefore st i of
        Nothing -> pure ()
        Just s -> do
          let (ran, unrun) = tailFrom st (i + 1)
          rerunTail i s ran unrun $ \rebuilt -> do
            st' <- get
            let doc = take i (stScript st') ++ rebuilt ++ unrun
            loadScriptAt st' { stScript = doc } (i - 1) (stScriptDraft st')

-- | **Discard the line under the caret and everything after it**, no
-- replacement run. Reached by @:script drop@ in the command bar; a no-op
-- with the caret on the composing line, where there is nothing committed
-- to drop.
--
-- **This was forward-delete until 2026-10-20 and that was wrong** — his
-- report: *"I put the cursor at the beginning and I do delete, it deletes
-- the entire line. That's not right."* It was worse than it looked: the
-- key discarded the caret's line *and the whole tail of the script*, with
-- no confirmation and nothing to undo it, on a keystroke whose meaning
-- everywhere else is "remove one character". Del is an ordinary editor key
-- here again, like every other text key in the mode.
--
-- **Whether dropping a line should truncate or splice is his to rule**, and
-- is in `.claude/CLOSEOUT.md` as `~c9rj9`; this keeps the semantics the
-- gesture already had and only moves it somewhere it cannot be hit by
-- accident.
scriptTruncate :: EventM Name St ()
scriptTruncate = do
  st <- get
  case stScriptPos st of
    Nothing -> pure ()
    Just i -> do
      put st
        { stScript = take i (stScript st)
        , stScriptPos = Nothing
        , stInput = E.editorText Input (Just 1) (Text.pack (stScriptDraft st))
        , stScriptDraft = ""
        , stScriptNote = Nothing
        }
      afterScriptEdit

-- | **Walking away from a line you have edited runs it, and everything below
-- it, exactly as Enter would** — `~htff2`, his ruling of 2026-11-18, which
-- superseded his own requirement of an hour earlier that the edit be left
-- standing and dim. His reasoning, and it is about what the two gestures are
-- for rather than about what they do to the document: /"enter is only the
-- natural thing to do if I am ok with ending up (my caret) on the next line.
-- If I want to go above and make changes there, enter is not really something
-- that makes sense."/ **So Enter and a move are the same commit with two
-- different destinations**, and an edit is never left behind unrun by walking
-- off it.
--
-- **It runs through 'foldRun' from the session above line @i@, the same rewind
-- 'scriptSubmit' does**, so a tail line that no longer works keeps its place
-- and its complaint and the rest carry on from whatever session it handed
-- back. The caret then goes where the arrow asked, which is the whole
-- difference from Enter.
--
-- **A line edited to nothing is left alone here on purpose.** Emptying a line
-- and committing it removes it ('scriptSubmit'), and backing out of an emptied
-- line removes it too (@~282h8@) — a third gesture that removed one would be
-- answering @~c9rj9@, his open question of whether dropping a line truncates
-- or splices, by attrition. So a blank edit walked away from stays blank and
-- unrun, and the two gestures that do mean /delete this line/ still mean it.
--
-- **A line that has never run is not edited in this sense and is not run
-- here**: @slRan@ is 'Nothing' for a line of an opened proof-script, there is
-- no session under it to re-run from, and @~22qjj@'s Down is what reaches it.
-- | **@after@ is what the caller wants once the document is settled** —
-- `~twdbp`. There was nothing to re-run: it happens at once, inline, exactly
-- as every caller always assumed. There was: it is chained onto the re-run's
-- own 'rrFinish' instead, because 'scriptDown' in particular reads
-- 'scriptFrontier' to decide its own next move, and that number is wrong
-- until the batch 'rerunTail' just started has an answer. Running @after@
-- early here is what used to race the background thread to the same splice.
runTheEdit :: EventM Name St () -> EventM Name St ()
runTheEdit after = do
  st <- get
  case stScriptPos st of
    Just i
      | Just sl <- nthOf i (stScript st)
      , staleLine sl
      , not (all isSpace (slText sl))
      , Just s <- scriptSessionBefore st i -> do
          let (ran, unrun) = tailFrom st (i + 1)
          commitTailFrom i s (slText sl) ran unrun $ \rebuilt -> do
            st' <- get
            put st' { stScript = take i (stScript st') <> rebuilt <> unrun }
            after
    _ -> after

-- | Up/Down walk the caret through the document. Up from the composing line
-- saves it into 'stScriptDraft' first; Down past the newest line restores it.
-- Stops at line 0, no wraparound, same as the history feature.
--
-- **An edit under the caret is run before the move** ('runTheEdit').
scriptUp :: EventM Name St ()
scriptUp = runTheEdit $ do
  st <- get
  let n = length (stScript st)
      live = concatMap Text.unpack (getEditContents (stInput st))
  case stScriptPos st of
    _ | n == 0 -> pure ()
    Nothing -> loadScriptAt st (n - 1) live
    Just i | i > 0 -> loadScriptAt st (i - 1) (stScriptDraft st)
    _ -> pure ()

-- | **Down is also how a line that has never run gets run** — his design,
-- @~22qjj@: a proof-script opened from disc is text until the arrow keys
-- walk into it, one line per keypress, and the engine's record grows to
-- exactly the caret and no further.
--
-- So Down means one of three things, in this order: move to the next line
-- that has already run; otherwise run the first line that has not; otherwise
-- there is nothing below and the caret leaves the document for the composing
-- line, as it always did.
--
-- **The caret standing on the frontier is what makes it one rule rather than
-- two.** Walking down a 500-line script and walking down a three-line one you
-- typed are the same keypress — in the second, every line has run, so the
-- first clause answers every time.
scriptDown :: EventM Name St ()
scriptDown = runTheEdit $ do
  st <- get
  let n = length (stScript st)
      f = scriptFrontier st
  case stScriptPos st of
    Nothing -> pure ()
    Just i
      | i + 1 < f -> loadScriptAt st (i + 1) (stScriptDraft st)
      | f < n -> runNextScriptLine st f
      | otherwise -> do
          put st
            { stScriptPos = Nothing
            , stInput = E.editorText Input (Just 1) (Text.pack (stScriptDraft st))
            , stScriptDraft = ""
            }
          afterScriptEdit

-- | Run the document's line @at@ — which has not run in this session — from
-- the session above it, and leave the caret on it. **One line, not a loop**:
-- a refusal stops the walk where it happened, with the complaint under the
-- line and the caret on it, which is the whole of the error handling this
-- needs.
runNextScriptLine :: St -> Int -> EventM Name St ()
runNextScriptLine st at = case (scriptSessionBefore st at, nthOf at (stScript st)) of
  (Just s, Just sl) -> do
    ran <- liftIO (runScriptLine s (slText sl))
    put st
      { stScript = take at (stScript st) ++ [ran] ++ drop (at + 1) (stScript st)
      , stScriptPos = Just at
      , stInput = E.editorText Input (Just 1) (Text.pack (slText ran))
      , stScriptNote = Nothing
      }
    afterScriptEdit
  _ -> pure ()

-- | Puts line @i@'s own text under the caret for editing in place.
loadScriptAt :: St -> Int -> String -> EventM Name St ()
loadScriptAt st i draft = case nthOf i (stScript st) of
  Nothing -> pure ()
  Just sl -> do
    put st
      { stScriptPos = Just i
      , stInput = E.editorText Input (Just 1) (Text.pack (slText sl))
      , stScriptDraft = draft
      , stScriptNote = Nothing
      }
    afterScriptEdit

-- | The command bar, summoned. One line, its own editor, and the only place
-- in script mode where a command can be typed.
-- | **The bar takes the keyboard, so it takes the dropdown's reason to be
-- open with it** — his report, 2026-10-20: *"doesn't make sense to have a
-- dropdown somewhere where it is not actively being written to."* Once the
-- bar is up, 'handleBarEvent' owns every key and the document's line cannot
-- change, so a completion box hanging off it is offering to complete a line
-- nothing can type into.
openScriptBar :: EventM Name St ()
openScriptBar = do
  closeDropdowns
  st <- get
  put st { stScriptBar = Just (E.editorText ScriptBar (Just 1) Text.empty), stScriptNote = Nothing }

closeScriptBar :: EventM Name St ()
closeScriptBar = do
  st <- get
  put st { stScriptBar = Nothing }

-- | Enter in the bar. A TUI-local command does its job and vanishes;
-- **anything else is a script line and is inserted at the caret** — his own
-- call, and the reason the bar is not merely a command line: with in-place
-- editing alone a line can be replaced or truncated but never added in the
-- middle.
scriptBarSubmit :: St -> String -> EventM Name St ()
scriptBarSubmit st text = case words text of
  [] -> closeScriptBar
  [":script"] -> leaveScriptMode
  [":script", "drop"] -> closeScriptBar >> scriptTruncate
  -- | **`cut`, not `rerun` — his rename, 2026-11-11.** The word is retired
  -- rather than reassigned: once plain Enter re-runs the tail (@~bxmsc@),
  -- `rerun` would name the one gesture that re-runs nothing.
  [":script", "cut"] -> closeScriptBar >> scriptCutAndRun
  (":script" : "save" : rest) -> scriptSave st (pathArg rest) False
  -- | **`save!` replaces, `save` asks** — his ruling of 2026-11-11
  -- (@~kqfbp@). The bang is only ever needed for a path the document was
  -- not opened from, because save-back never asks.
  (":script" : "save!" : rest) -> scriptSave st (pathArg rest) True
  [":script", "reload"] -> closeScriptBar >> scriptReload
  -- | **The session picker, reachable from inside the mode** — see the repl's
  -- own branch for why this did not exist before there was a dialog to open.
  -- The bar closes first: the picker owns the keyboard, and two things that
  -- both own it is the bug `~sfs2n` is about.
  [":script", "sessions"] -> openSessionPicker st { stScriptBar = Nothing }
  -- | **The rest of the line is the path** — `~td887`, the same rule the
  -- REPL's own `:script ‹path›` takes. Matching one word meant
  -- @:script open /a path/with a space.thena.script@ fell through to
  -- 'insertScriptLine' and was written into the document as a line, which
  -- then failed as an engine line.
  (":script" : "open" : rest@(_ : _)) -> do
    let path = unwords rest
    ok <- openScriptFile st path 0
    if ok
      then pure ()
      else put st { stScriptBar = Nothing, stScriptNote = Just ("no such file: " <> path) }
  -- | **Every other TUI-local word, `:quit` and `:clear` included, now
  -- reads off 'scriptLocal' — the same function the document itself checks**
  -- (`~fxc89`, `~p6g53`, `~kmprv`'s and 2026-11-18's quit work), so the bar
  -- and a typed line cannot answer one of these words two different ways.
  _ | Just action <- scriptLocal st text -> do
        said <- action
        st' <- get
        put st' { stScriptBar = Nothing, stScriptNote = Just said }
  _ -> insertScriptLine st text

-- | **One path argument, spaces and all, or none** — `~td887`. A save took
-- 'listToMaybe' of the words, so @:script save /a path/with a space@ wrote to
-- @\/a@ and said so: the wrong file, named in the confirmation, which is the
-- worst of the three doors this bug had.
pathArg :: [String] -> Maybe FilePath
pathArg [] = Nothing
pathArg ws = Just (unwords ws)

-- | A line typed in the bar goes into the document below the caret, and the
-- tail re-runs behind it — the same rebuild an edit takes, so the two cannot
-- drift apart.
insertScriptLine :: St -> String -> EventM Name St ()
insertScriptLine st text = do
  let at = maybe (length (stScript st)) (+ 1) (stScriptPos st)
  case scriptSessionBefore st at of
    Nothing -> put st { stScriptBar = Nothing }
    Just s -> do
      let (ran, unrun) = tailFrom st at
      put st { stScriptBar = Nothing }
      rerunTail at s (text : ran) unrun $ \rebuilt -> do
        st' <- get
        put (reseated st' at (take at (stScript st') ++ rebuilt ++ unrun)) { stScriptBar = Nothing }
        afterScriptEdit

-- | `:script save [name]` — writes the document's lines and nothing else.
-- **No modal.** His spec wanted one because there was nowhere to type a
-- filename; the command bar is that place, so the modal is a widget the
-- design no longer needs.
--
-- **Save means save — his ruling, 2026-11-11, which is `~kqfbp`.** With no
-- name the document goes back to the file it was opened from, silently and
-- with no confirmation, the way Cmd+S does everywhere else: *"Do you see
-- editors preventing saving a file for whatever stupid reason?"* Opening
-- keeps every line of the file, blanks and comments included, so a save-back
-- is the file as it was written plus the edit.
--
-- **The one case that is not that is Save-As onto something else.** Typing a
-- path the document did not come from, which already exists, means the lines
-- about to be written are not that file's lines — so it asks once, and
-- `:script save!` is the answer. That is the whole of what the old refusal
-- was protecting: before a proof-script could be opened (@~22qjj@), *every*
-- existing path was somebody else's content, which is why the guard read as a
-- blanket refusal and had to go rather than be tuned.
--
-- With no name and nothing to save back to — a document typed from scratch —
-- the name is the clock in words: @Wednesday-11-11-2026-at-22-15.thena.script@,
-- which is 'clockName'. It is not the session's slug: see that function for
-- why a thing you read and a thing you type a prefix of differ.
scriptSave :: St -> Maybe String -> Bool -> EventM Name St ()
scriptSave st given force
  | null (stScript st) = say "nothing to save"
  | otherwise = do
      path <- liftIO $ case (given, openedFrom) of
        (Just n, _) -> pure (suffixed n)
        (Nothing, Just p) -> pure (suffixed p)
        (Nothing, Nothing) -> freeClockPath
      -- **Where the document came from is never an overwrite.** It is the
      -- same file, and asking about it is the behaviour he threw out. An
      -- invented name is never one either, because 'freeClockPath' only ever
      -- answers a path that is free.
      ask <- if force || Just path == fmap suffixed openedFrom
        then pure False
        else liftIO (doesFileExist path)
      if ask
        then say (path <> " exists — :script save! " <> path <> " to replace")
        else do
          liftIO (writeFile path (unlines (map slText (stScript st))))
          -- **A save tags the session with the name it was saved under —
          -- his ruling of 2026-11-18 (`~73f2k`).** Before this, a
          -- typed-then-saved session showed only a bare clock-date in
          -- `:script sessions`, because nothing connected the file now on
          -- disc back to the index entry `persist` already writes on every
          -- committed line. 'persist' re-reads the state itself, so the
          -- stale @st@ captured above is abandoned the moment it has run.
          case stStored st of
            Just stored | stFrom stored /= Just path ->
              put st { stStored = Just stored { stFrom = Just path } } >> persist
            _ -> pure ()
          after <- get
          put after { stScriptBar = Nothing, stScriptNote = Just ("saved " <> path) }
  where
    openedFrom = stStored st >>= stFrom
    say note = put st { stScriptBar = Nothing, stScriptNote = Just note }

suffixed :: String -> FilePath
suffixed n = if ".thena.script" `isSuffixOf` n then n else n <> ".thena.script"

-- | **The name a save invents: 'clockName', stepped until it is free.**
-- @Wednesday-11-11-2026-at-22-15.thena.script@, and @…-at-22-15-2.thena.script@
-- if that one is already there — two saves in one minute is a thing that
-- happens, and 'freshStored' steps a slug the same way. **Nothing it answers
-- exists yet**, which is why an invented name never asks before writing.
freeClockPath :: IO FilePath
freeClockPath = do
  stem <- clockName
  let tries = stem : [stem <> "-" <> show n | n <- [2 .. 99 :: Int]]
      -- A hundred saves in one minute is not a state to have a plan for, and
      -- overwriting the first is better than refusing to save — the same
      -- call 'freshStored' makes about a slug.
      go [] = pure (suffixed stem)
      go (t : rest) = do
        there <- doesFileExist (suffixed t)
        if there then go rest else pure (suffixed t)
  go tries

-- | The slice of 'St' that 'Tui.Config' persists, read off whichever state the
-- command or the gesture just produced.
--
-- **The layout and the widths are in it as of `~vqsd8`** — his ruling of
-- 2026-11-13, the dotfile, with `~fxc89`'s positions taking the same answer
-- because they were put to him as one question.
--
-- **Only a pane whose width differs from the terminal's own default is
-- written.** 'stPaneWidths' is total over 'allPanes' — 'appStart' fills it from
-- 'defaultPaneWidth' — so writing it whole would turn "I have never touched a
-- pane" into six absolute numbers from whatever terminal happened to start the
-- TUI first, and the next narrower terminal would read them back as choices he
-- had made. **Filtering here is what keeps an untouched pane reading its width
-- off the window**, which is the behaviour the second-terminal objection to the
-- dotfile was about.
configOf :: St -> Config
configOf st = Config
  { cfgTheme      = themeName (stTheme st)
  , cfgAutoSelect = stAutoSelect st
  , cfgWhisperOn  = stWhisperOn st
  , cfgConfirmQuit = stConfirmQuit st
  , cfgLayout     = stLayout st
  , cfgWidths     =
      [ (p, w)
      | (p, w) <- Map.toAscList (stPaneWidths st)
      , Just w /= Map.lookup p (stDefaultWidths st)
      ]
  , cfgStrip      = stStrip st
  , cfgDropdownOn = stDropdownOn st
  , cfgJevOn = stJevOn st
  , cfgModel = Text.unpack (stModel st)
  }

appendTurn :: St -> Maybe String -> [String] -> EventM Name St ()
appendTurn st prompt output = do
  put (submitted st) { stTurns = stTurns st <> [Turn prompt output (stSession st)] }
  followInput
  -- The slate 'submitted' just computed is the new session's, and nothing has
  -- asked Jev about it — `~3gn2r`. Scheduling rather than firing, so a run of
  -- lines (a `:script reload`'s replay) coalesces into one request.
  scheduleJevRanking

-- | **What a submitted line leaves behind, apart from its own turn.**
-- Factored out of 'appendTurn' for `~p6g53`: `:clear` is the one submission
-- that answers with nothing at all, so it cannot go through 'appendTurn' and
-- must still leave the input exactly as every other submitted line does.
-- Sharing the record update is what keeps the two from drifting.
--
-- **The dropdown closes and the slate does not** — `~3gn2r`. Closing the
-- popup on Enter is the popup's own rule; the offers for the empty line in
-- the session the submission just produced are a different fact, and they
-- exist. The slate is recomputed from the state /after/ the input is
-- emptied, so it is the launch slate of the new session and not the slate of
-- the line that was just run.
submitted :: St -> St
submitted st = after { stSlate = slateFor after }
  where after = st { stInput = emptyInput, stDropdown = Nothing, stOfferDropdown = Nothing }

-- | **`:clear ‹n›` — the last @n@ turns off the transcript, and nothing else**
-- (`~p6g53`, his request of 2026-11-13: /"some shortcut removes the latest
-- output + its input combination as in my normal terminal on mac… I can't
-- remove stuff like help easily and it always clutters my entire view
-- forever"/).
--
-- **A turn is exactly his "output + input pair"** — 'Turn' is the prompt
-- line and the output it produced, so the count he gives is a count of turns
-- and needs no interpretation. Note that a few turns have no prompt at all
-- ('turnPrompt' is 'Maybe'): the startup trouble dump and `:theme`/`:fold`
-- never echoed what was typed. Those are still one turn each, which is what
-- he means by the thing on screen he wants gone.
--
-- **IT TAKES THE SESSION BACK WITH THE TURNS — HIS INSTRUCTION, 2026-11-19,
-- AND IT REVERSES WHAT THIS FUNCTION USED TO SAY** (`~hxzjq`): /"ctr + l,
-- when removing a command that change the machine-state\/proof-state, does
-- not revert to a previous snapshot. It should."/ The session restored is
-- 'turnSession' of the turn that is now last, or 'stSession0' with every
-- turn gone.
--
-- **Why the old rule was wrong, in his own terms.** It was argued from
-- @Cmd+L@ in Terminal.app, which clears a log and un-runs nothing — and the
-- argument was that the panes make the shortened log honest, since the proof
-- term and the goals keep saying what the session *is*. **That is exactly
-- what makes it dishonest here**: this transcript is not a log beside a
-- state, it is the only record of how the state was reached, so taking the
-- line out leaves a proof state on screen with nothing on screen that
-- produced it. @:script cut@ was always the other way round and was always
-- the better model: there the document is the record, and cutting moves the
-- session.
--
-- **Over-clearing is clamped and silent** — clearing to a mark that is not
-- there does nothing in a terminal either, and here it lands on the session
-- the TUI launched with.
--
-- **'stHistory' is deliberately untouched.** He wants the clutter gone, not
-- his Up-arrow, and the `:clear` line itself is recorded by 'recordHistory'
-- before dispatch like any other — so `:clear 1` is one Up away from being
-- repeated.
dropTurns :: Int -> St -> St
dropTurns n st = st { stTurns = kept, stSession = back }
  where
    kept = take (max 0 (length (stTurns st) - n)) (stTurns st)
    -- | **The state the screen is left showing** — `~hxzjq`. Each turn
    -- carries the session its own line left behind, so the turn now at the
    -- bottom of the transcript is the one whose session belongs with it.
    back = case reverse kept of
      t : _ -> turnSession t
      []    -> stSession0 st

-- | A count for `:clear`, or 'Nothing' if the word is not one. Non-negative:
-- @:clear 0@ is a legitimate "clear nothing" and is silent, where
-- @:clear -1@ is a typo and should be told so rather than guessed at.
readCount :: String -> Maybe Int
readCount w = case reads w of
  [(n, "")] | n >= 0 -> Just n
  _ -> Nothing

-- | **No turn is appended, which is the whole point.** A `:clear` that
-- answered /cleared 1/ would put a line on screen for every line it took
-- off, and the clutter he is clearing would just change its wording.
-- **'dropTurns' runs first and 'submitted' second** — `~hxzjq`. 'submitted'
-- recomputes the slate from the session in hand, and the session in hand is
-- the one the clear just went back to; the other order offered the cleared
-- session's rules.
clearTurns :: Int -> St -> EventM Name St ()
clearTurns n st = do
  put (submitted (dropTurns n st))
  followInput

-- | **`:clear 1` as a keystroke** — what Ctrl+L and Cmd+L both run, so there
-- is one description of the gesture rather than one per encoding.
--
-- **It does not touch the input.** The clutter is above the line he is
-- typing, and a shortcut that emptied the line to tidy the screen above it
-- would be the worse trade.
--
-- **It guards live-script mode itself** rather than being guarded at each
-- binding. There is no transcript in that mode — the document is the record —
-- and what the gesture would otherwise reach is the repl's turns sitting
-- intact behind the mode ('leaveScriptMode' keeps 'stTurns' on purpose).
-- Deleting those from behind a mode that does not show them is the one
-- outcome worth preventing, and preventing it here means a new binding
-- cannot forget to.
clearOneTurn :: EventM Name St ()
clearOneTurn = do
  st <- get
  if stScriptMode st
    then put st { stScriptNote = Just clearNotHere }
    else do
      put (dropTurns 1 st)
      followInput

-- | The usage line, for an argument that is not a count. **This one does
-- answer**, because it is a mistake and a silent no-op would read as a
-- `:clear` that did not work.
-- | Said in live-script mode's status line, by both doors into it.
clearNotHere :: String
clearNotHere = "nothing to clear here — the document is the record, and :script cut takes a line off"

clearUsage :: [String]
clearUsage =
  [ ":clear ‹n› takes off the last n lines and their output; :clear is :clear 1"
  , "  Ctrl+L is the same as :clear 1"
  ]

-- | Keep the live prompt in view while typing, same reasoning as
-- 'appendTurn' — the prompt is just the last line of the same scrollable
-- document now, not a fixed row, so it can scroll out of view like anything
-- else unless something puts it back.
followInput :: EventM Name St ()
followInput = vScrollToEnd (viewportScroll HistoryVP)

-- | Recomputes the `:load` dropdown from the input's current text —
-- called after anything that can change it (typing, Tab, an accepted
-- dropdown selection). Not called from arrow-key navigation, which changes
-- only 'ldSelected', never the text; recomputing there would immediately
-- overwrite the very selection the arrow key just made.
refreshDropdown :: EventM Name St ()
refreshDropdown = do
  st <- get
  let line = concatMap Text.unpack (getEditContents (stInput st))
  -- Dismissed by Esc ('stDismissed'): stay hidden while the line reads as
  -- it did, come back on any edit. Every path below clears the flag —
  -- reaching one means the line moved.
  if stDismissed st == Just line
    then put st { stDropdown = Nothing }
    else case loadPathPrefix line of
      Nothing -> put st { stDropdown = Nothing, stDismissed = Nothing }
      Just _ -> do
        entries <- liftIO (dropdownRows line)
        -- A shown dropdown always highlights one row (his `.jalivert/TUI.md`
        -- #9): the first, so Enter on a fresh list accepts rather than
        -- submitting the partial line — Esc clears it first when submitting
        -- as typed is what is wanted. Above the line the reversal below puts
        -- that same first row adjacent to the input. **Unless `:preselect
        -- off`** (`.jalivert/TUI.md` #23) — same toggle 'buildOfferDropdown'
        -- reads, so the two dropdowns cannot disagree about it.
        let initialSel = if stAutoSelect st then Just 0 else Nothing
            new = if null entries then Nothing else Just (LoadDropdown entries initialSel)
            oldRows = maybe [] ldEntries (stDropdown st)
        put st { stDropdown = new, stDismissed = Nothing }
        -- A new row generation scrolls from the top: the viewport offset
        -- belongs to the rows it was showing, and a rebuilt-shorter list
        -- viewed from a deep offset is all blank (his empty-dropdown bug).
        -- Identical rows keep their offset — a cursor move or a no-op edit
        -- must not yank a deliberately scrolled list. Above the line the
        -- fresh end is the bottom, where the reversed rows start — for a
        -- viewport that has rendered before; a never-opened one still opens
        -- at offset 0, and the preselected row's 'visible' pulls it right.
        if maybe [] ldEntries new /= oldRows
          then (if popupAbove st then vScrollToEnd else vScrollToBeginning) (viewportScroll LoadPopup)
          else pure ()

-- | Recomputes the completion dropdown from 'Thena.View.statementOfferView'
-- — called from the same places 'refreshDropdown' is, same reasoning.
--
-- **Only a path-taking command's own line gets none from here**
-- ('pathCommands') — its path is a directory listing, not a grammar
-- question, and 'refreshDropdown' already owns that answer ('stDropdown');
-- asking the statement grammar about ":load foo" too would just be asking
-- the wrong question a second time.
-- Every other colon line, including a bare ":" or one still being typed
-- towards ":load" itself, goes to 'statementOfferView' exactly like a
-- non-colon line now does. **This used to blank on any colon prefix
-- at all** — right when written (2026-09-29), because `:`-command
-- completion didn't exist engine-side yet. MS7 phase 142 (`9c9112a`,
-- `.jalivert/NOTES.md` 2026-09-30) answers it now, through the same
-- 'statementOfferView' call, no new one — the guard here just never
-- caught up to ask.
--
-- **The strip's slate is recomputed on every branch, including the two that
-- blank the dropdown** — `~3gn2r`. A dismissal and a `:load` line are about
-- the popup and about this grammar's relevance respectively; neither is the
-- engine withdrawing an offer, and only the second of the two leaves the
-- strip with nothing ('slateFor' answers 'emptySlate' there for the same
-- reason the dropdown declines).
refreshOfferDropdown :: EventM Name St ()
refreshOfferDropdown = do
  st0 <- get
  let line = concatMap Text.unpack (getEditContents (stInput st0))
      (_, col) = getCursorPosition (stInput st0)
      (before, after) = splitWritten line col
      -- **One view, read two ways** — `~3gn2r`. A `:load` path line asks
      -- nothing of the statement grammar (see 'slateFor'), so 'Nothing' here
      -- is both /no dropdown/ and /an empty slate/.
      offered
        | isJust (loadPathPrefix line) = Nothing
        | otherwise = Just (statementOfferView (activeSession st0) before after)
      new = offered >>= buildOfferDropdown (stAutoSelect st0) col
      slate = slateOfDropdown new
      oldSlateRows = slateRows (stSlate st0)
      st = st0 { stSlate = slate }
  -- Same dismissal as 'refreshDropdown': hidden while the line is as Esc
  -- left it, back on any edit. **The slate is already in 'st' and survives
  -- it** — `~3gn2r`: Esc is about the popup, not about what is offered.
  if stDismissed st == Just line
    then put st { stOfferDropdown = Nothing }
    else case offered of
      Nothing -> put st { stOfferDropdown = Nothing, stDismissed = Nothing, stRecoveredSpan = Nothing, stArrowsReleased = False }
      Just ov -> do
        let oldRows = maybe [] odRows (stOfferDropdown st)
        put st { stOfferDropdown = new, stDismissed = Nothing, stRecoveredSpan = underlineSpan ov, stArrowsReleased = False }
        -- Same rule as 'refreshDropdown': new rows start at the top, same
        -- rows keep their scroll — above the line, at the bottom instead.
        if maybe [] odRows new /= oldRows
          then (if popupAbove st then vScrollToEnd else vScrollToBeginning) (viewportScroll OfferPopup)
          else pure ()
  -- Score the slate, not every keystroke: only when the candidate set
  -- actually changed, and then on a trailing-edge timer rather than on the
  -- keystroke itself ('scheduleJevRanking'). The set comparison sorts both
  -- sides first: 'applyJevRanking' floats Jev's picks to the top, so an
  -- order-sensitive check would see a change after every answer landed and
  -- refire on the next keystroke even when the set is the same.
  --
  -- **Off the slate and outside the branches** — `~3gn2r`. It was inside the
  -- else, so a dismissed dropdown was never re-ranked; the strip is on screen
  -- in that frame now, and what is on screen is what Jev is asked about.
  when (sortOn sortKey (slateRows slate) /= sortOn sortKey oldSlateRows) scheduleJevRanking
  where
    sortKey r = (rowLabel r, rowInsert r)

-- | **How long a burst of keystrokes may run before Jev is asked** — 250ms
-- of quiet. Measured against @~/.cache/thena/jev.log@: typing and
-- backspacing arrive 100–150ms apart, so per-keystroke firing turned a
-- 20-character delete into 20 concurrent @:matches@ + HTTP rounds. 250ms
-- coalesces one burst into one request, stays well under the 1.5s ranking
-- timeout ('Tui.Jev.rankCandidates'), and keeps the green picks feeling
-- live. His instinct in @.jalivert/discussion/live-offers.md@ was 200ms;
-- this is that number rounded up to comfortably clear typing speed.
jevDebounceMicros :: Int
jevDebounceMicros = 250000

-- | **Schedule a ranking for the dropdown on screen, once it has sat still.**
-- Bumps 'stJevPending' and hands a timer a generation to report back with;
-- 'handleJevDue' drops every generation but the latest, so holding
-- Backspace schedules N timers and fires one request. The timer thread
-- sleeps and writes — no @:matches@, no HTTP — so a burst costs N sleeps
-- rather than N ranking rounds. The selectable-count policy stays in
-- 'fireJevForCurrentDropdown', which runs at fire time against the
-- dropdown as it then stands, not at schedule time.
scheduleJevRanking :: EventM Name St ()
scheduleJevRanking = do
  st <- get
  -- | **`:jev off` sends nothing** — `~zttnz`. Stopping here rather than at
  -- the request is deliberate: nothing is timed, nothing wakes up, and
  -- nothing of his quota is spent.
  when (stJevOn st) $ do
    let pending = stJevPending st + 1
        chan = stJevChan st
    put st { stJevPending = pending }
    liftIO (void (forkIO (threadDelay jevDebounceMicros >> writeBChan chan (JevDue pending))))

-- | **A debounce timer coming due.** A generation that no longer matches
-- 'stJevPending' was superseded by a later keystroke while it slept and is
-- dropped silently — there is nothing to log, no request went out. The
-- latest generation fires against whatever is on screen now.
handleJevDue :: Int -> EventM Name St ()
handleJevDue gen = do
  st <- get
  when (gen == stJevPending st) fireJevForCurrentOffers

-- | Fires a ranking request for the offers on screen right now, if there's
-- a key and more than one candidate to order.
--
-- **Also called once, unconditionally, straight after startup** (the
-- post-launch 'Tick') — the launch dropdown (his `.jalivert/TUI.md` #14:
-- the empty line opens with the full rule list already showing) is built
-- directly in 'runTui', never through 'refreshOfferDropdown', so without
-- this call Jev never saw it at all. That gap is exactly his report,
-- 2026-10-29: *"I just opened it, dropdown is shown... not a single one
-- is green"* — not a scoring bug, a dropdown Jev was never asked about.
--
-- **It asks 'stSlate' and not 'stOfferDropdown'** — `~3gn2r`. The slate is
-- what the strip draws and is still there after an Enter and after Esc, both
-- of which used to log /no dropdown on screen/ and leave the ranking stale.
--
-- **Nothing is sent when neither element is up**: the strip closed and the
-- dropdown off or dismissed means the answer would reorder a list nobody is
-- looking at, and a request costs a @:matches@ and a round trip.
fireJevForCurrentOffers :: EventM Name St ()
fireJevForCurrentOffers = do
  st <- get
  let line = concatMap Text.unpack (getEditContents (stInput st))
      (_, col) = getCursorPosition (stInput st)
      offered = slateRows (stSlate st)
      onScreen = stripOpen (stStrip st) || isJust (liveOffers st)
  case stJevConfig st of
    -- **`~n7vfq` — `:jev off` has to be checked HERE as well as in
    -- 'scheduleJevRanking', and that it was not is a defect `~zttnz`
    -- promised against** — /"off sends nothing at all"/, /"nothing of his
    -- quota is spent"/. This function is also called once unconditionally
    -- from the post-launch 'Tick' (see below), which is not a scheduled
    -- request and so never passed the switch: measured 2026-11-19 under a
    -- pty with @jev=off@ in the dotfile, one @request: 255 candidates@ went
    -- out on launch regardless.
    _ | not (stJevOn st) -> liftIO (jevLog "skip: :jev off")
    Nothing -> liftIO (jevLog "skip: no key loaded")
    Just jcfg
      | not onScreen -> liftIO (jevLog "skip: neither the strip nor the dropdown is on screen")
      | length offered >= 2 ->
        fireJevRanking jcfg (activeSession st) (Text.pack (take col line)) offered
      | otherwise -> liftIO (jevLog ("skip: only " <> show (length offered) <> " candidate(s) offered"))

-- | Sends one ranking request to Jev in the background and returns
-- immediately — nothing here ever blocks a keystroke on the network.
-- Bumps 'stJevGen' so a slower, earlier request can't land after a
-- faster, later one and put a stale order back on screen
-- ('applyJevRanking' checks the generation it comes back with).
--
-- **The 'Session' is carried in rather than the finished request, so that
-- 'jevRequest' runs inside the 'forkIO' and not on the keystroke.** It reads
-- the development and runs @:matches@, neither of which a frontend should pay
-- for between a key going down and the screen being redrawn. A 'Session' is
-- immutable and every call 'jevRequest' makes of it is pure, so handing one to
-- another thread is not sharing mutable state — it is passing a value.
fireJevRanking :: JevConfig -> Session -> Text -> [OfferRow] -> EventM Name St ()
fireJevRanking jcfg s typedSoFar offered = do
  st <- get
  let gen = stJevGen st + 1
      chan = stJevChan st
  put st { stJevGen = gen }
  liftIO $ do
    _ <- forkIO $ do
      -- | **Nothing this thread does may escape it**, which is the module
      -- contract 'Tui.Jev' states — /"a missing key, a failed call, or a
      -- timeout all mean exactly the same thing to the caller: no scores"/.
      -- 'rankCandidates' already wraps its own request, but `~d4qvm` moved
      -- real work in front of it: 'jevRequest' is forced here rather than on
      -- the keystroke, so whatever it forces is now this thread's to contain.
      -- An unhandled exception in a 'forkIO' prints to stderr, and stderr
      -- under brick is the screen.
      outcome <-
        try
          ( let (situation, candidates) = jevRequest s typedSoFar offered
             in rankCandidates jcfg situation candidates
          )
      result <- case outcome of
        Left (e :: SomeException) -> do
          jevLog ("answer: FAILED before the request went out — " <> show e)
          pure (Left (show e))
        Right r -> pure r
      writeBChan chan (JevRanked gen result)
    pure ()

-- | **What Jev is told, and it is the whole of `~d4qvm`'s fix.** HIS
-- instruction, 2026-11-13: /"Jev needs to be given enough information to make
-- an informed choice."/
--
-- What it replaced was one field — the characters typed so far. On an empty
-- line that is the empty string, so @:theorem@, then @attack@, then @intro@ put
-- a byte-for-byte identical question to Jev three times, and his report is the
-- only answer such a request can give: /"it just tells me the same three things
-- again."/
--
-- **The state and the candidates are built together because they share the
-- expensive part.** @:matches@ is run once; its text goes out as
-- @applies_here@, and the rule names in it are what marks a candidate as
-- applying here. Marking the candidate itself matters as much as the list
-- does: a 'Choice' scores criteria, so a note on the criterion is read where
-- the decision is made rather than cross-referenced out of a separate field.
--
-- **@:matches@ is a look and the driver says so** — /"no body runs, and
-- nothing is speculatively executed"/ ('Thena.Driver.Matched') — so running it
-- for context cannot move the session. The returned 'Session' is dropped on
-- purpose, and is not the same thing as discarding a write.
jevRequest :: Session -> Text -> [OfferRow] -> (JevState, [(Text, Text)])
jevRequest s typedSoFar offered = (JevState fields, candidates)
  where
    -- The same 'Budget' every pane is drawn with, so that what Jev reads and
    -- what is on screen are elided at the same place.
    budget = Budget 200
    links = developmentView budget s

    fields =
      (Text.pack "typed_so_far", typedSoFar)
        : [ (Text.pack k, Text.pack v)
          | (k, v) <-
              [ ("proving", proving)
              , ("open_goals", unlines' (goalTexts links))
              , ("proof_term", unlines' (developmentText links))
              , ("applies_here", unlines' (take matchesSent applying))
              ]
          , not (null v)
          ]

    -- | **A field with nothing in it is left out, not sent empty.** "No proof
    -- is open" and "a proof is open and its goal is the empty string" are
    -- different situations, and an empty string is how the second one would
    -- read.
    unlines' = intercalate "\n"

    proving = case proofsViewOn (proofsView budget s) of
      Just (QuestView word (AStatement st')) -> word <> " : " <> displayText st'
      -- An import standing in a @yield@ is not a theorem and has no statement
      -- to show ('Thena.View.Proofs.AnImportStanding' exists to say exactly
      -- that), so what is sent is what the session is on, in words.
      Just (QuestView word (AnImportStanding _)) ->
        "nothing — the session is on the import " <> word <> ", standing in a yield"
      Nothing -> ""

    -- | @:matches@, rendered. The driver's own order is kept — nearest first,
    -- dispatch order — because that is the only ranking in it.
    applying = case oneLine s ":matches" of
      (s', resp) -> renderResponse s' resp

    -- | **The rule's own name is the first word of its match line**, the rest
    -- being its head's pattern (@claim ‹ty›@, @one-case ‹t› ‹c› ‹sub› ‹bs›
    -- ‹fs›@). Taken from the *whole* list and not from the truncated text, so
    -- the cap below never un-marks a candidate that does apply.
    applyingNames = Set.fromList (map (takeWhile (not . isSpace)) applying)

    -- | **A label is a word to type or a production's @name: shape@**
    -- ('offerRow', 'productionRow'), and the boundary knows nothing further
    -- about either — so the description a criterion carries is the one thing
    -- that is ours to add: whether this candidate applies where the cursor
    -- stands. Before `~d4qvm` it was the label repeated, which is the field
    -- the API reads prose from, carrying none.
    candidates =
      [ ( Text.pack (rowLabel r)
        , Text.pack
            ( rowLabel r
                <> if takeWhile (not . isSpace) (rowLabel r) `Set.member` applyingNames
                  then " (applies at the current focus)"
                  else ""
            )
        )
      | r <- offered
      ]

-- | **How much of @:matches@ goes out.** Measured 2026-11-13 against
-- @exe:thena@: 110 lines with no proof open, 81 after @:theorem@ + @attack@ +
-- @intro@. **The length is a signal question and not a cost one** — 50 calls
-- after those three steps took 0.417s against 0.140s for the same run without
-- them, so ~5.5ms each, rendering included, and it is paid on the 'forkIO'
-- rather than on a keystroke anyway. The list is in dispatch order, so its
-- head is the tactics (@intro@, @solve@, @regret@, @prove@, @claim ‹ty›@,
-- @assume ‹ty›@, @quantify ‹ty›@) and its tail is helper rules whose heads are
-- irrefutable and pass everywhere.
--
-- **40 is a judgement and is not measured.** What it is weighed against is
-- answer quality with a key in the environment, which this track cannot test
-- without one; `~d4qvm` records that. 'applyingNames' is deliberately computed
-- before the cap, so being past it costs a candidate its text in the state
-- field and never its mark.
matchesSent :: Int
matchesSent = 40

-- | **What the model is told** — `~w2tk2` slice 6, and the six fields are
-- HIS list, 2026-11-19: /"it has to be told the proof term, it has to be
-- told what's in scope and this and that … It also has to know what is
-- already executed (in either modes, repl and script) and what is on my
-- current line."/
--
-- **Four of the six were already going to Jev and two were not.** @goals@,
-- @proof_term@, @applies_here@ and @typed_so_far@ are `~d4qvm`'s payload;
-- **@in_scope@ and @executed@ are new here**, and @executed@ is the one his
-- sentence turned on — without it the model cannot see how he arrived at
-- the state it is looking at.
--
-- **@executed@ comes from whichever mode he is in**, which is why this takes
-- an 'St' where 'jevRequest' takes only a 'Session': the repl's history is
-- 'stTurns' and the document's is 'stScript' down to 'scriptFrontier', and
-- neither is reachable from the engine — a 'Session' holds state, not a
-- narrative of how it was reached.
--
-- **A field with nothing in it is left out rather than sent empty**, the
-- rule 'jevRequest' already follows: "no proof is open" and "a proof is open
-- whose goal is the empty string" are different situations.
hintFields :: St -> [(Text, Text)]
hintFields st =
  [ (Text.pack k, Text.pack v)
  | (k, v) <-
      [ ("goals", unlines' (goalTexts links))
      , ("proof_term", unlines' (developmentText links))
      , ("applies_here", unlines' (take matchesSent applying))
      , ("in_scope", unlines' scopeLines)
      , ("executed", unlines' executed)
      , ("typed_so_far", typedSoFar)
      -- | **How much room the answer has, in his own terms** — HIS,
      -- 2026-11-19: /"the AI needs to always cap its response to 5 lines at
      -- most. That is always a little bit different. So perhaps that should
      -- be part of the prompt — telling it how many words/characters it
      -- has."/
      --
      -- **Measured off the live geometry rather than fixed at five.** The
      -- region's height is a function of how tall he has pulled the pane
      -- ('stripHintBudget') and its width is the pane's own, so the number
      -- he would count on screen is the number that goes out — a constant
      -- would be wrong the moment he drags the accent bar.
      , ("room", room)
      , ("vocabulary", vocabulary)
      , ("tactics", tactics)
      ]
  , not (null v)
  ]
  where
    s = activeSession st
    budget = Budget 200
    links = developmentView budget s
    unlines' = intercalate "\n"

    applying = case oneLine s ":matches" of
      (s', resp) -> renderResponse s' resp

    -- | **Namespace by namespace, the way the globals pane groups them** —
    -- one flat list of every exported name would be the same information
    -- with the module it came from thrown away, and which module a name is
    -- from is most of what makes it usable in a suggestion.
    scopeLines =
      [ group <> ": " <> intercalate ", " names
      | (group, names) <- globalGroups st
      , not (null names)
      ]

    -- | **The lines he has run, oldest first, in whichever mode he is in.**
    -- In the document it is the prefix that has actually run
    -- ('scriptFrontier') and not everything on screen: a line below the
    -- frontier is text he has typed and not yet executed, and calling that
    -- /executed/ would be a lie about the state the rest of the payload
    -- describes.
    executed
      | stScriptMode st = [slText l | l <- take (scriptFrontier st) (stScript st)]
      | otherwise = [prompt | Turn (Just prompt) _ _ <- stTurns st]

    typedSoFar = take col (concatMap Text.unpack (getEditContents (stInput st)))
    (_, col) = getCursorPosition (stInput st)

    -- | **The width is the one the last frame reported** — 'stStripWidth',
    -- the same one the F-key cap reads and one frame old for the reason
    -- `~ptg78` records. A frame's lag in a character count is not a defect;
    -- it is the same number he is looking at.
    room = case stStripWidth st of
      Nothing -> ""
      Just w ->
        show maxLines <> " lines of " <> show w <> " characters, so "
          <> show (maxLines * w) <> " characters at the very most"
      where
        maxLines = stripHintBudget (stripBodyRows (stripRows (stStrip st)))

    -- | **The engine's own list, not a copy of it** —
    -- 'Thena.Driver.commandSummary' is what `:help` prints, so the one part
    -- of the brief that could drift out of step with the engine cannot. His
    -- ask was for /"some short brief"/; the mechanics half of that is in the
    -- prompt file he owns, and this half is generated.
    vocabulary = unlines' [word <> "   " <> gloss | (word, gloss) <- commandSummary]

    -- | **`:rules`, and WITHOUT IT THE MODEL CANNOT KNOW THE TACTICS AT
    -- ALL** — his ask of 2026-11-19 for /"complete information about all
    -- the commands in our system"/, so that /"what if I want to do intro
    -- but specify the name of the argument?"/ has an answer.
    --
    -- **`commandSummary` does not cover them and that is not an omission in
    -- it**: @attack@, @intro@, @fill@, @solve@, @try-core@ and @prove@ are
    -- ordinary instral rules in a rule base, not words the engine knows, so
    -- the engine's own command list has no business listing them. The two
    -- fields are the two halves of the vocabulary and neither contains the
    -- other.
    --
    -- **Read through `:rules` rather than off @rules\/standard.thena.rules@**,
    -- which is the same discipline `applies_here` follows: a base he has
    -- @consult@ed this session is in the answer, and the shipped file would
    -- have been a guess about what is loaded. **It is each rule's head with
    -- its argument shape** — @intro@ against @fill ‹t›@ — which is exactly
    -- the arity question he asked.
    tactics = unlines' (case oneLine s ":rules" of (s', resp) -> renderResponse s' resp)

-- | **One ask, caused by his Enter on the reply row and by nothing else** —
-- `~w2tk2` slice 6. HIS ruling, 2026-11-19: /"We have no autohint …
-- Everything is explicit … The user has to hit enter on the \"give me a
-- hand\"."/ He had asked for an automatic ask behind a switch earlier in the
-- same message and withdrew it on landing this design; **there is no timer
-- and no switch, because there is nothing to switch off.**
--
-- **The dim sentence is sent when he has typed nothing over it** — also
-- his: /"sending the dimmed sentence makes sense to me too"/. So the ask is
-- never empty and what went out is always something he can read off his own
-- screen.
--
-- **A second Enter while one is out is refused in words** rather than
-- queued or fired: one ask is one charge, and two answers racing for one
-- region is the shape `~swxcf` was.
askHintNow :: EventM Name St ()
askHintNow = do
  st <- get
  let typed = Text.strip (maybe Text.empty typedReply (stStripReply st))
      -- **An emptied row still asks**, which is the placeholder's promise
      -- kept: he can clear the sentence and press Enter, and what goes out
      -- is the sentence rather than nothing at all.
      asked = if Text.null typed then hintPlaceholder else typed
  case stHintConfig st of
    -- **The cleared state is what is handed on, not the one in hand.**
    -- 'sayEither' builds the next state from its argument and puts that, so
    -- a 'put' before it is discarded — measured under a pty: the row still
    -- held the typed sentence after the refusal.
    Nothing -> do
      let st' = st { stStripReply = Nothing }
      put st'
      sayEither st' hintNoKeySaid
    Just cfg
      | stHintAsking st -> sayEither st hintBusySaid
      | otherwise -> do
          let fields = hintFields st
              chan = stJevChan st
              cfg' = cfg { hintModel = stModel st }
          put
            st
              { stHintAsking = True
              , stHintAsked = stHintAsked st + 1
              , stStripReply = Nothing
              }
          -- **The prompt file is read inside the fork and not here**, so a
          -- slow disc cannot sit between his Enter and the next frame; the
          -- whole point of reading it per ask is that an edit lands on the
          -- next one without a restart.
          liftIO . void . forkIO $ do
            prompt <- loadHintPrompt
            answer <- askHint cfg' prompt fields asked
            writeBChan chan (HintAnswered answer)

-- | The answer coming back. **A failure is shown in the hint region rather
-- than only logged**: he pressed a key and is owed a reply, and a region
-- that stays empty after an ask reads as a feature that does not work.
applyHintAnswer :: Either String Text -> EventM Name St ()
applyHintAnswer result = do
  st <- get
  put
    st
      { stHintAsking = False
      , stHint = Just (either ("the model could not be reached — " <>) Text.unpack result)
      }

-- | **`:model ‹id›`, and the picker's Enter goes through here too.** The id
-- is not checked against the catalogue: see 'Tui.Config.cfgModel' for why a
-- model this build has never heard of is still one he may have chosen.
setModel :: St -> Text -> EventM Name St String
setModel st m = do
  let st' = st { stModel = m }
  liftIO (saveConfig (configOf st'))
  put st'
  pure ("model: " <> Text.unpack m)

-- | **`:models` and `:models ‹filter›`** — the catalogue in the session
-- picker's own dialog, his instruction.
--
-- **Fetched once and held** ('stModels'): the list is about 900 KB and does
-- not move while he is proving. **The fetch is off the main thread** and
-- reports back through 'ModelsListed', so a cold connection cannot freeze a
-- keystroke.
openModelPicker :: St -> Text -> EventM Name St ()
openModelPicker st filt = case stModels st of
  Just ms -> showModels st filt ms
  Nothing -> do
    let chan = stJevChan st
    liftIO . void . forkIO $ fetchModels >>= writeBChan chan . ModelsListed filt
    sayEither st "models: asking openrouter for the catalogue…"

-- | **An empty result says so and opens nothing** — the rule
-- 'openSessionPicker' already follows: a dialog whose only content is
-- /there is nothing here/ is one you dismiss to be told what a line of text
-- could have told you.
showModels :: St -> Text -> [HintModel] -> EventM Name St ()
showModels st filt ms = case matchingModels filt ms of
  [] -> sayEither st ("models: nothing at openrouter matches " <> show (Text.unpack filt))
  rows -> put st { stPicker = Just (Picker (PickModel rows) 0) }

-- | **The label on the reply row, and the cue that a call went out** —
-- `~w2tk2` slice 6. HIS, 2026-11-19: the label itself (/"a small label, like
-- \`AI hint\`"/), and then /"there needs to be some visual que of when a new
-- request is sent to the API"/ with /"I need to know how often it is
-- asked"/. All three are this one string.
--
-- **It reads @AI hint@ before the first ask, @AI hint · asking…@ while one
-- is out, and @AI hint · 3@ after three** — so the cue and the count are
-- the same field rather than two things competing for the row, and the row
-- costs no extra height to carry either.
--
-- **No row of its own**, which is `~8cr56`'s lesson applied before he has to
-- report it twice: a label on a row of its own would be a second heading
-- over a pane whose title already says @suggestions@, and it would cost a
-- row of cells to say one word.
hintLabel :: St -> String
hintLabel st
  | stHintAsking st = "AI hint · asking…"
  | stHintAsked st == 0 = "AI hint"
  | otherwise = "AI hint · " <> show (stHintAsked st)

-- | What is actually typed in the reply row — one function, because three
-- places ask the same question: the drawing (whether to keep the
-- placeholder), 'askHintNow' (what to send) and the width the editor is
-- held to.
typedReply :: Editor Text Name -> Text
typedReply = Text.concat . getEditContents

-- | **The reply row as Tab leaves it: the sentence in place and the cursor
-- behind it** — `~3p9g2`, his /"I want the tab to do that"/.
--
-- **The cursor is sent to the end rather than left at the start**, which is
-- where 'E.editorText' puts it: a line he is meant to edit or send wants the
-- caret after the words, not in front of them, and a first keystroke landing
-- before the sentence would read as the text having been pushed aside.
openStripReply :: Text -> Editor Text Name
openStripReply t = E.applyEdit Zip.gotoEOF (E.editorText StripReply (Just 1) t)

hintNoKeySaid :: String
hintNoKeySaid =
  "no OPENROUTER_API_KEY in this process's environment — set it and restart to ask for a hint"

hintBusySaid :: String
hintBusySaid = "a hint is already on its way — one ask at a time"

-- | Reads a ranking answer back in — 'Left' (a failed call) and a
-- generation that no longer matches both mean the same thing: do
-- nothing, the dropdown 'refreshOfferDropdown' already built stands.
-- **It lands on the slate as well as on the dropdown** — `~3gn2r`, and the
-- slate is the half that is always there to land on. The two take the same
-- scores through the same 'floatJevRows', so the strip's order and the
-- popup's order are the same order and not two orders that happen to match.
applyJevRanking :: Int -> Either String (Map.Map Text Double) -> EventM Name St ()
applyJevRanking gen result = do
  st <- get
  case (gen == stJevGen st, result) of
    (True, Right scores) ->
      put st
        { stOfferDropdown = floatJevPicks scores <$> stOfferDropdown st
        , stSlate = floatJevSlate scores (stSlate st)
        }
    _ -> pure ()

-- | Jev's top three, whatever they are, float to the very top of the
-- whole list — his call, 2026-10-29, over the bucket-preserving version
-- this replaced: *"Jev's top three pick can be anything Jev wants...
-- for now."* Crossing "tokens before productions" for that band is the
-- experiment, not an oversight; 'odJevPicked' is how 'offerRowToPopup'
-- knows to colour exactly those rows.
--
-- Only a row Jev's answer actually names can be picked — 'Map.toList'
-- over the scores, not over 'odRows', so a short or empty answer
-- promotes fewer than three (never zero scored rows dressed up as
-- three). The rest keep their original relative order below the band,
-- same stability guarantee as before. The previously selected row, if
-- any, is found again by label rather than by its old index, so a
-- highlight set with Up/Down follows its candidate rather than landing
-- on whatever the reorder put in that slot.
floatJevPicks :: Map.Map Text Double -> OfferDropdown -> OfferDropdown
floatJevPicks scores od = od { odRows = newRows, odSelected = newSelected, odJevPicked = picked }
  where
    (newRows, picked) = floatJevRows scores (odRows od)
    selectedLabel = rowLabel . (odRows od !!) <$> odSelected od
    newSelected = selectedLabel >>= \lbl -> listToMaybe [i | (i, r) <- zip [0 ..] newRows, rowLabel r == lbl]

-- | **THE STRIP'S SLATE IS JEV'S ORDER, NOT THE ENGINE'S WITH THREE OF JEV'S
-- ON TOP** — `~w2tk2` slice 3b, and **his instruction, 2026-11-19**: /"ALL of
-- the top 12 suggestions are to be the ones that Jev suggested."/ The thought
-- is older and he flagged it as building — §11 of
-- @discussion/the-dropdown-is-the-wrong-element.md@, /"maybe the Jev
-- integration needs to be done **more** instead of solving the late arrival
-- problem… we use Jev to suggest top 12 picks"/.
--
-- **A full sort and not a truncation to twelve.** Every row Jev scored comes
-- first in Jev's own order; everything Jev did not score keeps the engine's
-- order below. **The property he asked for then holds at every grid size** —
-- seven cells or ten, the cells are Jev's best that many — where a slate cut
-- to twelve would have been a second number to keep in step with the grid.
-- Nothing is destroyed either: the tail is still the slate, simply past the
-- keys, exactly as the rows past the grid already were.
--
-- **'sortOn' is stable, so candidates Jev scores equally keep the engine's
-- relative order** — tokens before productions, which is a relevance order
-- and a better tiebreak than whatever a hash would give.
--
-- **The dropdown is NOT changed and that is `~492hq`.** 'floatJevPicks' still
-- floats three, because the dropdown is disabled and awaiting his word to be
-- deleted, and a slice that rewrote its behaviour on the way past is outside
-- what he authorised.
--
-- **The cold start shows nothing, and §15 q1 is ruled.** For the ~300ms
-- before an answer lands 'slateJevPicked' is zero, so the strip is empty
-- rather than showing the engine's order meanwhile — his instruction of
-- 2026-11-19, /"only when the Jev is disabled in the settings, do I ever
-- want to see any suggestion that didn't come from Jev"/. His property 1,
-- that a late arrival must not be penalised, is kept by the answer landing
-- in full whenever it lands; it never asked for a stand-in to be shown in
-- the meantime. The Jev mark (`~zt4jk`) therefore reads as /Jev has
-- answered/, which is the right reading once every cell is Jev's.
--
-- **`~63n23` bites harder here and he is holding it.** Jev is asked about at
-- most 255 candidates, so on a 318-row launch list the rest are unscored and
-- sort below every scored row — under the old design that cost them a
-- promotion, under this one they cannot reach a cell at all.
floatJevSlate :: Map.Map Text Double -> Slate -> Slate
floatJevSlate scores sl = sl { slateRows = newRows, slateJevPicked = picked }
  where (newRows, picked) = jevOrderRows scores (slateRows sl)

-- | Jev's order for every row Jev scored, then the engine's order for the
-- rest; and **how many of them Jev actually suggested**, which is
-- 'Tui.Jev.jevNucleus' and not the length of the first group. See
-- 'floatJevSlate'.
--
-- **The two were the same number until `~swxcf` and that was the defect.**
-- A 'Choice' scores every option it is sent — 191 of 191, 255 of 255, in
-- his own log — so @length scored@ was the whole candidate list, and
-- 'stripSlateOf''s @take picked@ therefore took all of it. The pane was
-- doing the ordering he rejected while its haddock claimed the exclusion he
-- asked for.
--
-- **The ordering of 'slateRows' is untouched**: every scored row still
-- sorts to the front in Jev's own order, because the rows below the cut are
-- still the pool the next request is built from and still the list
-- @:jev off@ sorts alphabetically. What narrowed is only how many of them
-- count as Jev's.
-- **The cut is counted over the distinct labels and that is not a
-- nicety.** A 'Choice' is sent @Map.fromList@ of the candidates, so two
-- rows sharing a label are one option to Jev and come back as one
-- probability; counting the nucleus over the rows instead would count that
-- mass twice and claim one cell more than the answer paid for. Measured
-- 2026-11-19: on the line @a@ the rows gave six and the answer's own
-- distribution gave five, and five is the true one.
jevOrderRows :: Map.Map Text Double -> [OfferRow] -> ([OfferRow], Int)
jevOrderRows scores rows = (scored <> rest, jevNucleus (Map.elems present))
  where
    label = Text.pack . rowLabel
    present = Map.fromList [(label r, sc) | r <- rows, Just sc <- [Map.lookup (label r) scores]]
    scoredPairs =
      sortOn (negate . snd) [(r, sc) | r <- rows, Just sc <- [Map.lookup (label r) scores]]
    scored = map fst scoredPairs
    scoredLabels = map rowLabel scored
    rest = filter (\r -> rowLabel r `notElem` scoredLabels) rows

-- | **The ordering rule itself, and the one copy of it** — the picks and how
-- many of them, given the scores and a list of candidates.
floatJevRows :: Map.Map Text Double -> [OfferRow] -> ([OfferRow], Int)
floatJevRows scores rows = (picked <> rest, length picked)
  where
    label = Text.pack . rowLabel
    scored = [ (r, sc) | r <- rows, Just sc <- [Map.lookup (label r) scores] ]
    picked = map fst (take 3 (sortOn (negate . snd) scored))
    pickedLabels = map rowLabel picked
    rest = filter (\r -> rowLabel r `notElem` pickedLabels) rows

-- | The offset range 'renderInputContent' underlines — his `.jalivert/
-- TUI.md` #7, a visible cue that the line (or the literal under the
-- cursor) will not run as written. Reads 'RecoveryView's own
-- @recoveredSpan@ field directly (MS7 phase 143, `9fbe469` — his ask filed
-- in `.jalivert/REPORT.md`, "fence to fence" and past the cursor too, both
-- landed) rather than deriving anything from 'recoveredColumn'/
-- 'recoveredText', which stay exactly what they always were: what an
-- accepted completion overwrites, a different question from what to
-- underline — a literal's own recovered span covers the tag and both
-- fences, but accepting a candidate for its content must never eat the
-- tag along with it. This function is named apart from the field itself
-- ('recoveredSpan' the field, 'underlineSpan' the function) since
-- 'RecoveryView (..)' brings the field's own name into scope too.
--
-- **One-indexed, inclusive-start/exclusive-end, converted once here**:
-- the field is "the first character, counting from 1, and one past the
-- last" (its own haddock) — @(s, e)@ becomes the zero-indexed
-- @(from, length)@ 'mergeRuns' wants: @(s - 1, e - s)@.
underlineSpan :: OfferView -> Maybe (Int, Int)
underlineSpan ov = case offeredRecovered ov of
  Nothing -> Nothing
  Just r  -> let (s, e) = recoveredSpan r in Just (s - 1, e - s)

-- | The row source depends on which question was actually answered.
--
-- **Bare-word recovery** (typing an ordinary partial word — 'att', mid-
-- statement) draws from 'offeredOptions' alone, prefix-filtered by
-- "Thena.View.Statement"'s own 'recover'. 'offeredProductions' is *not*
-- usable here — checked directly against the running engine, not assumed:
-- under bare-word recovery it is copied through unfiltered, still every
-- production the empty line offers, not narrowed by what has been typed.
--
-- **Everything else — an ordinary offer, or the cursor inside a tagged
-- term literal — draws from both, tokens first, then productions**, his
-- own correction: a bare symbol ("λ") is still worth listing on its own,
-- but a production ("abs: ( λ ‹x› : Ty . LC )") is what actually inserts
-- the rest of the shape, so both belong, not one or the other. Deduplicated
-- by what an accept would actually insert — a trivial single-literal
-- production (e.g. a statement keyword, always present in
-- 'offeredProductions' too) would otherwise show up twice for no reason,
-- once as a token and once as an identical production.
buildOfferDropdown :: Bool -> Int -> OfferView -> Maybe OfferDropdown
buildOfferDropdown autoSelect col ov
  | null allRows = Nothing
  -- A shown dropdown always highlights one row, the first selectable one
  -- (his `.jalivert/TUI.md` #9; hints never take an Enter) — in both
  -- placements, since above the line the reversal renders that same first
  -- row adjacent to the input. Clearing with Esc still submits as typed.
  -- **Unless `:preselect off`** (`.jalivert/TUI.md` #23) — then a fresh
  -- dropdown opens with nothing highlighted, same as an exhausted list
  -- always has, and an arrow key is what picks a row instead.
  | otherwise = Just (OfferDropdown allRows initialSelection wordStart replaceLen 0)
  where
    initialSelection = if autoSelect then listToMaybe (selectableIxs allRows) else Nothing
    bareWord = case offeredRecovered ov of
      Just r -> isNothing (recoveredLanguage r)
      Nothing -> False
    -- | **A row an accept could not write is not a row — his instruction,
    -- 2026-10-20, `~bkzw9`**: /"I think that we shouldn't show the
    -- unselectable in the dropdown at all. They should be shown but not like
    -- this, they don't make sense in the dropdown."/ A nonterminal ('LC') and
    -- a token class (@‹x›@) both arrive as 'offeredOptions' entries whose
    -- 'rowInsert' is 'Nothing', and both are dropped here.
    --
    -- **He assented to a narrower rule — drop a nonterminal only when its own
    -- productions are listed beside it — and it is not expressible at the
    -- boundary.** 'ProductionView' carries 'productionName',
    -- 'productionShape' and 'productionInsert' and nothing that says which
    -- nonterminal a production /produces/, so this frontend cannot tell that
    -- @abs@, @app@ and @var@ are LC's rather than some other category's.
    -- Dropping both unconditionally is his primary instruction; the gap and
    -- what it would take to honour the narrower rule are recorded on
    -- `~5f3k6`, which is also where the question of where this information
    -- goes instead now lives.
    tokenRows =
      sortOn rowLabel (filter (isJust . rowInsert) (map offerRow (offeredOptions ov)))
    productionRows =
      sortOn rowLabel
        [ r
        | r <- map productionRow (offeredProductions ov)
        , rowInsert r `notElem` map rowInsert tokenRows
        ]
    -- | Hints (a bare nonterminal or scan class — 'rowInsert' is 'Nothing',
    -- see 'OfferRow') sort after every real candidate, his `.jalivert/
    -- TUI.md` #4: they're shown, never selectable, and mixed in
    -- alphabetically they broke up the list you can actually act on.
    -- 'sortOn' is stable, so this only ever moves hints down — the
    -- token-then-production order above is undisturbed within each group.
    -- **"After" already means "farthest from the input" in both
    -- placements**, not just when the popup hangs below it: 'popupAt'
    -- reverses the row list for an above-the-line popup, so a row later in
    -- this list renders nearer the input when flipped and farther from it
    -- when not — the same reversal that already made "what's first sits
    -- closest to the input either way" (`c4bfe51`) true for the selected
    -- row does the rest here for free.
    -- **Nothing left to sort hints to the bottom of**, since `~bkzw9`
    -- removed them: every surviving row has something to insert, so the
    -- token-then-production order is the whole order.
    allRows
      | bareWord  = tokenRows
      | otherwise = tokenRows <> productionRows
    -- | A bare word replaces the partial word itself ('recoveredColumn'/
    -- 'recoveredText' name that span exactly). Every other case — an
    -- ordinary offer, or inside a literal, where 'recoveredText' names the
    -- *whole recovered unit since the literal opened*, not a word to
    -- replace — is a plain insert at the cursor, same as 'offeredReplaces'
    -- already decides for the ordinary path. Getting this wrong is exactly
    -- what ate an already-typed '(' the first time: accepting a candidate
    -- inside a literal deleted back to the literal's own start instead of
    -- just inserting at the caret.
    (wordStart, replaceLen) = case offeredRecovered ov of
      Just r | isNothing (recoveredLanguage r) -> (recoveredColumn r - 1, length (recoveredText r))
      _ -> (col, if offeredReplaces ov then 1 else 0)

-- | A literal is text to type; a scan class or a nonterminal names a *kind*
-- of thing that may stand here and is shown, not offered — see 'OfferRow'.
offerRow :: SymbolView -> OfferRow
offerRow sv = case sv of
  ALiteralSymbol w -> OfferRow w (Just w)
  _                -> OfferRow (symbolText sv) Nothing

-- | The bracket convention for a scan class is TIER-A.md's own: "‹name›".
symbolText :: SymbolView -> String
symbolText sv = case sv of
  ALiteralSymbol w     -> w
  AScanSymbol n        -> "\8249" <> n <> "\8250"
  ANonterminalSymbol n -> n

-- | A whole production as a row — his own spec, 2026-09-28: *"I want to see
-- something like @app: ( LC LC )@ and when I select it, I get @( █ █ )@."*
-- The label is the name and the shape exactly as he asked; the insert is
-- 'productionInsert' read back through 'writtenInsertText', so a slot
-- becomes a real box in the buffer, not just its own bare symbol.
productionRow :: ProductionView -> OfferRow
productionRow pv =
  OfferRow
    (productionName pv <> ": " <> unwords (map symbolText (productionShape pv)))
    (Just (writtenInsertText (productionInsert pv)))

-- | 'productionInsert' read back into buffer text — the same duality
-- 'toWritten' reads the other way: a placeholder is the engine's own glyph
-- in the text, a splice can't occur in a production's own insertion (its
-- 'Thena.View.Chart.insertion' only ever emits text or placeholders).
writtenInsertText :: [Written] -> String
writtenInsertText = concatMap one
  where
    one w = case w of
      WrittenText t      -> t
      WrittenPlaceholder -> [placeholderGlyph]
      WrittenSplice      -> ""

-- | The line, split at the cursor into the '[Written]' shape
-- 'Thena.View.statementOfferView' takes — the "buffer-tracking region
-- model" CLAUDE.md's bookkeeping named as this feature's real
-- prerequisite. **Not a custom zipper**: 'Written's own haddock spells out
-- the duality directly — a frontend that keeps placeholders as positions
-- hands them over as runs, one that "has only text puts the character in,"
-- and both reach the reader the same way. So the input line stays exactly
-- what it already is, a plain 'Text' buffer with the engine's own
-- placeholder glyph embedded in it when a box is inserted, and this is
-- purely the read side: split the string at the cursor, then split each
-- side into runs at that glyph.
splitWritten :: String -> Int -> ([Written], [Written])
splitWritten line col = (toWritten (take col line), toWritten (drop col line))

-- | 'Earley.placeholderChar' said back, since 'Thena.Language.Earley' isn't
-- on the frontend boundary (`thena:view`'s own 'reexported-modules') to
-- import it from — hardcoded rather than reexported because it's a fixed
-- glyph, not something that could drift on its own; 'ProductionView's own
-- haddock quotes this exact character ("I get @( \9608 \9608 )@").
placeholderGlyph :: Char
placeholderGlyph = '\9608'

toWritten :: String -> [Written]
toWritten = merge . map one
  where
    one c = if c == placeholderGlyph then WrittenPlaceholder else WrittenText [c]
    merge (WrittenText a : WrittenText b : rest) = merge (WrittenText (a <> b) : rest)
    merge (w : rest) = w : merge rest
    merge [] = []

-- | The input line's own content, a placeholder box drawn dimmer than
-- ordinary text — see the "placeholder" attr's own haddock for why (the
-- caret going dark standing on one) — and a recovered span underlined
-- ('recoveredSpan', his `.jalivert/TUI.md` #7). Real text splits into runs
-- at the glyph the same way 'toWritten' does, since it's answering the
-- same question one level down: not "is this a box" for the engine, but
-- "is this a box" for the renderer.
--
-- **The ghost ('ghostAt') rides inline at the caret, not appended past
-- everything** — his `.jalivert/TUI.md` #21: real text up to 'col' renders
-- first, unchanged; then the dimmed ghost; then real text resumes from
-- 'col + skip', skipping whatever the accept would consume there (a box,
-- typically). Splitting the real text at 'col' rather than threading the
-- ghost through 'mergeRuns' itself is what keeps Brick's own cursor
-- placement correct — 'Edit.hs's own 'renderEditor' fixes the caret at a
-- column count into the *unmodified* zipper, so everything rendered before
-- that many real characters have gone by must still measure the same
-- width, and only ever inserting the ghost at that exact boundary
-- guarantees it does.
renderInputContent :: [Text] -> Int -> String -> Int -> Maybe (Int, Int) -> Widget Name
renderInputContent ts col ghost skip recovered =
  hBox (map renderRun (mergeRuns before recovered)
        <> [withAttr (attrName "dim") (str ghost)]
        <> map renderRun (mergeRuns after (shift (col + skip) recovered)))
  where
    full   = concatMap Text.unpack ts
    before = take col full
    after  = drop (col + skip) full
    shift n = fmap (\(from, len) -> (from - n, len))
    -- | One named attr per combination, not two nested 'withAttr' calls —
    -- see the "recovered"/"placeholder.recovered" attrs' own haddock for
    -- why nesting silently drops one of the two.
    renderRun ((isPlaceholder, isRecovered), s) = case (isPlaceholder, isRecovered) of
      (True,  True ) -> withAttr (attrName "placeholder.recovered") (str s)
      (True,  False) -> withAttr (attrName "placeholder")           (str s)
      (False, True ) -> withAttr (attrName "recovered")             (str s)
      (False, False) -> str s

-- | Per-character tags, merged into runs the same way the placeholder-only
-- version did: is this a box, and does it fall in the recovered span, both
-- by offset into whatever string is passed in (a local index, not
-- necessarily the whole line's own column — see 'renderInputContent's own
-- 'shift' for the "after the caret" half).
mergeRuns :: String -> Maybe (Int, Int) -> [((Bool, Bool), String)]
mergeRuns s recovered = merge (zipWith tag [0 ..] s)
  where
    tag i c = ((c == placeholderGlyph, inSpan i), [c])
    inSpan i = case recovered of
      Just (from, len) -> i >= from && i < from + len
      Nothing           -> False
    merge ((a, x) : (b, y) : rest) | a == b = merge ((a, x <> y) : rest)
    merge (r : rest) = r : merge rest
    merge [] = []

-- | Replace 'len' characters starting at column 'start' with 'ins', cursor
-- landing right after — the same shape 'killWordBack' already established
-- for editing the zipper directly rather than rebuilding the editor from a
-- fresh string.
acceptOfferEdit :: Int -> Int -> String -> Zip.TextZipper Text -> Zip.TextZipper Text
acceptOfferEdit start len ins = Zip.insertMany (Text.pack ins) . deleteForward len . Zip.moveCursor (0, start)
  where
    deleteForward :: Int -> Zip.TextZipper Text -> Zip.TextZipper Text
    deleteForward 0 z = z
    deleteForward n z = deleteForward (n - 1) (Zip.deleteChar z)

-- | Tab-completion for a path-taking command's path only — his ruling,
-- 2026-09-29: *"it is not instral. Therefore special casing it in our TUI's
-- repl is ok."* 'pathCommands' is which lines those are. Scoped to a single
-- trailing path (several comma/space-separated paths completing independently
-- is the old experiment's finer-grained version of this and not built here yet
-- — narrower, not a hack), which is also the whole of what `:consult`'s list
-- needs: the path being typed is the last one.
--
-- **Back to silent on an ambiguous or missing match, 2026-09-29** — his
-- `.jalivert/TUI.md` feedback: once the live dropdown exists, printing
-- "N matches" to the repl on Tab is redundant with what the dropdown
-- already shows, and he asked for it to print nothing. This supersedes the
-- previous session's `stHistory` message, which existed only because the
-- dropdown didn't yet.
-- **Tab answers from the same vocabulary the dropdown is showing**
-- ('dropdownRows'), so the two can never offer different things. Only the
-- directory listing has a second trick — a typed name that is itself a
-- directory completes to its slash — and that is 'completePath'; for a list of
-- words there is nothing to extend past what they have in common.
completeLoadPath :: EventM Name St ()
completeLoadPath = do
  st <- get
  let line = concatMap Text.unpack (getEditContents (stInput st))
  case loadPathPrefix line of
    Nothing -> pure ()
    Just prefix -> do
      matched <-
        if pathArgument line
          then liftIO (completePath prefix)
          else do
            rows <- liftIO (dropdownRows line)
            pure (extended prefix rows)
      case matched of
        Nothing -> pure ()
        Just full -> do
          put st { stInput = E.editorText Input (Just 1) (Text.pack (replacePathPrefix line full)) }
          refreshDropdown
  followInput

-- | Whether this line's argument is a path on this machine, which is every
-- line 'dropdownRows' answers for except `:script`'s own two words and the
-- slug after `:script resume`.
pathArgument :: String -> Bool
pathArgument line =
  not (resumeArgument `isPrefixOf` line)
    && not (paneCommandPrefix `isPrefixOf` line)
    && not (scriptCommand `isPrefixOf` line && notElem ' ' (drop (length scriptCommand) line))

-- | What all the offered rows agree on past what is typed, or 'Nothing' when
-- that is nothing — Tab's shell-style extension over a plain list.
extended :: String -> [String] -> Maybe String
extended typed rows =
  let common = longestCommonPrefix rows
   in if length common > length typed then Just common else Nothing

-- | **Despite the name, what the dropdown anchors to — not always a path.**
-- `:script resume` completes a slug and `:pane` completes its own words
-- (`~fxc89`); both are the line's last word all the same, which is what this
-- answers and why the two commands needed nothing else to be offered.
loadPathPrefix :: String -> Maybe String
loadPathPrefix line
  | any (`isPrefixOf` line) pathCommands = Just (lastWord line)
  | paneCommandPrefix `isPrefixOf` line = Just (lastWord line)
  | otherwise = Nothing

-- | **What the dropdown offers on this line**, which is not always a
-- directory listing — his ask, 2026-11-11: *"does `:script resume`
-- autocomplete? it should."* It did not, and worse, it looked for a file named
-- after the slug, because `":script "` is one of 'pathCommands' and the path
-- listing answered for every argument that followed it.
--
-- Three vocabularies, and which one a line wants is decided by the line:
--
--   * **`:script resume ‹slug›`** — the stored sessions in the project
--     database, which is the only list where a slug can come from.
--   * **`:script ‹word›`** — the two words that are not paths, @sessions@ and
--     @resume@, offered beside whatever paths match, because `:script` takes
--     either and a user typing @:script re@ means the word.
--   * **anything else in 'pathCommands'** — the directory listing, unchanged.
--
-- **Every row is exactly what an accept inserts** (`~bkzw9`), which is why a
-- stored session is offered by its slug and not by its readable name: the name
-- has spaces in it and `:script resume` is a word-split command line. The
-- names are what `:script sessions` is for.
dropdownRows :: String -> IO [String]
dropdownRows line
  -- | **A fourth vocabulary, and it is the pane names** — `~fxc89`. Nothing
  -- here touches the disc: which panes there are, and which positions, are
  -- facts about the TUI. 'paneVocabulary' is the whole of it.
  | Just vocab <- paneVocabulary line =
      pure (settled [w | w <- vocab, typed `isPrefixOf` w])
  | resumeArgument `isPrefixOf` line = do
      index <- loadIndex
      pure (settled [stSlug st | st <- index, typed `isPrefixOf` stSlug st])
  | scriptCommand `isPrefixOf` line, notElem ' ' (drop (length scriptCommand) line) = do
      paths <- loadDropdownEntries typed
      pure (settled ([w | w <- scriptWords, typed `isPrefixOf` w] <> paths))
  | otherwise = loadDropdownEntries typed
  where
    typed = lastWord line
    -- | One row, and it is already typed in full: there is nothing left to
    -- offer, which is exactly what the directory listing answers in the same
    -- position. A dropdown standing open over its own answer is noise.
    settled rows = if rows == [typed] then [] else rows

scriptCommand :: String
scriptCommand = ":script "

resumeArgument :: String
resumeArgument = ":script resume "

-- | The words `:script` takes in place of a path. **`resume` carries its
-- space**, because it is not the end of the line — accepting it should leave
-- the caret where the slug goes, the same courtesy a completed directory's
-- slash is.
scriptWords :: [String]
scriptWords = ["sessions", "resume "]

-- | The colon commands whose argument is a path on this machine, and so the
-- lines this listing answers for. **It is not only `:load` any more** — MS11
-- added `:consult ‹path›` (phase 271) and `:replay ‹path›` (phase 302), the
-- two of the three words that replace `:load` which take a path rather than a
-- module name. A path argument is a directory listing wherever it is written,
-- so the affordance is the same one and the gate is a membership test.
--
-- **`import` is deliberately absent, and it is not an oversight**: it takes a
-- module NAME, resolved by the engine against its own search, and it is a bare
-- line at the prompt rather than a colon command. Offering `examples/` base
-- names against it would complete the wrong vocabulary.
--
-- The trailing space is part of each prefix: a line still being typed towards
-- `:consult` is a statement question like any other, and 'lastWord' would
-- otherwise read the command itself as the path being written.
pathCommands :: [String]
pathCommands = [":load ", ":consult ", ":replay ", ":script "]

lastWord :: String -> String
lastWord = reverse . takeWhile (/= ' ') . reverse

-- | The offset where the path currently being typed starts: the line minus
-- its last word. Constant while the word is extended a character at a time,
-- moving only when spacing changes or the word is restarted — which is what
-- makes it a position-once anchor for the dropdown ('dropdownLayer') rather
-- than a caret follower. Only meaningful when 'loadPathPrefix' matched, and
-- the dropdown layer never asks otherwise.
pathStartOff :: String -> Int
pathStartOff line = length line - length (lastWord line)

-- | How far past the path's start the segment being typed begins: the typed
-- directory and its slash ('examples/' in 'examples/Stlc01Syntax.thena'), or
-- zero when the path has no slash yet. The dropdown shows base names, so its
-- text anchors
-- here rather than at the whole path's start — and typing or deleting a
-- slash moves the segment, recomputing the position exactly when a
-- directory is entered or left (his `.jalivert/TUI.md` #2).
segOff :: String -> Int
segOff prefix = length prefix - length (takeFileName prefix)

-- | A word backward from the cursor, as a zipper edit: the whitespace
-- behind it first, then the word itself. Zero characters at the start of
-- the line, where there is nothing to remove.
killWordBack :: Zip.TextZipper Text -> Zip.TextZipper Text
killWordBack z =
  foldr (.) id (replicate (wordBackLen before) Zip.deletePrevChar) z
  where
    (_, col) = Zip.cursorPosition z
    before = reverse (Text.unpack (Text.take col (Zip.currentLine z)))
    wordBackLen rev = length spaces + length word
      where
        spaces = takeWhile isSpace rev
        word = takeWhile (not . isSpace) (drop (length spaces) rev)

replacePathPrefix :: String -> String -> String
replacePathPrefix line completed = take (length line - length (lastWord line)) line <> completed

-- | Every entry in a prefix's directory that starts with what's typed —
-- shared by Tab's shell-style extension and the live dropdown's listing.
matchingEntries :: String -> IO [String]
matchingEntries prefix = do
  let dir  = takeDirectory prefix
      name = takeFileName prefix
  exists <- doesDirectoryExist dir
  if not exists
    then pure []
    else do
      entries <- listDirectory dir
      let shown = if "." `isPrefixOf` name then entries else filter (not . isPrefixOf ".") entries
      pure (sort (filter (name `isPrefixOf`) shown))

-- | Shell-style completion: extended as far as every match agrees, or
-- 'Nothing' if that's no further than what's already typed (no matches, or
-- genuinely ambiguous with nothing more in common) — the live dropdown
-- covers telling the user why, so this doesn't need to any more.
--
-- **A result naming a directory carries its trailing slash** (his
-- `.jalivert/TUI.md` #1): Tab descends into it the way a terminal does, and
-- the dropdown goes on to list its contents rather than closing on the
-- exact match. Files pass through untouched.
completePath :: String -> IO (Maybe String)
completePath prefix = do
  matches <- matchingEntries prefix
  let dir  = takeDirectory prefix
      name = takeFileName prefix
      common = longestCommonPrefix matches
  if length common > length name
    then Just <$> slashDir (joinDir dir common)
    else do
      -- Nothing further in common — but what is typed may itself name a
      -- directory, and then the slash is the completion.
      let here = joinDir dir name
      slashed <- slashDir here
      pure (if slashed /= here then Just slashed else Nothing)

-- | A completed directory carries its slash, so the next Tab — and the
-- dropdown — continues inside it rather than stopping at its name.
slashDir :: FilePath -> IO FilePath
slashDir p = do
  isDir <- doesDirectoryExist p
  pure (if isDir && not ("/" `isSuffixOf` p) then p ++ "/" else p)

-- | Every match, full-path, for the dropdown to list — '[]' both for "no
-- directory"/"nothing matches" and for "one match, and it's already typed
-- in full," which the dropdown treats identically: nothing left to offer.
--
-- **Values already carry a directory's slash**: display strips it back
-- off, Tab and Enter land the value as is, and the ghost preview
-- ('inputGhost') reads exactly what an accept would write — one place
-- decides, nowhere derives it twice.
loadDropdownEntries :: String -> IO [String]
loadDropdownEntries prefix = do
  matches <- matchingEntries prefix
  let name = takeFileName prefix
      dir  = takeDirectory prefix
  case matches of
    [m] | m == name -> pure []
    ms -> mapM (slashDir . joinDir dir) ms

joinDir :: FilePath -> String -> String
joinDir "." name = name
joinDir dir  name = dir </> name

longestCommonPrefix :: [String] -> String
longestCommonPrefix [] = ""
longestCommonPrefix (x : xs) = foldl agree x xs
  where
    agree a b = map fst (takeWhile (uncurry (==)) (zip a b))
