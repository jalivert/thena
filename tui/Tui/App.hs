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
-- That's a one-cell stage-colored margin around the whole layout (see
-- `draw`'s own `padAll 1`), on top of the gap the panes already had
-- between each other — the accent-edge-plus-title scheme itself is
-- unchanged.
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
import Brick.BChan (newBChan, writeBChan)
import Control.Concurrent (forkIO, threadDelay)
import Control.Monad.IO.Class (liftIO)
import Data.Char (isSpace)
import Data.List (intercalate, isPrefixOf, isSuffixOf, sort, sortOn)
import Data.Maybe (isJust, isNothing, listToMaybe)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Zipper as Zip
import qualified Graphics.Vty as V
import Graphics.Vty.Platform.Unix (mkVty)
import Lens.Micro (Lens', lens)
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath (dropTrailingPathSeparator, takeDirectory, takeFileName, (</>))
import System.IO (hFlush, hPutStr, stdout)

import Thena.Driver (Response (Quit), Session, oneLine)
import Thena.Files (following, startingSession)
import Thena.Render (renderResponse, renderTrouble)
import Thena.View (developmentView, focusAddress, machineView, statementOfferView)
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
  , foldAttr
  , renderDevelopment
  , renderGoals
  , renderMachineView
  , spliceAttr
  )
import Tui.Config (Config (..), loadConfig, saveConfig)
import Tui.Theme (Theme (..), neonPinkDark, themeByName, themes)

data Name
  = Input
  | HistoryVP
  | ProofTermVP
  | GoalsVP
  | MachineVP
  | LoadPopup
  | OfferPopup
  deriving (Eq, Ord, Show)

-- | One completed round: the line that was run (absent for the startup
-- trouble dump and the `:theme`/`:fold` pseudo-commands, which never echoed
-- what was typed even before this) and the output lines it produced.
data Turn = Turn
  { turnPrompt :: Maybe String
  , turnOutput :: [String]
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
  }

data St = St
  { stTurns       :: [Turn]  -- ^ forward chronological — oldest first, an
                              -- append-only document, his correction 2026-09-29
  , stInput       :: Editor Text Name
  , stSession     :: Session
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
  , stInputExtent :: Maybe (Extent Name)  -- ^ looked up post-render, one
                                             -- frame behind — 'Brick.Main'
                                             -- has no way to ask for an
                                             -- extent mid-'draw'
  , stPaneExtent :: Maybe (Extent Name)  -- ^ same lag, the repl pane's own
                                             -- viewport bounds, needed to
                                             -- decide whether the dropdown
                                             -- has room below the caret
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
  , stHistoryDraft :: String
    -- ^ the live line 'historyBack' interrupted, restored by
    -- 'historyForward' on the way back past the newest entry — the same
    -- "what you were typing before you went looking" a shell keeps.
    -- Meaningless while 'stHistoryPos' is 'Nothing'.
  }

stInputL :: Lens' St (Editor Text Name)
stInputL = lens stInput (\st i -> st { stInput = i })

emptyInput :: Editor Text Name
emptyInput = E.editorText Input (Just 1) Text.empty

runTui :: IO ()
runTui = do
  (s0, trouble) <- startingSession
  cfg <- loadConfig
  let theme0 = maybe neonPinkDark id (themeByName (cfgTheme cfg))
      autoSelect0 = cfgAutoSelect cfg
  let st0 = St
        { stTurns       = case concatMap (renderTrouble s0) trouble of
            []  -> []
            out -> [Turn Nothing out]
        , stInput       = emptyInput
        , stSession     = s0
        , stTheme       = theme0
        , stFoldOn      = True
        , stDropdown    = Nothing
        -- The input opens with its dropdown already up (his
        -- `.jalivert/TUI.md` #14): the empty line offers the full rule
        -- list, first row lit — the same state deleting back to empty
        -- reaches.
        , stOfferDropdown = buildOfferDropdown autoSelect0 0 (statementOfferView s0 [] [])
        , stDismissed   = Nothing
        , stRecoveredSpan = Nothing
        , stAutoSelect  = autoSelect0
        , stWhisperOn   = cfgWhisperOn cfg
        , stHistory     = []
        , stHistoryPos  = Nothing
        , stHistoryDraft = ""
        , stInputExtent = Nothing
        , stPaneExtent  = Nothing
        }
  -- One synthetic event after startup: extents only exist once something
  -- has rendered, so the launch dropdown cannot position on the very first
  -- frame — this tick runs the outer wrapper (which records them) without
  -- touching anything, and the second frame lays out against real
  -- measurements. A single delayed write, then the thread is done; if the
  -- first draw somehow hasn't happened yet, the tick is a harmless no-op
  -- and the dropdown arrives on the first keystroke as before.
  chan <- newBChan 1
  _ <- forkIO (threadDelay 200000 >> writeBChan chan Tick)
  vty <- mkVty V.defaultConfig
  _ <- customMain vty (mkVty V.defaultConfig) (Just chan) app st0
  resetCursorStyle

-- | The synthetic post-startup tick above — handled by doing nothing: the
-- outer wrapper around every event still records the fresh extents.
data Tick = Tick

app :: App St Tick Name
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
  , (attrName "edge.proofterm", surface (themePanel th) (themeProof th))
  , (attrName "edge.goals",     surface (themePanel th) (themeGoals th))
  , (attrName "edge.machine",   surface (themePanel th) (themeMachine th))
  , (attrName "title.repl",     ink (themeRepl th))
  , (attrName "title.proofterm", ink (themeProof th))
  , (attrName "title.goals",    ink (themeGoals th))
  , (attrName "title.machine",  ink (themeMachine th))
  , (attrName "dim",            ink (themeDim th))
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
  , (attrName "dropdown",          surface (themePopup th) (themeInk th))
  -- A real background swap for the selected row, not a foreground tint
  -- beside an arrow — his `.jalivert/TUI.md` #20: the arrow was the only
  -- thing marking a row selected, which read as weak. The repl accent as a
  -- solid bar, panel-dark text on top of it, same "selected" contrast an
  -- ordinary list widget uses.
  , (attrName "dropdown.selected", surface (themeRepl th) (themePanel th))
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
draw st = dropdownLayer st <> offerDropdownLayer st <> [padAll 1 (hBox [replColumn, gapH, sideColumn])]
  where
    budget = Budget 200
    s = stSession st
    links = developmentView budget s
    machine = machineView budget s
    fold = if stFoldOn st then Fold (focusAddress s) else NoFold

    -- | A one-cell stage-colored strip between panes, his correction,
    -- 2026-09-29 — panes touched directly before this, `MS7-CLI`'s own
    -- convention is a thin stage gap both ways. Left at the ambient (base)
    -- attr rather than any pane's "panel" attr, same as the stage itself.
    gapH = hLimit 1 (fill ' ')
    gapV = vLimit 1 (fill ' ')

    -- | An append-only document, not a fixed-position input row — his
    -- correction, 2026-09-29: the prompt used to be pinned to the pane's
    -- bottom row regardless of how much history existed, "like a second-class
    -- element." It's now the last line of the same scrollable content as
    -- everything above it, and travels down with it. Starting with the
    -- plain version, his own call: let it reach the pane's actual bottom and
    -- scroll from there like a normal terminal, not a pre-built holding-point
    -- short of that — add one later only if this doesn't feel right.
    replColumn =
      withAttr (attrName "panel") $
        pane "repl" HistoryVP
          (padAll 1 (vBox (renderTurns (stTurns st) <> [inputLine])))

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
    inputLine = str "❯ " <+> reportExtent Input (renderEditor (\ts -> renderInputContent ts col ghost skip (stRecoveredSpan st)) True (stInput st))
      where
        -- | `:whisper off` (his `.jalivert/TUI.md` #23) silences this
        -- outright rather than 'ghostAt' itself carrying the flag — the
        -- accept-span math it returns alongside the text isn't wanted by
        -- anything else, so there's nothing to lose by short-circuiting here.
        (ghost, skip) = if stWhisperOn st then ghostAt line col (stDropdown st) (stOfferDropdown st) else ("", 0)
        line = concatMap Text.unpack (getEditContents (stInput st))
        (_, col) = getCursorPosition (stInput st)

    sideColumn =
      hLimitPercent 38 $
        vBox
          [ withAttr (attrName "panel") (pane "proofterm" ProofTermVP (padAll 1 (renderDevelopment fold links)))
          , gapV
          , withAttr (attrName "panel") (pane "goals"     GoalsVP     (padAll 1 (renderGoals fold links)))
          , gapV
          , withAttr (attrName "panel") (pane "machine"   MachineVP   (padAll 1 (vBox (map str (renderMachineView machine)))))
          ]

    -- | The accent edge, a title strip, then the content — never a full
    -- fill, per his correction. 'clickable' so a scroll-wheel event over
    -- this pane resolves to its own 'Name', not the row under it.
    --
    -- **A real border was tried here for `.jalivert/TUI.md` #8 and
    -- withdrawn the same session** — his own correction: what he actually
    -- wanted was the panes not touching the *screen's* edge, backdrop
    -- visible around the outside, not a drawn box around each one. The
    -- accent-edge-plus-title scheme stays exactly as it was; only 'draw's
    -- own outer margin (see 'padAll 1' there) is new.
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
    pane key vp content =
      clickable vp $
        hBox
          [ withAttr (attrName ("edge." <> key)) (hLimit 1 (fill '▎'))
          , vBox
              [ withAttr (attrName ("title." <> key)) (padLeftRight 1 (str key))
              , viewport vp Vertical content
              ]
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
    outputLine accented l = marker <+> str " " <+> str l
      where
        marker = if accented then withAttr (attrName "accent.output") (str "▏") else str " "

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
loadRow selected i name = PopupRow (takeFileName (dropTrailingPathSeparator name)) (Just i == selected) False

-- | The completion dropdown, positioned the same way — see 'popupAt'.
offerDropdownLayer :: St -> [Widget Name]
offerDropdownLayer st = case stOfferDropdown st of
  Just od | not (null (odRows od)) ->
    popupAt st (odWordStart od) (length (odRows od)) OfferPopup
      (zipWith (offerRowToPopup (odSelected od)) [0 :: Int ..] (odRows od))
  _ -> []

offerRowToPopup :: Maybe Int -> Int -> OfferRow -> PopupRow
offerRowToPopup selected i (OfferRow label ins) =
  PopupRow label (Just i == selected) (isNothing ins)

-- | One row of any dropdown, before it becomes a 'Widget' — shared by
-- ':load''s directory listing and the completion dropdown so both scroll
-- and pad exactly the same way, see 'renderPopup'.
data PopupRow = PopupRow
  { prText     :: String
  , prSelected :: Bool
  , prDim      :: Bool  -- ^ a hint row (a nonterminal or scan class): shown,
                          -- never a landing spot, drawn muted.
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
truncateRow cap r
  | length (prText r) > cap = r { prText = take (cap - 1) (prText r) <> "…" }
  | otherwise = r

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
  let typedLen = col - odWordStart od
  if typedLen < 0 || typedLen > length ins
    then Nothing
    else Just (drop typedLen ins, max 0 (odReplaceLen od - typedLen))

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
handleEvent :: BrickEvent Name e -> EventM Name St ()
handleEvent ev = do
  handleEventInner ev
  inputExt <- lookupExtent Input
  paneExt <- lookupExtent HistoryVP
  st <- get
  put st { stInputExtent = inputExt, stPaneExtent = paneExt }

handleEventInner :: BrickEvent Name e -> EventM Name St ()
handleEventInner (VtyEvent (V.EvKey V.KEnter [])) = do
  st <- get
  case (stDropdown st, stOfferDropdown st) of
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
        -- | `:help` runs through the engine as usual (below) — its table is
        -- `Thena.Driver`'s, and stays that way, since it's the one command
        -- the engine and every other frontend share. `:preselect`/`:whisper`
        -- never reach `Thena.Driver` at all (intercepted above), so its own
        -- `:help` can't know they exist; 'tuiHelpLines' is appended here
        -- instead of touching the engine's table for two commands that are
        -- only ever true from inside this frontend.
        [":help"] -> runEngineLine st0 line tuiHelpLines
        _ -> runEngineLine st0 line []
handleEventInner (VtyEvent (V.EvKey V.KEsc [])) = do
  st <- get
  case (stDropdown st, stOfferDropdown st) of
    -- | Esc walks an open dropdown back in two steps (his `.jalivert/TUI.md`
    -- #14): first the highlight, then the list itself, which stays hidden
    -- until an edit brings it back ('stDismissed'). With nothing open, Esc
    -- is simply a no-op — it used to fall through to 'halt' and quit the
    -- whole TUI, which is not "Esc's ordinary meaning" for a line editor
    -- and was never asked for. Quitting is still `:quit`.
    (Just ld@(LoadDropdown _ (Just _)), _) -> put st { stDropdown = Just ld { ldSelected = Nothing } }
    (_, Just od@(OfferDropdown _ (Just _) _ _)) -> put st { stOfferDropdown = Just od { odSelected = Nothing } }
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
handleEventInner (VtyEvent (V.EvKey (V.KChar 'd') [V.MCtrl])) = do
  st <- get
  let line = concatMap Text.unpack (getEditContents (stInput st))
  if null line
    then halt
    else Brick.zoom stInputL (handleEditorEvent (VtyEvent (V.EvKey (V.KChar 'd') [V.MCtrl])))
      >> followInput >> refreshDropdown >> refreshOfferDropdown
-- | Down travels visually down in both placements — toward the input below
-- it, likewise toward the input above it, where the rows run reversed and
-- rising indices climb away. So above the line the two move-function pairs
-- swap: 'moveUp'/'offerMoveUp' step down-screen, 'moveDown'/'offerMoveDown'
-- step up-screen. From a cleared selection the same swap lands the visual
-- ends symmetrically (top on Down, bottom on Up) rather than list ends.
handleEventInner ev@(VtyEvent (V.EvKey V.KDown [])) = do
  st <- get
  if popupAbove st
    then navigateCompletion moveUp offerMoveUp ev
    else navigateCompletion moveDown offerMoveDown ev
handleEventInner ev@(VtyEvent (V.EvKey V.KUp [])) = do
  st <- get
  if popupAbove st
    then navigateCompletion moveDown offerMoveDown ev
    else navigateCompletion moveUp offerMoveUp ev
-- | Tab takes what's lit, VS Code's rule (his `.jalivert/TUI.md` #10) —
-- the same accepts Enter performs above, so the two keys cannot disagree.
-- With nothing highlighted, Tab keeps its old job: shell-completion on a
-- ':load' path (Esc-clear the highlight to get that back with the list
-- open), silence everywhere else.
handleEventInner (VtyEvent (V.EvKey (V.KChar '\t') [])) = do
  st <- get
  case (stDropdown st, stOfferDropdown st) of
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
handleEventInner (VtyEvent (V.EvKey (V.KChar c) [])) = do
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
handleEventInner (VtyEvent (V.EvKey V.KBS [V.MMeta])) = do
  st <- get
  put st { stInput = E.applyEdit killWordBack (stInput st) }
  followInput
  refreshDropdown
  refreshOfferDropdown
handleEventInner (MouseDown n V.BScrollUp _ _) = vScrollBy (viewportScroll n) (-1)
handleEventInner (MouseDown n V.BScrollDown _ _) = vScrollBy (viewportScroll n) 1
-- | Press-and-release gestures end here, all of them. A wheel tick arrives
-- as a press *and* a release (SGR 'M' then 'm'), and so does an ordinary
-- click — neither half carries editing intent, so neither reaches the
-- editor nor moves the viewport. Without these, the release half of every
-- wheel tick falls into the catch-all below, whose 'followInput' yanks the
-- pane back to the bottom: the pane fighting back on each scroll.
-- (Click-to-navigate on a dev-link/goal will claim 'MouseDown' with the
-- left button here once per-line extents land; until then clicks stay
-- inert rather than quietly yanking.)
handleEventInner (MouseUp _ _ _) = pure ()
handleEventInner (MouseDown _ _ _ _) = pure ()
-- | The startup tick ('runTui', the only 'Tick' there is) does nothing
-- itself — the outer wrapper has already recorded the fresh extents by
-- the time this runs, which is the whole point of it.
handleEventInner (AppEvent _) = pure ()
handleEventInner ev =
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
  -> BrickEvent Name e
  -> EventM Name St ()
navigateCompletion moveLoad moveOffer ev = do
  st <- get
  case (stDropdown st, stOfferDropdown st) of
    (Just ld@(LoadDropdown entries sel), _) | not (null entries) ->
      put st { stDropdown = Just ld { ldSelected = Just (moveLoad sel (length entries)) } }
    -- | Only a row with something to insert ('selectableIxs') is ever a
    -- landing spot — a hint row (a nonterminal or scan class) is shown but
    -- names a *kind* of thing, not text an accept could write.
    (_, Just od) | not (null (selectableIxs (odRows od))) ->
      put st { stOfferDropdown = Just od { odSelected = moveOffer (selectableIxs (odRows od)) (odSelected od) } }
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
    _ -> case ev of
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
  case following s' resp of
    Just act | resp /= Quit -> do
      (sLoaded, responses, trouble) <- liftIO act
      let out =
            renderResponse s' resp
              ++ concatMap (renderResponse sLoaded) responses
              ++ concatMap (renderTrouble sLoaded) trouble
      appendTurn st { stSession = sLoaded } (Just line) (out ++ extra)
    _ -> do
      appendTurn st { stSession = s' } (Just line) (renderResponse s' resp ++ extra)
      if resp == Quit then halt else pure ()

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
    , (":preselect on|off", "highlight a fresh dropdown's first row on its own")
    , (":whisper on|off",   "show the untyped remainder of the selected candidate")
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

-- | The slice of 'St' that 'Tui.Config' persists, read off whichever state
-- a `:theme`/`:preselect`/`:whisper` command just produced.
configOf :: St -> Config
configOf st = Config
  { cfgTheme      = themeName (stTheme st)
  , cfgAutoSelect = stAutoSelect st
  , cfgWhisperOn  = stWhisperOn st
  }

appendTurn :: St -> Maybe String -> [String] -> EventM Name St ()
appendTurn st prompt output = do
  put st
    { stInput = emptyInput
    , stTurns = stTurns st <> [Turn prompt output]
    , stDropdown = Nothing
    , stOfferDropdown = Nothing
    }
  followInput

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
      Just prefix -> do
        entries <- liftIO (loadDropdownEntries prefix)
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
-- **Only ':load''s own line gets none from here** — its path is a
-- directory listing, not a grammar question, and 'refreshDropdown' already
-- owns that answer ('stDropdown'); asking the statement grammar about
-- ":load foo" too would just be asking the wrong question a second time.
-- Every other colon line, including a bare ":" or one still being typed
-- towards ":load" itself, goes to 'statementOfferView' exactly like a
-- non-colon line now does. **This used to blank on any colon prefix
-- at all** — right when written (2026-09-29), because `:`-command
-- completion didn't exist engine-side yet. MS7 phase 142 (`9c9112a`,
-- `.jalivert/NOTES.md` 2026-09-30) answers it now, through the same
-- 'statementOfferView' call, no new one — the guard here just never
-- caught up to ask.
refreshOfferDropdown :: EventM Name St ()
refreshOfferDropdown = do
  st <- get
  let line = concatMap Text.unpack (getEditContents (stInput st))
  -- Same dismissal as 'refreshDropdown': hidden while the line is as Esc
  -- left it, back on any edit.
  if stDismissed st == Just line
    then put st { stOfferDropdown = Nothing }
    else if isJust (loadPathPrefix line)
      then put st { stOfferDropdown = Nothing, stDismissed = Nothing, stRecoveredSpan = Nothing }
      else do
        let (_, col) = getCursorPosition (stInput st)
            (before, after) = splitWritten line col
            ov = statementOfferView (stSession st) before after
            new = buildOfferDropdown (stAutoSelect st) col ov
            oldRows = maybe [] odRows (stOfferDropdown st)
        put st { stOfferDropdown = new, stDismissed = Nothing, stRecoveredSpan = underlineSpan ov }
        -- Same rule as 'refreshDropdown': new rows start at the top, same
        -- rows keep their scroll — above the line, at the bottom instead.
        if maybe [] odRows new /= oldRows
          then (if popupAbove st then vScrollToEnd else vScrollToBeginning) (viewportScroll OfferPopup)
          else pure ()

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
  | otherwise = Just (OfferDropdown allRows initialSelection wordStart replaceLen)
  where
    initialSelection = if autoSelect then listToMaybe (selectableIxs allRows) else Nothing
    bareWord = case offeredRecovered ov of
      Just r -> isNothing (recoveredLanguage r)
      Nothing -> False
    tokenRows = sortOn rowLabel (map offerRow (offeredOptions ov))
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
    allRows
      | bareWord  = tokenRows
      | otherwise = sortOn (isNothing . rowInsert) (tokenRows <> productionRows)
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

-- | Tab-completion for `:load`'s path only — his ruling, 2026-09-29:
-- *"it is not instral. Therefore special casing it in our TUI's repl is
-- ok."* Scoped to a single trailing path (several comma/space-separated
-- paths completing independently is the old experiment's finer-grained
-- version of this and not built here yet — narrower, not a hack).
--
-- **Back to silent on an ambiguous or missing match, 2026-09-29** — his
-- `.jalivert/TUI.md` feedback: once the live dropdown exists, printing
-- "N matches" to the repl on Tab is redundant with what the dropdown
-- already shows, and he asked for it to print nothing. This supersedes the
-- previous session's `stHistory` message, which existed only because the
-- dropdown didn't yet.
completeLoadPath :: EventM Name St ()
completeLoadPath = do
  st <- get
  let line = concatMap Text.unpack (getEditContents (stInput st))
  case loadPathPrefix line of
    Nothing -> pure ()
    Just prefix -> do
      matched <- liftIO (completePath prefix)
      case matched of
        Nothing -> pure ()
        Just full -> do
          put st { stInput = E.editorText Input (Just 1) (Text.pack (replacePathPrefix line full)) }
          refreshDropdown
  followInput

loadPathPrefix :: String -> Maybe String
loadPathPrefix line
  | ":load " `isPrefixOf` line = Just (lastWord line)
  | otherwise = Nothing

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
-- directory and its slash ('examples/' in 'examples/01'), or zero when the
-- path has no slash yet. The dropdown shows base names, so its text anchors
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
