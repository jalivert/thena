-- | The TUI's entry point.
--
-- **Four panes, no borders** — a wide REPL on the left, proof-term/goals/
-- machine stacked narrower on the right (geometry from `MS7-CLI`, his
-- instruction: the layout only, never its code). Separation is a dark
-- panel fill plus one neon accent as a left edge, never a border glyph and
-- never a full-pane fill — his correction, 2026-09-29, after the first
-- pass used pale tints across the whole pane.
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
import Control.Monad.IO.Class (liftIO)
import Data.Char (isSpace)
import Data.List (isPrefixOf, sort, sortOn)
import Data.Maybe (isJust, listToMaybe)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Zipper as Zip
import qualified Graphics.Vty as V
import Graphics.Vty.Platform.Unix (mkVty)
import Lens.Micro (Lens', lens)
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath (takeDirectory, takeFileName, (</>))

import Thena.Driver (Response (Quit), Session, oneLine)
import Thena.Files (following, startingSession)
import Thena.Render (renderResponse, renderTrouble)
import Thena.View (developmentView, focusAddress, machineView, statementOfferView)
import Thena.View.Chart
  ( OfferView (..)
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
import Tui.Theme (Theme (..), neonPinkDark, themeByName)

data Name
  = Input
  | HistoryVP
  | ProofTermVP
  | GoalsVP
  | MachineVP
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

-- | The live completion dropdown driven by 'Thena.View.statementOfferView'
-- — recomputed on every keystroke a line that isn't a colon command
-- produces, same as the module header says.
data OfferDropdown = OfferDropdown
  { odRows       :: [OfferRow]
    -- ^ capped ('offerRowCap') and alphabetised — 'offeredOptions' can be
    -- the whole ~90-word statement vocabulary on an empty line, and nothing
    -- here builds a scrolling popup yet.
  , odSelected   :: Maybe Int
    -- ^ an index into 'odRows', but only ever one whose 'rowInsert' is
    -- 'Just' — see 'offerMoveDown'/'offerMoveUp'.
  , odRecovered  :: Bool
    -- ^ 'offeredRecovered' was 'Just' (or, degenerately, the line was
    -- 'offeredStuck' with nothing recovered) — **draw this dropdown and the
    -- input line distinctly**, his design: this line will not run as
    -- written.
  , odWordStart  :: Int
    -- ^ the column an accepted row replaces from. The recovered unit's own
    -- start when recovered; the cursor's own column otherwise, since the
    -- ordinary path only ever offers something to insert, never something
    -- partially typed to replace.
  , odReplaceLen :: Int
    -- ^ how many characters after 'odWordStart' an accept removes — the
    -- recovered text's own length when recovered; one placeholder character
    -- when the cursor sits on a box ('offeredReplaces'); zero otherwise.
  , odMore       :: Int
    -- ^ candidates past the cap, shown as a trailing count rather than
    -- silently dropped.
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
  , stPaneExtent  :: Maybe (Extent Name)  -- ^ same lag, the repl pane's own
                                            -- viewport bounds, needed to
                                            -- decide whether the dropdown
                                            -- has room below the caret
  }

stInputL :: Lens' St (Editor Text Name)
stInputL = lens stInput (\st i -> st { stInput = i })

emptyInput :: Editor Text Name
emptyInput = E.editorText Input (Just 1) Text.empty

runTui :: IO ()
runTui = do
  (s0, trouble) <- startingSession
  let st0 = St
        { stTurns       = case concatMap (renderTrouble s0) trouble of
            []  -> []
            out -> [Turn Nothing out]
        , stInput       = emptyInput
        , stSession     = s0
        , stTheme       = neonPinkDark
        , stFoldOn      = True
        , stDropdown    = Nothing
        , stOfferDropdown = Nothing
        , stInputExtent = Nothing
        , stPaneExtent  = Nothing
        }
  vty <- mkVty V.defaultConfig
  _ <- customMain vty (mkVty V.defaultConfig) Nothing app st0
  pure ()

app :: App St e Name
app = App
  { appDraw         = draw
  , appChooseCursor = showFirstCursor
  , appHandleEvent  = handleEvent
  , appStartEvent   = enableMouse
  , appAttrMap      = attrs . stTheme
  }

-- | Wheel-scroll works on whichever pane the pointer is over, "no matter
-- where the focus is" — his words, 2026-09-29 — which needs mouse mode on
-- at the terminal, not just clickable widgets.
enableMouse :: EventM Name St ()
enableMouse = do
  vty <- getVtyHandle
  liftIO (V.setMode (V.outputIface vty) V.Mouse True)

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
  , (attrName "accent.output",  ink (themeSoft th))
  , (attrName "dropdown",          surface (themePopup th) (themeInk th))
  , (attrName "dropdown.selected", surface (themePopup th) (themeRepl th))
  -- A recovered (or stuck) offer draws on 'themeWrong' instead of
  -- 'themePopup' — his design: a different background says *this will not
  -- run as written* before a row is even read.
  , (attrName "dropdown.wrong",          surface (themeWrong th) (themeInk th))
  , (attrName "dropdown.wrong.selected", surface (themeWrong th) (themePanel th))
  , (attrName "input.wrong", ink (themeWrong th))
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
draw st = dropdownLayer st <> offerDropdownLayer st <> [hBox [replColumn, gapH, sideColumn]]
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
          (padAll 1 (vBox (renderTurns (stTurns st) <> [inputLine] <> wrongLine)))

    -- | 'Input' reported here, on the editor itself, not the "❯ " ahead of
    -- it — so 'stInputExtent's own upper-left is column 0 of the *text*,
    -- and every text offset ('pathStartOff', the cursor, anything later)
    -- adds onto a real screen column directly, no prompt width to remember.
    inputLine = str "❯ " <+> reportExtent Input (renderEditor (str . concatMap Text.unpack) True (stInput st))

    -- | His design for a recovered (or stuck) offer: "a red underline under
    -- the whole input line." A thin bar in 'themeWrong', the same lower-
    -- eighth-block technique the latest-turn marker already uses for a
    -- thin accent — not vty text-underline styling, which has no separate
    -- color of its own to give it, and not drawn at all (rather than blank)
    -- when nothing is wrong, so the pane doesn't carry a permanently
    -- reserved blank line under every ordinary prompt.
    wrongLine
      | maybe False odRecovered (stOfferDropdown st) = [vLimit 1 (withAttr (attrName "input.wrong") (fill '▁'))]
      | otherwise = []

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

-- | One turn, prompt (if any) then output — the most recent turn's output
-- gets a thin accent bar to its left, his request 2026-09-29 (thinner than a
-- pane's own '▎' edge, so '▏', one-eighth block, distinct glyph). The bar
-- column is always reserved, blank on every other turn, so a turn's text
-- doesn't visibly shift left/right as a newer one takes over the accent.
renderTurns :: [Turn] -> [Widget n]
renderTurns turns = zipWith renderTurn [1 :: Int ..] turns
  where
    lastIx = length turns
    renderTurn ix t =
      vBox (promptLine <> map (outputLine (ix == lastIx)) (turnOutput t))
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
dropdownLayer st = case stDropdown st of
  Just ld -> popupAt st (pathStartOff line) (length (ldEntries ld)) (renderDropdown ld)
    where line = concatMap Text.unpack (getEditContents (stInput st))
  Nothing -> []

renderDropdown :: LoadDropdown -> Widget Name
renderDropdown (LoadDropdown entries selected) =
  withAttr (attrName "dropdown") (vBox (zipWith renderRow [0 :: Int ..] entries))
  where
    renderRow i name
      | Just i == selected = withAttr (attrName "dropdown.selected") (str (dropdownSelected <> name))
      | otherwise           = str (dropdownPlain <> name)

-- | The completion dropdown, positioned the same way — see 'popupAt'.
-- The trailing "+N more" line (when the candidate list was capped) counts
-- toward the popup's own height so the flip-above math still clears it.
offerDropdownLayer :: St -> [Widget Name]
offerDropdownLayer st = case stOfferDropdown st of
  Just od | not (null (odRows od)) ->
    popupAt st (odWordStart od) (length (odRows od) + (if odMore od > 0 then 1 else 0))
      (renderOfferDropdown od)
  _ -> []

renderOfferDropdown :: OfferDropdown -> Widget Name
renderOfferDropdown (OfferDropdown rows selected recovered _ _ more) =
  withAttr (attrName bgName) (vBox (zipWith renderRow [0 :: Int ..] rows <> moreLine))
  where
    bgName = if recovered then "dropdown.wrong" else "dropdown"
    selBg = if recovered then "dropdown.wrong.selected" else "dropdown.selected"
    renderRow i (OfferRow label ins)
      | Just i == selected = withAttr (attrName selBg) (str (dropdownSelected <> label))
      | Nothing <- ins      = withAttr (attrName "dim") (str (dropdownPlain <> label))
      | otherwise           = str (dropdownPlain <> label)
    moreLine = [withAttr (attrName "dim") (str (dropdownPlain <> "+" <> show more <> " more")) | more > 0]

-- | Position a caret-anchored popup at a given column of the input's own
-- text (column 0 is the text's own left edge, per 'stInputExtent's own
-- doc) — the math 'dropdownLayer' always used, factored out so a second
-- popup positions itself identically rather than drifting from a second
-- copy. Flips above the caret past 80% of the pane's depth, below it
-- otherwise — his rule, 2026-09-29; see the historical note this carries
-- forward from 'dropdownLayer's original home.
popupAt :: St -> Int -> Int -> Widget Name -> [Widget Name]
popupAt st col rowCount content = case stInputExtent st of
  Nothing -> []
  Just inputExt -> [translateBy (Location (popupCol, popupRow)) content]
    where
      paneExt = case stPaneExtent st of
        Just p  -> p
        Nothing -> inputExt
      popupCol   = max 0 (locationColumn (extentUpperLeft inputExt) + col - dropdownMarkerWidth)
      inputRow   = locationRow (extentUpperLeft inputExt)
      paneRow    = locationRow (extentUpperLeft paneExt)
      paneHeight = snd (extentSize paneExt)
      depthFrac :: Double
      depthFrac = if paneHeight <= 0 then 0 else fromIntegral (inputRow - paneRow) / fromIntegral paneHeight
      popupRow = if depthFrac > 0.8 then inputRow - rowCount else inputRow + 1

-- | The lead every dropdown row carries — the arrow on the selected row,
-- blank space everywhere else. **One glyph plus one space either way, so
-- every row's text starts at the same column**; 'dropdownLayer' anchors on
-- 'dropdownMarkerWidth' rather than a literal, so the two cannot drift apart.
dropdownSelected, dropdownPlain :: String
dropdownSelected = "→ "
dropdownPlain    = "  "

dropdownMarkerWidth :: Int
dropdownMarkerWidth = length dropdownSelected

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
    -- | Enter accepts the arrow-selected candidate into the input instead of
    -- submitting — his spec: "Enter selects it." Only fires once an arrow
    -- key has actually picked something; with the dropdown merely open and
    -- nothing selected, Enter still runs the line as typed.
    (Just (LoadDropdown entries (Just i)), _) | i < length entries -> do
      let line = concatMap Text.unpack (getEditContents (stInput st))
          line' = replacePathPrefix line (entries !! i)
      put st { stInput = E.editorText Input (Just 1) (Text.pack line') }
      refreshDropdown
      followInput
    -- | Same spec, the offer dropdown's own candidate — 'acceptOfferEdit'
    -- replaces exactly the recovered/replaced span, not the whole line, so
    -- this is a zipper edit rather than a rebuilt editor (same shape as
    -- 'killWordBack').
    (_, Just od) | Just i <- odSelected od, Just ins <- rowInsert (odRows od !! i) -> do
      put st { stInput = E.applyEdit (acceptOfferEdit (odWordStart od) (odReplaceLen od) ins) (stInput st) }
      refreshOfferDropdown
      followInput
    _ -> do
      let line = concatMap Text.unpack (getEditContents (stInput st))
      case words line of
        [":theme", name] | Just th <- themeByName name ->
          appendTurn st { stTheme = th } Nothing ["theme: " <> name]
        [":fold", mode] | mode `elem` ["on", "off"] ->
          appendTurn st { stFoldOn = mode == "on" } Nothing ["fold: " <> mode]
        _ -> do
          let (s', resp) = oneLine (stSession st) line
          case following s' resp of
            Just act | resp /= Quit -> do
              (sLoaded, responses, trouble) <- liftIO act
              let out =
                    renderResponse s' resp
                      ++ concatMap (renderResponse sLoaded) responses
                      ++ concatMap (renderTrouble sLoaded) trouble
              appendTurn st { stSession = sLoaded } (Just line) out
            _ -> do
              appendTurn st { stSession = s' } (Just line) (renderResponse s' resp)
              if resp == Quit then halt else pure ()
handleEventInner (VtyEvent (V.EvKey V.KEsc [])) = do
  st <- get
  case (stDropdown st, stOfferDropdown st) of
    -- | "Esc leaves the dropdown (arrow goes away) but leaves it open" —
    -- his spec exactly: clears the arrow-selection only, the candidate list
    -- stays up. With no selection to clear, Esc keeps its ordinary meaning.
    (Just ld@(LoadDropdown _ (Just _)), _) -> put st { stDropdown = Just ld { ldSelected = Nothing } }
    (_, Just od@(OfferDropdown _ (Just _) _ _ _ _)) -> put st { stOfferDropdown = Just od { odSelected = Nothing } }
    _ -> halt
handleEventInner ev@(VtyEvent (V.EvKey V.KDown [])) = navigateCompletion moveDown offerMoveDown ev
handleEventInner ev@(VtyEvent (V.EvKey V.KUp []))   = navigateCompletion moveUp offerMoveUp ev
handleEventInner (VtyEvent (V.EvKey (V.KChar '\t') [])) = completeLoadPath
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
handleEventInner ev =
  Brick.zoom stInputL (handleEditorEvent ev) >> followInput >> refreshDropdown >> refreshOfferDropdown

-- | Arrow-key navigation only takes over the keypress while a dropdown is
-- actually showing candidates — otherwise the original event falls through
-- to the editor as normal (a no-op either way, on a single-line editor).
-- ':load''s own dropdown takes priority (mutually exclusive with the offer
-- dropdown by construction, so this only ever matters in principle).
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
    _ -> Brick.zoom stInputL (handleEditorEvent ev) >> followInput

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
  case loadPathPrefix line of
    Nothing -> put st { stDropdown = Nothing }
    Just prefix -> do
      entries <- liftIO (loadDropdownEntries prefix)
      put st { stDropdown = if null entries then Nothing else Just (LoadDropdown entries Nothing) }

-- | Recomputes the completion dropdown from 'Thena.View.statementOfferView'
-- — called from the same places 'refreshDropdown' is, same reasoning.
-- **A colon line gets none**: '":`'-command completion doesn't exist
-- engine-side yet (TIER-A.md), and ':load''s own path is a directory
-- listing, not a grammar question — asking the statement grammar about
-- ":load foo" would just be asking the wrong question.
refreshOfferDropdown :: EventM Name St ()
refreshOfferDropdown = do
  st <- get
  let line = concatMap Text.unpack (getEditContents (stInput st))
  if ":" `isPrefixOf` line
    then put st { stOfferDropdown = Nothing }
    else do
      let (_, col) = getCursorPosition (stInput st)
          (before, after) = splitWritten line col
          ov = statementOfferView (stSession st) before after
      put st { stOfferDropdown = buildOfferDropdown col ov }

-- | 'offeredOptions', turned into rows and capped — sorted first so a
-- capped list is still the alphabetically-first candidates rather than
-- whatever order the op table happens to produce them in.
--
-- **Deliberately not drawing from 'offeredProductions'.** It would be the
-- right source for inserting a whole compound shape with its slots as
-- boxes (his 2026-09-28 request, "app: ( LC LC )" → "( █ █ )") — but
-- checked directly against the running engine, not assumed: under bare-word
-- recovery (see "Thena.View.Statement"'s own 'recover') it is copied
-- through unfiltered, still every production the empty line offers, not
-- narrowed by what has been typed. Using it here would show stale
-- candidates the moment a word is underway, which is worse than not
-- showing them. Revisit once the operand grammar itself is less thin
-- (TIER-A.md's own "what we are doing next") and a production is more than
-- a single literal or a single placeholder.
buildOfferDropdown :: Int -> OfferView -> Maybe OfferDropdown
buildOfferDropdown col ov
  | null allRows && not recovered = Nothing
  | otherwise = Just (OfferDropdown shown Nothing recovered wordStart replaceLen moreCount)
  where
    recovered = isJust (offeredRecovered ov)
    allRows = sortOn rowLabel (map offerRow (offeredOptions ov))
    shown = take offerRowCap allRows
    moreCount = length allRows - length shown
    (wordStart, replaceLen) = case offeredRecovered ov of
      Just r  -> (recoveredColumn r - 1, length (recoveredText r))
      Nothing -> (col, if offeredReplaces ov then 1 else 0)

offerRowCap :: Int
offerRowCap = 10

-- | A literal is text to type; a scan class or a nonterminal names a *kind*
-- of thing that may stand here and is shown, not offered — see 'OfferRow'.
-- The bracket convention for a scan class is TIER-A.md's own: "‹name›".
offerRow :: SymbolView -> OfferRow
offerRow sv = case sv of
  ALiteralSymbol w      -> OfferRow w (Just w)
  AScanSymbol n         -> OfferRow ("\8249" <> n <> "\8250") Nothing
  ANonterminalSymbol n  -> OfferRow n Nothing

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
completePath :: String -> IO (Maybe String)
completePath prefix = do
  matches <- matchingEntries prefix
  let dir  = takeDirectory prefix
      name = takeFileName prefix
      common = longestCommonPrefix matches
  pure $ if length common > length name then Just (joinDir dir common) else Nothing

-- | Every match, full-path, for the dropdown to list — '[]' both for "no
-- directory"/"nothing matches" and for "one match, and it's already typed
-- in full," which the dropdown treats identically: nothing left to offer.
loadDropdownEntries :: String -> IO [String]
loadDropdownEntries prefix = do
  matches <- matchingEntries prefix
  let name = takeFileName prefix
      dir  = takeDirectory prefix
  pure $ case matches of
    [m] | m == name -> []
    ms -> map (joinDir dir) ms

joinDir :: FilePath -> String -> String
joinDir "." name = name
joinDir dir  name = dir </> name

longestCommonPrefix :: [String] -> String
longestCommonPrefix [] = ""
longestCommonPrefix (x : xs) = foldl agree x xs
  where
    agree a b = map fst (takeWhile (uncurry (==)) (zip a b))
