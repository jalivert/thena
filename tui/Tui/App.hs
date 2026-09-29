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
-- **Not yet built, so as not to pretend otherwise**: the rules dropdown and
-- the object-term offer dropdown (both need positioned-popup machinery,
-- next slice); clicking a proof-term/goal line to move the cursor there
-- (agreed to stay, not yet wired — needs per-line extents).
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
import Data.List (isPrefixOf, sort)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Graphics.Vty as V
import Graphics.Vty.Platform.Unix (mkVty)
import Lens.Micro (Lens', lens)
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath (takeDirectory, takeFileName, (</>))

import Thena.Driver (Response (Quit), Session, oneLine)
import Thena.Files (following, startingSession)
import Thena.Render (renderResponse, renderTrouble)
import Thena.View (developmentView, focusAddress, machineView)
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

data St = St
  { stTurns       :: [Turn]  -- ^ forward chronological — oldest first, an
                              -- append-only document, his correction 2026-09-29
  , stInput       :: Editor Text Name
  , stSession     :: Session
  , stTheme       :: Theme
  , stFoldOn      :: Bool
  , stDropdown    :: Maybe LoadDropdown
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
  , (attrName "accent.output",  ink (themeRepl th))
  , (attrName "dropdown",          surface (themePopup th) (themeInk th))
  , (attrName "dropdown.selected", surface (themePopup th) (themeRepl th))
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
draw st = dropdownLayer st <> [hBox [replColumn, gapH, sideColumn]]
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
    -- and adding the editor's own cursor column (from 'getCursorPosition')
    -- gives the caret's real screen column directly, no offset to remember.
    inputLine = str "❯ " <+> reportExtent Input (renderEditor (str . concatMap Text.unpack) True (stInput st))

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
    -- **The edge bar sits outside the 'viewport', not inside it.** 'fill'
    -- is infinite in both directions; a 'Vertical' viewport has to know
    -- its content's real height to manage a scroll offset, and refuses at
    -- runtime — "tried to embed an infinite-height widget in vertical
    -- viewport" — if anything inside it reports infinite height, which
    -- 'fill' always does regardless of 'hLimit' pinning its width. Only
    -- the scrollable part (title + content) goes inside the viewport; the
    -- edge is a plain sibling, sized by the outer box like any other
    -- widget.
    pane key vp content =
      clickable vp $
        hBox
          [ withAttr (attrName ("edge." <> key)) (hLimit 1 (fill '▎'))
          , viewport vp Vertical $
              vBox
                [ withAttr (attrName ("title." <> key)) (padLeftRight 1 (str key))
                , content
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
dropdownLayer st = case (stDropdown st, stInputExtent st) of
  (Just ld, Just inputExt) -> [translateBy (Location (col, row)) (renderDropdown ld)]
    where
      paneExt = case stPaneExtent st of
        Just p  -> p
        Nothing -> inputExt
      -- | The caret's own screen column: the editor's left edge plus the
      -- cursor's column within it — "follows my caret" means the *caret*,
      -- not just wherever the input box happens to start, which only
      -- coincide while typing at the end.
      caretCol   = locationColumn (extentUpperLeft inputExt) + snd (getCursorPosition (stInput st))
      -- | The widget sits one marker-width left of the caret, so the entry
      -- *text* lands under it — the rows all lead with a two-column marker
      -- (see 'dropdownSelected'/'dropdownPlain'), and anchoring the widget
      -- edge itself would leave every name that width too far right.
      col        = max 0 (caretCol - dropdownMarkerWidth)
      inputRow   = locationRow (extentUpperLeft inputExt)
      paneRow    = locationRow (extentUpperLeft paneExt)
      paneHeight = snd (extentSize paneExt)
      depthFrac :: Double
      depthFrac = if paneHeight <= 0 then 0 else fromIntegral (inputRow - paneRow) / fromIntegral paneHeight
      dropdownHeight = length (ldEntries ld)
      row = if depthFrac > 0.8 then inputRow - dropdownHeight else inputRow + 1
  _ -> []

renderDropdown :: LoadDropdown -> Widget Name
renderDropdown (LoadDropdown entries selected) =
  withAttr (attrName "dropdown") (vBox (zipWith renderRow [0 :: Int ..] entries))
  where
    renderRow i name
      | Just i == selected = withAttr (attrName "dropdown.selected") (str (dropdownSelected <> name))
      | otherwise           = str (dropdownPlain <> name)

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
  case stDropdown st of
    -- | Enter accepts the arrow-selected candidate into the input instead of
    -- submitting — his spec: "Enter selects it." Only fires once an arrow
    -- key has actually picked something; with the dropdown merely open and
    -- nothing selected, Enter still runs the line as typed.
    Just (LoadDropdown entries (Just i)) | i < length entries -> do
      let line = concatMap Text.unpack (getEditContents (stInput st))
          line' = replacePathPrefix line (entries !! i)
      put st { stInput = E.editorText Input (Just 1) (Text.pack line') }
      refreshDropdown
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
  case stDropdown st of
    -- | "Esc leaves the dropdown (arrow goes away) but leaves it open" —
    -- his spec exactly: clears the arrow-selection only, the candidate list
    -- stays up. With no selection to clear, Esc keeps its ordinary meaning.
    Just ld@(LoadDropdown _ (Just _)) -> put st { stDropdown = Just ld { ldSelected = Nothing } }
    _ -> halt
handleEventInner ev@(VtyEvent (V.EvKey V.KDown [])) = navigateDropdown moveDown ev
handleEventInner ev@(VtyEvent (V.EvKey V.KUp []))   = navigateDropdown moveUp ev
handleEventInner (VtyEvent (V.EvKey (V.KChar '\t') [])) = completeLoadPath
handleEventInner (MouseDown n V.BScrollUp _ _) = vScrollBy (viewportScroll n) (-1)
handleEventInner (MouseDown n V.BScrollDown _ _) = vScrollBy (viewportScroll n) 1
handleEventInner ev = Brick.zoom stInputL (handleEditorEvent ev) >> followInput >> refreshDropdown

-- | Arrow-key navigation only takes over the keypress while the dropdown is
-- actually showing candidates — otherwise the original event falls through
-- to the editor as normal (a no-op either way, on a single-line editor).
navigateDropdown :: (Maybe Int -> Int -> Int) -> BrickEvent Name e -> EventM Name St ()
navigateDropdown move ev = do
  st <- get
  case stDropdown st of
    Just ld@(LoadDropdown entries sel) | not (null entries) ->
      put st { stDropdown = Just ld { ldSelected = Just (move sel (length entries)) } }
    _ -> Brick.zoom stInputL (handleEditorEvent ev) >> followInput

moveDown :: Maybe Int -> Int -> Int
moveDown Nothing  _ = 0
moveDown (Just i) n = min (n - 1) (i + 1)

moveUp :: Maybe Int -> Int -> Int
moveUp Nothing  n = n - 1
moveUp (Just i) _ = max 0 (i - 1)

-- | Appends one completed turn and scrolls the repl viewport to show it —
-- the document grows downward and the view always follows, same as any
-- terminal. Nothing did this before this session; 'HistoryVP' just stayed
-- wherever it started, which is exactly his bug report ("it doesn't scroll
-- so the end of the output is at the bottom... no terminal behaves like
-- that").
appendTurn :: St -> Maybe String -> [String] -> EventM Name St ()
appendTurn st prompt output = do
  put st { stInput = emptyInput, stTurns = stTurns st <> [Turn prompt output], stDropdown = Nothing }
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
