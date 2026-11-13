-- | The three panes of the second column — `~z5dmq`'s content.
--
-- **Every function here takes plain data and returns plain rows**, so that
-- what a pane says is decided without a 'Thena.Driver.Session' and without a
-- terminal. "Tui.App" does the session reads and hands the results in; this
-- module decides the rows and draws one. The point is that the drawing suite
-- can hold all of it to its text, which it does.
module Tui.Panes
  ( PaneRow (..)
  , paneWrap
  , globalRows
  , ModuleMark (..)
  , markGlyph
  , markColumns
  , wideGlyphs
  , ModuleEntry (..)
  , moduleRows
  , FileKind (..)
  , outputRows
  , paneRowWidget
  ) where

import Data.List (intercalate, nub, sort)

import Brick (Widget, clickable, strWrapWith, withAttr)
import Brick.AttrMap (attrName)
import Graphics.Text.Width (safeWcwidth)
import Text.Wrap
  ( FillStrategy (FillIndent)
  , WrapSettings (..)
  , defaultWrapSettings
  )

-- | One row of a list pane.
--
-- **Three kinds and no more**, because a pane of this column is a list with
-- headings: a 'Heading' names a group and counts it, an 'Entry' is a thing in
-- that group, and a 'Detail' is the one line of small print an entry is
-- allowed — a module's file, say. 'Tui.App' gives each its attribute.
data PaneRow n
  = Heading String (Maybe Int)
    -- ^ a group's name, and how many are in it where that is worth saying.
    -- 'Nothing' is the output pane's own heading: the line in focus, which is
    -- one line and does not need counting.
  | Entry String
  | Detail String
  | Tap n String
    -- ^ **an entry that answers to a click** — `~nf5tx`, the ⚠️ a module's
    -- unfinished list hangs off. **The whole row is the target, not the glyph**:
    -- a one-cell target is what `~rr8bx` was reported as, and the row carries
    -- the symbol anyway.
    --
    -- **The name is the row's own, not the pane's.** brick dispatches a click to
    -- the last extent reported under the pointer, and a 'clickable' inside the
    -- pane is reported after the pane itself — so a row wins over the pane
    -- without the pane's own accent-bar drag losing anything, that bar being
    -- outside the viewport this row is in.
  deriving (Eq, Show, Functor)

-- The 'Functor' is how a row reaches 'Tui.App''s own 'Name' without this
-- module ever mentioning one: 'moduleRows' names a row by the module it is
-- about, and the caller maps that into whatever it calls a clickable thing.
-- Keeping 'Name' out of here is what lets the drawing suite hold these
-- functions to their text with no brick resource type in scope.

-- | **The globals pane** — `~5d35q`, his request of 2026-11-11: *"a pane that
-- shows all the 'globals' in scope. In other words everything that is either
-- imported or certified."*
--
-- Groups in the order given, each with its count, and an empty group is
-- dropped rather than drawn as a heading with nothing under it. **Names are
-- sorted and deduplicated inside a group**: a proof suspended and resumed is
-- two runs under one name ('Thena.Driver.provedSlices'), and a pane listing a
-- theorem twice would be reporting the engine's bookkeeping rather than what
-- is in scope.
globalRows :: [(String, [String])] -> [PaneRow n]
globalRows groups =
  concat
    [ Heading label (Just (length names)) : map Entry names
    | (label, raw) <- groups
    , let names = sort (nub raw)
    , not (null names)
    ]

-- | **The modules pane** — `~t7wc8`, his request: *"a pane that shows every
-- file that is imported and consulted (every module)."*
--
-- Takes the modules that are in, newest first, each with the file it was read
-- from where there is one, and every other file the session read with what
-- kind it is. **The split is by kind and not by `import` versus `consult`**,
-- which is not a session read: 'Thena.Driver.moduleImports' and
-- 'moduleConsults' take a module's items, not a session. A @.thena.rules@ file
-- in the list got there by being consulted, which is the honest half of the
-- distinction and the half that is visible from here.
--
-- **A module with no file of its own is the prelude**, which arrives with the
-- session rather than being read as a module, and it is shown without one
-- rather than left out.
-- | **Each module says whether it came in whole** — `~nf5tx`, his instruction
-- of 2026-11-13, now that MS12 phase 315 lets a module come in partly:
-- /"I want the 'modules' pane to use these symbols ✅ ⚠️ ❌ next to each module
-- to show whether that import was successful."/ See 'ModuleMark' for what each
-- one means and 'ModuleEntry' for what a row is drawn from.
moduleRows :: [ModuleEntry] -> [(FileKind, FilePath)] -> [PaneRow String]
moduleRows modules files =
  concat
    [ Heading "modules" (Just (length modules)) : concatMap moduleGroup modules
    | not (null modules)
    ]
    <> group "rule bases" ARuleBase
    <> group "shipped with thena" AShippedFile
    <> group "other files read" AnotherFile
  where
    -- | A module's own row, its file, and — when it is unfolded — what did not
    -- go in. **Only a ⚠️ or ❌ row is a 'Tap'**: a whole module has nothing to
    -- unfold, and a row that looks clickable and does nothing is worse than one
    -- that does not look it.
    moduleGroup me =
      row : [Detail f | Just f <- [meFile me]] <> unfolded
      where
        row
          | meMark me == AllIn = Entry labelled
          | otherwise = Tap (meName me) labelled
        labelled = markGlyph (meMark me) <> " " <> meName me
        -- | **The first is the root and the rest are pending** — the engine's
        -- ruling of 2026-11-11, /"one failure and forty-seven pending, not
        -- forty-eight warnings"/. The root's own answer is shown; the rest are
        -- named and nothing is said about why, **because nothing worked out
        -- why** — the loader tries every later declaration and records what
        -- does not go through, so a reason for the second would be an invention.
        unfolded
          | not (meOpen me) = []
          | otherwise = case meUnfinished me of
              [] -> []
              (name, why) : pending ->
                Detail (name <> " did not go in:")
                  : map (Detail . ("  " <>)) why
                  <> [Detail (nm <> " is pending") | (nm, _) <- pending]
    group label kind =
      let ps = sort [shorten kind p | (k, p) <- files, k == kind]
       in concat [Heading label (Just (length ps)) : map Entry ps | not (null ps)]
    -- **Thena's own two files are shown by their tail and nothing else.**
    -- They live wherever the package was installed —
    -- @~\/.cabal\/share\/aarch64-osx-ghc-9.12.4-6f4d\/thena-0.1.0.0\/prelude\/prelude.thena@
    -- is a real one — and a pane this wide would show the install path and
    -- clip the filename, which is the half that says which file it is. His
    -- own paths are never shortened: those he typed, and they are short.
    shorten AShippedFile = tailSegments 2
    shorten _ = id
    tailSegments n = intercalate "/" . reverse . take n . reverse . splitOn '/'
    splitOn c t = case break (== c) t of
      (a, []) -> [a]
      (a, _ : rest) -> a : splitOn c rest

-- | What a file in 'Thena.Driver.filesRead' is, as far as a frontend can
-- tell: Thena's own prelude and standard base, a rule base somebody
-- consulted, or anything else — which is a module's own file, and is named by
-- its module in the modules group rather than repeated here.
-- **Not 'Thena.Driver.LoadKind' wearing another name.** That one says what a
-- path is — a rule base, a proof module, a script — and 'Tui.App' asks it. This
-- one says which group of this pane the file belongs in, which is a question
-- about the pane: Thena's own prelude is a proof module and does not belong
-- beside his, and a module's own file is named under its module rather than
-- twice.
data FileKind = AShippedFile | ARuleBase | AModuleFile | AnotherFile
  deriving (Eq, Show)

-- | **How much of a module went in** — `~nf5tx`, and the three states are the
-- three the engine can actually distinguish, measured under a pty on
-- 2026-11-13 rather than assumed:
--
--   * 'AllIn' — @moduleWhole@: it is in and nothing was left behind.
--   * 'SomeIn' — it is in, @modulePartly@ answers 'Just', and it did declare
--     something. The usual partial import.
--   * 'NoneIn' — it is in the list, @modulePartly@ answers 'Just', and it
--     declared **nothing at all**. @test\/modules\/AllBad.thena@, whose every
--     item fails, is still a loaded module with an empty namespace.
--
-- **A module whose file does not exist is not one of these**, because it never
-- reaches the list: the import answers /openFile: does not exist/ and the
-- session is unchanged. There is nothing on screen to mark.
--
-- **An empty module is 'AllIn', not 'NoneIn'.** The 'NoneIn' test is only ever
-- reached when @modulePartly@ already said something failed, so a module that
-- legitimately declares nothing cannot fall into it.
data ModuleMark = AllIn | SomeIn | NoneIn
  deriving (Eq, Show)

-- | The symbol for a mark — his three, 2026-11-13.
--
-- **THE VARIATION SELECTOR IS DELIBERATELY ABSENT. PUTTING IT BACK LOSES THE
-- MODULE'S NAME.** The emoji spelling of the warning sign is U+26A0 followed by
-- U+FE0F, and with it the row drew as @⚠@ and nothing else — the name never
-- appeared at all. Measured under a pty on 2026-11-13; **the cause was not
-- chased and is not claimed here**, only that the selector is what the row's
-- disappearance turns on. U+26A0 alone draws fine. **Do not "tidy" the spelling
-- back to the emoji one.**
--
-- **THE COLOURED ⚠️ IS THE EMOJI SPELLING, U+26A0 PLUS U+FE0F** — his
-- instruction, 2026-11-13: /"I like the colored version. The glyph version is
-- not visible enough."/ The selector is what asks the terminal for the coloured
-- presentation rather than the thin outline.
--
-- **An earlier note here said the selector lost the module's name. It was
-- wrong and the cause was `pyte`, the probe's own terminal emulator.** Read
-- straight off the pty as bytes, the TUI emits @⚠️ test.modules.PartlyGood@ —
-- selector and name both — and it always did. **Do not re-draw a conclusion
-- about a glyph from a reconstructed screen**; read what was written.
--
-- **WHAT IS REAL IS THE WIDTH, AND IT IS WHY 'wideGlyphs' EXISTS** — his report
-- the same day, /"the new symbol for ✅ next to the prelude moves the accent bar
-- of the next pane to the right."/ vty's built-in table calls all three of these
-- one column; a terminal draws them in two. See 'wideGlyphs'.
markGlyph :: ModuleMark -> String
markGlyph m = case m of
  AllIn -> "\x2705"
  SomeIn -> "\x26A0\xFE0F"
  NoneIn -> "\x274C"

-- | **The code points this pane needs vty to call two columns wide** —
-- `~8ztt3`. @Tui.App.declareWideGlyphs@ installs exactly these before it makes
-- a vty, and nothing else in the TUI declares a width.
--
-- **Why it is needed.** @Graphics.Text.Width.safeWcswidth@ — the function vty
-- lays cells out with — answers **1** for U+2705 ✅, U+26A0 ⚠ and U+274C ❌
-- alike: vty's built-in table predates the Unicode revision that made the
-- emoji-presentation ones Wide. A terminal spends **two** cells on them, so it
-- advances its cursor two where vty budgeted one, and **every cell to the right
-- of the glyph on that row is shoved along by one** — the neighbouring pane's
-- accent bar included. Measured under a pty: the ✅ and ❌ rows put that bar at
-- column 113 where every other row had it at 112, and at 112 once declared.
--
-- **Padding the glyph does not fix it and was tried.** The terminal advances two
-- columns for the wide character and writes whatever follows at the next
-- position, so a trailing space is shoved along with the rest. The shift starts
-- at the glyph and nothing after it can absorb it.
--
-- **U+FE0F is not in the list and must not be**: a variation selector is zero
-- columns in both reckonings, which is what makes @⚠️@ measure two once U+26A0
-- does.
wideGlyphs :: [Int]
wideGlyphs = [0x2705, 0x26A0, 0x274C]

-- | How many columns a mark takes **once 'wideGlyphs' has been declared**.
--
-- **The one invariant worth holding**: every mark is two, so the module names
-- line up down the pane and no row crosses into the pane beside it. The drawing
-- suite checks this rather than calling 'safeWcwidth' on the glyphs directly —
-- that would answer for an undeclared vty and report one, which is the state no
-- running TUI is ever in.
markColumns :: ModuleMark -> Int
markColumns = sum . map column . markGlyph
  where
    column c
      | fromEnum c `elem` wideGlyphs = 2
      | otherwise = max 0 (safeWcwidth c)

-- | What a module's row is drawn from.
--
-- **Plain data, like everything else here**: 'Tui.App' asks the session which
-- module is which and flattens the engine's 'Thena.Driver.Unfinished' into
-- lines, so this module stays a function from data to rows and the drawing
-- suite can hold all of it to its text.
data ModuleEntry = ModuleEntry
  { meName :: String
    -- ^ the module as 'Thena.Driver.moduleText' spells it. **Also the row's
    -- click name**, which is why it is a 'String' and not a 'ModuleName'.
  , meFile :: Maybe FilePath
    -- ^ 'Nothing' for the prelude, which arrives with the session.
  , meMark :: ModuleMark
  , meOpen :: Bool
    -- ^ whether its unfinished list is unfolded. **Clicking the row toggles
    -- this** — his instruction: /"when I click again, it hides that list"/.
  , meUnfinished :: [(String, [String])]
    -- ^ what did not go in, **in file order**: what the item would have
    -- declared, and the lines of the answer its own run gave. Only the first
    -- entry's lines are drawn; see 'moduleRows'.
  }
  deriving (Eq, Show)

-- | **The output pane** — `~wx6m3`, his request: *"That stuff that you show me
-- at the bottom of the screen when I do @:show o@ in a script-mode? That goes
-- into a new pane also."*
--
-- The line in focus as a heading, then everything it answered. **Nothing is
-- capped here and that is the point of the move**: the pane's foot could show
-- four lines, so `:show` on a proved theorem was cut off mid-term. A line that
-- answered nothing gets its heading and no rows, rather than a row saying so —
-- the pane is then visibly empty, which is what "this line said nothing" looks
-- like.
outputRows :: Maybe String -> [String] -> [PaneRow n]
outputRows Nothing _ = []
outputRows (Just line) out = Heading line Nothing : map Entry out

-- | One row of a list pane, with its attribute and its indent — the whole of
-- the second column's drawing, since 'Tui.Panes' decided the text.
--
-- **Three indents and they say the structure**: a heading at the pane's own
-- margin, a thing in that group one step in, and an entry's small print one
-- step further. Dim for both the heading and the small print, the accents
-- being the panes' own.
-- **Polymorphic in the name on purpose**: it reports no extent and owns no
-- viewport, so it has no business naming one — and the drawing suite can then
-- draw it without a 'Name' in scope.
--
-- **A row wraps rather than clipping** — `~r4gvd`, his report of 2026-11-12: /"the
-- 'output' is clipping horizontally. Not great, I can't read the message."/
-- These panes are a quarter of the screen each and the output pane's heading
-- is a whole line of someone's proof-script, so a row running past the pane's
-- edge is the ordinary case rather than the exception, and what was off the
-- right edge was simply gone — no marker, no scroll that reaches it. See
-- 'paneWrap' for the indent a continuation takes.
paneRowWidget :: Ord n => PaneRow n -> Widget n
paneRowWidget row = case row of
  Heading label count ->
    withAttr (attrName "pane.heading") (wrapped (label <> maybe "" (\n -> "  " <> show n) count))
  Entry t -> wrapped ("  " <> t)
  Detail t -> withAttr (attrName "pane.detail") (wrapped ("    " <> t))
  Tap n t -> clickable n (wrapped ("  " <> t))
  where
    wrapped = strWrapWith paneWrap

-- | How a pane's row wraps.
--
-- **A continuation line keeps its row's own indent and takes two columns
-- more**, so it sits under its row's text and inside it: an entry's text
-- starts at column 2 and its continuations at column 4, a heading's at 0 and 2.
-- That is 'preserveIndentation' for the row's own step and 'FillIndent' 2 for
-- the hang — word-wrap puts the preserved indentation before the fill, so the
-- two compose rather than fighting. **A continuation of a heading is dim like
-- the heading it belongs to**, which is what keeps it from reading as an entry
-- under it: the attribute is the row's, not the line's.
--
-- **A word longer than the pane breaks mid-word, deliberately.** Nothing here
-- is prose: a module path, a global's dotted name and a term are each one
-- unbreakable word most of the time, and refusing to break them is the clip
-- this is here to fix.
paneWrap :: WrapSettings
paneWrap =
  defaultWrapSettings
    { preserveIndentation = True
    , breakLongWords = True
    , fillStrategy = FillIndent 2
    }
