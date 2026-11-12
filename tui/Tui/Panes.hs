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
  , moduleRows
  , FileKind (..)
  , outputRows
  , paneRowWidget
  ) where

import Data.List (intercalate, nub, sort)

import Brick (Widget, strWrapWith, withAttr)
import Brick.AttrMap (attrName)
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
data PaneRow
  = Heading String (Maybe Int)
    -- ^ a group's name, and how many are in it where that is worth saying.
    -- 'Nothing' is the output pane's own heading: the line in focus, which is
    -- one line and does not need counting.
  | Entry String
  | Detail String
  deriving (Eq, Show)

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
globalRows :: [(String, [String])] -> [PaneRow]
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
moduleRows :: [(String, Maybe FilePath)] -> [(FileKind, FilePath)] -> [PaneRow]
moduleRows modules files =
  concat
    [ Heading "modules" (Just (length modules))
        : concat [ Entry m : [Detail f | Just f <- [file]] | (m, file) <- modules ]
    | not (null modules)
    ]
    <> group "rule bases" ARuleBase
    <> group "shipped with thena" AShippedFile
    <> group "other files read" AnotherFile
  where
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
outputRows :: Maybe String -> [String] -> [PaneRow]
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
paneRowWidget :: PaneRow -> Widget n
paneRowWidget row = case row of
  Heading label count ->
    withAttr (attrName "pane.heading") (wrapped (label <> maybe "" (\n -> "  " <> show n) count))
  Entry t -> wrapped ("  " <> t)
  Detail t -> withAttr (attrName "pane.detail") (wrapped ("    " <> t))
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
