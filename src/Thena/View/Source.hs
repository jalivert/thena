-- | A module, written back as text (MS7 phase 112c, cut down at 122).
--
-- **Text is the only stored form** — his ruling of 2026-09-27. It used to be
-- one of two, and this module used to carry a whole project's worth of files
-- (@printStoredModule@, @printProject@) beside a JSON spelling of the same
-- trees. The JSON went and the project manifest went with it, so what is left
-- is a module and the items in it.
--
-- **This module is small on purpose.** Everything that can be printed from the
-- syntax alone is in "Thena.Syntax.Print", beside the parser it inverts; what
-- is left here is the part that needs 'Thena.Driver.Item' — a module's
-- contents — which is why it sits above the driver rather than in "Print".
--
-- **What text round-trips is the /session/, not the tree.** A @language@,
-- @context@ or @judgment@ block carries the source line each of its
-- productions and rules was written on, and a printer that lays a block out
-- canonically cannot reproduce them. Nothing outside "Thena.Language.Reader"
-- reads those numbers, so they never reach a session — but they are in the
-- tree, so tree equality is not the claim to make for this direction.
module Thena.View.Source
  ( printItem
  , printSurfaceModule
  ) where

import Data.List (intercalate)

import Thena.Core.Term (GlobalName (..), Opened (..), nameDotted)
import Thena.Driver (Item (..), moduleHiding, moduleText)
import Thena.Surface.Concrete
  ( Surface (..)
  , Reach (..)
  , SurfaceConstructor (..)
  , SurfaceData (..)
  )
import Thena.Syntax.Print (printBlock, renderSurface)

-- | One top-level item.
printItem :: Item -> [String]
printItem i = case i of
  -- **Dotted, which is a name's whole spelling** (MS10 phase 243). The
  -- shortest ending that re-resolves is the printer's policy where a scope is
  -- known, and with nothing open it is this.
  ItemTheorem n ty body ->
    [ nameDotted n ++ " : " ++ renderSurface ty
    , nameDotted n ++ " = " ++ renderSurface body
    ]
  ItemData d -> printData d
  -- A top-level block is a term's @do@ and prints as one, so there is one
  -- printer for it rather than a second that has to agree with the first.
  ItemBlock is -> [renderSurface (SurfaceDo is)]
  ItemGrammar b -> lines (printBlock b)
  -- **One line, and the name as written** (MS10 phase 248). An @open@ is a
  -- declaration like any other and the printed module has to carry it: a file
  -- printed without its opens would not re-read.
  ItemOpen o -> [opens [o]]
  -- **One line, and the module's name as written** (MS11 phase 273). A consult
  -- declares nothing, so a file printed without it would read back and then be
  -- searched against the wrong bases — and without its @public@ (MS11 phase
  -- 288) a file that read back would stop handing the base on.
  -- **And the block it states, where it states one** (MS11 phase 292), printed
  -- as a @namespace@ block's is, since that is the layout the parser reads
  -- back: a consult printed without its block would put the base in the pool
  -- for the whole file.
  ItemConsult r m ds -> reaches (reaching r ++ "consult " ++ moduleText m) ds
  -- **The same, for the same reason** (MS11 phase 274): a file printed without
  -- its imports would read back and then not elaborate at all.
  ItemImport r m ds -> reaches (reaching r ++ "import " ++ moduleText m) ds
  -- **Never printed here** (MS11 phase 285) — it is the header's and
  -- 'printSurfaceModule' puts it back there. A module printed item by item
  -- without the header has no place for it.
  ItemExporting _ -> []
  ItemHiding _    -> []
  -- **The block, indented, with its items a blank line apart** — the layout the
  -- parser reads back (MS10 phase 254). The name is written as it was: a
  -- namespace's path is relative to the one it sits in, so what the item holds
  -- is what goes back on the line.
  -- **The open and the first line of the declaration it reaches are one line**
  -- — which is how it was written, and what reads back: @in@ takes a
  -- declaration, so a newline after it would start a new one (MS10 phase 254).
  -- **The word, then the declaration it marks, on one line** (MS11 phase 286) —
  -- which is how it was written, and what reads back: @private@ takes a
  -- declaration, so a newline after it would start a new one.
  ItemPrivate is -> case concatMap printItem is of
    first : rest -> ("private " ++ first) : rest
    []           -> ["private"]
  ItemOpenIn os is -> case concatMap printItem is of
    first : rest -> (opens os ++ " in " ++ first) : rest
    []           -> [opens os ++ " in"]
  ItemNamespace g is ->
    ("namespace " ++ nameDotted g ++ " where")
      : map ("  " ++) (intercalate [""] (map printItem is))

-- | An @import@ or @consult@ line, with the block it reaches under it (MS11
-- phases 291 and 292).
--
-- **One printer for both acts again**, because how far an act reaches is said
-- the same way by both — and it is a @namespace@ block's layout, two spaces in
-- with the items a blank line apart, because that is what reads back.
reaches :: String -> Maybe [Item] -> [String]
reaches line Nothing   = [line]
reaches line (Just is) =
  (line ++ " where") : map ("  " ++) (intercalate [""] (map printItem is))

-- | The word in front of an @import@ or a @consult@ that travels (MS11 phase
-- 288).
--
-- **One printer for both acts**, because @public@ means the same thing in front
-- of either: 'Thena.Surface.Concrete.Reach' is an attribute of the act.
reaching :: Reach -> String
reaching Own    = ""
reaching Public = "public "

-- | The @open@ line of an @open … in@, without its @in@ (MS10 phase 254).
--
-- **Only the plain form takes several namespaces**, so the restriction belongs
-- to whichever one carries it and there is never more than one.
opens :: [Opened] -> String
opens os =
  "open " ++ unwords [ intercalate "." (openedPath o) | o <- os ]
          ++ concatMap restriction os

-- | What an @open@ said about which names it brings in, written back (MS10
-- phase 254).
--
-- **A line says one of these or none**, so there is nothing to order here.
restriction :: Opened -> String
restriction o
  | Just ws <- openedOnly o            = " ( " ++ unwords ws ++ " )"
  | ws@(_ : _) <- openedHiding o        = " hiding ( " ++ unwords ws ++ " )"
  | rs@(_ : _) <- openedRenaming o      =
      " renaming ( " ++ unwords [ a ++ " -> " ++ b | (a, b) <- rs ] ++ " )"
  | otherwise                           = ""

-- | A datatype declaration.
--
-- A datatype with no constructors still ends in @where@ — @data Empty : Type
-- where@ is in the prelude — so the header is printed the same way whether or
-- not anything follows it.
printData :: SurfaceData -> [String]
printData d =
  ("data " ++ nm ++ params ++ " : " ++ renderSurface (surfaceDataType d) ++ " where")
    : [ "  " ++ nameDotted (GlobalName cps c) ++ " : " ++ renderSurface t
      | SurfaceConstructor cps c t <- surfaceDataConstructors d
      ]
  where
    nm = nameDotted (GlobalName (surfaceDataSteps d) (surfaceDataName d))
    params = concat [" (" ++ x ++ " : " ++ renderSurface t ++ ")" | (x, t) <- surfaceDataParameters d]

-- | A surface module: its header, then its items, one blank line apart.
-- **An @exporting ( … )@ clause goes back on the header line** (MS11 phase 285):
-- the grammar admits it only there, so printing it as a declaration would print
-- a file that does not read back. It is carried as an item because that is where
-- the load doors can reach it — 'Thena.Driver.ItemExporting' says why.
printSurfaceModule :: String -> [Item] -> String
printSurfaceModule nm items =
  unlines ((["module " ++ nm ++ clause ++ " where", ""]) ++ body)
  where
    -- **Either word, and never both** (MS11 phase 290): the grammar has one
    -- slot on the header, so at most one of these items is in the list.
    clause = case ([ es | ItemExporting es <- items ], moduleHiding items) of
      (es : _, _)  -> " exporting ( " ++ unwords (map nameDotted es) ++ " )"
      (_, hs@(_ : _)) -> " hiding ( " ++ unwords (map nameDotted hs) ++ " )"
      _            -> ""
    body = intercalate [""] [ printItem i | i <- items, notHeader i ]
    notHeader (ItemExporting _) = False
    notHeader (ItemHiding _)    = False
    notHeader _                 = True
