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

import Thena.Core.Term (GlobalName (..), nameDotted)
import Thena.Driver (Item (..))
import Thena.Surface.Concrete
  ( Surface (..)
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
  ItemOpen g -> ["open " ++ nameDotted g]
  -- **The block, indented, with its items a blank line apart** — the layout the
  -- parser reads back (MS10 phase 254). The name is written as it was: a
  -- namespace's path is relative to the one it sits in, so what the item holds
  -- is what goes back on the line.
  ItemNamespace g is ->
    ("namespace " ++ nameDotted g ++ " where")
      : map ("  " ++) (intercalate [""] (map printItem is))

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
printSurfaceModule :: String -> [Item] -> String
printSurfaceModule nm items =
  unlines (["module " ++ nm ++ " where", ""] ++ intercalate [""] (map printItem items))
