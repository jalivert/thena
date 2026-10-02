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
  ItemTheorem n ty body ->
    [ n ++ " : " ++ renderSurface ty
    , n ++ " = " ++ renderSurface body
    ]
  ItemData d -> printData d
  -- A top-level block is a term's @do@ and prints as one, so there is one
  -- printer for it rather than a second that has to agree with the first.
  ItemBlock is -> [renderSurface (SurfaceDo is)]
  ItemGrammar b -> lines (printBlock b)

-- | A datatype declaration.
--
-- A datatype with no constructors still ends in @where@ — @data Empty : Type
-- where@ is in the prelude — so the header is printed the same way whether or
-- not anything follows it.
printData :: SurfaceData -> [String]
printData d =
  ("data " ++ nm ++ params ++ " : " ++ renderSurface (surfaceDataType d) ++ " where")
    : [ "  " ++ c ++ " : " ++ renderSurface t
      | SurfaceConstructor c t <- surfaceDataConstructors d
      ]
  where
    nm = surfaceDataName d
    params = concat [" (" ++ x ++ " : " ++ renderSurface t ++ ")" | (x, t) <- surfaceDataParameters d]

-- | A surface module: its header, then its items, one blank line apart.
printSurfaceModule :: String -> [Item] -> String
printSurfaceModule nm items =
  unlines (["module " ++ nm ++ " where", ""] ++ intercalate [""] (map printItem items))
