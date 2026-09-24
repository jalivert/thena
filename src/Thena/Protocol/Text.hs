-- | A stored project, written back as text (MS7 phase 112c).
--
-- **The other half of done-when 4**, and the reason it exists is his standing
-- constraint that the textual medium is never discriminated against JSON
-- (@discussion\/editor-protocol.md@ §4 A3): a project must be writable and
-- readable as text, so that a CLI editor can store text and so that someone can
-- work on a project from VS Code.
--
-- **This module is small on purpose.** Everything that can be printed from the
-- syntax alone is in "Thena.Syntax.Print", beside the parser it inverts; what is
-- left here is the part that needs 'Thena.Driver.Item' — a module's contents —
-- and the framing of a file.
--
-- **What text promises is weaker than what JSON promises, and the difference is
-- worth knowing.** JSON round-trips the /tree/. Text round-trips the /session/:
-- a @language@, @context@ or @judgment@ block carries the source line each of
-- its productions and rules was written on, and a printer that lays a block out
-- canonically cannot reproduce them. Nothing outside
-- "Thena.Language.Reader" reads those numbers, so they do not reach a session —
-- but they are in the tree, so tree equality is not the right claim to make for
-- this direction.
module Thena.Protocol.Text
  ( printItem
  , printSurfaceModule
  , printStoredModule
  , printProject
  ) where

import Data.List (intercalate)

import Thena.Driver (Item (..))
import Thena.Protocol.Project (Project (..), StoredModule (..))
import Thena.Surface.Concrete
  ( Surface (..)
  , SurfaceConstructor (..)
  , SurfaceData (..)
  )
import Thena.Syntax.Print (printBlock, printRuleFile, renderSurface)

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

-- | A stored module as the file it would be written to.
--
-- The extension is what says which kind it is, exactly as it does for a project
-- written by hand.
printStoredModule :: Int -> StoredModule -> (FilePath, String)
printStoredModule i m = case m of
  StoredSurface nm items -> (name ".thena", printSurfaceModule nm items)
  StoredRules nm desc ds -> (name ".thena.rules", printRuleFile nm desc ds)
  where
    name ext = pad (show i) ++ ext
    pad s = replicate (max 0 (3 - length s)) '0' ++ s

-- | A whole project, as the text files it would be written to, in load order.
--
-- **Numbered, as the JSON storage is**, and for the same reason: the order is
-- load-bearing and an identifier may hold characters no file system will take
-- (§2.6). The module's real name is inside the file, on its header line.
printProject :: Project -> [(FilePath, String)]
printProject p = zipWith printStoredModule [0 ..] (projectModules p)
