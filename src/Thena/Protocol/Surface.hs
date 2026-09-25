-- | What a surface term looks like to the editor (MS7 phase 115h;
-- @discussion\/editor-display.md@ §8: "close to Core, and not the same").
--
-- **Nothing here needs the system.** Every other display in this milestone
-- exists because the server resolves something a bare tree cannot say —
-- which variable a name is, a normalised level, an object term's
-- production. A 'Thena.Surface.Concrete.Surface' is pre-elaboration: a name
-- is exactly the identifier written, a universe is exactly the digits
-- written, an object region is exactly its text and splices. So
-- 'displaySurface' takes no grammars, no environment, and no counter — the
-- one thing that makes it unlike every module before it in this milestone,
-- and it follows from what @Surface@ already is rather than from a shortcut
-- taken here.
--
-- **No address, and that is §8's own ruling, not an omission.** The valuable
-- thing a surface display could add over Core's is the address of what an
-- elaborated node became in the development — the surface-to-DC link,
-- @discussion\/editor-protocol.md@ §7's provenance. §8 says outright: "this
-- design does not provide it." There being no addressing scheme here is
-- that decision, not a gap this phase left by accident.
--
-- **A @do@ block is its own written text, not a walked structure.**
-- @SurfaceDo@ carries @['Thena.Instral.Concrete.RawInstr']@, the same
-- as-written instral syntax a rule file is made of. 'Thena.Syntax.Print' —
-- phase 112c, the as-written trees printed back as text — already round-trips
-- it (its own header: "what is here round-trips… `Thena.Syntax.Parser` on
-- this output gives the same tree"), so this is exact, not approximate.
-- Breaking it into the same kind of structure 115d gave @instral@ proper is
-- comparable in size to that phase and is left for one of its own, should it
-- ever be wanted here.
--
-- **Used beyond its own pane, immediately.** 'Thena.Instral.Ops.VSurface'
-- carries a live elaboration focus, and 'Thena.Repl.renderValue' already
-- shows its content — 'Thena.Protocol.Instral.ValueView' had been showing
-- only its shape, on the mistaken belief that no surface printer existed.
-- 'Thena.Protocol.Instral.displayValue' calls 'displaySurface' to fix that,
-- which is why this module has no dependency on @Instral@ at all: @Instral@
-- depends on this one, not the other way round.
module Thena.Protocol.Surface
  ( SurfaceShape (..)
  , SurfaceBinding (..)
  , SurfaceArgView (..)
  , SurfacePieceView (..)
  , displaySurface
  ) where

import Data.List (intercalate)
import qualified Data.List.NonEmpty as NE

import Thena.Core.Term (Literal (..))
import Thena.Surface.Concrete
  ( ObjectPiece (..)
  , Plicity (..)
  , Surface (..)
  , SurfaceArg (..)
  , SurfaceBinder (..)
  )
import Thena.Syntax.Print (escapeChar, escapeString, rawInstruction)

-- | A surface node's shape — never what it looks like, the same restraint
-- 'Thena.Protocol.Display.Shape' keeps.
data SurfaceShape
  = ASurfaceName String
  | ASurfaceUniverse Int
  | ASurfaceUniverseOpen
  | ASurfaceLiteral String
  | ASurfacePlaceholder
  | ASurfaceHole String
  | ASurfaceObjectTerm String (Maybe String) [SurfacePieceView]
  | ASurfaceApplication SurfaceShape [SurfaceArgView]
  | ASurfaceFunction [SurfaceBinding] SurfaceShape
    -- ^ @λ@.
  | ASurfaceQuantifier [SurfaceBinding] SurfaceShape
    -- ^ @∀@.
  | ASurfaceArrow SurfaceShape SurfaceShape
  | ASurfaceLet String (Maybe SurfaceShape) SurfaceShape SurfaceShape
    -- ^ the bound name, its annotation if written, its value, its body.
  | ASurfaceAnnotation SurfaceShape SurfaceShape
  | ASurfaceElimination String [SurfaceShape] SurfaceShape [SurfaceShape] [SurfaceShape] SurfaceShape
    -- ^ the datatype named, the parameters, the motive, the methods, the
    -- indices, the target — 'Thena.Surface.Concrete.Surface'\'s own order.
  | ASurfaceDo String
    -- ^ the block's own written text — see the module header.
  deriving (Eq, Show)

-- | One bound name: its plicity, its name, and its type if it was written.
data SurfaceBinding = SurfaceBinding Plicity String (Maybe SurfaceShape)
  deriving (Eq, Show)

-- | One argument of a spine, and whether it was written in braces.
data SurfaceArgView = SurfaceArgView Plicity SurfaceShape
  deriving (Eq, Show)

-- | One piece of an object-language region: literal text, or a splice.
data SurfacePieceView
  = ASurfacePieceText String
  | ASurfacePieceSplice SurfaceShape
  deriving (Eq, Show)

displaySurface :: Surface -> SurfaceShape
displaySurface s = case s of
  SurfaceName x -> ASurfaceName x
  SurfaceUniverse l -> ASurfaceUniverse l
  SurfaceUniverseOpen -> ASurfaceUniverseOpen
  SurfaceLiteral l -> ASurfaceLiteral (literalText l)
  SurfacePlaceholder -> ASurfacePlaceholder
  SurfaceHole h -> ASurfaceHole h
  SurfaceObject lang prod ps -> ASurfaceObjectTerm lang prod (map piece ps)
  SurfaceApp f as -> ASurfaceApplication (displaySurface f) (map arg (NE.toList as))
  SurfaceLam bs b -> ASurfaceFunction (map binding (NE.toList bs)) (displaySurface b)
  SurfacePi bs b -> ASurfaceQuantifier (map binding (NE.toList bs)) (displaySurface b)
  SurfaceArrow a b -> ASurfaceArrow (displaySurface a) (displaySurface b)
  SurfaceLet x ty v b -> ASurfaceLet x (fmap displaySurface ty) (displaySurface v) (displaySurface b)
  SurfaceAnnot e ty -> ASurfaceAnnotation (displaySurface e) (displaySurface ty)
  SurfaceElim d ps mot ms is tgt ->
    ASurfaceElimination d (map displaySurface ps) (displaySurface mot)
      (map displaySurface ms) (map displaySurface is) (displaySurface tgt)
  SurfaceDo is -> ASurfaceDo (intercalate " ; " (map rawInstruction is))
  where
    piece p = case p of
      ObjectText t -> ASurfacePieceText t
      ObjectSplice e -> ASurfacePieceSplice (displaySurface e)
    arg (SurfaceArg pl t) = SurfaceArgView pl (displaySurface t)
    binding (SurfaceBinder pl x ty) = SurfaceBinding pl x (fmap displaySurface ty)

-- | Mirrors 'Thena.Protocol.Instral.literalText' exactly. Duplicated rather
-- than shared: sharing it would make this module depend on
-- @Thena.Protocol.Instral@, and @Instral@ is about to depend on this module
-- for 'Thena.Instral.Ops.VSurface' — a four-line mapping is cheap to
-- duplicate and a module cycle is not.
literalText :: Literal -> String
literalText l = case l of
  LString t -> escapeString t
  LChar c   -> escapeChar c
  LInt k    -> show k
  LRegex r  -> "/" ++ r ++ "/"
