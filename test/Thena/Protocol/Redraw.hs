-- | A 'Display' drawn back to text (MS7 phase 115a, extended 115b) — what an
-- editor is: a function from a display representation to text, and nothing
-- else. No session, no context, no globals, no grammars.
--
-- **Shared, not duplicated** (phase 115c): 'Thena.Protocol.DisplayTests' and
-- 'Thena.Protocol.DevelopmentTests' both need to turn a term's 'Display' into
-- text to cross-check it against 'Thena.Repl''s printer, and a second copy of
-- a printer drifts exactly as a second copy of a word table does.
--
-- Notice what 'redraw' has to work out for itself, because that is the seam
-- under test: **where the parentheses go**, **whether a Π is an arrow** (only
-- whether the bound variable occurs, which it can see because occurrences
-- carry their binder), **how to chain consecutive binders**, and, for an
-- object term, **the fence, not its contents** (§6). None of that crosses.
--
-- **'redrawSurface' joined it at 115h**, for the same reason and one more:
-- once 115h gave 'Thena.Protocol.Instral.ValueView' a real
-- 'Thena.Protocol.Surface.SurfaceShape' case, every module that already drew
-- a 'ValueView' (115d, 115f, 115g) needed a 'ValSurface' case too, and a
-- fourth copy of a fifty-line printer is exactly the drift this module
-- exists to stop.
module Thena.Protocol.Redraw (redraw, occurs, redrawSurface) where

import Thena.Protocol.Address (Address)
import Thena.Protocol.Display
  ( Binding (..)
  , Display (..)
  , ObjectItem (..)
  , Shape (..)
  )
import Thena.Protocol.Surface
  ( SurfaceArgView (..)
  , SurfaceBinding (..)
  , SurfacePieceView (..)
  , SurfaceShape (..)
  )
import Thena.Surface.Concrete (Plicity (..))
import Thena.Syntax.Print (tick)

-- | What an editor is: a function from a 'Display' to text, and nothing else.
redraw :: Display -> String
redraw = at Loose
  where
    at prec (Display here s) = case s of
      AVariable nm _ -> nm
      AGlobal g ls -> g <> levels ls
      AUniverse l -> l
      ALiteral t -> t
      ADangling i -> "\8249bound " <> show i <> "\8250"
      AnElision -> "\8230"
      AnApplication f a -> paren (prec > Spine) (at Spine f <> " " <> at Atom a)
      AnAbstraction b body -> paren (prec > Loose) ("\955 " <> chainLam [] here b body)
      AFunction b body
        -- **The editor works this out, and that is the seam being tested.** An
        -- arrow is a Π whose variable does not occur; an occurrence carries the
        -- address of its binder, and a binder binds at its own node — so this is
        -- answerable from the display alone.
        | occurs here body -> paren (prec > Loose) ("\8704 " <> chainPi [] here b body)
        | otherwise -> paren (prec > Loose) (at Spine (bindingType b) <> " -> " <> at Loose body)
      ALet b val body ->
        paren (prec > Loose) $
          "let " <> bindingName b
            <> " = " <> at Loose val
            <> " : " <> at Loose (bindingType b)
            <> " in " <> at Loose body
      AFormer g ls as -> spine (prec > Spine) (g <> levels ls) as
      -- **The slot groups are drawn as groups**, which the editor can do only
      -- because they arrive labelled rather than as one list of arguments.
      AnElimination d ls ps m ms is t ->
        paren (prec > Spine) $
          unwords
            [ "elim " <> d <> levels ls
            , bracket ps
            , at Atom m
            , bracket ms
            , bracket is
            , at Atom t
            ]
      -- **A tagged region is atomic, at every precedence** (phase 110): the
      -- backticks already delimit it, so nothing here ever parenthesises one.
      -- 'layout' is the bare interleaving *inside* the tag; it is also what an
      -- inline (unfenced) nested term continues into, with no tag of its own.
      AnObjectTerm lang _ items -> lang <> "`" <> layout items <> "`"
      AToken txt -> txt

    layout :: [ObjectItem] -> String
    layout items = unwords (map item items)
      where
        item i = case i of
          ObjectText t -> t
          ObjectToken d -> at Atom d
          ObjectChild False d -> case displayShape d of
            AnObjectTerm _ _ innerItems -> layout innerItems
            _ -> at Atom d -- unreached: an unfenced child always drafted inline
          -- **The fence, not its contents, is what crosses** (§6): the editor
          -- still lays this out from the grammar — 'at' does, recursing into
          -- 'AnObjectTerm' for a term still in notation and into the ordinary
          -- shapes for one that fell back to them — this only adds the
          -- boundary phase 110 says is needed.
          ObjectChild True d -> "${" <> at Loose d <> "}"

    bracket xs = "(" <> unwords (map (at Atom) xs) <> ")"

    spine p headText as
      | null as = headText
      | otherwise = paren p (unwords (headText : map (at Atom) as))

    levels [] = ""
    levels ls = " {" <> unwords ls <> "}"

    paren True t = "(" <> t <> ")"
    paren False t = t

    group b = "(" <> bindingName b <> " : " <> at Loose (bindingType b) <> ")"

    -- Consecutive binders are grouped. Presentation, therefore the editor's.
    chainLam acc _ b body = case displayShape body of
      AnAbstraction b' body' -> chainLam (group b : acc) (displayAt body) b' body'
      _ -> unwords (reverse (group b : acc)) <> " -> " <> at Loose body

    chainPi acc _ b body = case displayShape body of
      AnAbstraction {} -> stop
      AFunction b' body' | occurs (displayAt body) body' -> chainPi (group b : acc) (displayAt body) b' body'
      _ -> stop
      where
        stop = unwords (reverse (group b : acc)) <> " -> " <> at Loose body

data Prec = Loose | Spine | Atom
  deriving (Eq, Ord)

-- | Does anything under here point at that binder?
--
-- **The editor's own walk**, and it is possible only because an occurrence says
-- which binder it belongs to. Nothing about the term's internals crosses.
occurs :: Address -> Display -> Bool
occurs a (Display _ s) = case s of
  AVariable _ b -> b == Just a
  AnApplication f x -> occurs a f || occurs a x
  AFunction b body -> occurs a (bindingType b) || occurs a body
  AnAbstraction b body -> occurs a (bindingType b) || occurs a body
  ALet b val body -> occurs a (bindingType b) || occurs a val || occurs a body
  AFormer _ _ as -> any (occurs a) as
  AnElimination _ _ ps m ms is t ->
    any (occurs a) (ps <> [m] <> ms <> is <> [t])
  AnObjectTerm _ _ items -> any occursItem items
  _ -> False
  where
    occursItem i = case i of
      ObjectChild _ d -> occurs a d
      _               -> False

-- ---------------------------------------------------------------------------
-- A surface term (115h), crossed against 'Thena.Repl.renderSurface'. Its own
-- 'SurfacePrec' is not imported from 'Thena.Syntax.Print' — an independent
-- precedence scheme is the whole point of a crossing rather than a round
-- trip.

data SurfacePrec = SLoose | SArrowed | SSpine | STight
  deriving (Eq, Ord)

-- | What an editor is, for a surface term: a function from a 'SurfaceShape'
-- to text, and nothing else.
redrawSurface :: SurfaceShape -> String
redrawSurface = surf SLoose
  where
    surf _ (ASurfaceName x) = x
    surf _ (ASurfaceUniverse l) = "Type" ++ subscriptOf l
    surf _ ASurfaceUniverseOpen = "Type"
    surf _ (ASurfaceLiteral t) = t
    surf _ ASurfacePlaceholder = "_"
    surf _ (ASurfaceHole h) = "?" ++ h
    surf _ (ASurfaceObjectTerm lang prod ps) =
      lang ++ maybe "" (\p -> "[" ++ p ++ "]") prod
        ++ [tick] ++ concatMap piece ps ++ [tick]
    surf p (ASurfaceApplication f as) =
      paren (p >= STight) (surf SSpine f ++ concatMap arg as)
    surf p (ASurfaceFunction bs b) =
      paren (p >= SSpine) ("\955" ++ concatMap binding bs ++ " -> " ++ surf SArrowed b)
    surf p (ASurfaceQuantifier bs b) =
      paren (p >= SSpine) ("\8704" ++ concatMap binding bs ++ " -> " ++ surf SArrowed b)
    surf p (ASurfaceArrow a b) =
      paren (p >= SSpine) (surf STight a ++ " -> " ++ surf SArrowed b)
    surf p (ASurfaceLet x ty v b) =
      paren (p >= SSpine)
        ("let " ++ x ++ maybe "" (\t -> " : " ++ surf SLoose t) ty
           ++ " = " ++ surf SLoose v ++ " in " ++ surf SArrowed b)
    surf p (ASurfaceAnnotation e ty) =
      paren (p >= SArrowed) (surf SArrowed e ++ " : " ++ surf SArrowed ty)
    surf p (ASurfaceElimination d ps mot ms is tgt) =
      paren (p >= STight)
        ("elim " ++ d ++ " " ++ list ps ++ " " ++ surf STight mot ++ " " ++ list ms
           ++ " " ++ list is ++ " " ++ surf STight tgt)
    surf _ (ASurfaceDo t) = "do { " ++ t ++ " }"

    arg (SurfaceArgView Explicit t) = " " ++ surf STight t
    arg (SurfaceArgView Implicit t) = " {" ++ surf SLoose t ++ "}"

    binding (SurfaceBinding Explicit x Nothing) = " " ++ x
    binding (SurfaceBinding Explicit x (Just ty)) = " (" ++ x ++ " : " ++ surf SLoose ty ++ ")"
    binding (SurfaceBinding Implicit x Nothing) = " {" ++ x ++ "}"
    binding (SurfaceBinding Implicit x (Just ty)) = " {" ++ x ++ " : " ++ surf SLoose ty ++ "}"

    list ts = "(" ++ unwords (map (surf STight) ts) ++ ")"

    piece p = case p of
      ASurfacePieceText txt -> concatMap escapeRaw txt
      ASurfacePieceSplice e -> "$" ++ "{" ++ surf SLoose e ++ "}"

    escapeRaw c
      | c `elem` [tick, '\\', '$'] = ['\\', c]
      | otherwise = [c]

    paren True t = "(" ++ t ++ ")"
    paren False t = t

    subscriptOf n = map digit (show n)
      where
        digit c = "\8320\8321\8322\8323\8324\8325\8326\8327\8328\8329" !! (fromEnum c - fromEnum '0')
