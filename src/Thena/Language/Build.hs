-- | Between a parse and a term (MS6 phase 103; @ms6\/SPEC.md@ §4.6, §8).
--
-- 'buildTerm' turns a reading into the constructor application it denotes:
-- @LC`( λ x : ι . x )`@ is @abs "x" base (var "x")@. 'printTerm' is the other
-- way, and it is §4.6's remark that **a production is also a printing rule** —
-- the items in order, terminals as themselves and slots as their arguments.
--
-- The two are inverse on what a grammar can express, which is what phase 103's
-- done-when asks: print a generated term, parse it, build it, and the term is
-- the one you started with. A grammar that parses one text two ways is refused
-- when the text is read (§7.5), so the round trip is not a claim that every
-- grammar is unambiguous — it is the claim that printing writes what parsing
-- reads.
--
-- **A term is built as the constructor's wrapper applied**, which is what
-- elaboration produces for the same text, and 'printTerm' reduces what it is
-- given, so either form prints.
module Thena.Language.Build
  ( buildTerm
  , buildSurface
  , skeletonOf
  , printTerm
  ) where

import Data.List (elemIndex)
import qualified Data.List.NonEmpty as NE

import Thena.Core.Reduce (whnf)
import Thena.Core.Term (Core (..), GlobalName (..), Literal (..))
import Thena.Errors (BuildError (..))
import Thena.Global.Env (GlobalEnv)
import Thena.Language.Earley (Tree (..))
import Thena.Language.Grammar
  ( Argument (..)
  , GProduction (..)
  , Grammar (..)
  , Item (..)
  , Sort (..)
  )
import Thena.Instral.Pattern (Skeleton (..), Slot (..))
import Thena.Language.Regex (matches)
import Thena.Surface.Concrete (Plicity (..), Surface (..), SurfaceArg (..))

-- | The term a reading denotes.
--
-- **A reading alone, so a splice has nothing to be**: 'buildSurface' supplies
-- them from a surface term, and 'skeletonOf' leaves them as holes.
buildTerm :: [Grammar] -> Tree -> Either BuildError Core
buildTerm gs tree = case tree of
  Node name children -> do
    p <- maybe (Left (NoSuchProduction name)) Right (production gs name)
    args <- traverse (slot name) =<< arguments p children
    Right (foldl App (Global (GlobalName name) []) args)
  _ -> Left (NotForSlot "" (shapeOf tree))
  where
    slot name (a, child) = case argumentSort a of
      OfClass _ t _ -> Primitive <$> literal name (argumentName a) t child
      OfLanguage _  -> buildTerm gs child

-- | The **surface** term a reading denotes, with the splices supplied (MS6
-- phase 104; @ms6\/SPEC.md@ §8).
--
-- The same walk 'buildTerm' makes, writing a 'Thena.Surface.Concrete.Surface'
-- application instead of a 'Core' one — so what it hands back is a term whose
-- splices are ordinary sub-terms, elaborated where they stand and at the type
-- the constructor's argument has. That is what keeps §7.6's rule (/a splice
-- supplies a slot's value and its type is the slot's/) from needing any
-- mechanism of its own.
--
-- The splices are indexed as the input pieces numbered them, so the @k@th
-- 'Thena.Language.Earley.Splice' reads the @k@th term here.
buildSurface :: [Grammar] -> [Surface] -> Tree -> Either BuildError Surface
buildSurface gs splices = build
  where
    build tree = case tree of
      SpliceOf k -> supplied k
      Node name children -> do
        p <- maybe (Left (NoSuchProduction name)) Right (production gs name)
        args <- traverse (slot name) =<< arguments p children
        Right $ case args of
          [] -> SurfaceName name
          a : as -> SurfaceApp (SurfaceName name)
                      (NE.map (SurfaceArg Explicit) (a NE.:| as))
      _ -> Left (NotForSlot "" (shapeOf tree))

    slot name (a, child) = case (argumentSort a, child) of
      (_, SpliceOf k) -> supplied k
      (OfClass _ t _, _) -> SurfaceLiteral <$> literal name (argumentName a) t child
      (OfLanguage _, _) -> build child

    supplied k = case drop k splices of
      e : _ -> Right e
      []    -> Left (NotForSlot "" (shapeOf (SpliceOf k)))

-- | A reading as a grammar-free shape, with @holes@ put at its splices in
-- order (MS6 phase 104c; @ms6\/SPEC.md@ §8).
--
-- **This is where a grammar is consulted for the last time.** Everything a
-- later stage needs to know — which constructor a node is, which argument each
-- slot fills, what a token class matched, and whether a hole takes a term or a
-- literal — is written into the 'Skeleton' here. So neither the machine nor
-- the matcher has to be told about grammars at all.
--
-- The @k@th 'Thena.Language.Earley.Splice' takes the @k@th hole. A reading
-- with fewer splices than holes, or more, is the caller's mistake and is
-- refused.
skeletonOf :: [Grammar] -> [a] -> Tree -> Either BuildError (Skeleton a)
skeletonOf gs holes = go
  where
    go tree = case tree of
      SpliceOf k -> hole AtTerm k
      Node name children -> do
        p <- maybe (Left (NoSuchProduction name)) Right (production gs name)
        kids <- traverse (slot name) =<< arguments p children
        Right (SNode (GlobalName name) kids)
      _ -> Left (NotForSlot "" (shapeOf tree))

    slot name (a, child) = case (argumentSort a, child) of
      (OfClass _ t _, SpliceOf k) -> hole (AtPrimitive t) k
      (OfLanguage _, SpliceOf k)  -> hole AtTerm k
      (OfClass _ t _, _) -> SLit <$> literal name (argumentName a) t child
      (OfLanguage _, _)  -> go child

    hole what k = case drop k holes of
      h : _ -> Right (SHole what h)
      []    -> Left (NotForSlot "" (shapeOf (SpliceOf k)))

-- | Each argument of a production, with the child that reads it.
--
-- **The distinct names in order of first appearance** (§4.6): a name written
-- twice is one argument, and the occurrences agree, because the parser's
-- filter kept only the readings where they do (§7.4).
arguments :: GProduction -> [Tree] -> Either BuildError [(Argument, Tree)]
arguments p children = traverse one (gproductionArguments p)
  where
    names = [ x | Slot x _ _ <- gproductionItems p ]
    name = case gproductionName p of GlobalName n -> n
    one a = case elemIndex (argumentName a) names of
      Just k | child : _ <- drop k children -> Right (a, child)
      _ -> Left (NotForSlot name (argumentName a))

-- | What a token class matched, as the literal it stands for.
literal :: String -> String -> GlobalName -> Tree -> Either BuildError Literal
literal name x t child = case (child, t) of
  (Token s, GlobalName "String") -> Right (LString s)
  (Token [c], GlobalName "Char") -> Right (LChar c)
  (Token s, GlobalName "Int") | [(k, "")] <- reads s -> Right (LInt k)
  (HoleAt _, _) -> Left (Incomplete x)
  _ -> Left (NotForSlot name x)

-- | What a tree is, for a message about one that is not a term.
shapeOf :: Tree -> String
shapeOf tree = case tree of
  Node n _   -> n
  Token t    -> t
  HoleAt _   -> "?"
  SpliceOf k -> "${" ++ show k ++ "}"

-- | The text a term is written as, or 'Nothing' when it is not one an object
-- language can write: something that is not a constructor of a grammar, or a
-- literal its class would not accept.
printTerm :: GlobalEnv -> [Grammar] -> Core -> Maybe String
printTerm env gs t = unwords <$> pieces t
  where
    pieces term = case spine (whnf env [] term) of
      Just (GlobalName name, args) -> do
        p <- production gs name
        let names = map argumentName (gproductionArguments p)
        concat <$> traverse (item p names args) (gproductionItems p)
      Nothing -> Nothing

    item p names args i = case i of
      Terminal txt -> Just [txt]
      Slot x _ _ -> do
        k <- elemIndex x names
        arg <- at k args
        case argumentSort <$> lookupArgument p x of
          Just (OfClass _ _ re) -> (: []) <$> text re (whnf env [] arg)
          _ -> pieces arg

    lookupArgument p x = case [ a | a <- gproductionArguments p, argumentName a == x ] of
      a : _ -> Just a
      [] -> Nothing

    -- A class's match prints as itself, and only if the class would read it
    -- back — @"a b"@ is a fine 'String' and no identifier.
    text re term = case term of
      Primitive (LString s) -> readable s
      Primitive (LChar c) -> readable [c]
      Primitive (LInt k) -> readable (show k)
      _ -> Nothing
      where readable s = if length s `elem` matches re s then Just s else Nothing

    at k xs = case drop k xs of
      y : _ -> Just y
      [] -> Nothing

    spine term = case term of
      Canonical c _ args -> Just (c, args)
      Global c _ -> Just (c, [])
      App {} -> case flatten term [] of
        (Global c _, args) -> Just (c, args)
        _ -> Nothing
      _ -> Nothing
    flatten term acc = case term of
      App f a -> flatten f (a : acc)
      _ -> (term, acc)

production :: [Grammar] -> String -> Maybe GProduction
production gs name =
  case [ p | g <- gs, p <- grammarProductions g, gproductionName p == GlobalName name ] of
    p : _ -> Just p
    [] -> Nothing
