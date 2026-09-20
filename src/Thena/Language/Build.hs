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
  ( BuildError (..)
  , buildTerm
  , printTerm
  ) where

import Data.List (elemIndex)

import Thena.Core.Reduce (whnf)
import Thena.Core.Term (Core (..), GlobalName (..), Literal (..))
import Thena.Global.Env (GlobalEnv)
import Thena.Language.Earley (Tree (..))
import Thena.Language.Grammar
  ( Argument (..)
  , GProduction (..)
  , Grammar (..)
  , Item (..)
  , Sort (..)
  )
import Thena.Language.Regex (matches)

data BuildError
  = NoSuchProduction String
    -- ^ a reading of a production no installed grammar has
  | Incomplete String
    -- ^ a hole: a constructor cannot have a missing argument (§7.6)
  | SpliceUnsupported String
    -- ^ a splice; supplying one is phase 104's
  | NotForSlot String String
    -- ^ the production, and a slot whose reading is not what it takes
  deriving (Eq, Show)

-- | The term a reading denotes.
buildTerm :: [Grammar] -> Tree -> Either BuildError Core
buildTerm gs tree = case tree of
  HoleAt _ -> Left (Incomplete "")
  SpliceOf _ -> Left (SpliceUnsupported "")
  Token t -> Left (NotForSlot "" t)
  Node name children -> do
    p <- maybe (Left (NoSuchProduction name)) Right (production gs name)
    let names = [ x | Slot x _ _ <- gproductionItems p ]
    args <- traverse (argument name children names) (gproductionArguments p)
    Right (foldl App (Global (GlobalName name) []) args)
  where
    -- **The distinct names in order of first appearance** (§4.6): a name
    -- written twice is one argument, and the occurrences agree, because the
    -- parser's filter kept only the readings where they do (§7.4).
    argument name children names a = case elemIndex (argumentName a) names of
      Nothing -> Left (NotForSlot name (argumentName a))
      Just k -> case (argumentSort a, drop k children) of
        (OfClass _ t _, child : _) -> literal name (argumentName a) t child
        (OfLanguage _, child : _) -> buildTerm gs child
        _ -> Left (NotForSlot name (argumentName a))

    literal name x t child = case (child, t) of
      (Token s, GlobalName "String") -> Right (Primitive (LString s))
      (Token [c], GlobalName "Char") -> Right (Primitive (LChar c))
      (Token s, GlobalName "Int") | [(k, "")] <- reads s -> Right (Primitive (LInt k))
      (HoleAt _, _) -> Left (Incomplete x)
      (SpliceOf _, _) -> Left (SpliceUnsupported x)
      _ -> Left (NotForSlot name x)

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
