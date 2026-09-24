-- | A context's lookup relation (MS6 phase 107; @ms6\/SPEC.md@ §5.3).
--
-- From
--
-- > context Ctx, Γ where
-- >   empty  -> ·
-- >   extend -> Γ , x : T
--
-- two things, and both are ordinary:
--
-- * **a grammar**, 'lookupGrammar', whose one production is the notation
--   @x : T ∈ Γ@ — the extension with the context slot and its separator taken
--   out, then @∈@ and the context. It builds @Ctx-in x T Γ@, so the relation
--   is read by the same parser, printed by the same printer, and written as
--   @Ctx-in`x : ι ∈ ·`@ like any object term. **It is the first judgment**
--   (his answer, 2026-09-21): a judgment is a grammar production (§6.1), and
--   phase 108 reuses this rather than inventing it.
-- * **a datatype**, 'lookupDatatype', written as surface @data@ and elaborated
--   like a written one:
--
-- > data Ctx-in : String -> Ty -> Ctx -> Type₀ where
-- >   Ctx-here  : ∀ (Γ : Ctx) (x : String) (T : Ty) -> Ctx-in x T (extend Γ x T)
-- >   Ctx-there : ∀ (Γ : Ctx) (x : String) (T : Ty) (x' : String) (T' : Ty)
-- >                 (ne : Eq String x x' -> Empty) (i : Ctx-in x T Γ)
-- >                 -> Ctx-in x T (extend Γ x' T')
--
-- **The indices are the notation's slots in order**, as every judgment's are
-- (§6.1) — so the context is last, where §5.3 first put it first. One rule for
-- every judgment rather than an argument order for this one.
--
-- **@ne@ is what makes a later binding shadow an earlier one** (§5.3): without
-- it @Γ, x : T, x : S@ would derive both. It compares the extension's one name,
-- which 'Thena.Language.Grammar.checkGrammar' has made sure there is.
module Thena.Language.Lookup
  ( lookupGrammar
  , lookupDatatype
  ) where

import qualified Data.List.NonEmpty as NE

import Thena.Core.Term (GlobalName (..))
import Thena.Global.Env (ArgRole (..))
import Thena.Language.Grammar
  ( Argument (..)
  , GProduction (..)
  , Grammar (..)
  , Item (..)
  , Sort (..)
  , extensionOf
  , isName
  , lookupNames
  )
import Thena.Surface.Concrete
  ( Plicity (..)
  , Surface (..)
  , SurfaceArg (..)
  , SurfaceBinder (..)
  , SurfaceConstructor (..)
  , SurfaceData (..)
  )
import Thena.Syntax.Lexer (BlockKind (..))

-- | The notation's grammar. 'Nothing' for anything that is not a context.
lookupGrammar :: Grammar -> Maybe Grammar
lookupGrammar g = do
  e <- extensionOf g
  inN : _ <- Just (lookupNames g)
  let (before, rest) = break own (gproductionItems e)
  (ctxSlot, after) <- case rest of
    s : more -> Just (s, more)
    [] -> Nothing
  -- **The separator is the terminals between the context slot and its
  -- neighbouring slot**: the next one if there is one, else the previous. So
  -- @Γ , x : T@ and @x : T :: Γ@ both give @x : T@, and a terminal anywhere
  -- else is part of the entry and stays.
  let kept
        | any isSlot after = before ++ dropWhile (not . isSlot) after
        | otherwise = reverse (dropWhile (not . isSlot) (reverse before)) ++ after
      items = kept ++ [Terminal "\8712", ctxSlot]
      args = [ Argument x srt Plain | x <- distinct [ y | Slot y _ _ <- items ]
                                    , srt <- take 1 [ t | Slot y t _ <- items, y == x ] ]
  Just (Grammar JudgmentBlock (GlobalName inN) [inN] [GProduction (GlobalName inN) items args])
  where
    own i = case i of
      Slot _ srt _ -> srt == OfLanguage (grammarName g)
      _ -> False
    isSlot i = case i of
      Slot {} -> True
      _ -> False
    distinct = foldr (\x acc -> x : filter (/= x) acc) []

-- | The relation's datatype and its two constructors, and the roles
-- 'Thena.Instral.Ops.MakeData' carries — all 'Plain', since nothing here is
-- object syntax. 'Nothing' for anything that is not a context.
lookupDatatype :: Grammar -> Maybe (SurfaceData, [[ArgRole]])
lookupDatatype g = do
  e <- extensionOf g
  lg <- lookupGrammar g
  [inN, hereN, thereN] <- Just (lookupNames g)
  p : _ <- Just (grammarProductions lg)
  -- The context is the notation's last slot, because 'lookupGrammar' put it
  -- there; the entry is everything before it.
  ctxArg : reversedOthers <- Just (reverse (gproductionArguments p))
  let others = reverse reversedOthers
      indices = others ++ [ctxArg]
  key : _ <- Just [ a | a <- others, isName a ]
  let extArgs = gproductionArguments e

      -- Every binder is primed until it names no type the constructor
      -- mentions and nothing bound before it, as 'Thena.Driver.grammarDatatype'
      -- primes a constructor's.
      taken = [inN, "Eq", "Empty", nm (grammarName g)] ++ map (typeName . argumentSort) indices
      fresh used x | x `elem` taken || x `elem` used = fresh used (x ++ "'")
                   | otherwise = x
      names used xs = foldl (\(ys, u) x -> let y = fresh u x in (ys ++ [y], y : u)) ([], used) xs

      gamma = fresh [] (argumentName ctxArg)
      (outer, used1) = names [gamma] (map argumentName others)
      (inner, used2) = names used1 (map ((++ "'") . argumentName) others)
      neN = fresh used2 "ne"
      iN = fresh (neN : used2) "i"

      ref = SurfaceName
      binder x a = SurfaceBinder Explicit x (Just (typeOf a))
      -- The extension applied, with the context and the entry's own names.
      extend ctx entry = app (ref (nm (gproductionName e)))
        [ if argumentSort a == OfLanguage (grammarName g) then ref ctx
          else ref (lookupOr (argumentName a) entry)
        | a <- extArgs ]
      lookupOr x entry = case lookup x entry of
        Just y -> y
        Nothing -> x
      inRel entry ctx = app (ref inN) ([ ref y | (_, y) <- entry ] ++ [ctx])
      outerEntry = zip (map argumentName others) outer
      innerEntry = zip (map argumentName others) inner
      keyOf entry = ref (lookupOr (argumentName key) entry)

      here = SurfaceConstructor hereN $
        SurfacePi (NE.fromList (binder gamma ctxArg : zipWith binder outer others))
          (inRel outerEntry (extend gamma outerEntry))
      there = SurfaceConstructor thereN $
        SurfacePi (NE.fromList
          ( binder gamma ctxArg : zipWith binder outer others ++ zipWith binder inner others
            ++ [ SurfaceBinder Explicit neN (Just (SurfaceArrow
                   (app (ref "Eq") [typeOf key, keyOf outerEntry, keyOf innerEntry]) (ref "Empty")))
               , SurfaceBinder Explicit iN (Just (inRel outerEntry (ref gamma))) ]))
          (inRel outerEntry (extend gamma innerEntry))
      relType = foldr (SurfaceArrow . typeOf) (SurfaceUniverse 0) indices
  Just ( SurfaceData inN [] relType [here, there]
       , [ replicate (1 + length others) Plain, replicate (3 + 2 * length others) Plain ] )
  where
    nm (GlobalName n) = n
    typeName srt = case srt of
      OfLanguage l -> nm l
      OfClass _ t _ -> nm t
    typeOf = SurfaceName . typeName . argumentSort
    app f [] = f
    app f xs = SurfaceApp f (NE.fromList (map (SurfaceArg Explicit) xs))
