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
--
-- **ONE RELATION PER EXTENSION PRODUCTION since MS8 phase 156** — `~23rg2`, and
-- the reason the milestone has it: F-sub's Γ carries both @x : T@ and @X <: T@,
-- so until now its context could not be declared at all. @n@ extensions give
-- @n@ relations of @1 + n@ constructors, one @here@ and one @there@ for each
-- extension a lookup may step over, and each relation is named after its own
-- extension production rather than after the context (his ruling, 2026-10-04).
--
-- **The @ne@ premise is generated only where the stepped-over extension is at
-- the SAME class.** Its job is making a later binding shadow an earlier one, and
-- shadowing is within a namespace — so a term lookup stepping over @X <: T@
-- carries no inequality, and nothing has to be proved about a name of another
-- kind to look past it.
module Thena.Language.Lookup
  ( lookupGrammars
  , lookupDatatypes
  ) where

import qualified Data.List.NonEmpty as NE

import Thena.Core.Term (GlobalName (..))
import Thena.Global.Env (ArgRole (..))
import Thena.Language.Grammar
  ( Argument (..)
  , GProduction (..)
  , ProductionKind (..)
  , Grammar (..)
  , Item (..)
  , Sort (..)
  , extensionsOf
  , isName
  , lookupNamesOf
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

-- | One notation grammar per extension. Empty for anything that is not a
-- context.
lookupGrammars :: Grammar -> [Grammar]
lookupGrammars g = [ lg | e <- extensionsOf g, Just lg <- [notationOf g e] ]

-- | The notation's grammar for one extension.
notationOf :: Grammar -> GProduction -> Maybe Grammar
notationOf g e = do
  inN : _ <- Just (lookupNamesOf g e)
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
  Just (Grammar JudgmentBlock (GlobalName inN) [inN] [GProduction (GlobalName inN) items args Constructor])
  where
    own i = case i of
      Slot _ srt _ -> srt == OfLanguage (grammarName g)
      _ -> False
    isSlot i = case i of
      Slot {} -> True
      _ -> False
    distinct = foldr (\x acc -> x : filter (/= x) acc) []

-- | One relation per extension: its datatype, its constructors, and the roles
-- 'Thena.Instral.Ops.MakeData' carries — all 'Plain', since nothing here is
-- object syntax. Empty for anything that is not a context.
lookupDatatypes :: Grammar -> [(SurfaceData, [[ArgRole]])]
lookupDatatypes g = [ d | e <- extensionsOf g, Just d <- [relationOf g e] ]

-- | The relation for one extension production.
relationOf :: Grammar -> GProduction -> Maybe (SurfaceData, [[ArgRole]])
relationOf g e = do
  lg <- notationOf g e
  inN : hereN : thereNs <- Just (lookupNamesOf g e)
  p : _ <- Just (grammarProductions lg)
  -- The context is the notation's last slot, because 'notationOf' put it
  -- there; the entry is everything before it.
  ctxArg : reversedOthers <- Just (reverse (gproductionArguments p))
  let others = reverse reversedOthers
      indices = others ++ [ctxArg]
  key : _ <- Just [ a | a <- others, isName a ]
  let -- Every binder is primed until it names no type the constructor
      -- mentions and nothing bound before it, as 'Thena.Driver.grammarDatatype'
      -- primes a constructor's.
      taken = [inN, "Eq", "Empty", nm (grammarName g)] ++ map (typeName . argumentSort) indices
      fresh used x | x `elem` taken || x `elem` used = fresh used (x ++ "'")
                   | otherwise = x
      names used xs = foldl (\(ys, u) x -> let y = fresh u x in (ys ++ [y], y : u)) ([], used) xs

      gamma = fresh [] (argumentName ctxArg)
      (outer, used1) = names [gamma] (map argumentName others)

      ref = SurfaceName
      binder x a = SurfaceBinder Explicit x (Just (typeOf a))
      -- An extension applied, with the context and the entry's own names.
      extend k ctx entry = app (ref (nm (gproductionName k)))
        [ if argumentSort a == OfLanguage (grammarName g) then ref ctx
          else ref (lookupOr (argumentName a) entry)
        | a <- gproductionArguments k ]
      lookupOr x entry = case lookup x entry of
        Just y -> y
        Nothing -> x
      inRel entry ctx = app (ref inN) ([ ref y | (_, y) <- entry ] ++ [ctx])
      outerEntry = zip (map argumentName others) outer
      keyOf a entry = ref (lookupOr (argumentName a) entry)

      here = SurfaceConstructor hereN $
        SurfacePi (NE.fromList (binder gamma ctxArg : zipWith binder outer others))
          (inRel outerEntry (extend e gamma outerEntry))

      -- **One @there@ per extension a lookup may step over** (MS8 phase 156).
      -- The binders are this relation's own entry, then the stepped-over
      -- extension's, primed; the @ne@ premise is there only when that extension
      -- reads names of the same class, because shadowing is within a namespace.
      stepping (thereN, k) =
        let kOthers = entryOf k
            kKeys = [ a | a <- kOthers, isName a ]
            (inner, used2) = names used1 (map ((++ "'") . argumentName) kOthers)
            innerEntry = zip (map argumentName kOthers) inner
            neN = fresh used2 "ne"
            shadows = [ a | a <- kKeys, classOf a == classOf key ]
            premises =
              [ SurfaceBinder Explicit neN (Just (SurfaceArrow
                  (app (ref "Eq") [typeOf key, keyOf key outerEntry, keyOf a innerEntry]) (ref "Empty")))
              | a <- take 1 shadows ]
            iN = fresh (neN : used2) "i"
         in ( SurfaceConstructor thereN $
                SurfacePi (NE.fromList
                  ( binder gamma ctxArg : zipWith binder outer others ++ zipWith binder inner kOthers
                    ++ premises
                    ++ [ SurfaceBinder Explicit iN (Just (inRel outerEntry (ref gamma))) ]))
                  (inRel outerEntry (extend k gamma innerEntry))
            , replicate (2 + length others + length kOthers + length premises) Plain )
      theres = map stepping (zip thereNs (extensionsOf g))
      relType = foldr (SurfaceArrow . typeOf) (SurfaceUniverse 0) indices
  Just ( SurfaceData inN [] relType (here : map fst theres)
       , replicate (1 + length others) Plain : map snd theres )
  where
    entryOf k = [ a | a <- gproductionArguments k, argumentSort a /= OfLanguage (grammarName g) ]
    classOf a = case argumentSort a of
      OfClass cls _ _ -> Just cls
      _ -> Nothing
    nm (GlobalName n) = n
    typeName srt = case srt of
      OfLanguage l -> nm l
      OfClass _ t _ -> nm t
    typeOf = SurfaceName . typeName . argumentSort
    app f [] = f
    app f xs = SurfaceApp f (NE.fromList (map (SurfaceArg Explicit) xs))
