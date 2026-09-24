-- | Generated substitution (MS6 phase 105, @ms6\/SPEC.md@ §4.7).
--
-- For a language with a variable production, four functions, written as
-- ordinary surface definitions and elaborated like any other — §1: nothing a
-- block generates is out of reach of a hand-written file.
--
-- > L-fresh     : String -> List String -> String
-- > L-fv        : L -> List String
-- > L-subst-all : L -> List (And String L) -> L
-- > L-subst     : L -> String -> L -> L
--
-- **Simultaneous substitution is the primitive one**, because capture
-- avoidance is not structurally recursive otherwise: under a binder the body is
-- substituted with the map extended by the binder's renaming, which is the same
-- recursive call with a longer list, where renaming first and substituting
-- after would recurse on a term that is not a subterm.
--
-- **A binder is renamed only when keeping it would capture** — his choice,
-- 2026-09-21. At a binder the names to avoid are the free variables of what
-- the map sends each free variable of the node to (Stoughton's definition, from
-- memory), and @L-fresh x avoid@ is the first of @x@, @x'@, @x''@, … not among
-- them — so @x@ itself whenever nothing would be captured, and capture stays
-- something a user can see happen and not happen.
--
-- **Everything is done by @elim@**, and the only primitives are @decString@ and
-- @appendString@: two names are compared by eliminating a @Dec@, and a fresh one
-- is made by priming.
--
-- **@decString@, not @eqString@** (MS6 phase 109a, his choice on
-- @ms6\/CLOSEOUT.md@ 32). A proof about substitution has to follow the same
-- decision the function makes, and on a name it does not know it can only do
-- that by eliminating the same term. @decString y x@ hands each branch its
-- evidence — @Eq String y x@ or its refutation — where @eqString y x@ said only
-- which branch, so no proof over an open name could get past it.
module Thena.Language.Substitution
  ( substitutionDefinitions
  ) where

import qualified Data.List.NonEmpty as NE

import Thena.Core.Term (GlobalName (..), Literal (..))
import Thena.Global.Env (ArgRole (..))
import Thena.Language.Grammar
  ( Argument (..)
  , GProduction (..)
  , Grammar (..)
  , Sort (..)
  , substitutionNames
  , variableProduction
  )
import Thena.Surface.Concrete (Plicity (..), Surface (..), SurfaceArg (..), SurfaceBinder (..))

-- | The definitions, as name, type and body, in the order they are declared —
-- each uses only the ones before it. None for a language with no variable
-- production; 'Thena.Language.Grammar.checkGrammar' has already refused a
-- language this cannot be generated for.
substitutionDefinitions :: Grammar -> [(String, Surface, Surface)]
substitutionDefinitions g = case (variableProduction g, substitutionNames g) of
  (Just vp, [freshN, fvN, allN, oneN]) ->
    let var y = app (name (conName vp)) [y]
     in [ (freshN, arrows [string, listOf string] string, freshBody)
        , (fvN, arrows [self] (listOf string), fvBody)
        , (allN, arrows [self, listOf pair] self, allBody fvN freshN var)
        , (oneN, arrows [self, string, self] self, oneBody allN)
        ]
  _ -> []
  where
    GlobalName lang = grammarName g
    self = name lang
    string = name "String"
    pair = app (name "And") [string, self]
    listOf t = app (name "List") [t]
    prods = grammarProductions g
    conName p = let GlobalName n = gproductionName p in n

    -- A bound name may not be one the generated code refers to, or a
    -- constructor called @s@ would be shadowed by the map. Primed until free,
    -- as 'Thena.Driver.grammarDatatype' primes a constructor's binders.
    referenced = lang : map conName prods
      ++ [ "String", "List", "And", "Comparison", "nil", "cons", "both", "same", "different"
         , "Dec", "yes", "no", "Eq", "decString", "appendString" ]
      ++ substitutionNames g
    local x | x `elem` referenced = local (x ++ "'")
            | otherwise = x
    v = name . local
    lamL = lam . map local

    nilOf t = app (name "nil") [t]
    consOf t h rest = app (name "cons") [t, h, rest]

    -- @y ∈ xs@, as a 'Comparison': @same@ when it is there.
    member y xs =
      elimOn "List" [string] (lamL ["l"] (name "Comparison"))
        [ name "different"
        , lamL ["b", "bs", "rb"]
            (compareNames (name "Comparison") y (v "b") (name "same") (v "rb"))
        ]
        xs

    -- The first method when @y@ and @k@ are the same name, the second
    -- otherwise, deciding with @decString@ — whose evidence each method is
    -- given and ignores.
    compareNames ty y k whenSame whenDifferent =
      elimOn "Dec" [app (name "Eq") [string, y, k]] (lamL ["d"] ty)
        [lamL ["p"] whenSame, lamL ["n"] whenDifferent]
        (app (name "decString") [y, k])

    -- The first constructor's method when @c@ is @same@, the second's otherwise.
    decide ty c whenSame whenDifferent =
      elimOn "Comparison" [] (lamL ["q"] ty) [whenSame, whenDifferent] c

    -- ---------------------------------------------------------------------
    -- L-fresh: the fuel is the list itself. Among x, x', …, x⁽ⁿ⁾ one is not
    -- among n names, so n primings are enough and the recursion is on the list.
    freshBody =
      lamL ["y", "avoid"]
        (app (elimOn "List" [string] (lamL ["l"] (arrows [string] string))
                [ lamL ["c"] (v "c")
                , lamL ["a", "rest", "r", "c"]
                    (decide string (member (v "c") (v "avoid"))
                       (app (v "r") [app (name "appendString") [v "c", SurfaceLiteral (LString "'")]])
                       (v "c"))
                ]
                (v "avoid"))
             [v "y"])

    -- ---------------------------------------------------------------------
    -- L-fv: an accumulator and the names bound on the way down, so that
    -- neither an append nor a removal is needed. A name may be listed twice;
    -- it is a list, not a set, and everything that reads it only asks
    -- membership.
    fvBody =
      lamL ["t"]
        (app (elimOn lang [] (lamL ["u"] (arrows [listOf string, listOf string] (listOf string)))
                (map fvMethod prods) (v "t"))
             [nilOf string, nilOf string])

    fvMethod p =
      let args = gproductionArguments p
          as = argNames args
          rs = recNames args
          step (a, arg) acc = case (argumentRole arg, recOf args rs a) of
            (Occurrence, _) ->
              decide (listOf string) (member (v a) (v "bound")) acc (consOf string (v a) acc)
            (Scope bs, Just r) ->
              app (v r) [foldr (consOf string . v) (v "bound") [ as !! i | i <- bs ], acc]
            (Plain, Just r) -> app (v r) [v "bound", acc]
            _ -> acc
       in lamL (as ++ rs ++ ["bound", "acc"]) (foldr step (v "acc") (zip as args))

    -- ---------------------------------------------------------------------
    -- L-subst-all.
    allBody fvN freshN var =
      lamL ["t"]
        (elimOn lang [] (lamL ["u"] (arrows [listOf pair] self))
           (map (allMethod fvN freshN var) prods) (v "t"))

    -- What the map sends @y@ to: the first pair that names it, or @y@ itself.
    lookupIn var y s =
      elimOn "List" [pair] (lamL ["l"] self)
        [ var y
        , lamL ["p", "ps", "rp"]
            (elimOn "And" [string, self] (lamL ["q"] self)
               [ lamL ["k", "w"] (compareNames self y (v "k") (v "w") (v "rp")) ]
               (v "p"))
        ]
        s

    allMethod fvN freshN var p =
      let args = gproductionArguments p
          as = argNames args
          rs = recNames args
          binders = [ i | (i, arg) <- zip [0 :: Int ..] args, argumentRole arg == Binder ]
          renamed i = "z" ++ show i
          -- A renaming for each binder, and each avoids the names already
          -- chosen for the ones before it and the names of the ones after.
          avoid j = foldr (consOf string) (v "avoid")
            ([ v (renamed i) | i <- take j binders ] ++ [ v (as !! i) | i <- drop (j + 1) binders ])
          -- The last binder at the head, so that of two binders with one name
          -- the later is the one found, as the later shadows on paper.
          extend bs s = foldl (\rest i -> consOf pair (app (name "both") [string, self, v (as !! i), var (v (renamed i))]) rest) s bs
          rebuilt = app (name (conName p))
            [ case (argumentRole arg, recOf args rs a) of
                (Binder, _) -> v (renamed i)
                (Scope bs, Just r) -> app (v r) [extend bs (v "s")]
                (Plain, Just r) -> app (v r) [v "s"]
                _ -> v a
            | (i, (a, arg)) <- zip [0 :: Int ..] (zip as args) ]
          images =
            elimOn "List" [string] (lamL ["l"] (listOf string))
              [ nilOf string
              , lamL ["y", "ys", "ry"]
                  (elimOn "List" [string] (lamL ["l"] (listOf string))
                     [ v "ry", lamL ["h", "hs", "rh"] (consOf string (v "h") (v "rh")) ]
                     (app (name fvN) [lookupIn var (v "y") (v "s")]))
              ]
              (app (name fvN) [app (name (conName p)) (map v as)])
          withRenamings =
            foldr (\(j, i) body ->
                     SurfaceLet (local (renamed i)) (Just string)
                       (app (name freshN) [v (as !! i), avoid j]) body)
                  rebuilt (zip [0 ..] binders)
       in lamL (as ++ rs ++ ["s"]) $ case (map argumentRole args, as, binders) of
            -- The variable production: the whole node is what the map says.
            ([Occurrence], [y], _) -> lookupIn var (v y) (v "s")
            (_, _, []) -> rebuilt
            _ -> SurfaceLet (local "avoid") (Just (listOf string)) images withRenamings

    -- ---------------------------------------------------------------------
    oneBody allN =
      lamL ["e", "y", "n"]
        (app (name allN)
           [ v "e"
           , consOf pair (app (name "both") [string, self, v "y", v "n"]) (nilOf pair) ])

    -- A method's parameters: every argument, then a result for each argument
    -- of this language, in order (thesis §4.1.4, as 'Thena.Core.Reduce.iota'
    -- applies them).
    argNames args = [ local ("a" ++ show i) | i <- [0 .. length args - 1] ]
    recNames args = [ local ("r" ++ show i) | (i, arg) <- zip [0 :: Int ..] args, ownSort arg ]
    ownSort arg = argumentSort arg == OfLanguage (grammarName g)
    recOf args rs a = lookup a (zip [ x | (x, arg) <- zip (argNames args) args, ownSort arg ] rs)

-- ---------------------------------------------------------------------------
-- Surface, written by hand

name :: String -> Surface
name = SurfaceName

app :: Surface -> [Surface] -> Surface
app f [] = f
app f xs = SurfaceApp f (NE.fromList (map (SurfaceArg Explicit) xs))

lam :: [String] -> Surface -> Surface
lam [] b = b
lam xs b = SurfaceLam (NE.fromList [ SurfaceBinder Explicit x Nothing | x <- xs ]) b

arrows :: [Surface] -> Surface -> Surface
arrows ds r = foldr SurfaceArrow r ds

elimOn :: String -> [Surface] -> Surface -> [Surface] -> Surface -> Surface
elimOn d ps motive methods = SurfaceElim d ps motive methods []
