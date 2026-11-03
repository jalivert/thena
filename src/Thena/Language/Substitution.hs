-- | Generated substitution (MS6 phase 105, @ms6\/SPEC.md@ §4.7; one family per
-- occurrence class at MS8 phase 155).
--
-- For a language that reaches a class some language owns, one function per class
-- and one simultaneous substitution over all of them, written as ordinary surface
-- definitions and elaborated like any other — §1: nothing a block generates is
-- out of reach of a hand-written file.
--
-- > L.fresh-‹k›  : String -> List String -> String      -- for each class L owns
-- > L.fv-‹k›     : L -> List String                     -- for each class L reaches
-- > L.subst-all  : L -> List (And String O₁) -> … -> L   -- one map per class
-- > L.subst-‹k›  : L -> String -> O‹k› -> L              -- for each class L reaches
--
-- @O‹k›@ is the language that /owns/ class @k@ — the one whose variable
-- production reads an occurrence at it. For a one-class language that owns its
-- class, every @O‹k›@ is the language itself and these are MS6's four functions
-- with the class in their names.
--
-- **Simultaneous substitution is the primitive one**, because capture avoidance
-- is not structurally recursive otherwise: under a binder the body is substituted
-- with the map extended by the binder's renaming, which is the same recursive call
-- with a longer list, where renaming first and substituting after would recurse on
-- a term that is not a subterm.
--
-- **And it is simultaneous across classes too, which is why there is one
-- @L.subst-all@ and not one per class — his correction, 2026-10-04.**
-- Substituting for one class renames binders of /every/ class, so the recursive
-- call needs every map: substituting @λ y : X . y@, which has a free type
-- variable, for @x@ in @Λ X <: Top . x@ captures that @X@ unless the type binder
-- is renamed too. The names a class-@j@ binder avoids are therefore the free
-- @j@-names of the images of /every/ map, which is what @avoid-‹j›@ is.
--
-- **A binder is renamed only when keeping it would capture** — his choice,
-- 2026-09-21 — and @L.fresh-‹k› x avoid@ is the first of @x@, @x'@, @x''@, … not
-- among them, so @x@ itself whenever nothing would be captured. **A binder at a
-- class no language owns is never renamed at all**, because nothing can occur at
-- it; that falls out of the class not being in the set, with no branch of its own.
--
-- **A slot of another language is walked through that language's own
-- substitution** (MS8 phase 155, @ms8\/CLOSEOUT.md@ 25): @L.subst-all@ calls
-- @P.subst-all@ with the maps for the classes @P@ reaches, extended by any binder
-- of @L@ that scopes over the slot. @P@ is declared before @L@, so this is not
-- mutual recursion — which `~m5dvd` would need.
--
-- **Everything is done by @elim@**, and the only primitives are @String.dec@ and
-- @String.append@: two names are compared by eliminating a @Dec@, and a fresh one
-- is made by priming.
--
-- **@String.dec@, not @String.eq@** (MS6 phase 109a, his choice on
-- @ms6\/CLOSEOUT.md@ 32). A proof about substitution has to follow the same
-- decision the function makes, and on a name it does not know it can only do
-- that by eliminating the same term. @String.dec y x@ hands each branch its
-- evidence — @Eq String y x@ or its refutation — where @String.eq y x@ said only
-- which branch, so no proof over an open name could get past it.
module Thena.Language.Substitution
  ( substitutionDefinitions
  , substitutionNotations
  ) where

import qualified Data.List.NonEmpty as NE

import Data.List (nub)
import Data.Maybe (fromMaybe, listToMaybe)
import Thena.Core.Term (GlobalName (..), declarationNamed, inDeclarationOf, nameDotted, rootName, Literal (..))
import Thena.Global.Env (ArgRole (..))
import Thena.Language.Grammar
  ( Argument (..)
  , GProduction (..)
  , constructorProductions
  , Grammar (..)
  , Sort (..)
  , allOf
  , classOwner
  , classWord
  , classesSubstituted
  , freshOf
  , fvOf
  , substOf
  , variableProductions
  , variableRegex
  , grammarWord
  , grammarWritten
  )
import Thena.Language.Reader (Param (..), Block (..), Production (..), RawItem (..))
import Thena.Language.Regex (primingChar)
import Thena.Syntax.Lexer (BlockKind (..))
import Thena.Surface.Concrete (Plicity (..), Surface (..), SurfaceArg (..), SurfaceBinder (..), surfaceName)

-- | The definitions, as name, type and body, in the order they are declared —
-- each uses only the ones before it, and the ones of a language declared
-- earlier. None for a language that reaches no class with an owner.
--
-- @gs@ is the dependency graph: the grammars installed, including this one.
-- **Each is named in the language's own namespace** (MS10 phase 244), and a
-- reference to one is written with its path — @LC.fv-x@ — because that is what
-- the ordinary declaration path now admits and what the environment holds.
substitutionDefinitions :: [Grammar] -> Grammar -> [(GlobalName, Surface, Surface)]
substitutionDefinitions gs g =
  [ (freshOf langName (classWord k), arrows [string, listOf string] string, freshBody k) | k <- owned ]
    ++ [ (fvOf langName (classWord k), arrows [self] (listOf string), fvBody k) | k <- reached ]
    ++ [ (allOf langName, arrows (self : map mapType reached) self, allBody) | not (null reached) ]
    ++ [ (substOf langName (classWord k), arrows [self, string, ownerSelf k] self, oneBody k) | k <- reached ]
  where
    -- **MINTED RELATIVE, WRITTEN AS A WORD** (MS10 phase 258). @langName@ is
    -- what the generated names hang off and it must carry no namespace, because
    -- 'Thena.Engine.declaredIn' places what the declaring op admits; @lang@ is
    -- written into the types, so it is the word the author would have written.
    langName = grammarWritten g
    lang = grammarWord g
    -- **A CLASS IS CARRIED AS ITS NAME AND SPELLED AS ITS WORD** (MS10 phase
    -- 259). Resolved in scope, @A.x@ and @B.x@ are two classes, so what is
    -- compared below is the name; what a generated name hangs off, and what a
    -- bound variable this code writes is called, is
    -- 'Thena.Language.Grammar.classWord'.
    reached = classesSubstituted gs g
    owned = map fst (variableProductions g)
    -- **Constructors only** (MS8 phase 158): these become the eliminator's
    -- methods, one per constructor of the datatype, and a @notation@ block's
    -- function production is not one of them.
    prods = constructorProductions g

    -- **A prelude constructor, written with its path** (MS10 phase 248):
    -- @nil@ is @List.nil@ and @both@ is @And.both@, because a @data@
    -- declaration puts its constructors in its own namespace. **Generated code
    -- may not rely on an @open@** — the file it is spliced into need not have
    -- written one, and a name with a path resolves by the path alone.
    con d w = global (inDeclarationOf (declarationNamed (rootName d)) w)

    self = name lang
    string = name "String"
    listOf t = app (name "List") [t]
    pairType k = app (name "And") [string, ownerSelf k]
    mapType = listOf . pairType

    -- ---------------------------------------------------------------------
    -- Which language owns a class, and what it generated. 'reached' has
    -- filtered out the classes with no owner, so these are total on it.
    owner k = case classOwner gs g k of
      Just h -> h
      Nothing -> g
    ownerName k = grammarWord (owner k)
    ownerSelf = name . ownerName
    -- The owning language's variable production for the class: what a renamed
    -- binder of that class becomes.
    ownerVar k y = app (global (varConOf (owner k) k)) [y]
    varConOf h k = fromMaybe (rootName "") (listToMaybe
      [ gproductionName p | (c', p) <- variableProductions h, c' == k ])
    -- The classes another language has substitution for — a subset of this
    -- one's, because reaching it reaches everything it reaches.
    reachedBy l = classesSubstituted gs (grammarNamed l)
    grammarNamed l = case [ h | h <- gs, grammarName h == l ] of
      h : _ -> h
      [] -> g

    -- A bound name may not be one the generated code refers to, or a
    -- constructor called @s@ would be shadowed by the map. Primed until free,
    -- as 'Thena.Driver.grammarDatatype' primes a constructor's binders.
    -- **Every grammar's**, not only this one's, since a foreign slot is walked
    -- through its own language's functions.
    -- **Only the ROOT-LEVEL words are here since MS10 phase 248.** A
    -- constructor, a production and every generated function now carry a path,
    -- and a qualified name skips Γ altogether, so no binder can shadow one.
    -- What is left is a language's own short name — which is the alias
    -- 'Thena.Core.Term.declarationNamed' supplies and so /is/ shadowable — and
    -- the prelude names this code writes short.
    referenced =
      map (nameDotted . grammarName) gs
        ++ [ "String", "List", "And", "Comparison", "Dec", "Eq" ]
    local x | x `elem` referenced = local (x ++ "'")
            | otherwise = x
    v = name . local
    lamL = lam . map local

    nilOf t = app (con "List" "nil") [t]
    consOf t h rest = app (con "List" "cons") [t, h, rest]

    -- @y ∈ xs@, as a 'Comparison': @same@ when it is there.
    member y xs =
      elimOn "List" [string] (lamL ["l"] (name "Comparison"))
        [ con "Comparison" "different"
        , lamL ["b", "bs", "rb"]
            (compareNames (name "Comparison") y (v "b") (con "Comparison" "same") (v "rb"))
        ]
        xs

    -- The first method when @y@ and @key@ are the same name, the second
    -- otherwise, deciding with @String.dec@ — whose evidence each method is
    -- given and ignores. **Qualified since MS10 phase 262**, so it is out of
    -- 'referenced' for the same reason @String.append@ never was: a path
    -- resolves on its own and no binder can shadow it.
    compareNames ty y key whenSame whenDifferent =
      elimOn "Dec" [app (name "Eq") [string, y, key]] (lamL ["d"] ty)
        [lamL ["p"] whenSame, lamL ["n"] whenDifferent]
        (app (qname ["String"] "dec") [y, key])

    -- The first constructor's method when @c@ is @same@, the second's otherwise.
    decide ty c whenSame whenDifferent =
      elimOn "Comparison" [] (lamL ["q"] ty) [whenSame, whenDifferent] c

    -- Everything in @ys@ that is not in @bound@, onto @acc@. **Only a foreign
    -- slot needs it**: this language's own subterms are given the bound names on
    -- the way down, where a slot of another language answers with its own free
    -- names and cannot be.
    without ys bound acc =
      elimOn "List" [string] (lamL ["l"] (listOf string))
        [ acc
        , lamL ["h", "hs", "rh"]
            (decide (listOf string) (member (v "h") bound) (v "rh") (consOf string (v "h") (v "rh")))
        ]
        ys

    -- ---------------------------------------------------------------------
    -- L.fresh-‹k›: the fuel is the list itself. Among x, xc, …, xc⁽ⁿ⁾ one is not
    -- among n names, so n primings are enough and the recursion is on the list.
    --
    -- **The priming character comes from the class, not from a hardcoded @'@**
    -- (MS6 closeout 23, phase 146; per class at MS8 phase 155).
    -- 'Thena.Language.Regex.primingChar' picks one the class is closed under, so
    -- every name this mints is a name the language can write back **by
    -- construction** — it tries @'@ first, so a class that accepts it keeps the
    -- names it always produced.
    --
    -- **When the class admits no such character the generated code keeps @'@**,
    -- and the name it mints then cannot be printed in the notation. That is not
    -- prevented — his second principle — and 'Thena.Language.Grammar.checkGrammar'
    -- warns at the block instead, so the author is told rather than refused.
    primeChar k = fromMaybe '\'' (variableRegex g k >>= primingChar)

    freshBody k =
      lamL ["y", "avoid"]
        (app (elimOn "List" [string] (lamL ["l"] (arrows [string] string))
                [ lamL ["c"] (v "c")
                , lamL ["a", "rest", "r", "c"]
                    (decide string (member (v "c") (v "avoid"))
                       (app (v "r") [app (qname ["String"] "append") [v "c", SurfaceLiteral (LString [primeChar k])]])
                       (v "c"))
                ]
                (v "avoid"))
             [v "y"])

    -- ---------------------------------------------------------------------
    -- L.fv-‹k›: an accumulator and the names bound on the way down, so that
    -- neither an append nor a removal is needed for this language's own
    -- subterms. A name may be listed twice; it is a list, not a set, and
    -- everything that reads it only asks membership.
    --
    -- **Only the binders at class k remove anything**: a binder of another class
    -- does not bind a k-name, which is the whole of what the class on a role is
    -- for.
    fvBody k =
      lamL ["t"]
        (app (elimOn lang [] (lamL ["u"] (arrows [listOf string, listOf string] (listOf string)))
                (map (fvMethod k) prods) (v "t"))
             [nilOf string, nilOf string])

    fvMethod k p =
      let args = gproductionArguments p
          as = argNames args
          rs = recNames args
          under bs = foldr (consOf string . v) (v "bound") [ as !! i | i <- bs, binderAt args i == Just k ]
          step (a, arg) acc = case (argumentRole arg, recOf args rs a, argumentSort arg) of
            (Occurrence c, _, _) | c == k ->
              decide (listOf string) (member (v a) (v "bound")) acc (consOf string (v a) acc)
            (Scope bs, Just r, _) -> app (v r) [under bs, acc]
            (Plain, Just r, _) -> app (v r) [v "bound", acc]
            -- A slot of another language that can hold a free k-name: ask that
            -- language, then take out the names bound on the way in.
            (Scope bs, Nothing, OfLanguage l) | k `elem` reachedBy l ->
              without (app (global (fvOf l (classWord k))) [v a]) (under bs) acc
            (Plain, Nothing, OfLanguage l) | k `elem` reachedBy l ->
              without (app (global (fvOf l (classWord k))) [v a]) (v "bound") acc
            _ -> acc
       in lamL (as ++ rs ++ ["bound", "acc"]) (foldr step (v "acc") (zip as args))

    -- ---------------------------------------------------------------------
    -- L.subst-all.
    allBody =
      lamL ["t"]
        (elimOn lang [] (lamL ["u"] (arrows (map mapType reached) self))
           (map allMethod prods) (v "t"))

    mapVar k = "s-" ++ classWord k

    -- What the class-k map sends @y@ to: the first pair that names it, or @y@
    -- itself as a term of the class's owning language.
    lookupIn k y s =
      elimOn "List" [pairType k] (lamL ["l"] (ownerSelf k))
        [ ownerVar k y
        , lamL ["p", "ps", "rp"]
            (elimOn "And" [string, ownerSelf k] (lamL ["q"] (ownerSelf k))
               [ lamL ["key", "w"] (compareNames (ownerSelf k) y (v "key") (v "w") (v "rp")) ]
               (v "p"))
        ]
        s

    allMethod p =
      let args = gproductionArguments p
          as = argNames args
          rs = recNames args
          -- A binder is renamed when its class has a map; one at a class no
          -- language owns keeps its name, because nothing can occur at it.
          binders = [ i | (i, arg) <- zip [0 :: Int ..] args
                        , Binder c <- [argumentRole arg], c `elem` reached ]
          binderClasses = nub [ c | i <- binders, Just c <- [binderAt args i] ]
          bindersAt c = [ i | i <- binders, binderAt args i == Just c ]
          renamed i = "z" ++ show i
          avoidName c = "avoid-" ++ classWord c
          -- A renaming for each binder of the class, and each avoids the names
          -- already chosen for the ones before it and the names of the ones
          -- after — the ones of its own class only, since no other can capture.
          avoidTerm i c =
            let bs = bindersAt c
                m = length (takeWhile (/= i) bs)
             in foldr (consOf string) (v (avoidName c))
                  ([ v (renamed i') | i' <- take m bs ] ++ [ v (as !! i') | i' <- drop (m + 1) bs ])
          -- The maps to hand a subterm: each extended with the renamings of the
          -- binders of its own class that scope over it. The last binder at the
          -- head, so that of two binders with one name the later is the one
          -- found, as the later shadows on paper.
          mapsOf ks bs =
            [ foldl (\rest i -> consOf (pairType c)
                                  (app (con "And" "both")
                                     [string, ownerSelf c, v (as !! i), ownerVar c (v (renamed i))])
                                  rest)
                    (v (mapVar c))
                    [ i | i <- bs, i `elem` binders, binderAt args i == Just c ]
            | c <- ks ]
          descend a arg bs = case (recOf args rs a, argumentSort arg) of
            (Just r, _) -> app (v r) (mapsOf reached bs)
            -- A slot of another language, walked through its own substitution.
            -- Nothing to do when that language reaches no class: nothing in it
            -- can mention a name.
            (Nothing, OfLanguage l) | not (null (reachedBy l)) ->
              app (global (allOf l)) (v a : mapsOf (reachedBy l) bs)
            _ -> v a
          rebuilt = app (global (gproductionName p))
            [ case argumentRole arg of
                Binder _ | i `elem` binders -> v (renamed i)
                Scope bs -> descend a arg bs
                Plain -> descend a arg []
                _ -> v a
            | (i, (a, arg)) <- zip [0 :: Int ..] (zip as args) ]
          -- The names a class-c binder must avoid: the free c-names of what
          -- every map sends each free name of this node to. A map's images are
          -- terms of the class's owning language, so it contributes only when
          -- that language reaches c at all.
          images c =
            foldl (\acc k ->
                     elimOn "List" [string] (lamL ["l"] (listOf string))
                       [ acc
                       , lamL ["y", "ys", "ry"]
                           (elimOn "List" [string] (lamL ["l"] (listOf string))
                              [ v "ry", lamL ["h", "hs", "rh"] (consOf string (v "h") (v "rh")) ]
                              (app (global (fvOf (grammarName (owner k)) (classWord c))) [lookupIn k (v "y") (v (mapVar k))]))
                       ]
                       (app (global (fvOf langName (classWord k))) [app (global (gproductionName p)) (map v as)]))
                  (nilOf string)
                  [ k | k <- reached, c `elem` reachedBy (grammarName (owner k)) ]
          withRenamings =
            foldr (\i body ->
                     let c = fromMaybe (rootName "") (binderAt args i)
                      in SurfaceLet (local (renamed i)) (Just string)
                           (app (global (freshOf (grammarWritten (owner c)) (classWord c))) [v (as !! i), avoidTerm i c]) body)
                  rebuilt binders
       in lamL (as ++ rs ++ map mapVar reached) $ case (map argumentRole args, as) of
            -- A variable production: the whole node is what its class's map says.
            ([Occurrence c], [y]) -> lookupIn c (v y) (v (mapVar c))
            _ | null binders -> rebuilt
              | otherwise ->
                  foldr (\c body -> SurfaceLet (local (avoidName c)) (Just (listOf string)) (images c) body)
                        withRenamings binderClasses

    -- ---------------------------------------------------------------------
    oneBody k =
      lamL ["e", "y", "n"]
        (app (global (allOf langName))
           (v "e" : [ if c == k
                        then consOf (pairType c)
                               (app (con "And" "both") [string, ownerSelf c, v "y", v "n"])
                               (nilOf (pairType c))
                        else nilOf (pairType c)
                    | c <- reached ]))

    -- A method's parameters: every argument, then a result for each argument
    -- of this language, in order (thesis §4.1.4, as 'Thena.Core.Reduce.iota'
    -- applies them).
    argNames args = [ local ("a" ++ show i) | i <- [0 .. length args - 1] ]
    recNames args = [ local ("r" ++ show i) | (i, arg) <- zip [0 :: Int ..] args, ownSort arg ]
    ownSort arg = argumentSort arg == OfLanguage (grammarName g)
    recOf args rs a = lookup a (zip [ x | (x, arg) <- zip (argNames args) args, ownSort arg ] rs)

-- | The class a binder argument of this production binds at, by position — a
-- 'Thena.Global.Env.Scope' names positions, and the class is on the role there
-- rather than carried twice.
binderAt :: [Argument] -> Int -> Maybe GlobalName
binderAt args i = case drop i args of
  a : _ | Binder cn <- argumentRole a -> Just cn
  _ -> Nothing

-- | The @notation@ block generated substitution declares — @E[x -> M]@, one
-- production per class the grammar has substitution for (§6.3, §4.8; MS8 phase
-- 159, `~hwxrx`). Empty for a grammar that has none.
--
-- **This is the demotion of the one privileged notation to an instance of the
-- ordinary one.** Until phase 159 the bracket form was Earley rules that
-- "Thena.Language.Judgment" added to a /rule's/ grammar and a special case in
-- the elaborator that recognised them by node name. Now it is what any
-- user-declared spelling is: a production of the grammar whose name is a
-- declared function, so the parser, the builder and the printer need to know
-- nothing about it. **His ruling, 2026-10-07**: `Γ[X -> T]` is proof the
-- mechanism exists and is granted to exactly one function as a privilege, and
-- `~hwxrx` demotes it.
--
-- **The user declares nothing and no spelling changes.** The block is generated
-- as a surface item, like the definitions above, and runs through the same
-- 'Thena.Language.Grammar.checkNotation' a written one does — which is also what
-- checks that each function's type really takes what its slots hold. **So it is
-- spliced AFTER the definitions**: the check needs the function declared.
--
-- **The names of the slots are metavariables already in scope** — the grammar's
-- own for the term being substituted into, the class's for the name, and the
-- /owning/ language's for what replaces it, since the right of @->@ is a term of
-- the class's owner (§6.3). They must be distinct, because two slots of one name
-- are one non-linear argument (§4.3) and the two readings would have to be equal;
-- a language that owns its own class takes its next metavariable rather than
-- repeating one.
--
-- **Only the one-pair form.** @E[x -> M, y -> N]@ is simultaneous substitution and
-- builds a /list/ per class, which no object grammar spells, so it stays what it
-- was: sugar in a rule's own grammar, elaborating to @L.subst-all@. The split is
-- principled rather than arbitrary — the one-pair form /is/ a function applied to
-- what its slots hold, which is exactly what a notation production is, and the
-- list form constructs an argument instead.
substitutionNotations :: [Grammar] -> Grammar -> [Block]
substitutionNotations gs g
  | null prods = []
  | otherwise  = [Block NotationBlock lang [] prods []]
  where
    -- **The header is the word a user would write** (MS10 phase 258), and
    -- 'Thena.Language.Grammar.checkNotation' resolves it in the scope the block
    -- sits in — the same door a written @notation Ty where@ goes through.
    lang = grammarWord g
    -- **The three names are the production's own, since MS8 phase 171.** They
    -- used to be metavariables hunted out of the grammars — the target from this
    -- one, the replacement from whichever language owns the class — and the hunt
    -- existed only because a slot's word had to be a metavariable somewhere. A
    -- @notation@ production names its arguments now, so the generator says what
    -- it means and no grammar has to carry a word for it.
    prods =
      -- **A CLASS IS WRITTEN AS ITS WORD HERE TOO** (MS10 phase 259), both in
      -- the function's name and in the slot's ascription — and the ascription
      -- is then resolved in scope by 'Thena.Language.Grammar.checkNotation',
      -- which is the same door a written @notation@ block's goes through.
      [ Production 0 (nameDotted (substOf (grammarWritten g) (classWord k)))
          [ Param (target k) Nothing, Param (classWord k) (Just (classWord k)), Param (replacement k) Nothing ]
          Nothing
          (map Word [target k, "[", classWord k, "->", replacement k, "]"])
      | k <- classesSubstituted gs g
      ]

    -- **Three parameters: the term, the name replaced, and what replaces it.**
    -- The middle one reads a name of the class, so it is the one that carries an
    -- ascription — @String@ is all its declared argument says, and this grammar
    -- may read several classes over @String@.
    --
    -- The two language slots only have to avoid the class's own name, which is
    -- the middle parameter's. They used to be metavariables hunted out of the
    -- grammars, and the hunt existed only because a slot's word had to be a
    -- metavariable somewhere; a parameter list says what it means.
    target k = pick "e" [ c | c <- ["e", "e1"], c /= classWord k ]
    replacement k = pick "n" [ c | c <- ["n", "n1"], c /= classWord k, c /= target k ]
    pick dflt cs = fromMaybe dflt (listToMaybe cs)

-- ---------------------------------------------------------------------------
-- Surface, written by hand

name :: String -> Surface
name = SurfaceName []

-- | A name with a path, which no local can shadow (MS10 phase 246).
--
-- **@String.append@ is why this exists.** A primitive lives in its type's
-- namespace, and a qualified name is resolved by its path alone — so it is not
-- in 'referenced' above, where every /root/ name the generated code mentions
-- has to be, to stop a bound variable shadowing one.
qname :: [String] -> String -> Surface
qname = SurfaceName

-- | A reference to a generated global, written with its path (MS10 phase 244).
--
-- **Qualified and never short**, because the short word would be looked for in
-- the context first and the recursion assumption of the declaration being
-- elaborated is the one local there — @LC.subst-all@ reaching for @subst-all@
-- while @LC.subst-x@ is being declared would find nothing at all.
global :: GlobalName -> Surface
global = surfaceName

app :: Surface -> [Surface] -> Surface
app f [] = f
app f xs = SurfaceApp f (NE.fromList (map (SurfaceArg Explicit) xs))

lam :: [String] -> Surface -> Surface
lam [] b = b
lam xs b = SurfaceLam (NE.fromList [ SurfaceBinder Explicit x Nothing | x <- xs ]) b

arrows :: [Surface] -> Surface -> Surface
arrows ds r = foldr SurfaceArrow r ds

-- | **The datatype is named by a bare word and resolved like any other**, so
-- nothing generated here writes a path: @elim List@ finds @List.List@ through
-- the same lookup a user's @elim List@ goes through.
elimOn :: String -> [Surface] -> Surface -> [Surface] -> Surface -> Surface
elimOn d ps motive methods = SurfaceElim [] d ps motive methods []
