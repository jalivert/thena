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
  , buildCore
  , buildSurface
  , skeletonOf
  , printTerm
  , printRegion
  , production
  , languageNames
  , productionNames
  , objectInput
  , objectText
  , atCharacters
  , arguments
  ) where

import Data.List (elemIndex, intercalate)
import qualified Data.List.NonEmpty as NE

import Thena.Core.Term (Core (..), GlobalName (..), Literal (..))
import Thena.Errors (BuildError (..))
import Thena.Language.Earley (Piece (..), Tree (..))
import qualified Thena.Language.Earley as Earley
import Thena.Language.Grammar
  ( Argument (..)
  , GProduction (..)
  , Grammar (..)
  , Item (..)
  , Sort (..)
  , earleyRules
  )
import Thena.Syntax.Lexer (rawEscapes)
import Thena.Instral.Pattern (Skeleton (..), Slot (..))
import Thena.Language.Regex (matches)
import Thena.Surface.Concrete (Plicity (..), Surface (..), SurfaceArg (..))

-- | The term a reading denotes.
--
-- **A reading alone, so a splice has nothing to be**: 'buildSurface' supplies
-- them from a surface term, and 'skeletonOf' leaves them as holes.
buildTerm :: [Grammar] -> Tree -> Either BuildError Core
buildTerm gs = buildCore gs []

-- | The term a reading denotes, with @splices@ supplying its @${…}@ in order
-- (MS6 phase 110) — 'buildSurface' for 'Core', and what the development
-- calculus's reader builds a region with.
buildCore :: [Grammar] -> [Core] -> Tree -> Either BuildError Core
buildCore gs splices = build
  where
    build tree = case tree of
      SpliceOf k -> supplied k
      Node name children -> do
        p <- maybe (Left (NoSuchProduction name)) Right (production gs name)
        args <- traverse (slot name) =<< arguments p children
        Right (foldl App (Global (GlobalName name) []) args)
      _ -> Left (NotForSlot "" (shapeOf tree))

    slot name (a, child) = case (argumentSort a, child) of
      (_, SpliceOf k)    -> supplied k
      (OfClass _ t _, _) -> Primitive <$> literal name (argumentName a) t child
      (OfLanguage _, _)  -> build child

    supplied k = case drop k splices of
      e : _ -> Right e
      []    -> Left (NotForSlot "" (shapeOf (SpliceOf k)))

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

-- | The tagged literal a term is written as — @LC`( λ x : ι . x )`@ — or
-- 'Nothing' when it is not one an object language can write: something a
-- grammar's production does not head, a constructor at level arguments or at
-- the wrong arity, or a literal its class would not read back.
--
-- **It does not reduce** (phase 110). A term prints as what it is, so a name
-- the user gave a term stays that name in a goal, and a stuck call is not
-- unfolded into the generated code behind it. Both spellings of a saturated
-- constructor application are accepted instead, which is what reducing bought.
--
-- @render@ prints what the notation cannot — it is the host's own printer, and
-- what it returns stands inside a splice.
printTerm :: [Grammar] -> (Core -> String) -> Core -> Maybe String
printTerm gs render t = do
  d <- draft gs t
  txt <- settle gs render d
  let GlobalName lang = draftLanguage d
  pure (lang ++ "`" ++ txt ++ "`")

-- | What stands inside the region, without the tag and the backticks.
printRegion :: [Grammar] -> (Core -> String) -> Core -> Maybe String
printRegion gs render t = settle gs render =<< draft gs t

-- | A term laid out for printing, before it is known where the fences go.
data Draft
  = DNode GProduction GlobalName [Draft] Core
    -- ^ a production, the grammar whose nonterminal it is, **one child per
    -- slot item** — a name written twice is printed at both its positions
    -- (§4.3) — and the term it came from
  | DToken String                  -- ^ a token class's match, printed as itself
  | DForeign Core                  -- ^ not object text: it goes in a splice
  | DFenced GlobalName Core Draft
    -- ^ an object term the reading must keep whole: a splice holding a literal
    -- of its own

-- | The nonterminal a draft is read at.
draftLanguage :: Draft -> GlobalName
draftLanguage d = case d of
  DNode _ g _ _ -> g
  DFenced g _ _ -> g
  _             -> GlobalName ""

-- | A term laid out, with nothing fenced yet.
--
-- A token class's slot keeps its match as a 'DToken' only when the class would
-- read that text back — @"a b"@ is a fine 'String' and no identifier — so the
-- printer never writes a text the reader would take apart differently.
draft :: [Grammar] -> Core -> Maybe Draft
draft gs term = do
  (name@(GlobalName n), args) <- spine term
  p <- production gs n
  g <- grammarOf gs name
  let names = map argumentName (gproductionArguments p)
      slotOf (x, sort) = do
        k <- elemIndex x names
        a <- at k args
        pure $ case sort of
          OfClass _ _ re -> token re a
          OfLanguage _   -> maybe (DForeign a) id (draft gs a)
  if length args == length names then Just () else Nothing
  children <- traverse slotOf [ (x, s) | Slot x s _ <- gproductionItems p ]
  pure (DNode p (grammarName g) children term)
  where
    spine t = case t of
      Canonical c ls as | null ls -> Just (c, as)
      Global c ls       | null ls -> Just (c, [])
      App {}                      -> case flatten t [] of
        (Global c ls, as) | null ls -> Just (c, as)
        _                           -> Nothing
      _ -> Nothing
    flatten t acc = case t of
      App f a -> flatten f (a : acc)
      _       -> (t, acc)

    token re a = case a of
      Primitive (LString s) | readsBack re s        -> DToken s
      Primitive (LChar c)   | readsBack re [c]      -> DToken [c]
      Primitive (LInt k)    | readsBack re (show k) -> DToken (show k)
      _ -> DForeign a
    readsBack re s = length s `elem` matches re s

    at k xs = case drop k xs of
      y : _ -> Just y
      []    -> Nothing

-- | The grammar a production belongs to.
grammarOf :: [Grammar] -> GlobalName -> Maybe Grammar
grammarOf gs name =
  case [ g | g <- gs, p <- grammarProductions g, gproductionName p == name ] of
    g : _ -> Just g
    []    -> Nothing

-- | **Print it, read it back, and fence what the reading disagrees about.**
--
-- His conclusion, 2026-09-22: start with nothing and add. The first attempt
-- writes the term flat; the parser is asked for that text at the same
-- nonterminal; and the attempt stands only when the reading is unique and is
-- the tree that was meant. Otherwise the outermost subterm still written
-- inline becomes a splice — a literal of its own, which the parse around it
-- cannot look into (§7.6) — and the text is read back again.
--
-- **A grammar that brackets its productions never reaches the second
-- attempt**; one that does not gets exactly the splices @examples/05@ writes
-- by hand. And because the check is on the text rather than on the shape of
-- the grammar, it catches what no table over positions could: a token class
-- matching one of the grammar's own terminals, which nothing reserves, so that
-- @let f = a in in b@ is fenced where @let f = a b in c@ is not.
--
-- 'Nothing' when fencing everything still does not read back. The caller then
-- prints the term in the host's syntax, which always reads.
settle :: [Grammar] -> (Core -> String) -> Draft -> Maybe String
settle gs render = go
  where
    rules = earleyRules gs
    go d =
      let (chunks, input, tree) = laid gs render d
          GlobalName lang       = draftLanguage d
       in if Earley.parse rules (Earley.StartAt lang) input == Right tree
            then Just (concatMap escaped chunks)
            else case loose d of
              path : _ -> go (fenceAt path d)
              []       -> Nothing

-- | A piece of a region's text: object text, which is escaped as the lexer
-- unescapes it, or a splice, which is the host's syntax and already written.
data Chunk = Written String | Spliced String

-- | What goes between the backticks. 'rawEscapes' is the lexer's own list, so
-- the printer cannot drift from what reads it.
escaped :: Chunk -> String
escaped c = case c of
  Written s -> concatMap esc s
  Spliced s -> s
  where
    esc ch | ch `elem` rawEscapes = ['\\', ch]
           | otherwise            = [ch]

-- | The text, the input the parser is given for it, and the tree it must come
-- back as. One traversal, because the splice indices have to agree.
laid :: [Grammar] -> (Core -> String) -> Draft -> ([Chunk], [Piece], Tree)
laid gs render d0 = let (cs, ps, tr, _) = go 0 d0 in (cs, ps, tr)
  where
    go k d = case d of
      DToken s   -> ([Written s], map Char s, Token s, k)
      DForeign c -> splice k (render c)
      DFenced (GlobalName lang) c inner -> case settle gs render inner of
        Just txt -> splice k (lang ++ "`" ++ txt ++ "`")
        Nothing  -> splice k (render c)
      DNode p _ children _ ->
        let step (cs, ps, trs, k1, rest) i = case i of
              Terminal t -> (cs ++ [[Written t]], ps ++ [map Char t], trs, k1, rest)
              Slot {} -> case rest of
                c : more -> let (cs1, ps1, tr1, k2) = go k1 c
                             in (cs ++ [cs1], ps ++ [ps1], trs ++ [tr1], k2, more)
                []       -> (cs, ps, trs, k1, rest)
            (css, pss, trs', k', _) =
              foldl step ([], [], [], k, children) (gproductionItems p)
            GlobalName name = gproductionName p
         in ( intercalate [Written " "] css
            , intercalate [Char ' '] pss
            , Node name trs'
            , k'
            )
    splice k s = ([Spliced ("${" ++ s ++ "}")], [Splice k], SpliceOf k, k + 1)

-- | The object subterms still written inline: the order they are fenced in.
-- The root is not among them, because a region is already delimited by its
-- backticks.
--
-- **Deepest first, and a subterm with slots of its own before a leaf.** Any
-- order is correct — the reading is checked either way — but this one fences
-- what a person would fence, and the two rules are for two different reasons.
--
-- Deepest first keeps a fence as small as the disagreement: inside a judgment,
-- @f a b !@ is settled by @${Ex`f a`} b !@, and fencing the outermost subterm
-- instead would wrap the whole argument for the sake of its left half.
--
-- Branching first, because fencing a leaf rarely settles anything: in @f a b@
-- the reading in dispute is over the juxtaposition, so @f ${Ex`a b`}@ settles
-- it where @${Ex`f`} a b@ does not, and an order that took a leaf first would
-- write both splices.
loose :: Draft -> [[Int]]
loose d0 = [ p | (p, d) <- deepest, branching d ]
        ++ [ p | (p, d) <- deepest, not (branching d) ]
  where
    deepest = concat (reverse (levels [([], d0)]))
    levels [] = []
    levels ds =
      let kids = [ (path ++ [i], c)
                 | (path, DNode _ _ cs _) <- ds, (i, c) <- zip [0 ..] cs ]
       in [ (p, d) | (p, d@DNode {}) <- kids ] : levels kids
    branching d = case d of
      DNode p _ _ _ -> not (null [ () | Slot _ (OfLanguage _) _ <- gproductionItems p ])
      _             -> False

-- | Make the draft at a path a splice of its own.
fenceAt :: [Int] -> Draft -> Draft
fenceAt [] d = case d of
  DNode _ g _ c -> DFenced g c d
  _             -> d
fenceAt (i : is) d = case d of
  DNode p g cs c ->
    DNode p g [ if j == i then fenceAt is k else k | (j, k) <- zip [0 ..] cs ] c
  _ -> d


production :: [Grammar] -> String -> Maybe GProduction
production gs name =
  case [ p | g <- gs, p <- grammarProductions g, gproductionName p == GlobalName name ] of
    p : _ -> Just p
    [] -> Nothing

-- ---------------------------------------------------------------------------
-- Regions (MS6 phase 104, shared by both readers at phase 110)
-- ---------------------------------------------------------------------------

-- | The languages installed, by the name a tag would write.
languageNames :: [Grammar] -> [String]
languageNames gs = [ n | g <- gs, let GlobalName n = grammarName g ]

-- | The productions of one installed language, by name.
--
-- **Of that language and not of any**, which is what @LC[app]@ asks: a
-- production name is unique across grammars (phase 101), so the filter changes
-- no accepted literal and it is what lets the refusal name the language.
productionNames :: [Grammar] -> String -> [String]
productionNames gs lang =
  [ n | g <- gs, GlobalName lang == grammarName g
      , p <- grammarProductions g, let GlobalName n = gproductionName p ]

-- | The pieces the object parser reads. A region is text and splices, and
-- both readers have it that way — @Left@ text, @Right@ what fills a slot — so
-- these three work for either (phase 110).
--
-- **A splice is one column**, whatever it holds, because it completes one slot
-- (@ms6\/SPEC.md@ §7.6). Its number is its position among the splices, which
-- is how 'buildSurface' and 'buildCore' find it again.
objectInput :: [Either String a] -> [Piece]
objectInput = go 0
  where
    go _ [] = []
    go k (Left txt : rest)  = map Char txt ++ go k rest
    go k (Right _ : rest)   = Splice k : go (k + 1) rest

-- | What the region says, for a message. A splice stands for itself: the
-- printer is "Thena.Repl"'s and this module sits below it.
objectText :: [Either String a] -> String
objectText = concatMap piece
  where
    piece pc = case pc of
      Left txt -> txt
      Right _  -> spliceMark

spliceMark :: String
spliceMark = "$" ++ ['{'] ++ "…" ++ ['}']

-- | A parser position is a column and a message is about characters.
--
-- A splice is one column and several characters, so 'Earley.Stuck' is moved to
-- where its column begins in 'objectText'. Everything else says the same thing
-- in both.
atCharacters :: [Either String a] -> Earley.ParseFailure -> Earley.ParseFailure
atCharacters ps why = case why of
  Earley.Stuck p expected -> Earley.Stuck (sum (take p (concatMap widths ps))) expected
  other -> other
  where
    widths pc = case pc of
      Left txt -> map (const 1) txt
      Right _  -> [length spliceMark]
