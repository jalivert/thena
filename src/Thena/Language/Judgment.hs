-- | A judgment's rules, and the datatype they are (MS6 phase 108;
-- @ms6\/SPEC.md@ §6).
--
-- A @judgment@ block is its notation — installed as a 'JudgmentBlock' grammar,
-- as a context's lookup is (phase 107) — and its rules. **A rule is object
-- text**, read with the grammars installed when the load reaches the block,
-- plus three things only a rule can write:
--
-- * **a metavariable** where a term of its language goes, with a suffix of
--   primes, digits or subscripts (§6.2): @M@, @M'@, @M₁@. Where a token class
--   goes, the class's own name is the metavariable: @x@, @x'@. **Nothing else
--   stands there** — a rule has no object literals, so a name that is not a
--   metavariable is an error rather than an implicit binding;
-- * **a substitution** @E[x->M]@, @E[x->M, y->N]@ (§6.3), in any language that
--   has one, as the functions of §4.7;
-- * above the rule line, **a sequence of premises**, each a judgment,
--   optionally named @d : …@ — separated by whitespace, so where one premise
--   ends is the parser's question, and a line break is whitespace like any
--   other.
--
-- These are extra rules for the same Earley parser ('ruleGrammar'), named with
-- a space so that no production can be called the same.
--
-- A rule becomes a constructor (§6.5): its metavariables, quantified in order
-- of first appearance (§6.2) or as its @∀@ writes them (§6.4); then its
-- premises; then its conclusion, which is the judgment's notation applied.
-- @:show@ prints what came out, and it could have been written by hand.
module Thena.Language.Judgment
  ( judgmentDatatype
  , ruleGrammar
  , isMetavariable
  ) where

import Data.Char (isAlphaNum)
import Data.List (nub)
import qualified Data.List.NonEmpty as NE

import Thena.Core.Term (GlobalName (..))
import qualified Thena.Language.Earley as Earley
import Thena.Language.Earley (Piece (..), Start (..), Tree (..))
import Thena.Language.Grammar
  ( Argument (..)
  , GProduction (..)
  , Grammar (..)
  , GrammarError (..)
  , GrammarProblem (..)
  , Item (..)
  , RulePart (..)
  , RuleProblem (..)
  , Sort (..)
  , earleyRules
  , substitutionNames
  , variableProduction
  )
import Thena.Errors (BuildError (..))
import Thena.Global.Env (ArgRole (..))
import Thena.Language.Build (arguments, production)
import Thena.Language.Reader (RawRule (..))
import Thena.Language.Regex (Regex (..), alternatives, andThen, complement, fromRanges, oneOf, singleChar, star)
import Thena.Surface.Concrete (Plicity (..), Surface (..), SurfaceArg (..), SurfaceBinder (..), SurfaceConstructor (..), SurfaceData (..))
import Thena.Surface.Read (parseSurfaceText)
import Thena.Syntax.Lexer (BlockKind (..))

-- | The judgment's datatype, one constructor per rule, and the roles
-- 'Thena.Instral.Ops.MakeData' carries — all 'Plain': nothing here is object
-- syntax. **@gs@ has the judgment's own grammar in it**, since a rule may have
-- a premise of the judgment it defines.
judgmentDatatype :: [Grammar] -> Grammar -> [RawRule] -> Either GrammarError (SurfaceData, [[ArgRole]])
judgmentDatatype gs g rules = do
  ctors <- traverse (\r -> either (Left . GrammarError JudgmentBlock name . InRule (ruleName r)) Right
                                  (constructor gs g r))
                    rules
  Right ( SurfaceData name [] (foldr (SurfaceArrow . typeOf) (SurfaceUniverse 0) indices) (map fst ctors)
        , map snd ctors )
  where
    GlobalName name = grammarName g
    indices = concatMap gproductionArguments (grammarProductions g)
    typeOf = SurfaceName . sortType . argumentSort

-- | One rule, as a constructor.
constructor :: [Grammar] -> Grammar -> RawRule -> Either RuleProblem (SurfaceConstructor, [ArgRole])
constructor gs g r = do
  -- **Each premise line is parsed on its own**: a line break ends a premise,
  -- and only premises sharing a line are told apart by parsing.
  premises <- concat <$> traverse (fmap premisesOf . parseIn Premises "premises" (StartAt premisesNT))
                                  (rulePremises r)
  conclusion <- parseIn Conclusion judgment (StartRule judgment) (ruleConclusion r)
  mentioned <- either (Left . RuleUnbuilt) (Right . nub . concat)
                 (traverse (mentions gs) (map snd premises ++ [conclusion]))
  -- A premise's name is the user's, and must not be taken for anything else.
  let named = [ n | (Just n, _) <- premises ]
  case [ n | n <- named, isMetavariable gs n ] of
    n : _ -> Left (PremiseNameIsMetavariable n)
    [] -> Right ()
  case [ n | (n, k) <- zip named [0 :: Int ..], n `elem` take k named || n `elem` types ] of
    n : _ -> Left (PremiseNameTaken n)
    [] -> Right ()
  -- The quantified metavariables: written, or implicit in order of first
  -- appearance (§6.2), each at its language's type or its class's.
  (quantified, renaming) <- case ruleQuantifier r of
    Just q -> do
      bs <- telescope q
      let bound = [ x | SurfaceBinder _ x _ <- bs ]
      -- A rule's @∀@ lists its metavariables; it is not a nested scope, so a
      -- name bound twice is a mistake rather than a shadowing.
      case [ x | (x, k) <- zip bound [0 :: Int ..], x `elem` take k bound ] of
        x : _ -> Left (QuantifiedTwice x)
        [] -> Right ()
      case [ x | (x, _) <- mentioned, x `notElem` bound ] of
        x : _ -> Left (NotQuantified x)
        [] -> Right ()
      case [ n | n <- named, n `elem` bound ] of
        n : _ -> Left (PremiseNameTaken n)
        [] -> Right ()
      Right (bs, id)
    Nothing ->
      -- **A metavariable is primed when it is named like a type the
      -- constructor mentions** — @LC@ is one of @LC@'s own metavariables — as
      -- a generated constructor's binders are ('Thena.Driver.grammarDatatype').
      let avoid = types ++ named
          go _ [] = []
          go used ((x, t) : rest) =
            let x' = fresh (used ++ map fst rest) x in (x, x', t) : go (x' : used) rest
          fresh used x | x `elem` avoid || x `elem` used = fresh used (x ++ "'")
                       | otherwise = x
          renamed = go [] mentioned
       in Right ( [ SurfaceBinder Explicit x' (Just (SurfaceName t)) | (_, x', t) <- renamed ]
                , \x -> case [ x' | (y, x', _) <- renamed, y == x ] of
                    x' : _ -> x'
                    [] -> x )
  -- An unnamed premise is @d1@, @d2@, … by its position, primed away from
  -- every other name the constructor binds or mentions.
  let bound = [ x | SurfaceBinder _ x _ <- quantified ]
      taken = bound ++ named ++ types
      premiseName k = \case
        Just n -> n
        Nothing -> let go x = if x `elem` taken then go (x ++ "'") else x in go ("d" ++ show k)
  premiseTypes <- either (Left . RuleUnbuilt) Right (traverse (term gs renaming . snd) premises)
  result <- either (Left . RuleUnbuilt) Right (term gs renaming conclusion)
  let premiseBinders =
        [ SurfaceBinder Explicit (premiseName k n) (Just ty')
        | (k, ((n, _), ty')) <- zip [1 :: Int ..] (zip premises premiseTypes) ]
      binders = quantified ++ premiseBinders
      ty = case binders of
        [] -> result
        b : bs -> SurfacePi (b NE.:| bs) result
  Right (SurfaceConstructor (ruleName r) ty, replicate (length binders) Plain)
  where
    GlobalName judgment = grammarName g
    rules = ruleGrammar gs

    parseIn part what start txt = case Earley.parse rules start (map Char txt) of
      Right t -> Right t
      Left (Earley.Stuck p expected)
        | any isScan expected, w@(_ : _) <- wordAt p txt, w `notElem` terminals gs, not (isMetavariable gs w) ->
            Left (RuleNotAMetavariable w)
      Left why -> Left (RuleUnparsed part what txt why)

    isScan s = case s of
      Earley.Scan {} -> True
      _ -> False

    -- Every type or global the constructor's type can mention, which a
    -- metavariable must not shadow.
    types = nub $
      [ n | h <- gs, let GlobalName n = grammarName h ]
        ++ [ sortType srt | h <- gs, p <- grammarProductions h, Slot _ srt _ <- gproductionItems p ]
        ++ concatMap substitutionNames gs
        ++ ["And", "both", "cons", "nil"]

    telescope q = case parseSurfaceText (q ++ " -> Type\8320") of
      Left e -> Left (QuantifierUnreadable e)
      Right (SurfacePi bs _) -> Right (NE.toList bs)
      Right _ -> Right []

-- | The premises of a parse of @the premises@, in order, with their names.
premisesOf :: Tree -> [(Maybe String, Tree)]
premisesOf t = case t of
  Node _ [p] -> [premise p]
  Node _ [p, rest] -> premise p : premisesOf rest
  _ -> []
  where
    premise p = case p of
      Node _ [Token n, Node _ [j]] -> (Just n, j)
      Node _ [Node _ [j]] -> (Nothing, j)
      _ -> (Nothing, p)

-- | The text of what looks like a name at a position — letters, digits,
-- primes and subscripts — for §6.2's message about a name that is not a
-- metavariable.
wordAt :: Int -> String -> String
wordAt p = takeWhile nameChar . drop p
  where nameChar c = isAlphaNum c || c == '\'' || c == '_'

terminals :: [Grammar] -> [String]
terminals gs = [ t | g <- gs, p <- grammarProductions g, Terminal t <- gproductionItems p ]

-- | The metavariables a reading mentions, in order, each with its type's name.
mentions :: [Grammar] -> Tree -> Either BuildError [(String, String)]
mentions gs t = case t of
  Node n [Token x] | [MetavariableOf l] <- special n -> Right [(x, l)]
  Node n [e, s] | [SubstituteIn _] <- special n -> (++) <$> mentions gs e <*> mentions gs s
  Node n (Token x : rest) | [PairIn l] <- special n ->
    ((x, classType gs l) :) . concat <$> traverse (mentions gs) rest
  Node n children -> case production gs n of
    Nothing -> Left (NoSuchProduction n)
    Just p -> do
      slots <- arguments p children
      concat <$> sequence
        [ case (argumentSort a, child) of
            (OfClass _ ty _, Token x) -> Right [(x, nameOf ty)]
            _ -> mentions gs child
        | (a, child) <- slots ]
  _ -> Right []

-- | A reading as a surface term, its metavariables named through @rename@.
term :: [Grammar] -> (String -> String) -> Tree -> Either BuildError Surface
term gs rename t = case t of
  Node n [Token x] | [MetavariableOf _] <- special n -> Right (SurfaceName (rename x))
  Node n [e, s] | [SubstituteIn l] <- special n -> do
    e' <- go e
    ps <- pairs s
    Right $ case ps of
      -- §6.3: one pair is @L-subst@, a list @L-subst-all@ — simultaneous.
      [(x, m)] -> app (SurfaceName (l ++ "-subst")) [e', x, m]
      _ -> app (SurfaceName (l ++ "-subst-all")) [e', foldr (cons l) (nil l) ps]
  Node n children -> case production gs n of
    Nothing -> Left (NoSuchProduction n)
    Just p -> do
      slots <- arguments p children
      app (SurfaceName n) <$> traverse slot slots
  _ -> Left (NotForSlot "" (show t))
  where
    go = term gs rename
    slot (a, child) = case (argumentSort a, child) of
      (OfClass {}, Token x) -> Right (SurfaceName (rename x))
      _ -> go child
    pairs s = case s of
      Node _ [Token x, m] -> (\m' -> [(SurfaceName (rename x), m')]) <$> go m
      Node _ [Token x, m, more] -> (\m' rest -> (SurfaceName (rename x), m') : rest) <$> go m <*> pairs more
      _ -> Left (NotForSlot "" (show s))
    pairType l = app (SurfaceName "And") [SurfaceName (classType gs l), SurfaceName l]
    cons l (x, m) rest =
      app (SurfaceName "cons") [pairType l, app (SurfaceName "both") [SurfaceName (classType gs l), SurfaceName l, x, m], rest]
    nil l = app (SurfaceName "nil") [pairType l]

app :: Surface -> [Surface] -> Surface
app f [] = f
app f (a : as) = SurfaceApp f (NE.map (SurfaceArg Explicit) (a NE.:| as))

-- ---------------------------------------------------------------------------
-- The grammar a rule is read with

-- | The rules a rule's text is parsed with: every installed grammar, with a
-- token class's scan narrowed to its metavariables, and the rules of this
-- module's own nonterminals.
ruleGrammar :: [Grammar] -> [Earley.Rule]
ruleGrammar gs =
  map narrowed (earleyRules gs)
    ++ concatMap own [ g | g <- gs, grammarKind g /= JudgmentBlock ]
    ++ [ Earley.Rule "a judgment" judgmentNT [Earley.Nonterminal j] []
       | g <- gs, grammarKind g == JudgmentBlock, let GlobalName j = grammarName g ]
    ++ [ Earley.Rule "a premise" premiseNT [Earley.Nonterminal judgmentNT] []
       , Earley.Rule "a named premise" premiseNT
           [Earley.Scan "a premise name" premiseName, Earley.Literal ":", Earley.Nonterminal judgmentNT] []
       , Earley.Rule "a premise" premisesNT [Earley.Nonterminal premiseNT] []
       , Earley.Rule "premises" premisesNT [Earley.Nonterminal premiseNT, Earley.Nonterminal premisesNT] []
       ]
  where
    narrowed r = r { Earley.ruleBody = map narrow (Earley.ruleBody r) }
    narrow s = case s of
      Earley.Scan x _ -> Earley.Scan x (metavariables [x])
      _ -> s

    own g =
      let GlobalName l = grammarName g
       in Earley.Rule ("metavariable " ++ l) l
            [Earley.Scan ("a metavariable of " ++ l) (metavariables (grammarMetavars g))] []
            : case variableClass g of
                Nothing -> []
                Just x ->
                  let pair = [Earley.Scan x (metavariables [x]), Earley.Literal "->", Earley.Nonterminal l]
                   in [ Earley.Rule ("substitute " ++ l) l
                          [Earley.Nonterminal l, Earley.Literal "[", Earley.Nonterminal (pairsNT l), Earley.Literal "]"] []
                      , Earley.Rule ("pair " ++ l) (pairsNT l) pair []
                      , Earley.Rule ("pair " ++ l) (pairsNT l)
                          (pair ++ [Earley.Literal ",", Earley.Nonterminal (pairsNT l)]) []
                      ]

    -- A premise name is anything up to a space, a colon or a bracket.
    premiseName = let c = oneOf (complement (fromRanges ([ (d, d) | d <- ":()[]{}," ] ++ spaces)))
                   in andThen c (star c)
    spaces = [ (d, d) | d <- " \t\n\r" ]

-- | The nonterminals only a rule has. Each has a space in its name, which no
-- language, context or judgment can.
judgmentNT, premiseNT, premisesNT :: String
judgmentNT = "a judgment"
premiseNT = "a premise"
premisesNT = "the premises"

pairsNT :: String -> String
pairsNT l = "substitution in " ++ l

-- | What a rule-only node of a reading is: its rule's name, read back.
data Special = MetavariableOf String | SubstituteIn String | PairIn String

special :: String -> [Special]
special n = case words n of
  ["metavariable", l] -> [MetavariableOf l]
  ["substitute", l] -> [SubstituteIn l]
  ["pair", l] -> [PairIn l]
  _ -> []

-- | The token class of a language's variable production — the one a
-- substitution's left-hand side is a metavariable of (§6.3).
variableClass :: Grammar -> Maybe String
variableClass g = do
  _ <- if null (substitutionNames g) then Nothing else Just ()
  p <- variableProduction g
  x : _ <- Just [ x | Slot x (OfClass {}) _ <- gproductionItems p ]
  Just x

classType :: [Grammar] -> String -> String
classType gs l = case [ t | g <- gs, grammarName g == GlobalName l, Just x <- [variableClass g]
                          , p <- grammarProductions g, Slot y (OfClass _ (GlobalName t) _) _ <- gproductionItems p, y == x ] of
  t : _ -> t
  [] -> "String"

-- | These names, each followed by any suffix of primes, digits, subscripts
-- (§6.2) and, his addition of 2026-09-21, Redex's underscore subscripts:
-- @M'@, @M1@, @M₁@, @M_1@, @M_left@.
metavariables :: [String] -> Regex
metavariables ns =
  andThen (alternatives (map literally ns))
          (star (alternatives
            [ oneOf (fromRanges [('\'', '\''), ('0', '9'), ('\8320', '\8329')])
            , andThen (oneOf (singleChar '_')) (andThen alnum (star alnum)) ]))
  where
    literally = foldr (andThen . oneOf . singleChar) EmptyString
    alnum = oneOf (fromRanges [('a', 'z'), ('A', 'Z'), ('0', '9')])

-- | Is this a metavariable of some installed grammar or class, with a suffix?
--
-- Every way of taking suffixes off is tried, so a metavariable whose own name
-- has an underscore in it is still found.
isMetavariable :: [Grammar] -> String -> Bool
isMetavariable gs n = any (`elem` names) (bases n)
  where
    bases m = m : case reverse m of
      c : rest | suffix c -> bases (reverse rest)
      _ -> case break (== '_') (reverse m) of
        (after@(_ : _), '_' : before) | all alnum after -> bases (reverse before)
        _ -> []
    suffix c = c == '\'' || (c >= '0' && c <= '9') || (c >= '\8320' && c <= '\8329')
    alnum c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
    names = [ m | g <- gs, grammarKind g /= JudgmentBlock, m <- grammarMetavars g ]
         ++ [ x | g <- gs, p <- grammarProductions g, Slot x (OfClass {}) _ <- gproductionItems p ]

sortType :: Sort -> String
sortType srt = case srt of
  OfLanguage l -> nameOf l
  OfClass _ t _ -> nameOf t

nameOf :: GlobalName -> String
nameOf (GlobalName n) = n
