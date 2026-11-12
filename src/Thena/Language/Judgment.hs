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

import Data.Char (isAlphaNum, isSpace)
import Data.List (nub)
import Data.Maybe (listToMaybe)
import qualified Data.List.NonEmpty as NE

import Thena.Core.Term (GlobalName (..), declarationNamed, inDeclarationOf, nameFromText, rootName, nameDotted)
import qualified Thena.Language.Earley as Earley
import Thena.Language.Earley (Piece (..), Start (..), Tree (..))
import Thena.Language.Grammar
  ( Argument (..)
  , GProduction (..)
  , typeFormerProductions
  , nameBases
  , typeNT
  , TypeReading (..)
  , typeReading
  , universeWord
  , Grammar (..)
  , GrammarError (..)
  , GrammarProblem (..)
  , Item (..)
  , RulePart (..)
  , RuleProblem (..)
  , Sort (..)
  , allOf
  , earleyRules
  , classOwner
  , classWord
  , classIn
  , classesSubstituted
  , substitutionNames
  , variableProductions
  , grammarKey
  , grammarWord
  , sortType
  )
import Thena.Errors (BuildError (..))
import Thena.Global.Env (ArgRole (..))
import Thena.Language.Build (arguments, production)
import Thena.Language.Reader (RawRule (..))
import Thena.Language.Regex (Regex (..), alternatives, andThen, complement, fromRanges, oneOf, singleChar, star)
import Thena.Surface.Concrete (Plicity (..), Surface (..), SurfaceArg (..), SurfaceBinder (..), SurfaceConstructor (..), SurfaceData (..), surfaceName)
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
  Right ( SurfaceData [] name [] (foldr (SurfaceArrow . typeOf) (SurfaceUniverse 0) indices) (map fst ctors)
        , map snd ctors )
  where
    -- **The WORD, because placing it is 'Thena.Driver.datatypeProgram''s job**
    -- (MS10 phase 258), exactly as a @language@ block's datatype already did.
    name = grammarWord g
    -- **The judgment's own notation, which is its one type-former production**
    -- (MS8 phase 160) — the spelling of the statement this family makes, so its
    -- slots are the family's indices. A @notation@ block may add a function
    -- production to a judgment's grammar too, and that is notation and not an
    -- index (MS8 phase 158); the rules are the constructors.
    indices = concatMap gproductionArguments (typeFormerProductions g)
    typeOf = SurfaceName [] . sortType . argumentSort

-- | One rule, as a constructor.
constructor :: [Grammar] -> Grammar -> RawRule -> Either RuleProblem (SurfaceConstructor, [ArgRole])
constructor gs g r = do
  -- **Each premise line is parsed on its own**: a line break ends a premise,
  -- and only premises sharing a line are told apart by parsing.
  --
  -- **A NAMED PREMISE IS IN SCOPE FROM THE NEXT LINE ON** (MS8 phase 172, HIS
  -- ruling of 2026-10-16). The lines are parsed left to right and each named one
  -- extends the grammar the rest are read with, so a later premise and the
  -- conclusion may write the name wherever a term of that premise's type goes —
  -- which is what lets a rule say @p2 : \8866 \915 , M , T by p1 valid@. Before this
  -- the name was refused as @p1 is not a metavariable@: premise text was parsed
  -- against a grammar fixed before any name was bound.
  --
  -- **Within one line it is not in scope**, because the line is one parse and
  -- the names in it are not known until that parse is done. Premises are written
  -- one per line in every paper and every example here.
  (premises, bound') <- premiseLines [] [] (rulePremises r)
  conclusion <- parseWith bound' Conclusion judgment (StartRule judgmentRule) (ruleConclusion r)
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
       in Right ( [ SurfaceBinder Explicit x' (Just (SurfaceName [] t)) | (_, x', t) <- renamed ]
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
  premiseTypes <- either (Left . RuleUnbuilt) Right (traverse (term gs beingDeclared renaming . snd) premises)
  result <- either (Left . RuleUnbuilt) Right (term gs beingDeclared renaming conclusion)
  let premiseBinders =
        [ SurfaceBinder Explicit (premiseName k n) (Just ty')
        | (k, ((n, _), ty')) <- zip [1 :: Int ..] (zip premises premiseTypes) ]
      binders = quantified ++ premiseBinders
      ty = case binders of
        [] -> result
        b : bs -> SurfacePi (b NE.:| bs) result
  Right (SurfaceConstructor [] (ruleName r) ty, replicate (length binders) Plain)
  where
    -- **The word, not the key** (MS10 phase 258): this is written into a
    -- surface type, and a block inside @namespace A@ writes @typing@.
    judgment = grammarWord g
    -- **The parser knows the production by its own name** (MS10 phase 248),
    -- which is @typing.typing@ now that a block's productions live in the
    -- namespace its datatype opens. @judgment@ stays the written word, because
    -- that is what a refusal names.
    judgmentRule = case typeFormerProductions g of
      p : _ -> nameDotted (gproductionName p)
      []    -> judgment
    -- **What the judgment's own name is while its own declaration is being
    -- elaborated** (MS10 phase 248). @data@ puts the type inside its namespace,
    -- so the family is @typing.typing@ — but a constructor's type is elaborated
    -- under @assume typing : ‹its type›@, exactly as a hand-written @data@'s is,
    -- and an assumption is a local with no path. So a rule's conclusion, and a
    -- premise of the judgment being declared, write the short word; every other
    -- production writes its full name, because it is already declared.
    beingDeclared = (judgmentRule, judgment)
    rules = ruleGrammar gs

    -- **Left to right, each named premise extending what the rest may write.**
    -- The accumulator is the extra grammar rules, which is also what the
    -- conclusion is parsed with.
    premiseLines extra acc [] = Right (reverse acc, extra)
    premiseLines extra acc (txt : rest) = do
      (line, extra') <- premisesInLine extra txt
      premiseLines extra' (reverse line ++ acc) rest

    -- **One premise at a time, inside the line as well as across lines** (MS8
    -- phase 173, HIS instruction of 2026-10-16: making it work between lines and
    -- not within one is unprincipled).
    --
    -- **Where one premise ends is the parser's answer, not a guess.** A line is
    -- a list of premises told apart only by parsing, so the split cannot be
    -- found lexically — but the chart holds it: every prefix that completes
    -- @premiseNT@ from the start is a possible first premise. Each is tried,
    -- longest first, and the rest of the line is read with that premise's name
    -- in scope; the first split whose remainder also reads is the parse. **Any
    -- split the list grammar would have found is among these**, so a line that
    -- parsed before parses the same way now.
    --
    -- The whole-line parse is still what reports a failure, so a line that
    -- cannot be read says what it always said.
    premisesInLine extra txt = case go extra txt of
      Just done -> Right done
      Nothing -> do
        -- **No split works, so read the line as one list** — which is what every
        -- line did before this phase, and which is also what reports the
        -- failure when the line cannot be read at all.
        line <- premisesOf <$> parseWith extra Premises "premises" (StartAt premisesNT) txt
        added <- concat <$> traverse inScope line
        Right (line, extra ++ added)
      where
        go ex s
          | all isSpace s = Just ([], ex)
          | otherwise = listToMaybe
              [ (p' : more, ex'')
              | j <- splitsOf ex s
              , Right t <- [parseWith ex Premises "premises" (StartAt premiseNT) (take j s)]
              , let p' = premiseOf t
              , Right added <- [inScope p']
              , let ex' = ex ++ added
              , Just (more, ex'') <- [go ex' (drop j s)]
              ]

        -- The prefix lengths at which a complete premise ends, longest first.
        splitsOf ex s =
          let c = Earley.chart (rules ++ ex) (StartAt premiseNT) (map Char s)
           in reverse (nub
                [ j
                | j <- [1 .. Earley.inputLength c]
                , it <- Earley.itemsAt c j
                , Earley.itemOrigin it == 0
                , let r' = Earley.chartRule c it
                , Earley.ruleHead r' == premiseNT
                , Earley.itemDot it == length (Earley.ruleBody r')
                ])

    -- **What a premise name may be written as: a term of that premise's own
    -- type.** A premise at a judgment's statement names a derivation, so the
    -- name reads at that judgment's nonterminal — exactly where a slot at it
    -- reads. A premise written as a bare type (@LC@) names a term of it, and
    -- reads at the same place a term of @LC@ does.
    --
    -- Nothing is added for an unnamed premise, and nothing for one at a
    -- universe: @P140\8320@ says the argument is a type, and a type is not written at
    -- a grammar's nonterminal.
    inScope (Nothing, _) = Right []
    inScope (Just n, t) = case nonterminalOf t of
      Nothing -> Right []
      Just l  -> Right [ Earley.Rule ("the premise " ++ n) l
                           [Earley.Scan ("the premise " ++ n) (exactly n)] [] ]

    -- The grammar whose nonterminal a premise's reading sits at. A reading at
    -- 'typeNT' is a named type, a universe, or a wrapper round a type former's
    -- spelling, and it is the last of those that has a grammar to find.
    nonterminalOf t = case t of
      Node n children -> case typeReading n children of
        Just (TypeCalled l) -> Just l
        Just (AtUniverse _) -> Nothing
        Just (TypeInside (Node p' _)) ->
          case [ l | h <- gs, q <- grammarProductions h
                   , gproductionName q == nameFromText p'
                   , let l = grammarKey h ] of
            l : _ -> Just l
            []    -> Nothing
        _ -> Nothing
      _ -> Nothing

    -- A regex for one word and nothing else. 'metavariables' would also admit
    -- the suffixed forms, and a suffix of a premise name is bound to nothing.
    exactly = foldr (andThen . oneOf . singleChar) EmptyString

    parseWith extra part what start txt =
      case Earley.parse (rules ++ extra) start (map Char txt) of
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
      -- **Words, because a metavariable is a word** (MS10 phase 258): what
      -- must not be shadowed is what the author can write.
      [ n | h <- gs, let n = grammarWord h ]
        ++ [ sortType srt | h <- gs, p <- grammarProductions h, Slot _ srt _ <- gproductionItems p ]
        ++ concatMap (substitutionNames gs) gs
        ++ ["And", "both", "cons", "nil"]

    telescope q = case parseSurfaceText (q ++ " -> Type\8320") of
      Left e -> Left (QuantifierUnreadable e)
      Right (SurfacePi bs _) -> Right (NE.toList bs)
      Right _ -> Right []

-- | **One parse of @premiseNT@, with its name** (MS8 phase 173) — what
-- 'premisesOf' does to each element of a list, for a premise read on its own.
premiseOf :: Tree -> (Maybe String, Tree)
premiseOf p = case p of
  Node _ [Token n, j] -> (Just n, j)
  Node _ [j] -> (Nothing, j)
  _ -> (Nothing, p)

-- | The premises of a parse of @the premises@, in order, with their names.
premisesOf :: Tree -> [(Maybe String, Tree)]
premisesOf t = case t of
  Node _ [p] -> [premise p]
  Node _ [p, rest] -> premise p : premisesOf rest
  _ -> []
  where
    -- **The reading at @typeNT@ is kept, not unwrapped** (MS8 phase 160): it may
    -- be a grammar's nonterminal, a grammar's own name read as a type, or a
    -- universe, and only the first of those has a child to unwrap. 'term' and
    -- 'mentions' take the three apart.
    premise p = case p of
      Node _ [Token n, j] -> (Just n, j)
      Node _ [j] -> (Nothing, j)
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
  -- **The node carries the grammar's KEY and a binder wants the WORD** (MS10
  -- phase 258) — this is the type a quantified metavariable is written at.
  Node n [Token x] | [MetavariableOf l] <- special n -> Right [(x, wordOfKey gs l)]
  -- **A type is not a metavariable** (phase 160): @LC@ or @𝕌₀@ written as a
  -- premise is a type the rule's argument is at, so there is nothing to
  -- quantify over and nothing to rename.
  Node n [child] | [TypeWrapper] <- special n -> mentions gs child
  Node n _ | [TypeNamed _] <- special n -> Right []
           | [UniverseRead] <- special n -> Right []
           -- A premise name is bound by this constructor, so there is nothing
           -- to quantify over and nothing to rename (MS8 phase 172).
           | [PremiseRef _] <- special n -> Right []
  Node n [e, s] | [SubstituteIn _] <- special n -> (++) <$> mentions gs e <*> mentions gs s
  Node n [a, b] | [PairsIn _] <- special n -> (++) <$> mentions gs a <*> mentions gs b
  Node n [Token x, m] | [PairIn _ cls] <- special n ->
    ((x, classType gs cls) :) <$> mentions gs m
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
term :: [Grammar] -> (String, String) -> (String -> String) -> Tree -> Either BuildError Surface
term gs self@(selfRule, selfWord) rename t = case t of
  Node n [Token x] | [MetavariableOf _] <- special n -> Right (SurfaceName [] (rename x))
  -- **A reading at a universe** (phase 160). A grammar's own name is the type
  -- that grammar's datatype is; @𝕌₀@ is @Type₀@. Neither is renamed — a type
  -- is not a metavariable.
  Node n [child] | [TypeWrapper] <- special n -> term gs self rename child
  -- **A KEY BECOMES A WORD HERE** (MS10 phase 258): the node carries the
  -- grammar's dotted key, which is what keeps two languages of one word apart,
  -- and what goes into a surface type is the word the author would have written.
  Node n _ | [TypeNamed l] <- special n -> Right (SurfaceName [] (wordOfKey gs l))
  Node n [Token u] | [UniverseRead] <- special n -> Right (SurfaceUniverse (maybe 0 id (universeWord u)))
  -- **Not renamed** (MS8 phase 172): the premise binder carries the user's own
  -- name, so this is the name of the thing it reaches.
  Node n _ | [PremiseRef x] <- special n -> Right (SurfaceName [] x)
  -- §6.3: a comma list is @L.subst-*@ — simultaneous, and across classes, so
  -- each class's map takes the pairs written at it and the rest are empty (MS8
  -- phase 155). **A single pair never reaches here since MS8 phase 159**: it is
  -- a generated @notation@ production, so it is an ordinary 'Node' and the
  -- clause below builds @L.subst.‹k›@ applied without knowing anything about it.
  Node n [e, s] | [SubstituteIn l] <- special n -> do
    e' <- go e
    ps <- pairs s
    -- **ONE LIST PER CLASS, KEYED BY THE CLASS'S WHOLE NAME.** Keyed by the
    -- word, a language reaching two classes both written @x@ built two lists
    -- under one key and every pair went into both.
    Right (app (surfaceName (allOf (nameFromText l)))
             (e' : [ foldr (cons l c) (nil l c) [ (x, m) | (c', x, m) <- ps, c' == c ]
                   | h <- grammarNamed gs l
                   , c <- map nameDotted (classesSubstituted gs h) ]))
  Node n children -> case production gs n of
    Nothing -> Left (NoSuchProduction n)
    Just p -> do
      slots <- arguments p children
      -- **The production's own name, path and all** (MS10 phase 244) — except
      -- the judgment this rule belongs to, which is an assumption and not yet a
      -- global (phase 248).
      let hd | n == selfRule = SurfaceName [] selfWord
             | otherwise     = surfaceName (gproductionName p)
      app hd <$> traverse slot slots
  _ -> Left (NotForSlot "" (show t))
  where
    go = term gs self rename
    slot (a, child) = case (argumentSort a, child) of
      (OfClass {}, Token x) -> Right (SurfaceName [] (rename x))
      _ -> go child
    pairs s = case s of
      Node n [a, b] | [PairsIn _] <- special n -> (++) <$> pairs a <*> pairs b
      Node n [Token x, m] | [PairIn _ cls] <- special n ->
        (\m' -> [(cls, SurfaceName [] (rename x), m')]) <$> go m
      _ -> Left (NotForSlot "" (show s))
    -- **A prelude constructor is written with its path** (MS10 phase 248):
    -- @cons@ is @List.cons@ now, and generated code may not rely on the file it
    -- is spliced into having written an @open@. The /types/ stay short, because
    -- a @data@ declaration's short name reaches them.
    con d w = surfaceName (inDeclarationOf (declarationNamed (rootName d)) w)
    pairType l c = app (SurfaceName [] "And") [SurfaceName [] (classType gs c), ownerType gs l c]
    cons l c (x, m) rest =
      app (con "List" "cons")
        [ pairType l c
        , app (con "And" "both") [SurfaceName [] (classType gs c), ownerType gs l c, x, m]
        , rest ]
    nil l c = app (con "List" "nil") [pairType l c]

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
    ++ concatMap own [ g | g <- gs, not (null (grammarMetavars g)) ]
    -- **A PREMISE IS AN ARGUMENT'S TYPE, SO THE PREMISE POSITION IS A SLOT AT A
    -- UNIVERSE** (MS8 phase 160, `~8b8gz`, `~z8n28`). @typeNT@ is where every
    -- reading at a universe is collected, and it has three kinds of rule:
    --
    --   * a grammar that has a 'TypeFormer' production — its statement, @Γ ⊢ M : T@
    --     or a generated @x : T ∈ Γ@;
    --   * **every installed grammar's own name**, which is the nullary case —
    --     HIS, *"@LC@ is its own notation"* — so a rule may take a term of @LC@
    --     as a premise, since a rule is a constructor and an argument may be at
    --     any type;
    --   * **a universe**, @𝕌₀@, @𝕌₁@, …, which is `Type₀` and so on spelled.
    --
    -- **What this replaced was a test on the kind of block that declared the
    -- grammar**, which is the one question the design forbids: measured by
    -- relabelling the generated lookup relation, after which @x : T ∈ Γ@ stopped
    -- parsing above a bar although nothing about its type had changed.
    ++ [ Earley.Rule "a premise" premiseNT [Earley.Nonterminal typeNT] []
       , Earley.Rule "a named premise" premiseNT
           [Earley.Scan "a premise name" premiseName, Earley.Literal ":", Earley.Nonterminal typeNT] []
       , Earley.Rule "a premise" premisesNT [Earley.Nonterminal premiseNT] []
       , Earley.Rule "premises" premisesNT [Earley.Nonterminal premiseNT, Earley.Nonterminal premisesNT] []
       ]
  where
    narrowed r = r { Earley.ruleBody = map narrow (Earley.ruleBody r) }
    -- **A class slot in a rule's text reads a metavariable and nothing else.**
    -- A scan whose name has a space in it is not a class slot but one of the
    -- nonterminals this module and 'Thena.Language.Grammar.typeRules' own —
    -- @a universe@ — and narrowing that to the metavariables named @\120588\8320@ would
    -- make a universe unwritable in a rule (MS8 phase 160). No class can have a
    -- space in its name, which is the same convention the nonterminals use.
    narrow s = case s of
      Earley.Scan x _ | ' ' `notElem` x -> Earley.Scan x (metavariables [x])
      _ -> s

    own g =
      let l = grammarKey g
       in Earley.Rule ("metavariable " ++ l) l
            -- **THE RULE IS KEYED BY THE NAME AND THE SCAN IS LABELLED BY THE
            -- WORD — MS12 phase 313.** The rule's name is read back by
            -- 'Special' and must stay the key; the scan's name is only ever
            -- printed, in @expecting a metavariable of Ctx@, and a module's
            -- declarations live under the module's own name from this phase, so
            -- the key there read @a metavariable of J.Ctx@ for a language the
            -- author of the rule writes @Ctx@.
            [ Earley.Scan ("a metavariable of " ++ grammarWord g)
                          (metavariables (grammarMetavars g)) ] []
            : case classesSubstituted gs g of
                [] -> []
                cs ->
                  -- **TWO OR MORE PAIRS, and that is the whole of what MS8 phase
                  -- 159 left here.** The one-pair form @E[x -> M]@ is now a
                  -- generated @notation@ production of the grammar itself
                  -- ('Thena.Language.Substitution.substitutionNotations'), so it
                  -- arrives through 'earleyRules' like any other production — and
                  -- a rule for it here as well would make @E[x -> M]@ parse two
                  -- ways, which is how this was found. What a notation production
                  -- cannot be is **variadic**: a comma list is simultaneous
                  -- substitution and builds a /list/ per class, which no object
                  -- grammar spells.
                  --
                  -- **One pair rule per class — MS8 phase 155.** A pair's
                  -- right-hand side is a term of the class's /owning/ language,
                  -- not of the one being substituted into: a type substituted
                  -- into a term is written @M[X -> P]@ with @P@ a type. One
                  -- substitution may mix classes, so they share the nonterminal.
                  Earley.Rule ("substitute " ++ l) l
                    [Earley.Nonterminal l, Earley.Literal "[", Earley.Nonterminal (pairsNT l), Earley.Literal "]"] []
                    -- Exactly two, then three or more: @pairsNT@ is never one
                    -- pair, which is what keeps the two forms apart.
                    : Earley.Rule ("pairs " ++ l) (pairsNT l)
                        [Earley.Nonterminal (pairNT l), Earley.Literal ",", Earley.Nonterminal (pairNT l)] []
                    : Earley.Rule ("pairs " ++ l) (pairsNT l)
                        [Earley.Nonterminal (pairNT l), Earley.Literal ",", Earley.Nonterminal (pairsNT l)] []
                    -- **TWO SPELLINGS PER CLASS — HIS RULING OF 2026-11-10 —
                    -- AND THE PAIR IS NAMED BY THE CLASS, NOT BY ITS WORD.**
                    -- A pair says which class it is for in the same way the
                    -- generated bracket does
                    -- ('Thena.Language.Substitution.substitutionNotations'):
                    -- @‹class›: x -> M@ carries the class's whole name, and the
                    -- bare @x -> M@ stays for every language that reaches one
                    -- class of each word. Both are built for every class, never
                    -- one or the other by case. **The rule's NAME carries the
                    -- class's whole name** because that is what says which map
                    -- the pair belongs in (MS8 phase 155), and two classes of
                    -- one word have one word and two names.
                    : concat
                        [ [ Earley.Rule nm (pairNT l) body []
                          , Earley.Rule nm (pairNT l)
                              -- **The class is named relative to the language
                              -- — MS12 phase 313** ('classIn'): the whole name
                              -- carries the module's namespace, which the
                              -- language in front of the bracket has already
                              -- said, so this wanted @E[J.x: x -> M]@ while the
                              -- generated notation for the one-pair form wanted
                              -- @E[x: x -> M]@. **The rule's NAME stays whole**
                              -- — it is what says which map the pair belongs
                              -- in, and it is read back by 'Special'.
                              ( Earley.Literal (nameDotted (classIn g c))
                                  : Earley.Literal ":" : body ) []
                          ]
                        | c <- cs
                        , let nm = "pair " ++ l ++ " " ++ nameDotted c
                              x = classWord c
                              body = [ Earley.Scan x (metavariables [x])
                                     , Earley.Literal "->"
                                     , Earley.Nonterminal (ownerKey gs l (nameDotted c)) ]
                        ]

    -- A premise name is anything up to a space, a colon or a bracket.
    premiseName = let c = oneOf (complement (fromRanges ([ (d, d) | d <- ":()[]{}," ] ++ spaces)))
                   in andThen c (star c)
    spaces = [ (d, d) | d <- " \t\n\r" ]

-- | The nonterminals only a rule has. Each has a space in its name, which no
-- language, context or judgment can.
--
-- @typeNT@ is **readings at a universe** (MS8 phase 160) and replaced
-- @"a judgment"@, which was the set of grammars declared by a @judgment@ block.
premiseNT, premisesNT :: String
premiseNT = "a premise"
premisesNT = "the premises"


-- | The comma list of pairs, two or more of them, and one pair (MS8 phase 159).
-- Each has a space in its name, which no language, context or judgment can.
pairsNT, pairNT :: String -> String
pairsNT l = "substitution in " ++ l
pairNT l = "a substitution in " ++ l

-- | What a rule-only node of a reading is: its rule's name, read back.
data Special
  = MetavariableOf String
  | SubstituteIn String
  | PairsIn String
  | PairIn String String
  | TypeWrapper
    -- ^ @typeNT@ over a grammar's nonterminal: one child, the reading (phase 160)
  | TypeNamed String
    -- ^ a grammar's own name read as a type — the nullary case, @LC@ (phase 160)
  | UniverseRead
    -- ^ @𝕌₀@, @𝕌₁@, … (phase 160)
  | PremiseRef String
    -- ^ **an earlier premise of this rule, written by its name** (MS8 phase
    -- 172). It is a binder this very constructor introduces, not a
    -- metavariable, so it quantifies nothing and is never renamed.

special :: String -> [Special]
special n = case words n of
  ["metavariable", l] -> [MetavariableOf l]
  ["substitute", l] -> [SubstituteIn l]
  -- Phase 160's two readings at a universe. Neither mentions a metavariable, so
  -- neither adds anything to a rule's implicit quantification.
  ["a", "type"] -> [TypeWrapper]
  ["the", "type", l] -> [TypeNamed l]
  ["a", "universe"] -> [UniverseRead]
  ["the", "premise", x] -> [PremiseRef x]
  -- The node a comma list builds (MS8 phase 159), which always holds two
  -- children: a pair, then a pair or another list.
  ["pairs", l] -> [PairsIn l]
  -- The class is in the rule's name because that is what says which map the
  -- pair belongs in (MS8 phase 155). **It is the class's whole name**
  -- (2026-11-10): a word is not enough once a language may reach two classes
  -- that share one, and a name holds no space, so @words@ still cuts it out.
  ["pair", l, cls] -> [PairIn l cls]
  _ -> []

-- | The grammar of that name, among those installed.
-- | The word a grammar's key is written with — @A.Ty@ becomes @Ty@.
--
-- **Through the grammar and not by taking the last step off the string**, so a
-- grammar whose own word holds no dot is the only thing this can answer with
-- (MS10 phase 258). An unknown key is left as it stands, which keeps a refusal
-- naming what was written.
wordOfKey :: [Grammar] -> String -> String
wordOfKey gs l = case grammarNamed gs l of
  g : _ -> grammarWord g
  []    -> l

-- **@l@ IS A KEY, SO IT IS SPLIT ON ITS DOTS** (MS10 phase 258). @rootName@
-- here made @A.Ty@ a root-level word holding dots, which matches no grammar.
grammarNamed :: [Grammar] -> String -> [Grammar]
grammarNamed gs l = [ g | g <- gs, grammarName g == nameFromText l ]

-- | The language that owns a class — what the right-hand side of one of its
-- pairs is a term of, and what its map is a map into.
--
-- **The class is found by its WORD among the ones that language reaches** (MS10
-- phase 259), because a class carries a path now and @x@ is what the rule
-- wrote. A grammar reaching two classes of one word is no longer refused —
-- phase 304 deleted that refusal — so this answers with the first, and which
-- one a comma list meant is the open question of the generated notation.
ownerGrammar :: [Grammar] -> String -> String -> Maybe Grammar
ownerGrammar gs l cls = listToMaybe [ g | h <- grammarNamed gs l
                                        , c <- classesSubstituted gs h, nameDotted c == cls
                                        , Just g <- [classOwner gs h c] ]

-- | The owner as a PARSER KEY, which is the dotted name every nonterminal is
-- installed under ('Thena.Language.Grammar.grammarKey').
--
-- **The word is not a nonterminal** — a language inside a @namespace@ is
-- @Source.LC@ to the parser, so a pair rule built with @LC@ referred to a
-- nonterminal that did not exist and the comma-list form could not parse at
-- all. Measured: a file whose class and language sit at the top level took
-- @( x_1 x_2 )[x_1->x_2, x_2->x_1]@ and the same file under a @namespace@
-- refused it with /unexpected ','/.
ownerKey :: [Grammar] -> String -> String -> String
ownerKey gs l cls = maybe cls grammarKey (ownerGrammar gs l cls)

-- | The owner as a type to WRITE, path and all (MS10 phase 244's rule, which
-- this had escaped): generated code may not rely on the file it is spliced
-- into having opened the owner's namespace.
ownerType :: [Grammar] -> String -> String -> Surface
ownerType gs l cls =
  maybe (surfaceName (nameFromText cls)) (surfaceName . grammarName) (ownerGrammar gs l cls)

-- | A class's @T@ — @String@ for every class a binder or an occurrence may be
-- at (§4.5 refuses any other), asked rather than assumed so that `~tmnrr`'s
-- @Int@ class has one place to change.
-- **BY THE CLASS'S WHOLE NAME** (2026-11-10), since two classes of one word
-- are no longer refused and a comma list now says which of them a pair is for.
classType :: [Grammar] -> String -> String
classType gs cls = case [ t | g <- gs, (c, _) <- variableProductions g, nameDotted c == cls
                            , p <- grammarProductions g
                            , Slot y (OfClass _ tn _) _ <- gproductionItems p
                            , let t = nameDotted tn, y == classWord c ] of
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
-- **'Thena.Language.Grammar.nameBases' is the same rule one layer down** (MS8
-- phase 160), where it resolves a suffixed word in a /production/ to the
-- metavariable it is a suffix of. Shared so the two cannot disagree.
isMetavariable :: [Grammar] -> String -> Bool
isMetavariable gs n = any (`elem` names) (nameBases n)
  where
    -- A judgment declares none, so there is nothing to exclude by block kind
    -- (MS8 phase 160): its header has no metavariables and its notation's are
    -- the languages' (§6.1).
    names = [ m | g <- gs, m <- grammarMetavars g ]
         ++ [ x | g <- gs, p <- grammarProductions g, Slot x (OfClass {}) _ <- gproductionItems p ]

nameOf :: GlobalName -> String
nameOf = nameDotted
