-- | Object-language grammars, validated (MS6 phase 101; @ms6\/SPEC.md@ §4.2–4.5,
-- §5.1).
--
-- "Thena.Language.Reader" gives a 'Block' as written; 'checkGrammar' asks what
-- each name in it means against what is already declared, runs every check of
-- §4.5 and the context restriction of §5.1, and gives back a 'Grammar' — the
-- productions with their items resolved and, per production, the arguments
-- the generated constructor will take (§4.6) with their roles (§4.7).
--
-- **Nothing is generated here.** A grammar is installed on the machine beside
-- 'Thena.Engine.signatures' (his ruling, 2026-09-19) and read by the phases
-- that parse with it (102) and generate from it (103).
--
-- A name in a production is looked up **first as a metavariable** — of this
-- block, or of a grammar already installed — **then as a token class**, a
-- definition of type @Token T@. A metavariable may not be declared under a name
-- that is already either, so within one block the two never compete.
module Thena.Language.Grammar
  ( Grammar (..)
  , GProduction (..)
  , Item (..)
  , Argument (..)
  , Sort (..)
  , ArgRole (..)
  , GrammarError (..)
  , GrammarProblem (..)
  , ProductionProblem (..)
  , checkGrammar
  , tokenClassOf
  , earleyRules
  ) where

import Data.List (nub, (\\))
import Data.Maybe (isJust)

import Thena.Core.Reduce (whnf)
import Thena.Core.Term (Core (..), GlobalName (..), Literal (..), tokenName)
import qualified Thena.Language.Earley as Earley
import Thena.Language.Regex (Regex, parseRegex)
import Thena.Errors (Warning (..))
import Thena.Global.Env (GlobalEnv, definitionBody, definitionType, isDeclared, lookupDefinition)
import Thena.Language.Reader (Block (..), Metadata (..), Production (..), RawItem (..))
import Thena.Syntax.Lexer (BlockKind (..))

-- | A validated grammar.
data Grammar = Grammar
  { grammarKind         :: BlockKind
  , grammarName         :: GlobalName   -- ^ the datatype phase 103 generates
  , grammarMetavars     :: [String]     -- ^ its name first, then the rest of the head
  , grammarProductions  :: [GProduction]
  }
  deriving (Eq, Show)

data GProduction = GProduction
  { gproductionName      :: GlobalName    -- ^ the constructor
  , gproductionItems     :: [Item]
  , gproductionArguments :: [Argument]
    -- ^ **the distinct names, in order of first appearance** (§4.6). A name
    -- written twice is one argument (§4.3, non-linear).
  }
  deriving (Eq, Show)

-- | An item, resolved.
data Item
  = Terminal String
  | Slot String Sort [String]
    -- ^ a metavariable or class, what it ranges over, and the binders free in it
  deriving (Eq, Show)

data Argument = Argument
  { argumentName :: String
  , argumentSort :: Sort
  , argumentRole :: ArgRole
  }
  deriving (Eq, Show)

-- | What an argument ranges over.
data Sort
  = OfLanguage GlobalName            -- ^ a metavariable's grammar
  | OfClass GlobalName GlobalName Regex
    -- ^ a token class, its @T@, and its expression — read once, when the
    -- grammar is checked, so that parsing never looks the class up again
  deriving (Eq, Show)

-- | §4.7's roles, the ones phase 103 puts on the constructor.
data ArgRole
  = Plain
  | Occurrence        -- ^ an occurrence of an object identifier
  | Binder            -- ^ binds in the arguments that list it
  | Scope [Int]       -- ^ the binder arguments free in this one, by position
  deriving (Eq, Show)

-- | Why a block was refused. The kind and name say which block, and the
-- renderer says @in the grammar of LC@ or @in the context Ctx@ from them.
data GrammarError = GrammarError BlockKind String GrammarProblem
  deriving (Eq, Show)

data GrammarProblem
  = MetavariableRepeated String
    -- ^ written twice in the head
  | MetavariableTaken String
    -- ^ already a metavariable of another grammar, or a token class — a name
    -- in a production must mean one thing
  | NameTaken
    -- ^ the datatype's name is already declared
  | ConstructorTaken String
    -- ^ a production's name is already declared, by anything or by another
    -- production. **No magic** (§4.5): the user disambiguates
  | ContextShape
    -- ^ §5.1: a context needs one empty and one extension production
  | InProduction String ProductionProblem
  deriving (Eq, Show)

data ProductionProblem
  = NoItems
  | NotAMetavariable String
    -- ^ a binding form's head, or a name in the metadata, that is neither a
    -- metavariable nor a class. A plain word is a terminal (§4.2), so this is
    -- only ever about a name in a position that must be one
  | NotAnArgument String
    -- ^ a name inside @[…]@, or in the metadata, that is not written as an
    -- item of this production
  | OccurrenceBinds String
    -- ^ a name inside @[…]@ declared @as occurrence@
  | NotADeclaredBinder String
    -- ^ binders were declared, and a @[…]@ names one that is not among them
  | BinderNotString String Sort
    -- ^ a binder whose argument is not a @Token String@ class
  | OccurrenceNotString String Sort
    -- ^ the same, for the argument declared @as occurrence@
  | ScopesDiffer String
    -- ^ a name written twice with different binders free in it — one
    -- argument (§4.3) cannot have two scopes
  deriving (Eq, Show)

-- | Validate a block against the grammars already installed and the global
-- environment. The warnings are §4.5's vacuous binders.
checkGrammar :: [Grammar] -> GlobalEnv -> Block -> Either GrammarError (Grammar, [Warning])
checkGrammar installed env b = do
  -- The block's own name first: a language named like something declared is
  -- that, before it is anything about metavariables.
  if taken name then refuse NameTaken else Right ()
  case heads \\ nub heads of
    x : _ -> refuse (MetavariableRepeated x)
    [] -> Right ()
  case [ x | x <- heads, isJust (lookup x metavarsElsewhere) || isJust (tokenClassOf env x) ] of
    x : _ -> refuse (MetavariableTaken x)
    [] -> Right ()
  let prodNames = map productionName (blockProductions b)
  case [ p | (p, k) <- zip prodNames [0 :: Int ..]
           , taken p || p == name || p `elem` take k prodNames ] of
    p : _ -> refuse (ConstructorTaken p)
    [] -> Right ()
  prods <- traverse (\p -> either (refuse . InProduction (productionName p)) Right (production p))
             (blockProductions b)
  let g = Grammar kind (GlobalName name) heads (map fst prods)
  if kind == ContextBlock && not (contextShaped heads g) then refuse ContextShape else Right ()
  Right (g, concatMap snd prods)
  where
    kind = blockKind b
    name = blockName b
    heads = name : blockMetavars b

    refuse :: GrammarProblem -> Either GrammarError a
    refuse = Left . GrammarError kind name

    metavarsElsewhere =
      [ (m, grammarName g) | g <- installed, m <- grammarMetavars g ]

    -- A global, or a name a grammar already installed will generate.
    taken x =
      isDeclared (GlobalName x) env
        || GlobalName x `elem` concat
             [ grammarName g : map gproductionName (grammarProductions g) | g <- installed ]

    sortOf x
      | x == name || x `elem` blockMetavars b = Just (OfLanguage (GlobalName name))
      | Just g <- lookup x metavarsElsewhere = Just (OfLanguage g)
      | Just (t, re) <- tokenClassOf env x = Just (OfClass (GlobalName x) t re)
      | otherwise = Nothing

    production p = do
      items <- traverse item (productionItems p)
      if null items then Left NoItems else Right ()
      let slots = [ (x, bs) | Slot x _ bs <- items ]
          args = nub (map fst slots)
          scopeOf x = nub [ bs | (y, bs) <- slots, y == x ]
          bracketed = nub (concatMap snd slots)
      case [ x | x <- args, length (scopeOf x) > 1 ] of
        x : _ -> Left (ScopesDiffer x)
        [] -> Right ()
      (occurrences, declared) <- case productionMetadata p of
        Nothing -> Right ([], Nothing)
        Just (AsOccurrence x) -> named args x >> Right ([x], Nothing)
        Just (AsBinders xs) -> mapM_ (named args) xs >> Right ([], Just xs)
      let binders = maybe bracketed id declared
      mapM_ (bound args occurrences declared) bracketed
      mapM_ (stringClass OccurrenceNotString) occurrences
      mapM_ (stringClass BinderNotString) binders
      let role x
            | x `elem` occurrences = Occurrence
            | x `elem` binders = Binder
            | (bs : _) <- scopeOf x, not (null bs) =
                Scope [ i | (y, i) <- zip args [0 ..], y `elem` bs ]
            | otherwise = Plain
          arguments = [ Argument x srt (role x) | x <- args, srt <- take 1 [ t | Slot y t _ <- items, y == x ] ]
          vacuous = [ VacuousBinder kind name (productionName p) x
                    | Just xs <- [declared], x <- xs, x `notElem` bracketed ]
      Right (GProduction (GlobalName (productionName p)) items arguments, vacuous)

    item i = case i of
      Word w -> Right (maybe (Terminal w) (\srt -> Slot w srt []) (sortOf w))
      Binding hd bs -> case sortOf hd of
        Just srt@(OfLanguage _) -> Right (Slot hd srt bs)
        _ -> Left (NotAMetavariable hd)

    named args x
      | x `elem` args = Right ()
      | isJust (sortOf x) = Left (NotAnArgument x)
      | otherwise = Left (NotAMetavariable x)

    bound args occurrences declared y
      | y `notElem` args = Left (NotAnArgument y)
      | y `elem` occurrences = Left (OccurrenceBinds y)
      | Just xs <- declared, y `notElem` xs = Left (NotADeclaredBinder y)
      | otherwise = Right ()

    stringClass wrong x = case sortOf x of
      Just (OfClass _ (GlobalName "String") _) -> Right ()
      Just s -> Left (wrong x s)
      Nothing -> Left (NotAMetavariable x)

-- | §5.1: exactly two productions, one with no slot of the context's own sort
-- and one with exactly one.
contextShaped :: [String] -> Grammar -> Bool
contextShaped own g =
  case map ownSlots (grammarProductions g) of
    counts -> length counts == 2 && 0 `elem` counts && 1 `elem` counts
  where
    ownSlots p = length [ () | Slot x _ _ <- gproductionItems p, x `elem` own ]

-- | The @T@ of a token class, and its expression: a definition whose type
-- reduces to @Token T@ and whose value to a regex literal (MS6 phase 100
-- refused any other).
tokenClassOf :: GlobalEnv -> String -> Maybe (GlobalName, Regex)
tokenClassOf env x = do
  d <- lookupDefinition (GlobalName x) env
  t <- case whnf env [] (definitionType d) of
    App (Global g []) t | g == tokenName -> case whnf env [] t of
      Global tn [] -> Just tn
      _ -> Nothing
    _ -> Nothing
  re <- case whnf env [] (definitionBody d) of
    App (Primitive (LRegex src)) _ -> either (const Nothing) Just (parseRegex src)
    _ -> Nothing
  Just (t, re)

-- | The installed grammars as one Earley grammar (phase 102): a production is a
-- rule of its language's nonterminal; a terminal is a literal, a class slot a
-- scan with the class's expression, a metavariable slot its language's
-- nonterminal. The non-linear groups are the slot positions of each name
-- written more than once.
earleyRules :: [Grammar] -> [Earley.Rule]
earleyRules gs =
  [ Earley.Rule (nameOf (gproductionName p)) (nameOf (grammarName g)) (map symbol items) same
  | g <- reverse gs
  , p <- grammarProductions g
  , let items = gproductionItems p
        slots = [ x | Slot x _ _ <- items ]
        same = [ (x, ps) | x <- nub slots, let ps = [ k | (y, k) <- zip slots [0 ..], y == x ], length ps > 1 ]
  ]
  where
    nameOf (GlobalName n) = n
    symbol i = case i of
      Terminal t -> Earley.Literal t
      Slot x (OfClass _ _ re) _ -> Earley.Scan x re
      Slot _ (OfLanguage h) _ -> Earley.Nonterminal (nameOf h)
