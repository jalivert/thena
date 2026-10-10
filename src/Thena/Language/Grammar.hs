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
  , ProductionKind (..)
  , Item (..)
  , Argument (..)
  , Sort (..)
  , ArgRole (..)
  , GrammarError (..)
  , GrammarProblem (..)
  , ProductionProblem (..)
  , RulePart (..)
  , RuleProblem (..)
  , checkGrammar
  , checkNotation
  , notationInto
  , constructorProductions
  , builtInTags
  , substitutionNames
  , lookupNames
  , lookupNamesOf
  , extensionsOf
  , isName
  , variableProductions
  , variableRegex
  , classesNamed
  , classesReached
  , classesSubstituted
  , classOwner
  , grammarsReached
  , tokenClassOf
  , earleyRules
  , productionBody
  ) where

import Data.List (nub, (\\))
import Data.Maybe (isJust, listToMaybe)

import Thena.Core.Reduce (whnf)
import Thena.Core.Term (Core (..), GlobalName (..), Literal (..), instantiate, tokenName)
import qualified Thena.Language.Earley as Earley
import Thena.Language.Earley (placeholderChar)
import Thena.Language.Regex (Regex, matches, parseRegex, primingChar)
import Thena.Errors (BuildError, SyntaxError, Warning (..))
import Thena.Global.Env (ArgRole (..), GlobalEnv, definitionBody, definitionType, isDeclared, lookupDefinition)
import Thena.Language.Reader (Block (..), Metadata (..), Production (..), RawItem (..), RawRule (..))
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
  { gproductionName      :: GlobalName    -- ^ the constructor, or the function
  , gproductionItems     :: [Item]
  , gproductionArguments :: [Argument]
    -- ^ **the distinct names, in order of first appearance** (§4.6). A name
    -- written twice is one argument (§4.3, non-linear).
  , gproductionKind      :: ProductionKind
  }
  deriving (Eq, Show)

-- | What a production's name denotes (MS8 phase 158, §4.8, `~hwxrx`).
--
-- **A production either builds the datatype or applies a function to it**, and
-- everything that is about the /datatype/ reads 'constructorProductions' while
-- everything that is about the /notation/ reads them all. The parser and the
-- builder cannot tell the two apart, and that is the point: a reading is a
-- 'Thena.Language.Earley.Node' either way and
-- 'Thena.Language.Build.buildCore' writes the head applied to its arguments,
-- which is a constructor application or a function call by what the head is.
--
-- **Why a function production exists at all**: a rule may only write what the
-- grammar parses, and the paper's @Γ, X\<:Q, Δ ⊢ t : T@ joins two contexts.
-- The joining /constructor/ is refused on purpose — it would make @Ctx@ a tree
-- in which @join (join a b) c@, @join a (join b c)@ and @join empty a@ are
-- distinct terms for one context, with conversion structural and nothing to
-- identify them. **A function reduces; a constructor does not.** So @append@ is
-- an ordinary definition by @elim Ctx@, and the notation is what was missing.
data ProductionKind
  = Constructor
    -- ^ a production of the @language@, @context@ or @judgment@ block itself
  | Function
    -- ^ a production of a @notation@ block: its name is a declared function and
    -- the reading elaborates to that function applied. **It contributes nothing
    -- to what the block generates** — not a constructor, not a class, not an
    -- extension — and the datatype is the one it was before
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
    -- ^ §5.1: a context needs one production with no slot of its own sort and
    -- at least one with exactly one. **More than one extension is allowed since
    -- MS8 phase 156** — each gets its own lookup relation, which is what the
    -- count ever existed for; a production with /two/ of its own slots is still
    -- refused, because no lookup relation reads one
  | BuiltInTag
    -- ^ the language is named like one of Thena's own tags (MS6 phase 106):
    -- a rule base reads an installed grammar's tag before the built-ins
  | ContextKey String [String]
    -- ^ an extension production, and its @String@ arguments when there is not
    -- exactly one: the generated lookup compares one name (§5.3's @ne@), and
    -- which argument that is has to be unambiguous (MS6 phase 107; named per
    -- extension at MS8 phase 156)
  | LookupTaken String
    -- ^ a name the context's lookup relation would declare — @Ctx-in@,
    -- @Ctx-here@, @Ctx-there@ — is already declared (MS6 phase 107)
  | FunctionTaken String
    -- ^ a function generated substitution would declare (§4.7) is already
    -- declared, by anything or by a production of this block
  | VariableProductions GlobalName [String]
    -- ^ the class, and more than one production of this language declaring an
    -- occurrence **at it**: substitution would not know which one a renamed
    -- binder of that class becomes. **Narrowed to one class at MS8 phase 155**
    -- — it used to be more than one occurrence production of any kind, which is
    -- what gave a language exactly one notion of a variable
  | ClassOwnedTwice GlobalName [GlobalName]
    -- ^ a class this grammar reaches, and the languages it reaches that read an
    -- occurrence at it (MS8 phase 155). **A class a grammar reaches belongs to
    -- one of the languages it reaches**, because what a renamed name of that
    -- class becomes is that language's variable production and the map
    -- substituting for it is a map into that language's terms — reach two and
    -- neither is determined. Two /unrelated/ languages reading one token class
    -- is ordinary and not this
  | NoSuchGrammar
    -- ^ §4.8: a @notation@ block naming no installed grammar. **The one block
    -- that does not declare its own name** — it adds productions to a grammar
    -- that is already there, so the name has to be found rather than be free
  | NotationMetavars [String]
    -- ^ §4.8: a @notation@ block whose header names more than the grammar. Its
    -- productions are written in the grammar's own metavariables, and declaring
    -- a new one would change what every other block's productions may say
  | InProduction String ProductionProblem
  | InRule String RuleProblem
    -- ^ a judgment's rule (MS6 phase 108, §6)
  deriving (Eq, Show)

-- | Which part of a rule a parse was of.
data RulePart = Premises | Conclusion
  deriving (Eq, Show)

-- | Why a judgment's rule was refused (MS6 phase 108, §6.1–6.4).
data RuleProblem
  = RuleUnparsed RulePart String String Earley.ParseFailure
    -- ^ the part, what it had to be (@typing@, or @premises@) and its text
  | RuleNotAMetavariable String
    -- ^ §6.2: a name where a metavariable was expected that is not one, with
    -- any suffix — never an implicit binding
  | PremiseNameIsMetavariable String
    -- ^ a premise named like a metavariable, which it would then shadow
  | PremiseNameTaken String
    -- ^ two premises of one rule named alike, or a premise named like a type
    -- the rule mentions
  | QuantifierUnreadable SyntaxError
    -- ^ the annotated tier's @∀ …@ is not a surface telescope
  | NotQuantified String
    -- ^ the annotated tier writes its quantification, and this metavariable
    -- is used in the rule without being bound there
  | QuantifiedTwice String
    -- ^ the annotated tier's @∀@ binds a name twice: it lists the rule's
    -- metavariables, and there is nothing for the first one to scope over
  | RuleUnbuilt BuildError
    -- ^ a reading the parser gave that is not a term — what
    -- "Thena.Language.Build" refuses for any object term
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
  | OccurrenceNotAlone String
    -- ^ the occurrence is not the production's only argument (MS6 phase 105):
    -- substitution replaces the whole node, so anything beside it would be lost
  | ScopeElsewhere String GlobalName GlobalName
    -- ^ a binder is free in an argument of another language, that language,
    -- and the class the binder binds at — a class the other language does not
    -- reach, so nothing in that argument can ever occur at it (MS6 phase 105,
    -- narrowed to unreachable classes at MS8 phase 154)
  | NotationBinds String
    -- ^ a judgment's notation writes a binding form: its slots are indices,
    -- and nothing binds in an index (MS6 phase 108)
  | ReservedTerminal String
    -- ^ a terminal that writes 'Thena.Language.Earley.placeholderChar'
    -- (MS7 phase 127)
  | ReservedClass String
    -- ^ a token class that would scan it (MS7 phase 127) — the same refusal one
    -- step further back, because a class that reads the glyph makes it a term
    -- exactly as a terminal does
  -- §4.8's checks on a @notation@ production (MS8 phase 158). All five are
  -- about the one thing a function production claims that a constructor does
  -- not: that a definition of that name exists and takes exactly what the
  -- notation's slots will hand it.
  | NotADeclaredFunction
    -- ^ the production's name is not a declared function. **Inference from
    -- this condition was refused** (his ruling, 2026-10-07): \"a function of
    -- that name is in scope\" is already the clash check a @language@ block
    -- makes, so reading the two forms off it would consume that diagnostic and
    -- let a typo colliding with a prelude name become a function production
  | FunctionHasNotation
    -- ^ the name is already a production of an installed grammar. A production
    -- name is unique across every grammar ('productionBody' relies on it), and
    -- a second spelling for one function would break that
  | FunctionArity Int Int
    -- ^ what the function takes, and how many slots the production has
  | FunctionSlot String Core GlobalName
    -- ^ a slot, the type the function takes there **as written**, and the type
    -- the slot is. The first is a 'Core' and not a name because the whole point
    -- of the refusal is that it may not be a datatype at all — a universe, a
    -- function type, @List Ty@ — and a message has to show the author what their
    -- own signature says
  | FunctionResult Core
    -- ^ what the function returns, when it is not the grammar's datatype — the
    -- production stands where a term of the grammar stands, so nothing else
    -- could be built from it. A 'Core' for the same reason as 'FunctionSlot' 
  | FunctionBinds String
    -- ^ a @notation@ production writing a binding form. A function's argument
    -- is a term it is handed, and nothing about an application binds
  | FunctionMetadata
    -- ^ a @notation@ production with @as occurrence@ or @as binder@ metadata.
    -- A role is read off the /constructor/ it is on (§4.7) and a function
    -- production generates none
  deriving (Eq, Show)

-- | Validate a block against the grammars already installed and the global
-- environment. The warnings are §4.5's vacuous binders.
checkGrammar :: [Grammar] -> GlobalEnv -> Block -> Either GrammarError (Grammar, [Warning])
checkGrammar installed env b = do
  -- The block's own name first: a language named like something declared is
  -- that, before it is anything about metavariables.
  if taken name then refuse NameTaken else Right ()
  if name `elem` builtInTags then refuse BuiltInTag else Right ()
  case heads \\ nub heads of
    x : _ -> refuse (MetavariableRepeated x)
    [] -> Right ()
  case [ x | x <- heads, isJust (lookup x metavarsElsewhere) || isJust (tokenClassOf env x) ] of
    x : _ -> refuse (MetavariableTaken x)
    [] -> Right ()
  -- A judgment's constructors are its rules; its one production is its
  -- notation and carries the judgment's own name.
  let prodNames
        | kind == JudgmentBlock = map ruleName (blockRules b)
        | otherwise = map productionName (blockProductions b)
  case [ p | (p, k) <- zip prodNames [0 :: Int ..]
           , taken p || p == name || p `elem` take k prodNames ] of
    p : _ -> refuse (ConstructorTaken p)
    [] -> Right ()
  prods <- traverse (\p -> either (refuse . InProduction (productionName p)) Right (production p))
             (blockProductions b)
  let g = Grammar kind (GlobalName name) heads (map fst prods)
  if kind == ContextBlock && not (contextShaped heads g) then refuse ContextShape else Right ()
  case [ (nameOf (gproductionName e), xs)
       | kind == ContextBlock, e <- extensionsOf g
       , let xs = [ argumentName a | a <- gproductionArguments e, isName a ]
       , length xs /= 1 ] of
    (p, xs) : _ -> refuse (ContextKey p xs)
    [] -> Right ()
  case [ f | f <- lookupNames g, taken f || f `elem` prodNames ] of
    f : _ -> refuse (LookupTaken f)
    [] -> Right ()
  -- **A context is checked too, since MS8 phase 157 generates substitution for
  -- one**: what matters to it is that a class it reaches has one owner, so that
  -- the map replacing a name has one language to be into. A judgment generates
  -- no functions and is not checked.
  if kind /= JudgmentBlock then either refuse Right (substitutable (installed ++ [g]) g) else Right ()
  case [ f | f <- substitutionNames (installed ++ [g]) g, taken f || f `elem` prodNames ] of
    f : _ -> refuse (FunctionTaken f)
    [] -> Right ()
  Right (g, concatMap snd prods ++ unprimeable g)
  where
    kind = blockKind b
    name = blockName b

    -- **A language whose identifier class no character extends** (MS6 closeout
    -- 23, phase 146). 'Thena.Language.Regex.primingChar' decides it on the
    -- automaton; when it answers 'Nothing' the generated @L-fresh@ falls back to
    -- @'@ and a renamed binder is a name the notation cannot write. Said here
    -- because this is where an author finds out, and said rather than refused
    -- because nothing is actually broken but the printing.
    unprimeable gr =
      [ UnprimeableClass kind name (nameOf cls)
      | (cls, p) <- variableProductions gr
      , a <- gproductionArguments p
      , Occurrence cls' <- [argumentRole a]
      , cls' == cls
      , OfClass _ _ re <- [argumentSort a]
      , primingChar re == Nothing
      ]
    nameOf (GlobalName x) = x
    -- **A judgment's name is not a metavariable**: its header has none, and
    -- its notation's are the languages' (§6.1).
    heads
      | kind == JudgmentBlock = []
      | otherwise = name : blockMetavars b

    refuse :: GrammarProblem -> Either GrammarError a
    refuse = Left . GrammarError kind name

    metavarsElsewhere =
      [ (m, grammarName g) | g <- installed, m <- grammarMetavars g ]

    -- A global, or a name a grammar already installed will generate.
    taken x =
      isDeclared (GlobalName x) env
        || GlobalName x `elem` concat
             [ grammarName g : map gproductionName (grammarProductions g) | g <- installed ]

    -- **This block's metavariables first, then every other grammar's**, which
    -- is only an order because @MetavariableTaken@ has already refused a name
    -- that is both.
    sortOf = sortIn env ([ (m, GlobalName name) | m <- heads ] ++ metavarsElsewhere)

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
      -- **The class a role carries comes from the check that validated it**
      -- (MS8 phase 153). 'stringClass' has to look the sort up anyway to
      -- refuse an occurrence or a binder that is not at a @Token String@
      -- class, so it hands the class back rather than being asked twice —
      -- which is also what leaves 'role' below with no unreachable branch to
      -- fall through into.
      occClasses <- traverse (withClass OccurrenceNotString) occurrences
      bndClasses <- traverse (withClass BinderNotString) binders
      let role x
            | Just cls <- lookup x occClasses = Occurrence cls
            | Just cls <- lookup x bndClasses = Binder cls
            | (bs : _) <- scopeOf x, not (null bs) =
                Scope [ i | (y, i) <- zip args [0 ..], y `elem` bs ]
            | otherwise = Plain
          arguments = [ Argument x srt (role x) | x <- args, srt <- take 1 [ t | Slot y t _ <- items, y == x ] ]
          vacuous = [ VacuousBinder kind name (productionName p) x
                    | Just xs <- [declared], x <- xs, x `notElem` bracketed ]
      Right (GProduction (GlobalName (productionName p)) items arguments Constructor, vacuous)

    item i = case i of
      Word w -> case sortOf w of
        Nothing  -> reservedTerminal w >> Right (Terminal w)
        Just srt -> reservedScan w srt >> Right (Slot w srt [])
      Binding hd _ | kind == JudgmentBlock -> Left (NotationBinds hd)
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

    -- **An occurrence and a binder are at a @Token String@ class, and this
    -- answers which class** (MS8 phase 153). The sort it reads is 'sortOf' of
    -- the name, which is the same function 'item' built the slot's sort from,
    -- so the class recorded on the role and the class on the 'Argument' beside
    -- it cannot disagree.
    withClass wrong x = (,) x <$> stringClass wrong x

    stringClass wrong x = case sortOf x of
      Just (OfClass cls (GlobalName "String") _) -> Right cls
      Just s -> Left (wrong x s)
      Nothing -> Left (NotAMetavariable x)

-- | What a name in a production means: a metavariable of one of these
-- grammars, or a token class (§4.2). 'Nothing' makes it a terminal.
--
-- Lifted out of 'checkGrammar' at MS8 phase 158 so that 'checkNotation' asks
-- the same question — a @notation@ block's slots are the grammar's own
-- metavariables and nothing about resolving one differs there.
sortIn :: GlobalEnv -> [(String, GlobalName)] -> String -> Maybe Sort
sortIn env metavars x
  | Just g <- lookup x metavars = Just (OfLanguage g)
  | Just (t, re) <- tokenClassOf env x = Just (OfClass (GlobalName x) t re)
  | otherwise = Nothing

-- | **The placeholder's glyph is reserved — HIS RULING, 2026-09-28, MS7 phase
-- 127.** A grammar that could write it or read it would make one glyph mean two
-- things in the same buffer, told apart only by looking closely; his reason for
-- refusing that outright is that it fails anyone who cannot, and that a user
-- will type it to see what happens within ten minutes. The check is here so
-- that \"reserved\" is a property of every installed grammar rather than a
-- convention nothing enforces.
reservedTerminal :: String -> Either ProductionProblem ()
reservedTerminal w
  | placeholderChar `elem` w = Left (ReservedTerminal w)
  | otherwise = Right ()

-- | A class is refused when it would *accept* the glyph, which is what makes it
-- a term. @\/.\/@ does; @\/[a-z]+\/@ does not.
reservedScan :: String -> Sort -> Either ProductionProblem ()
reservedScan x srt = case srt of
  OfClass _ _ re | any (> 0) (matches re [placeholderChar]) -> Left (ReservedClass x)
  _ -> Right ()

-- | Validate a @notation@ block (MS8 phase 158, §4.8, `~hwxrx`): the
-- productions to add to the grammar it names, which 'notationInto' puts there.
--
-- **It declares nothing and generates nothing.** The grammar's datatype, its
-- lookup relations and its substitution were all generated when its own block
-- loaded, and none of them changes: a function production is not a constructor,
-- so 'constructorProductions' does not have it and every consumer written
-- against that sees what it saw before. What the block adds is one Earley rule
-- per production, which is why @Γ ∪ Δ@ then parses wherever a @Ctx@ is
-- expected — a judgment rule's index included, which is the whole point.
--
-- **The checks are the ones a constructor production does not need**: the name
-- is a declared function, it is not already a production of some grammar, and
-- its type takes exactly the slots in order and returns the grammar's datatype.
-- The ones about a production's /shape/ are §4.2's and are shared with
-- 'checkGrammar' through 'sortIn', 'reservedTerminal' and 'reservedScan'.
--
-- **A binding form and @as@ metadata are refused.** Both say something about a
-- constructor's arguments (§4.7) and a function has no constructor to say it
-- of; an application binds nothing.
checkNotation :: [Grammar] -> GlobalEnv -> Block -> Either GrammarError Grammar
checkNotation installed env b = do
  g <- maybe (refuse NoSuchGrammar) Right named
  case blockMetavars b of
    [] -> Right ()
    ms -> refuse (NotationMetavars ms)
  prods <- traverse (\p -> either (refuse . InProduction (productionName p)) Right (production g p))
             (blockProductions b)
  Right (Grammar NotationBlock (grammarName g) (grammarMetavars g) prods)
  where
    name = blockName b
    named = case [ g | g <- installed, grammarName g == GlobalName name ] of
      g : _ -> Just g
      []    -> Nothing

    refuse :: GrammarProblem -> Either GrammarError a
    refuse = Left . GrammarError NotationBlock name

    -- Every installed grammar's metavariables, the named one's included — it is
    -- in @installed@, so this is the same list 'checkGrammar' resolves against
    -- with nothing of its own to add.
    sortOf = sortIn env [ (m, grammarName g) | g <- installed, m <- grammarMetavars g ]

    taken f = f `elem` concat [ map gproductionName (grammarProductions g) | g <- installed ]

    production g p = do
      items <- traverse item (productionItems p)
      if null items then Left NoItems else Right ()
      case productionMetadata p of
        Nothing -> Right ()
        Just _  -> Left FunctionMetadata
      -- **The distinct names in order of first appearance**, as §4.3 has it for
      -- a constructor: a name written twice is one argument, and the parser's
      -- non-linear filter is what makes the two readings agree. Every argument
      -- is 'Plain' — a role is metadata on a constructor and there is none here.
      let slots = [ (x, srt) | Slot x srt _ <- items ]
          args = [ Argument x srt Plain
                 | x <- nub (map fst slots), srt <- take 1 [ t | (y, t) <- slots, y == x ] ]
          f = GlobalName (productionName p)
      if taken f then Left FunctionHasNotation else Right ()
      (domains, result) <- maybe (Left NotADeclaredFunction) Right (functionShape env f)
      if length domains == length args
        then Right ()
        else Left (FunctionArity (length domains) (length args))
      sequence_ [ slotIs a dom | (a, dom) <- zip args domains ]
      if typeNamed env result == Just (grammarName g)
        then Right ()
        else Left (FunctionResult (whnf env [] result))
      Right (GProduction f items args Function)

    -- **The parameter has to be the slot's own type, named.** A function whose
    -- argument is anything else could not be handed what the notation reads
    -- there, and one whose argument is a /dependent/ type is refused the same
    -- way: the slots of a production are independent, so there is nothing for
    -- a later type to depend on.
    slotIs a dom
      | typeNamed env dom == Just wanted = Right ()
      | otherwise = Left (FunctionSlot (argumentName a) (whnf env [] dom) wanted)
      where
        wanted = case argumentSort a of
          OfLanguage l  -> l
          OfClass _ t _ -> t

    item i = case i of
      Word w -> case sortOf w of
        Nothing  -> reservedTerminal w >> Right (Terminal w)
        Just srt -> reservedScan w srt >> Right (Slot w srt [])
      Binding hd _ -> Left (FunctionBinds hd)

-- | **The datatype a type is**, reduced — and 'Nothing' for anything that is not
-- one. The refusal shows the type itself rather than a stand-in name, so the
-- caller keeps the 'Core' for its message.
--
-- A datatype whose wrapper is saturated reduces to a 'Canonical', a postulated
-- one stays a 'Global', and a slot's sort is always one of those applied to
-- nothing — a language, a context or a class's @T@, every one of which is
-- declared with no parameters and no indices. So a parameterised type, a
-- universe, a function type and a type that depends on an earlier argument all
-- answer 'Nothing' and are all refused.
typeNamed :: GlobalEnv -> Core -> Maybe GlobalName
typeNamed env t = case whnf env [] t of
  Global g []      -> Just g
  Canonical g _ [] -> Just g
  _                -> Nothing

-- | What a declared function takes, in order, and what it returns — 'Nothing'
-- for a name that is not an ordinary definition at all (MS8 phase 158, §4.8).
--
-- **A constructor's wrapper is a definition and answers like any other**, so
-- this does not tell a function from a constructor and @NotADeclaredFunction@
-- is for a name that is declared nowhere. Naming a constructor is refused one
-- check earlier, by @FunctionHasNotation@ when it is a grammar's production, and
-- otherwise by its result type: a constructor of @X@ returns an @X@, and the
-- grammar whose notation this is would have to be @X@ — whose productions are
-- that same constructor.
--
-- The scope under each @Π@ is instantiated with a name no module can write, so
-- a type that actually depends on an earlier argument fails the slot check
-- rather than being read as though it did not. Reduced at every step, so a
-- function whose type is written through an abbreviation is peeled the same.
functionShape :: GlobalEnv -> GlobalName -> Maybe ([Core], Core)
functionShape env f = peel . definitionType <$> lookupDefinition f env
  where
    peel t = case whnf env [] t of
      Pi _ dom body -> let (ds, r) = peel (instantiate opaque body) in (dom : ds, r)
      r             -> ([], r)
    opaque = Global (GlobalName "") []

-- | **A @notation@ block's productions, in the grammar they are for** (MS8
-- phase 158): the installed grammars with that one replaced.
--
-- Appended, so declaration order is the order they were written in and every
-- constructor still comes first — which is what keeps 'constructorProductions'
-- answering exactly what it answered before the block loaded.
notationInto :: Grammar -> [Grammar] -> [Grammar]
notationInto delta = map add
  where
    add g
      | grammarName g == grammarName delta =
          g { grammarProductions = grammarProductions g ++ grammarProductions delta }
      | otherwise = g

-- | **The productions that are constructors of the grammar's datatype** — every
-- production of a @language@, @context@ or @judgment@ block, and none of a
-- @notation@ block's (MS8 phase 158, §4.8).
--
-- **This is what everything about the datatype is written against**: the
-- constructors it generates ('Thena.Driver.grammarDatatype'), the classes its
-- roles name ('classesNamed'), the extensions a context has ('extensionsOf',
-- and so its lookup relations), the methods generated substitution writes
-- ('Thena.Language.Substitution.substitutionDefinitions'), and §5.1's shape.
-- 'grammarProductions' itself is for the parser and the printer, which is
-- everything that is about /notation/.
constructorProductions :: Grammar -> [GProduction]
constructorProductions g =
  [ p | p <- grammarProductions g, gproductionKind p == Constructor ]

-- | The tags that name Thena's own parsers: @surface`…`@ and @core`…`@.
--
-- **A language may not take one** (MS5's review, 2026-09-12; moved here at MS6
-- phase 106). A tag in a rule base is looked up among the installed grammars
-- /first/ ('Thena.Rules.operandOf'), so @language core, M where …@ in a module
-- silently turned every later @core`…`@ into a term of that grammar. MS5's
-- check guarded only MS5's own languages, which phase 106 deleted.
builtInTags :: [String]
builtInTags = ["surface", "core"]

-- | The body of a named production, as Earley symbols (MS7 phase 147, moved out
-- of "Thena.Language.Instral" where phase 141 wrote it).
--
-- **The search is across every loaded grammar with no language filter, and that
-- is safe because a production name is unique across all of them.** Each
-- production becomes a datatype constructor, and a second language declaring one
-- of the same name is refused when it loads — @A's constructor same is already
-- declared@. Verified by loading such a pair rather than reasoned about;
-- @productionNamesAreUnique@ pins it with a fixture, because if constructor
-- uniqueness ever relaxed this lookup would quietly hand one language another's
-- production.
--
-- **Empty for a name no grammar has**, which cannot arise from either caller —
-- both take the name from 'Thena.Language.Build.productionNames' of a grammar in
-- the very list they pass. Answered rather than crashed, because both callers are
-- views.
productionBody :: [Grammar] -> String -> [Earley.Symbol]
productionBody gs p = case [ Earley.ruleBody r | r <- earleyRules gs, Earley.ruleName r == p ] of
  b : _ -> b
  []    -> []

-- | Can substitution be generated for this language (§4.7, MS6 phase 105,
-- generalised to @n@ classes at MS8 phase 155)?
--
-- **One variable production per class, not per language.** The production that
-- declares an occurrence at a class is the only way to turn a name of that class
-- into a term, so two of them at one class leave a renamed binder with no term
-- to become; at two /different/ classes they are two notions of a variable,
-- which is `~tmnrr`'s whole point. An occurrence production takes only its
-- occurrence, because substitution replaces the whole node.
--
-- **A class belongs to one language.** Its variable production builds what a
-- renamed binder becomes, and the map that substitutes for it is a map into that
-- language's terms, so a second language reading the same class leaves both
-- undetermined — and a grammar reaching the class through two slots could not be
-- given one map for it. 'classOwner' is that language and this is what makes it
-- a function.
--
-- **A binder is free only in an argument of a language that reaches its class.**
-- Until MS8 phase 154 it had to be an argument of /this/ language; the own-language
-- case is not written down, because a binder's class is one this grammar names
-- and so 'classesReached' of this grammar contains it.
--
-- **There is no longer a check that a language with binders has a variable
-- production** (deleted at MS8 phase 155). A renamed binder becomes a term of
-- the class's /owning/ language, which may be another one — `~5k3mg`'s
-- "bindable by any later language" — and a binder at a class no grammar owns is
-- never renamed at all, because nothing can occur at it. Both are correct rather
-- than refused, and the second is what @BinderClassUnowned@ used to warn about.
--
-- The grammars are the dependency graph: the installed ones and the one being
-- checked.
substitutable :: [Grammar] -> Grammar -> Either GrammarProblem ()
substitutable gs g = do
  case [ (cls, ps) | (cls, ps) <- grouped, length ps > 1 ] of
    (cls, ps) : _ -> Left (VariableProductions cls [ nameOf (gproductionName p) | p <- ps ])
    [] -> Right ()
  case [ (p, a) | (_, ps) <- grouped, p <- ps, a <- gproductionArguments p
               , length (gproductionArguments p) /= 1 ] of
    (p, a) : _ -> inProduction p (OccurrenceNotAlone (argumentName a))
    [] -> Right ()
  case [ (cls, hs) | cls <- classesReached gs g, let hs = owners cls, length hs > 1 ] of
    (cls, hs) : _ -> Left (ClassOwnedTwice cls hs)
    [] -> Right ()
  case [ (p, a, l, cls)
       | p <- constructorProductions g
       , a <- gproductionArguments p
       , Scope bs <- [argumentRole a]
       , OfLanguage l <- [argumentSort a]
       , cls <- [ c | i <- bs, Just c <- [binderClass p i] ]
       , cls `notElem` reachedBy l
       ] of
    (p, a, l, cls) : _ -> inProduction p (ScopeElsewhere (argumentName a) l cls)
    [] -> Right ()
  where
    -- The occurrence productions by class: the metadata names at most one
    -- occurrence per production, so a production appears under one class.
    grouped = [ (cls, [ p | (c, p) <- variableProductions g, c == cls ])
              | cls <- nub (map fst (variableProductions g)) ]
    -- A 'Scope' names binder argument positions (§4.7), and the class is on
    -- the role there — asked of the position rather than carried twice, which
    -- is the same reason 'Scope' has no class of its own.
    binderClass p i = case drop i (gproductionArguments p) of
      a : _ | Binder cls <- argumentRole a -> Just cls
      _ -> Nothing
    reachedBy l = concat [ classesReached gs h | h <- gs, grammarName h == l ]
    owners cls = [ grammarName h | h <- grammarsReached gs g, cls `elem` map fst (variableProductions h) ]
    nameOf (GlobalName x) = x
    inProduction p why = let GlobalName n = gproductionName p in Left (InProduction n why)

-- | The functions generated substitution declares for a language (§4.7), in
-- the order they are declared; none for a language that reaches no class with
-- an owner.
--
-- **One per class, and the class is in the name — MS8 phase 155.** The names
-- used to come from the language alone (@LC-fv@, @LC-subst@), which two classes
-- collide on, and keeping the unsuffixed name when there happens to be one class
-- would be a special case in the naming rule. His ruling on the context's lookup
-- relation, 2026-10-04, settled the same question the same way and accepted the
-- migration.
--
-- * @L-fresh-‹k›@ for each class @L@ **owns**, because minting a name of a class
--   belongs to the language whose notation can write one — so a grammar that
--   reaches a class without owning it calls the owner's.
-- * @L-fv-‹k›@ and @L-subst-‹k›@ for each class @L@ **reaches**, owning it or
--   not: a class can occur free inside a slot of another language.
-- * one @L-subst-all@, taking one map per class reached. Simultaneous
--   substitution is the primitive one, and now across classes too — renaming a
--   binder of one class to avoid capture needs the map of every class.
substitutionNames :: [Grammar] -> Grammar -> [String]
substitutionNames gs g
  | null reached = []
  | otherwise =
      [ n ++ "-fresh-" ++ k | k <- owned ]
        ++ [ n ++ "-fv-" ++ k | k <- reached ]
        ++ [ n ++ "-subst-all" ]
        ++ [ n ++ "-subst-" ++ k | k <- reached ]
  where
    GlobalName n = grammarName g
    reached = [ k | GlobalName k <- classesSubstituted gs g ]
    owned = [ k | GlobalName k <- map fst (variableProductions g) ]

-- | **Every occurrence class the language reads, with the production that
-- reads it** — one entry per class, in declaration order (MS8 phase 153).
--
-- This is the shape `~tmnrr` and `~5k3mg` need and the one everything about
-- classes should be written against: a language may read more than one kind of
-- name, and which classes it reads is a question about the whole grammar
-- rather than about one production.
--
-- A production declares at most one occurrence (the metadata names one), so a
-- production appears here once; two productions at the /same/ class would
-- appear twice and are what 'substitutable' refuses.
variableProductions :: Grammar -> [(GlobalName, GProduction)]
variableProductions g
  | grammarKind g /= LanguageBlock = []
  | otherwise =
      [ (cls, p)
      | p <- constructorProductions g
      , a <- gproductionArguments p
      , Occurrence cls <- [argumentRole a]
      ]

-- | **Every class a grammar's own roles name**, an occurrence's or a binder's,
-- in order of first appearance (MS8 phase 154).
--
-- Both roles, because both are a reason the grammar's substitution has to know
-- the class: an occurrence is what substitution replaces, and a binder is what
-- it renames to avoid capture. A grammar that binds a class it reads no
-- occurrence at still has to rename that binder, which is the whole of
-- 'Thena.Errors.BinderClassUnowned'.
--
-- Not filtered by block kind: this says what the roles say, and a caller that
-- only wants a language's asks a language.
classesNamed :: Grammar -> [GlobalName]
classesNamed g =
  nub [ cls | p <- constructorProductions g, a <- gproductionArguments p, cls <- classOf (argumentRole a) ]
  where
    classOf r = case r of
      Occurrence cls -> [cls]
      Binder cls     -> [cls]
      _              -> []

-- | **Every class a grammar reaches**: the ones its own roles name, and
-- everything the grammars in its slots reach. This grammar's own first, then
-- first-encounter order (MS8 phase 154, `~5k3mg`).
--
-- **This is REACHABILITY, computed as a least fixed point — his ruling,
-- 2026-10-04, and the topological shortcut is refused.** A grammar is reached
-- through a slot of another, so the answer closes over the dependency graph:
-- the loop below adds a grammar once and queues what it reaches, so a cycle
-- ends the walk rather than not terminating. **The graph is acyclic today**
-- because 'sortOf' resolves a metavariable against this grammar or one already
-- installed, so a declaration-order walk would agree — and that is exactly the
-- shortcut to refuse, because `~m5dvd` makes grammars mutually dependent and a
-- fixpoint written now costs nothing then. **Declaration order is still what
-- gives the generation order; it is not what this is written in terms of.**
--
-- Why a generator wants it, rather than 'classesNamed': substituting for one
-- class has to rename binders of /every/ class the term can contain, including
-- the ones that only appear inside a slot of another language — his correction
-- of 2026-10-04, and it is already true in F-sub, where substituting a term
-- with a free type variable into @Λ X <: Top . x@ captures that variable unless
-- the type binder is renamed too. So a grammar gets one substitution taking one
-- map per class it reaches, owning the class or not.
--
-- @gs@ is the dependency graph, and @g@ need not be in it: the walk starts
-- there. A slot naming a grammar that is not in @gs@ reaches nothing, which
-- cannot arise from 'checkGrammar' — every slot's language is this grammar or
-- an installed one.
classesReached :: [Grammar] -> Grammar -> [GlobalName]
classesReached gs g = foldl addClass [] (concatMap classesNamed (grammarsReached gs g))
  where
    addClass cs c
      | c `elem` cs = cs
      | otherwise = cs ++ [c]

-- | **The grammars a grammar reaches**, itself first, then first-encounter order
-- — the closure of \"holds a slot of\" (MS8 phase 154).
--
-- The loop adds a grammar once and queues what it holds, so a cycle ends the
-- walk rather than not terminating; that is the least fixed point, and it is why
-- `~m5dvd` costs nothing here. A slot naming a grammar not in @gs@ reaches
-- nothing, which cannot arise from 'checkGrammar'.
grammarsReached :: [Grammar] -> Grammar -> [Grammar]
grammarsReached gs g = walk [] [g]
  where
    walk done [] = done
    walk done (h : queue)
      | grammarName h `elem` map grammarName done = walk done queue
      | otherwise = walk (done ++ [h]) (queue ++ slotGrammars h)
    slotGrammars h =
      [ k | p <- constructorProductions h
          , Slot _ (OfLanguage l) _ <- gproductionItems p
          , k <- gs, grammarName k == l ]

-- | **The classes a grammar has substitution generated for**: those it reaches
-- that some language owns, in 'classesReached' order (MS8 phase 155).
--
-- Not every class reached is one of these. A class that is only ever /bound/ and
-- read nowhere has no owning language, so nothing can occur at it, no map into
-- any language's terms substitutes for it, and a binder at it is never renamed —
-- it is correct and generates nothing, which is what @BinderClassUnowned@ warned
-- about before the generator could say so.
--
-- **A context as well as a language — MS8 phase 157, `~mnr39`.** It is the same
-- question and the same answer: a context reaches the classes of the languages
-- in its slots, so F-sub's Γ reaches the type class and gets @Ctx-subst-X@,
-- which is the @[X↦P]Δ@ of the type-substitution lemma. Nothing special had to
-- be written for it — a context simply /owns/ no class, so it generates no
-- @fresh@, and its name slots are neither occurrences nor binders, so nothing in
-- one is substituted or renamed.
--
-- **A judgment gets none**: it generates a datatype of rules and no functions.
classesSubstituted :: [Grammar] -> Grammar -> [GlobalName]
classesSubstituted gs g
  | grammarKind g == JudgmentBlock = []
  | otherwise = [ cls | cls <- classesReached gs g, isJust (classOwner gs g cls) ]

-- | **The language a grammar reaches a class through** — the one among the
-- grammars it reaches whose variable production reads an occurrence at it
-- (MS8 phase 155).
--
-- **Relative to @g@, and that is the point.** Two unrelated languages may both
-- read @x : Token String@ and each is the owner for itself; what 'substitutable'
-- refuses is one grammar reaching /two/ of them, where the map for the class
-- would have no single language to be into.
classOwner :: [Grammar] -> Grammar -> GlobalName -> Maybe Grammar
classOwner gs g cls = case
  [ h | h <- grammarsReached gs g, cls `elem` map fst (variableProductions h) ] of
    [h] -> Just h
    _ -> Nothing

-- | **The regular expression of one of a language's occurrence classes** — the
-- class's own, so that a generated @L-fresh-‹k›@ mints names that class accepts
-- (MS6 closeout 23, per class at MS8 phase 155).
--
-- 'Nothing' for a class this language reads no occurrence at, or one whose
-- occurrence is not at a class — neither has an @L-fresh-‹k›@ to name.
variableRegex :: Grammar -> GlobalName -> Maybe Regex
variableRegex g cls =
  listToMaybe [ re | (c, p) <- variableProductions g, c == cls
                   , a <- gproductionArguments p
                   , Occurrence c' <- [argumentRole a], c' == cls
                   , OfClass _ _ re <- [argumentSort a] ]

-- | A context's extension productions — those with a slot of the context's own
-- sort (§5.1), in declaration order. Empty for anything that is not a context.
--
-- **Plural since MS8 phase 156**, which is the whole of `~23rg2`: F-sub's Γ
-- carries both @x : T@ and @X <: T@, and one extension per kind of binding gets
-- one lookup relation each.
extensionsOf :: Grammar -> [GProduction]
extensionsOf g
  | grammarKind g /= ContextBlock = []
  | otherwise = [ p | p <- constructorProductions g
                    , any ((== OfLanguage (grammarName g)) . argumentSort) (gproductionArguments p) ]

-- | An argument that is a name: a @Token String@ class's match.
isName :: Argument -> Bool
isName a = case argumentSort a of
  OfClass _ (GlobalName "String") _ -> True
  _ -> False

-- | Everything a context's lookup relations declare (§5.3), in order — one
-- relation per extension production (MS8 phase 156).
lookupNames :: Grammar -> [String]
lookupNames g = concatMap (lookupNamesOf g) (extensionsOf g)

-- | What one extension's lookup relation declares, in order: the relation, its
-- @here@, then one @there@ for each extension it may step over.
--
-- **Named after the EXTENSION PRODUCTION, not after the context — his ruling,
-- 2026-10-04, and the migration is his too.** The three names used to come from
-- the context's name alone (@Ctx-in@, @Ctx-here@, @Ctx-there@), which two
-- extensions collide on; keeping those for the one-extension case would be a
-- special case in the naming rule, and he took the renaming instead when both
-- were put to him. A production name is unique across every installed grammar
-- (@ConstructorTaken@), so this cannot clash either.
lookupNamesOf :: Grammar -> GProduction -> [String]
lookupNamesOf g e =
  [ n ++ "-in", n ++ "-here" ]
    ++ [ n ++ "-there-" ++ named k | k <- extensionsOf g ]
  where
    n = named e
    named p = let GlobalName x = gproductionName p in x

-- | §5.1: **one** production with no slot of the context's own sort — the empty
-- context — and **at least one** with exactly one, each an extension. A
-- production with two or more of its own slots is refused, because a lookup
-- relation steps over one binding and there is nothing for it to read in a form
-- that joins two contexts.
contextShaped :: [String] -> Grammar -> Bool
contextShaped own g =
  length [ () | c <- counts, c == 0 ] == 1
    && not (null [ () | c <- counts, c == 1 ])
    && all (<= 1) counts
  where
    counts = map ownSlots (constructorProductions g)
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
