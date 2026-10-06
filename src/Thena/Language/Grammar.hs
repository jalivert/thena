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
  , RulePart (..)
  , RuleProblem (..)
  , checkGrammar
  , builtInTags
  , substitutionNames
  , lookupNames
  , extensionOf
  , isName
  , variableProduction
  , variableProductions
  , variableClass
  , classesNamed
  , classesReached
  , tokenClassOf
  , earleyRules
  , productionBody
  ) where

import Data.List (nub, (\\))
import Data.Maybe (isJust, listToMaybe)

import Thena.Core.Reduce (whnf)
import Thena.Core.Term (Core (..), GlobalName (..), Literal (..), tokenName)
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
  | BuiltInTag
    -- ^ the language is named like one of Thena's own tags (MS6 phase 106):
    -- a rule base reads an installed grammar's tag before the built-ins
  | ContextKey [String]
    -- ^ the extension production's @String@ arguments, when there is not
    -- exactly one: the generated lookup compares one name (§5.3's @ne@), and
    -- which argument that is has to be unambiguous (MS6 phase 107)
  | LookupTaken String
    -- ^ a name the context's lookup relation would declare — @Ctx-in@,
    -- @Ctx-here@, @Ctx-there@ — is already declared (MS6 phase 107)
  | FunctionTaken String
    -- ^ a function generated substitution would declare (§4.7) is already
    -- declared, by anything or by a production of this block
  | NoVariableProduction
    -- ^ a language with binders and no production @‹x› as occurrence@, so a
    -- renamed binder has no term to become (§4.7)
  | VariableProductions [String]
    -- ^ more than one production declares an occurrence; substitution would
    -- not know which one a renamed binder becomes
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
  case (kind, extensionOf g) of
    (ContextBlock, Just e) -> case [ argumentName a | a <- gproductionArguments e, isName a ] of
      [_] -> Right ()
      xs -> refuse (ContextKey xs)
    _ -> Right ()
  case [ f | f <- lookupNames g, taken f || f `elem` prodNames ] of
    f : _ -> refuse (LookupTaken f)
    [] -> Right ()
  if kind == LanguageBlock then either refuse Right (substitutable (installed ++ [g]) g) else Right ()
  case [ f | f <- substitutionNames g, taken f || f `elem` prodNames ] of
    f : _ -> refuse (FunctionTaken f)
    [] -> Right ()
  Right (g, concatMap snd prods ++ unprimeable g ++ unownedBinders g ++ scopesUnwalked g)
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
    -- **A binder at a class the language has no occurrence for** (MS8 phase
    -- 153). The classes a language /reads/ are 'variableProductions'; the
    -- classes it /binds/ are on its 'Occurrence' and 'Binder' roles, which is
    -- the whole reason the class is there. Where a binder's class is not one
    -- of the read ones, generated substitution renames it with the single map
    -- it carries and rebuilds it with the single variable production's
    -- constructor — so the binder comes back as one of this language's own
    -- variables. Said and not refused: `~5k3mg` is going to make this correct,
    -- and until then an author who writes it should see what it causes.
    unownedBinders gr =
      [ BinderClassUnowned kind name (nameOf (gproductionName p)) (nameOf cls)
      | kind == LanguageBlock
      , p <- grammarProductions gr
      , a <- gproductionArguments p
      , Binder cls <- [argumentRole a]
      , cls `notElem` map fst (variableProductions gr)
      ]
    -- **A binder free in an argument of another language** (MS8 phase 154).
    -- 'substitutable' used to refuse this outright and now refuses only the
    -- case the other language cannot reach the class at all; what is left is
    -- the generator, which gives a method a recursive result only for an
    -- argument of its own language, so the foreign argument is rebuilt as
    -- written while the binder beside it is renamed. Said rather than refused
    -- for the same reason the refusal narrowed: this is `~5k3mg`'s target.
    scopesUnwalked gr =
      [ ScopeUnwalked kind name (nameOf (gproductionName p)) (argumentName a)
      | kind == LanguageBlock
      , p <- grammarProductions gr
      , a <- gproductionArguments p
      , Scope _ <- [argumentRole a]
      , argumentSort a /= OfLanguage (grammarName gr)
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

    sortOf x
      | x `elem` heads = Just (OfLanguage (GlobalName name))
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
      Right (GProduction (GlobalName (productionName p)) items arguments, vacuous)

    -- **The placeholder's glyph is reserved — HIS RULING, 2026-09-28, MS7 phase
    -- 127.** A grammar that could write it or read it would make one glyph mean
    -- two things in the same buffer, told apart only by looking closely; his
    -- reason for refusing that outright is that it fails anyone who cannot, and
    -- that a user will type it to see what happens within ten minutes. The
    -- check is here so that \"reserved\" is a property of every installed
    -- grammar rather than a convention nothing enforces.
    reserved w
      | placeholderChar `elem` w = Left (ReservedTerminal w)
      | otherwise = Right ()

    -- A class is refused when it would *accept* the glyph, which is what makes
    -- it a term. @/./@ does; @/[a-z]+/@ does not.
    reservedClass x srt = case srt of
      OfClass _ _ re | any (> 0) (matches re [placeholderChar]) -> Left (ReservedClass x)
      _ -> Right ()

    item i = case i of
      Word w -> case sortOf w of
        Nothing  -> reserved w >> Right (Terminal w)
        Just srt -> reservedClass w srt >> Right (Slot w srt [])
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

-- | Can substitution be generated for this language (§4.7, MS6 phase 105)?
--
-- A language with no binder and no occurrence has nothing to generate, and
-- passes. One that has either needs **exactly one variable production** — the
-- one production that declares an occurrence, taking only that — because a
-- binder renamed to avoid capture must become a term, and that production is
-- the only way to make a name one. **That is what "one identifier class"
-- (§4.7) comes to**: every binder is already a @String@, and one variable
-- production means one sort of name. It cannot mean one class /name/, since
-- §4.4's own @let : { x, y } as binders@ needs two.
--
-- **And a binder is free only in an argument of a language that reaches its
-- class** (MS8 phase 154, `~5k3mg`). Until then it had to be an argument of
-- /this/ language, the only one substitution over it walks into — which refused
-- the shape `~5k3mg` exists for, a binder of one grammar scoping over a slot of
-- another that reads that very class. **The own-language case is not special and
-- is not written down**: a binder's class is one this grammar names, so
-- 'classesReached' of this grammar contains it, and the rule below passes it
-- without knowing whose argument it is.
--
-- The grammars are the dependency graph — the installed ones and the one being
-- checked — because reaching a class is a question about more than one grammar.
substitutable :: [Grammar] -> Grammar -> Either GrammarProblem ()
substitutable gs g
  | null named = Right ()
  | otherwise = do
      -- The metadata names at most one occurrence per production, so a
      -- production appears here once for each it declares, which is once.
      case [ (p, a) | (p, a) <- named, isOccurrence a ] of
        [] -> Left NoVariableProduction
        [(p, a)]
          | length (gproductionArguments p) == 1 -> Right ()
          | otherwise -> inProduction p (OccurrenceNotAlone (argumentName a))
        pas -> Left (VariableProductions [ n | (p, _) <- pas, let GlobalName n = gproductionName p ])
      case [ (p, a, l, cls)
           | p <- grammarProductions g
           , a <- gproductionArguments p
           , Scope bs <- [argumentRole a]
           , OfLanguage l <- [argumentSort a]
           , cls <- [ c | i <- bs, Just c <- [binderClass p i] ]
           , cls `notElem` reachedBy l
           ] of
        (p, a, l, cls) : _ -> inProduction p (ScopeElsewhere (argumentName a) l cls)
        [] -> Right ()
  where
    -- A 'Scope' names binder argument positions (§4.7), and the class is on
    -- the role there — asked of the position rather than carried twice, which
    -- is the same reason 'Scope' has no class of its own.
    binderClass p i = case drop i (gproductionArguments p) of
      a : _ | Binder cls <- argumentRole a -> Just cls
      _ -> Nothing
    reachedBy l = concat [ classesReached gs h | h <- gs, grammarName h == l ]
    named = [ (p, a) | p <- grammarProductions g, a <- gproductionArguments p, isNamed (argumentRole a) ]
    isNamed r = case r of
      Occurrence _ -> True
      Binder _     -> True
      _            -> False
    isOccurrence a = case argumentRole a of
      Occurrence _ -> True
      _            -> False
    inProduction p why = let GlobalName n = gproductionName p in Left (InProduction n why)

-- | The functions generated substitution declares for a language (§4.7), in
-- the order they are declared; none for a language with no occurrence.
substitutionNames :: Grammar -> [String]
substitutionNames g = case variableProduction g of
  Nothing -> []
  Just _ -> [ n ++ suffix | suffix <- ["-fresh", "-fv", "-subst-all", "-subst"] ]
  where GlobalName n = grammarName g

-- | **Every occurrence class the language reads, with the production that
-- reads it** — one entry per class, in declaration order (MS8 phase 153).
--
-- This is the shape `~tmnrr` and `~5k3mg` need and the one everything about
-- classes should be written against: a language may read more than one kind of
-- name, and which classes it reads is a question about the whole grammar
-- rather than about one production. **'substitutable' still refuses a second
-- variable production**, so today this list is empty or a singleton — the list
-- is the design arriving ahead of the refusal being lifted, not a claim that
-- it already is.
--
-- A production declares at most one occurrence (the metadata names one), so a
-- production appears here once; two productions at the /same/ class would
-- appear twice and are what 'substitutable' is refusing.
variableProductions :: Grammar -> [(GlobalName, GProduction)]
variableProductions g
  | grammarKind g /= LanguageBlock = []
  | otherwise =
      [ (cls, p)
      | p <- grammarProductions g
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
  nub [ cls | p <- grammarProductions g, a <- gproductionArguments p, cls <- classOf (argumentRole a) ]
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
classesReached gs g = foldl addClass [] (concatMap classesNamed (walk [] [g]))
  where
    addClass cs c
      | c `elem` cs = cs
      | otherwise = cs ++ [c]
    walk done [] = done
    walk done (h : queue)
      | grammarName h `elem` map grammarName done = walk done queue
      | otherwise = walk (done ++ [h]) (queue ++ slotGrammars h)
    slotGrammars h =
      [ k | p <- grammarProductions h
          , Slot _ (OfLanguage l) _ <- gproductionItems p
          , k <- gs, grammarName k == l ]

-- | A language's variable production, if it has one — the production that
-- declares an occurrence. 'substitutable' has checked there is at most one.
--
-- **The single-class door, and it is the one phase 155 removes.** Everything
-- that has to work for @n@ classes reads 'variableProductions' instead.
variableProduction :: Grammar -> Maybe GProduction
variableProduction g = case variableProductions g of
  (_, p) : _ -> Just p
  []         -> Nothing

-- | **The regular expression of the language's identifier class** — the one its
-- 'variableProduction' reads an occurrence at (§4.7 gives a language exactly
-- one).
--
-- Added at phase 146 so that a generated @L-fresh@ can mint names the class
-- accepts (MS6 closeout 23). 'Nothing' for a grammar with no variable
-- production, or one whose occurrence is not at a class — neither generates
-- substitution, so neither has an @L-fresh@ to name.
variableClass :: Grammar -> Maybe Regex
variableClass g = do
  p <- variableProduction g
  listToMaybe [ re | a <- gproductionArguments p
                   , Occurrence _ <- [argumentRole a]
                   , OfClass _ _ re <- [argumentSort a] ]

-- | A context's extension production — the one with a slot of the context's
-- own sort (§5.1). 'Nothing' for anything that is not a context.
extensionOf :: Grammar -> Maybe GProduction
extensionOf g
  | grammarKind g /= ContextBlock = Nothing
  | otherwise = case [ p | p <- grammarProductions g
                         , any ((== OfLanguage (grammarName g)) . argumentSort) (gproductionArguments p) ] of
      p : _ -> Just p
      [] -> Nothing

-- | An argument that is a name: a @Token String@ class's match.
isName :: Argument -> Bool
isName a = case argumentSort a of
  OfClass _ (GlobalName "String") _ -> True
  _ -> False

-- | What a context's lookup relation declares (§5.3, MS6 phase 107), in order:
-- the relation, then its two constructors — prefixed with the context's name,
-- his answer of 2026-09-21, so that two contexts in one session cannot clash.
lookupNames :: Grammar -> [String]
lookupNames g
  | grammarKind g /= ContextBlock = []
  | otherwise = [ n ++ suffix | suffix <- ["-in", "-here", "-there"] ]
  where GlobalName n = grammarName g

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
