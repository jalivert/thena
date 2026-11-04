-- | Turning the named tree the parser produces into 'Core', into a 'Partial',
-- or into an 'InductiveDefinition' (§2.5, §2.7, §3.7).
module Thena.Syntax.Resolve
  ( resolve
  , resolveWith
  , Splices
  , Filling (..)
  , resolvePartial
  , resolveData
  ) where

import Thena.Core.Context (Context, Entry (..), entryIdent, entryVar)
import Thena.Core.Level (Level (..), freshLevelMeta, levelOfNat)
import Thena.Core.Term
  ( Core (..)
  , GlobalName (..)
  , declarationNamed
  , globalUnder
  , inDeclarationOf
  , nameDotted
  , rootName
  , Ident (..)
  , InScope
  , Scope
  , Var
  , close
  , fresh
   )
import Thena.Development.Component (Component (..))
import Thena.Development.Partial (Constraint (..), Partial (..))
import Thena.Errors (DevForm (..), ObjectError (..), ResolveError (..), SyntaxError (..))
import Thena.Global.Declare (targetIndices)
import Thena.Global.Env
  ( ArgRole (..)
  , ConstructorDefinition (..)
  , GlobalEnv
  , InductiveDefinition (..)
  , definitions
  , primitives
  , inductiveConstructors
  , inductiveIndices
  , inductiveParameters
  , lookupInductive
  )
import qualified Thena.Language.Earley as Earley
import Thena.Language.Build
  ( atCharacters
  , buildCore
  , objectInput
  , objectText
  , productionNames
  , productionRule
  )
import Thena.Language.Grammar (Grammar, builtInTags, earleyRules, grammarForTag, grammarKey)
import Thena.Syntax.Concrete
  ( Raw (..)
  , RawPiece (..)
  , RawBinder (..)
  , RawIdent (..)
  , RawConstraint (..)
  , RawConstructor (..)
  , RawData (..)
  )
import Thena.Syntax.Lexer (lexTokens)
import Thena.Syntax.Parser (parseTerm)


-- | Names bound locally, innermost first.
type Local = [(String, Var)]

-- | The global names a written name may resolve to.
--
-- The definitions of the environment — not the constants, and not the inductive
-- records — plus, while a declaration is resolving its own constructors, the
-- datatype being declared, which is not in the environment yet and cannot be:
-- its own constructors gr mention it (see 'resolveData'). A 'Global' node names
-- something with a body (§3.6), which is what makes it the third form of δ.
--
-- A constant with no body is reached from 'Canonical' or 'Eliminate' instead.
-- 'Canonical' is still never written — the resolver never builds one, and the
-- user writes @succ n@, which is @App (Global "succ") n@ (§3.6). 'Eliminate'
-- **is** written, as of phase 7's @elim@ (§2.6); its head resolves through
-- this same list, in 'datatypeNamed'.
--
-- Kept separate from the 'GlobalEnv' that 'core' also threads (phase 7):
-- name resolution and an @elim@\'s shape check are different questions, and
-- the self-reference above is exactly the case an @elim@ must NOT see, since
-- 'lookupInductive' has nothing to find for a datatype mid-declaration.
data Globals = Globals
  { scopeNames :: [GlobalName]
    -- ^ what answers to a written name directly
  , scopeIn :: InScope
    -- ^ where a written name is looked up from: the namespaces an @open@ has
    -- brought into view, and the ones this point is inside
    --
    -- __It rides with the names and is not a parameter of its own__ (MS10
    -- phase 249). It was absent, and 'plainAt' said so in a comment calling
    -- the omission \"a seam and not an oversight\" on the grounds that this
    -- resolver is handed no machine to read it from — which is a fact about a
    -- signature and not a reason, and it was a live defect: after @open Ctx@ a
    -- written @empty@ resolved in a surface term and not in @:theorem@'s type.
    -- Carried here so that a caller saying what is in scope says it in full,
    -- rather than every door having to remember a second argument.
  }

globalsOf :: GlobalEnv -> InScope -> Globals
globalsOf e sc =
  Globals (map fst (definitions e) ++ map fst (primitives e)) sc

-- | What a written term's @${x}@ holes are filled with (MS5 phase 81).
--
-- **A splice supplies a nonterminal** — his observation — so a hole stands
-- exactly where a term stands and what fills it is a term. The list is by name
-- because 'Thena.Syntax.Concrete.RawSplice' names a binding; see its comment
-- for why it names one rather than holding an expression.
type Splices = [(String, Filling)]

-- | What a splice is filled with, and it is decided by the POSITION (MS5 phase
-- 88).
--
-- **A splice supplies a nonterminal** — his principle — so the grammar already
-- knows which of these a given hole wants: a term position parses to
-- 'Thena.Syntax.Concrete.RawSplice' and wants a 'Core'; a name position parses
-- to 'Thena.Syntax.Concrete.RawIdentSplice' and wants an 'Ident'. Nothing has
-- to be annotated and the two cannot be confused, because no position accepts
-- both.
data Filling
  = FillTerm Core
  | FillName Ident
  deriving (Eq, Show)

-- | A written name, or the one a splice supplies (MS5 phase 88).
--
-- **The one place a name splice is read**, so every position that wants a name
-- gets the same behaviour and the same error for an unfilled one.
nameOf :: Splices -> RawIdent -> Either ResolveError String
nameOf sp i = case i of
  RawWord x        -> Right x
  RawIdentSplice x -> case lookup x sp of
    Just (FillName (Ident nm)) -> Right nm
    -- Cannot arise for the same reason the term case cannot: a name position
    -- parses to 'RawIdentSplice' and only a name can be asked for it.
    Just (FillTerm _)          -> Left (SpliceNotFilled x)
    Nothing                    -> Left (SpliceNotFilled x)

-- | Resolve a raw tree as a core gr term. Holes, guesses and constraints are
-- rejected here: they live only in a development (§3.1).
resolve
  :: [Grammar] -> GlobalEnv -> InScope -> Context -> Int -> Raw
  -> Either ResolveError (Core, Int)
resolve gr env = resolveWith gr [] env

-- | 'resolve', with the template's splices filled (MS5 phase 81).
--
-- **Two entry points over one worker**, as 'Thena.Core.Unify' has @unify@ and
-- @unifyInto@ and 'Thena.Core.Convert' has @convert@ and @subsumes@: a term
-- with no @${…}@ in it resolves identically either way, so nothing that existed
-- before this phase can have changed meaning.
resolveWith
  :: [Grammar] -> Splices -> GlobalEnv -> InScope -> Context -> Int -> Raw
  -> Either ResolveError (Core, Int)
resolveWith gr sp env sc ctx = core gr env (globalsOf env sc) sp ctx []


-- | Resolve a raw tree as a development, taking the LONGEST PREFIX (§2.7):
-- every leading binder becomes a chain link, so 'Trailing' ends up holding
-- something that is not a binder, and a @core@ region is the way to say so
-- for a term that is one.
resolvePartial
  :: [Grammar] -> GlobalEnv -> InScope -> Context -> Int -> Raw
  -> Either ResolveError (Partial, Int)
resolvePartial gr env sc ctx = partial gr env (globalsOf env sc) [] ctx []

-- --------------------------------------------------------------------------
-- Core terms
-- --------------------------------------------------------------------------

-- | @env@ answers "is @d@ a declared datatype, and what is its shape" for an
-- @elim@ (phase 7); @gs@ answers "is @s@ in scope as an ordinary name" for
-- everything else, and is not always @globalsOf env@ — see 'Globals'.
core
  :: [Grammar] -> GlobalEnv -> Globals -> Splices -> Context -> Local -> Int
  -> Raw -> Either ResolveError (Core, Int)
core gr env gs sp ctx local n raw = case raw of
  -- **A tagged term literal resolves to the constructor application it
  -- denotes** (MS6 phase 110) — the same four checks the surface makes when
  -- one elaborates, on the same 'ObjectError', so a region that is refused
  -- says the same thing wherever it was written.
  --
  -- **Its splices are ordinary terms of this language**, resolved here and
  -- passed to 'buildCore' in the order they were written, which is the order
  -- the parser numbers them in.
  -- **THE TAG RESOLVES BY THE WALK** (MS10 phase 260, `~zjkvd`, his ruling of
  -- 2026-10-30): the written word reaches a grammar wherever its namespace is
  -- open, exactly as the datatype's name does, and the /key/ the parser wants
  -- comes off the grammar it found rather than off what was written.
  -- **THE TWO BUILT-IN TAGS ARE TAGS HERE TOO** (MS10 phase 266). A tagged
  -- literal is resolved by asking which /declared/ object language the tag
  -- names, and @core@ and @surface@ are declared by nothing — the words are
  -- reserved so that no @language@ block can take them
  -- ('Thena.Language.Grammar.builtInTags', refused as @BuiltInTag@). So the
  -- walk below answers nothing for them, and a reader that stops there says
  -- @no language called core has been declared@, which is the opposite of the
  -- truth. **'Thena.Rules' has always had this branch** for an operand's
  -- region; the term's reader never got it, so @core`t`@ was refused where
  -- @\8988 t \8989@ worked and the two notations looked complementary rather
  -- than one of them being unfinished.
  --
  -- **@core`t`@ is the term written inside it, exactly as the corners are** —
  -- transparent here, and stopping the spine in 'partial' for free, since a
  -- 'RawObject' matches none of that function's binder cases and falls to its
  -- trailing case just as 'RawQuote' does.
  RawObject tag prod ps | tag `elem` builtInTags -> case prod of
    -- A built-in tag has no productions to start at, so @core[var]`…`@ is the
    -- same mistake as a declared language's unknown production and says so.
    Just w  -> Left (NotAnObjectTerm (NoSuchObjectProduction tag w))
    Nothing
      | tag /= "core" -> Left (NotAnObjectTerm (BuiltInTagNotATerm tag))
      | otherwise -> do
          src <- regionSource
          inner <- case lexTokens src of
            Left why -> Left (NotAnObjectTerm (CoreRegionUnread tag (LexFailed why)))
            Right ts -> case parseTerm ts of
              Left why -> Left (NotAnObjectTerm (CoreRegionUnread tag (ParseFailed why)))
              Right t -> Right t
          core gr env gs sp ctx local n inner
   where
    -- **The region is handed back to the parser as text**, which is what the
    -- development calculus's own lexer and parser take and what a rule base's
    -- @core@ region has always been. An escape was split out by the region
    -- scanner and is put back verbatim: the parser reads @${x}@ itself, as an
    -- atom, so this is a reader for what the scanner produced and not a second
    -- meaning. **Only a bare word survives the round trip** — there is no
    -- printer for a 'Raw', which is also why 'Thena.Render' prints an
    -- unresolved term as its shape.
    regionSource = concat <$> traverse back ps
    back pc = case pc of
      RawChunk txt            -> Right txt
      RawSpliced (RawName [] x) -> Right ("$" ++ ['{'] ++ x ++ ['}'])
      RawSpliced _            -> Left (NotAnObjectTerm (RegionSpliceNotAName tag))

  RawObject lang prod ps -> case grammarForTag (scopeIn gs) gr lang of
    Left []  -> Left (NotAnObjectTerm (NoSuchObjectLanguage lang))
    Left amb -> Left (NotAnObjectTerm (ObjectLanguageAmbiguous lang (map nameDotted amb)))
    Right g | Just w <- prod, w `notElem` productionNames gr (grammarKey g) ->
                Left (NotAnObjectTerm (NoSuchObjectProduction lang w))
            | otherwise -> object (grammarKey g)
   where
      object key = do
        (ts, n1) <- spliced n ps
        let bits = [ either Left (const (Right ())) (piece pc) | pc <- ps ]
        tree <- case Earley.parse (earleyRules gr) (start' key) (objectInput bits) of
          Left why -> Left (NotAnObjectTerm
                              (ObjectNotParsed lang (objectText bits)
                                 (atCharacters bits why)))
          Right tree -> Right tree
        case buildCore gr ts tree of
          Left why -> Left (NotAnObjectTerm (ObjectNotATerm lang why))
          Right t  -> Right (t, n1)
      -- **The bracket is a word and the parser wants the rule's name** (MS10
      -- phase 248), and the word is looked up in the grammar the tag resolved
      -- to. The guard above has already refused a word it has no production
      -- for, so the fallback cannot be reached.
      start' key = maybe (Earley.StartAt key)
                         (\w -> maybe (Earley.StartAt key) Earley.StartRule
                                  (productionRule gr key w))
                         prod
      piece pc = case pc of
        RawChunk txt -> Left txt
        RawSpliced e -> Right e
      spliced k [] = Right ([], k)
      spliced k (RawChunk _ : rest) = spliced k rest
      spliced k (RawSpliced e : rest) = do
        (t, k1) <- core gr env gs sp ctx local k e
        (ts, k2) <- spliced k1 rest
        Right (t : ts, k2)

  -- Local, then the ambient context, then the globals. A binder shadows a
  -- global of the same name, which is what one namespace (§3.6) requires: the
  -- names collide and the innermost wins.
  -- **A qualified name is a global and nothing else** (MS10 phase 240): a
  -- binder and a context entry have no path, so there is nothing for the two
  -- lookups to find and nothing local can shadow @Nat.elim@.
  RawName ps s | not (null ps) -> plain (GlobalName ps s)

  RawName _ s -> case lookup s local of
    Just v  -> Right (Free v, n)
    Nothing -> case lookupEntry s ctx of
      Just v  -> Right (Free v, n)
      Nothing -> plain (rootName s)

  -- **A hole in the template, filled from the binding it names** (MS5 phase
  -- 81). The value arrived already resolved — it is a 'Core' the rule built —
  -- so there is nothing to look up in the context and nothing to open: it is
  -- spliced as it stands, and a binder above it weakens it, which is what
  -- @close@ does for every other term this function builds.
  RawSplice x -> case lookup x sp of
    Just (FillTerm t) -> Right (t, n)
    -- Cannot arise: a term position parses to 'RawSplice' and a name position
    -- to 'RawIdentSplice', so what fills one is decided before this runs.
    Just (FillName _) -> Left (SpliceNotFilled x)
    Nothing           -> Left (SpliceNotFilled x)

  RawUniverse k -> Right (Universe (levelOfNat k), n)

  -- A literal resolves to itself: it binds nothing and mentions nothing
  -- (MS6 phase 97a).
  RawPrimitive l -> Right (Primitive l, n)

  -- @Type@ — a universe whose level is left to be worked out (phase 33).
  -- **Typical ambiguity is this line**: the level is a meta from the shared
  -- counter, and conversion, unification and the collector at @qed@ are what
  -- decide it. Writing @Typeₙ@ instead is always available and is the recovery
  -- when they cannot (§6.3).
  RawUniverseOpen ->
    let (v, n1) = freshLevelMeta n
     in Right (Universe (LVar v), n1)

  -- @foo {ℓ 0}@ — a global at level arguments. **Refused on a local**: only a
  -- definition has level parameters, and a λ-bound name has none to give.
  RawAt ps i rls -> nameOf sp i >>= \s ->
    let at g = plainAt g (map levelOfNat rls)
     in if not (null ps) then at (GlobalName ps s) else case lookup s local of
          Just _  -> Left (LevelArgumentsOnALocal s)
          Nothing -> case lookupEntry s ctx of
            Just _  -> Left (LevelArgumentsOnALocal s)
            Nothing -> at (rootName s)

  RawApp f a -> do
    (f', n1) <- core gr env gs sp ctx local n f
    (a', n2) <- core gr env gs sp ctx local n1 a
    Right (App f' a', n2)

  -- A non-dependent arrow is a 'Pi' whose variable does not occur.
  RawArrow s b -> do
    (s', n1) <- core gr env gs sp ctx local n s
    (b', n2) <- core gr env gs sp ctx local n1 b
    let (v, n3) = fresh n2
    Right (Pi (Ident "_") s' (close v b'), n3)

  RawLam bs b -> binders gr env gs sp Lam ctx local n bs b
  RawPi bs b  -> binders gr env gs sp Pi ctx local n bs b

  RawLet i val ty b -> do
    x          <- nameOf sp i
    (val', n1) <- core gr env gs sp ctx local n val
    (ty', n2)  <- core gr env gs sp ctx local n1 ty
    let (v, n3) = fresh n2
    (b', n4)   <- core gr env gs sp ctx ((x, v) : local) n3 b
    Right (Let (Ident x) val' ty' (close v b'), n4)

  -- Phase 7: no concrete syntax existed for 'Eliminate' before this. Checked
  -- against the datatype's own record, exactly as a constructor's target is
  -- (below) — this is the same "what you wrote does not fit the form" shape
  -- check, just against 'InductiveDefinition' instead of a spine.
  --
  -- **The head goes through the same scope chain as every other name**, via
  -- 'core' on a 'RawName' rather than straight to 'lookupInductive'. DECIDED
  -- by the user 2026-08-22, for uniformity: as first written this was the one
  -- identifier in the language that ignored locals and the ambient context,
  -- so @λ (Nat : Type₀) -> elim Nat …@ silently meant the global datatype
  -- inside a binder that shadowed its name — an unannounced exception to
  -- §3.6's "one namespace, the innermost wins" that round-tripped perfectly
  -- and so was invisible to every test. Now a shadowed name resolves to the
  -- local and is refused, because a local is not a datatype.
  RawElim dps di rls ps m ms is t -> do
    w         <- nameOf sp di
    let d = nameDotted (GlobalName dps w)
    dn        <- datatypeNamed gr env gs sp ctx local dps w
    def       <- maybe (Left (NotADatatype d)) Right (lookupInductive dn env)
    let dls = map levelOfNat rls
    (ps', n1) <- coreList gr env gs sp ctx local n ps
    (m', n2)  <- core gr env gs sp ctx local n1 m
    (ms', n3) <- coreList gr env gs sp ctx local n2 ms
    (is', n4) <- coreList gr env gs sp ctx local n3 is
    (t', n5)  <- core gr env gs sp ctx local n4 t
    let wantP = length (inductiveParameters def)
        wantM = length (inductiveConstructors def)
        wantI = length (inductiveIndices def)
    if length ps' /= wantP
      then Left (WrongNumberOfEliminationParameters d wantP (length ps'))
      else if length ms' /= wantM
        then Left (WrongNumberOfMethods d wantM (length ms'))
        else if length is' /= wantI
          then Left (WrongNumberOfEliminationIndices d wantI (length is'))
          else Right (Eliminate dn dls ps' m' ms' is' t', n5)

  -- @trusted claimed actual body@ (MS8 phase 150). Nothing to look up and
  -- nothing to count: three terms, resolved left to right in the same context.
  -- **Whether the claim is plausible is not a question for resolution** — it is
  -- not a question for the checker either, which is the feature.
  RawTrusted c a b -> do
    (c', n1) <- core gr env gs sp ctx local n  c
    (a', n2) <- core gr env gs sp ctx local n1 a
    (b', n3) <- core gr env gs sp ctx local n2 b
    Right (Trusted c' a' b', n3)

  RawClaim {}   -> Left (NotACoreTerm AHole)
  RawGuess {}   -> Left (NotACoreTerm AGuess)
  RawPending {} -> Left (NotACoreTerm AConstraint)
  where
    -- | A global, at no level arguments, or the refusal that names it in full.
    plain g = plainAt g []

    -- | A global at level arguments. **The refusal prints the whole path**,
    -- because that is what was written: @Nat.elim is not in scope@ and
    -- @elim is not in scope@ are different reports (MS10 phase 240).
    --
    -- **A written word is also tried as a declaration's short name** (MS10
    -- phase 248), so @Nat@ reaches the datatype @Nat.Nat@ — the alias a @data@
    -- declaration mints. Nothing is in the environment under @Nat@, which is
    -- what makes it an alias rather than a definition, so the probe is the only
    -- way to find it. **The written name still wins**, as it does under an
    -- @open@: an alias can add a way to resolve and never change one.
    --
    -- **The open namespaces are walked here too, through the one function
    -- both doors call** (MS10 phase 249, repairing @~7zn7k@):
    -- 'Thena.Core.Term.globalUnder' is shared with
    -- 'Thena.Engine.globalNamed', so a written word cannot mean one thing in a
    -- surface term and another in a command's argument. The alias above is
    -- part of that walk, which is why it is no longer tried separately.
    plainAt g args = case globalUnder (`elem` scopeNames gs) (scopeIn gs) g of
      Right g'  -> Right (Global g' args, n)
      Left []   -> Left (NotInScope (nameDotted g))
      Left amb  -> Left (NameIsAmbiguous (nameDotted g) (map nameDotted amb))

-- | Resolve @elim@\'s head through the ordinary scope chain, and insist it
-- named a global.
--
-- 'core' on a 'RawName' is what does the looking, so locals and the ambient
-- context shadow a global of the same name here exactly as they do
-- everywhere else (§3.6). Anything that does not come back a 'Global' is not
-- a datatype: a shadowed binder resolves to 'Free', and reporting that as
-- 'NotADatatype' is accurate — it is not one.
--
-- A name that is a 'Global' but has no inductive record is left for the
-- caller's 'lookupInductive' to refuse, which is also what reports a datatype
-- named inside its own declaration. That refusal is correct and stays
-- (@AGENDA.md@ item 28) — the constructors gr are checked in a context where the
-- type former exists but its eliminator does not, because the eliminator is
-- generated from the completed declaration.
datatypeNamed
  :: [Grammar] -> GlobalEnv -> Globals -> Splices -> Context -> Local
  -> [String] -> String
  -> Either ResolveError GlobalName
datatypeNamed gr env gs sp ctx local ps d =
  case core gr env gs sp ctx local 0 (RawName ps d) of
    Right (Global g _, _) -> Right g
    _                     -> Left (NotADatatype (nameDotted (GlobalName ps d)))

-- | A run of terms in the same local scope, left to right, threading the
-- counter — what @elim@\'s three list-valued fields need (§2.6).
coreList
  :: [Grammar] -> GlobalEnv -> Globals -> Splices -> Context -> Local -> Int
  -> [Raw] -> Either ResolveError ([Core], Int)
coreList _ _ _ _ _ _ n [] = Right ([], n)
coreList gr env gs sp ctx local n (r : rs) = do
  (t, n1)  <- core gr env gs sp ctx local n r
  (ts, n2) <- coreList gr env gs sp ctx local n1 rs
  Right (t : ts, n2)

-- | One binder group at a time, each nested inside the last.
binders
  :: [Grammar] -> GlobalEnv -> Globals -> Splices
  -> (Ident -> Core -> Scope Core -> Core)
  -> Context -> Local -> Int -> [RawBinder] -> Raw
  -> Either ResolveError (Core, Int)
binders gr env gs sp con ctx local n bs b = case bs of
  [] -> core gr env gs sp ctx local n b
  RawBinder i ty : rest -> do
    x         <- nameOf sp i
    (ty', n1) <- core gr env gs sp ctx local n ty
    let (v, n2) = fresh n1
    (b', n3) <- binders gr env gs sp con ctx ((x, v) : local) n2 rest b
    Right (con (Ident x) ty' (close v b'), n3)

-- --------------------------------------------------------------------------
-- Developments
-- --------------------------------------------------------------------------

partial
  :: [Grammar] -> GlobalEnv -> Globals -> Splices -> Context -> Local -> Int
  -> Raw -> Either ResolveError (Partial, Int)
partial gr env gs sp ctx local n raw = case raw of
  RawLam bs b -> binderLinks gr env gs sp Assume ctx local n bs b

  -- **A leading @∀@ run is components, exactly as a leading @λ@ run is** (MS4
  -- phase 41f). The fifth component is a ∀-binder, so the concrete syntax it
  -- needs is the one a core gr Π already has, and adding it here is the whole of
  -- what the DC's syntax owes it — no token, no production.
  --
  -- It costs what the @λ@ case has always cost: a development whose trailing
  -- term is a bare Π cannot be written as itself. @core\`∀ (x : A) -> B\`@ is
  -- the escape, and it stops the spine by being no binder at all \8212 the
  -- fall-through at the end of this function is what takes it (MS10 phase 269;
  -- until then the escape was @⌜ … ⌝@ and had a case of its own here).
  RawPi bs b -> binderLinks gr env gs sp Quantify ctx local n bs b

  RawLet i val ty b -> do
    x          <- nameOf sp i
    (val', n1) <- core gr env gs sp ctx local n val
    (ty', n2)  <- core gr env gs sp ctx local n1 ty
    let (v, n3) = fresh n2
    (b', n4)   <- partial gr env gs sp ctx ((x, v) : local) n3 b
    Right (Under (Define v (Ident x) val' ty') b', n4)

  RawClaim i ty b -> do
    x         <- nameOf sp i
    (ty', n1) <- core gr env gs sp ctx local n ty
    let (v, n2) = fresh n1
    (b', n3)  <- partial gr env gs sp ctx ((x, v) : local) n2 b
    Right (Under (Claim v (Ident x) ty') b', n3)

  -- The guess body does NOT see the hole it fills: Γ_(?x ≐ P : S . p) = Γ_P
  -- (§4.5). Resolved with 'local' as it was; only the continuation gains @x@.
  RawGuess i ty g b -> do
    x         <- nameOf sp i
    (ty', n1) <- core gr env gs sp ctx local n ty
    (g', n2)  <- partial gr env gs sp ctx local n1 g
    let (v, n3) = fresh n2
    (b', n4)  <- partial gr env gs sp ctx ((x, v) : local) n3 b
    Right (Under (Guess v (Ident x) g' ty') b', n4)

  RawPending k b -> do
    (k', n1) <- constraint gr env gs sp ctx local n k
    (b', n2) <- partial gr env gs sp ctx local n1 b
    Right (Pending k' b', n2)

  -- Everything else is the trailing term. This is the whole of longest prefix:
  -- the binder cases above consume as much as they can, and this catches the
  -- first thing that is not a binder.
  _ -> do
    (t', n1) <- core gr env gs sp ctx local n raw
    Right (Trailing t', n1)

-- | Each binder group in a @λ@ or a @∀@ becomes its own link.
--
-- Parameterised by which component it builds, the way 'binders' above is
-- parameterised by 'Thena.Core.Term.Lam' or 'Thena.Core.Term.Pi': the two runs
-- differ in exactly that and in nothing else.
binderLinks
  :: [Grammar] -> GlobalEnv -> Globals -> Splices -> (Var -> Ident -> Core -> Component)
  -> Context -> Local -> Int
  -> [RawBinder] -> Raw -> Either ResolveError (Partial, Int)
binderLinks gr env gs sp build ctx local n bs b = case bs of
  [] -> partial gr env gs sp ctx local n b
  RawBinder i ty : rest -> do
    x         <- nameOf sp i
    (ty', n1) <- core gr env gs sp ctx local n ty
    let (v, n2) = fresh n1
    (b', n3) <- binderLinks gr env gs sp build ctx ((x, v) : local) n2 rest b
    Right (Under (build v (Ident x) ty') b', n3)

-- | Ξ's binders gr scope over @s@, @t@ and @T@ and nothing else.
constraint
  :: [Grammar] -> GlobalEnv -> Globals -> Splices -> Context -> Local -> Int
  -> RawConstraint -> Either ResolveError (Constraint, Int)
constraint gr env gs sp ctx local n (RawConstraint bs s t ty) = do
  (xi, local', n1) <- telescope gr env gs ctx local n bs
  (s', n2)  <- core gr env gs sp ctx local' n1 s
  (t', n3)  <- core gr env gs sp ctx local' n2 t
  (ty', n4) <- core gr env gs sp ctx local' n3 ty
  Right (Equate xi s' t' ty', n4)

-- --------------------------------------------------------------------------
-- Declarations (§3.7)
-- --------------------------------------------------------------------------

-- | Resolve a @data@ declaration.
--
-- A declaration is closed: it is read in the empty context, not in the
-- development's, because what enters the global environment must mean the same
-- thing in every later development (§3.3.1). Only the parameters, and the datatype's
-- own name, are added to the scope it is read in.
--
-- **The indices are not in scope in the constructors.** Each constructor
-- supplies its own index expressions and the record keeps those; the type
-- former's index binders gr name positions, not values (§3.7).
resolveData
  :: [Grammar] -> GlobalEnv -> InScope -> Int -> RawData
  -> Either ResolveError (InductiveDefinition, Int)
resolveData gr env sc n (RawData name ps ty cs) = do
  -- **A declaration writes no level parameters** (MS3 phase 33c). It used to —
  -- @data D {ℓ}@, minted here as 'LRigid's and in scope throughout — and that
  -- was scaffolding, the only way to make a datatype polymorphic before metas
  -- existed. Now every written @Type@ mints a meta like any other, and
  -- "Thena.Global.Declare" computes the declared universe from the
  -- constructors' arguments and generalises whatever is left.
  (params, afterParams, n1)  <- telescope gr env gs [] [] n ps
  (indices, _, rest, n2)     <- prefix gr env gs afterParams n1 ty
  (level, n3) <- case rest of
    RawUniverse k   -> Right (levelOfNat k, n2)
    -- A bare @Type@: the level is worked out by the declaration path, which is
    -- where the constructors' arguments are known.
    RawUniverseOpen -> let (v, n') = freshLevelMeta n2 in Right (LVar v, n')
    _               -> Left (NotAUniverse name)
  -- The datatype being declared joins 'Globals' here, and only here: a
  -- constructor may recursively mention it (@succ : Nat -> Nat@), and
  -- 'lookupInductive' would find nothing for it in @env@ mid-declaration.
  (cs', n4) <- constructors gr env gs { scopeNames = dn : scopeNames gs } dn params (length indices) afterParams n3 cs
  Right (InductiveDefinition dn [] params indices level cs', n4)
  where
    gs = globalsOf env sc
    -- **The declaration lives in the namespace it opens** (MS10 phase 248), the
    -- same placement 'Thena.Driver.datatypeProgram' gives a @data@ item in a
    -- file: @data Nat@ typed at the REPL declares @Nat.Nat@, @Nat.zero@ and
    -- @Nat.elim@. Rooting it here left @elim@ and @case@ at the root — a name
    -- 'Thena.Global.Env.eliminatorName' derives from the datatype's, and
    -- 'inDeclarationOf' of a root name is a root name — so the FIRST datatype a
    -- session declared took the global @elim@ and the second was refused
    -- @elim is already declared@.
    dn = declarationNamed (rootName name)

constructors
  :: [Grammar] -> GlobalEnv -> Globals -> GlobalName -> Context -> Int -> Local
  -> Int -> [RawConstructor]
  -> Either ResolveError ([ConstructorDefinition], Int)
constructors _ _ _ _ _ _ _ n [] = Right ([], n)
constructors gr env gs dn params want local n (RawConstructor cn ty : rest) = do
  (args, inside, tgt, n1) <- prefix gr env gs local n ty
  (tgt', n2)              <- core gr env gs [] [] inside n1 tgt
  ixs                     <- targetIndices dn params want cn tgt'
  (rest', n3)             <- constructors gr env gs dn params want local n2 rest
  Right (ConstructorDefinition (inDeclarationOf dn cn) args ixs (map (const Plain) args) : rest', n3)

-- --------------------------------------------------------------------------
-- Telescopes
-- --------------------------------------------------------------------------

-- | A binder group list, outermost first. Only 'Hypothesis' entries ever
-- appear (§3.3).
telescope
  :: [Grammar] -> GlobalEnv -> Globals -> Context -> Local -> Int
  -> [RawBinder] -> Either ResolveError (Context, Local, Int)
telescope _ _ _ _ local n [] = Right ([], local, n)
-- **No splices here** (MS5 phase 88): a telescope gr is a declaration's, read
-- from a file rather than built by a rule, so there is no environment for a
-- splice to be filled from — which is why 'core' is called with @[]@ below and
-- was before this phase too.
telescope gr env gs ctx local n (RawBinder i ty : rest) = do
  x         <- nameOf [] i
  (ty', n1) <- core gr env gs [] ctx local n ty
  let (v, n2) = fresh n1
  (xi, local', n3) <- telescope gr env gs ctx ((x, v) : local) n2 rest
  Right (Hypothesis v (Ident x) ty' : xi, local', n3)

-- | Peel the binder prefix gr of a declared type, and hand back what is left.
--
-- Used at the two places a declaration writes a telescope: the type former's
-- own type, whose prefix gr is the indices and whose tail must be a universe, and
-- a constructor's type, whose prefix gr is its arguments and whose tail is its
-- target. @∀@ groups and bare arrows both contribute — @succ : Nat -> Nat@ has
-- one argument and it happens to be nameless.
prefix
  :: [Grammar] -> GlobalEnv -> Globals -> Local -> Int -> Raw
  -> Either ResolveError (Context, Local, Raw, Int)
prefix gr env gs local n raw = case raw of
  RawPi bs b -> do
    (tel, local1, n1)        <- telescope gr env gs [] local n bs
    (tel', local2, rest, n2) <- prefix gr env gs local1 n1 b
    Right (tel ++ tel', local2, rest, n2)

  -- An arrow's argument has no written name, and unlike the @Ident "_"@ that
  -- 'core' puts on a non-dependent 'Pi' this one is visible: the generated
  -- wrapper abstracts it, and @λ (_ : Nat) -> ‹succ _›@ is not something to
  -- hand a student (§3.7 — the point of generating into the environment is that
  -- it can be read). The printer freshens a repeat to @x1@.
  RawArrow s b -> do
    (s', n1) <- core gr env gs [] [] local n s
    let (v, n2) = fresh n1
    (tel, local', rest, n3) <- prefix gr env gs local n2 b
    Right (Hypothesis v (Ident "x") s' : tel, local', rest, n3)

  _ -> Right ([], local, raw, n)

-- --------------------------------------------------------------------------
-- Odds and ends
-- --------------------------------------------------------------------------


-- | The innermost entry wins, so the fold keeps the last match: a 'Context' is
-- outermost first (§3.2).
lookupEntry :: String -> Context -> Maybe Var
lookupEntry s = foldl pick Nothing
  where
    pick acc e
      | entryIdent e == Ident s = Just (entryVar e)
      | otherwise               = acc

