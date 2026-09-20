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
  , Ident (..)
  , Scope
  , Var
  , close
  , fresh
   )
import Thena.Development.Component (Component (..))
import Thena.Development.Partial (Constraint (..), Partial (..))
import Thena.Errors (DevForm (..), ResolveError (..))
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
import Thena.Syntax.Concrete
  ( Raw (..)
  , RawBinder (..)
  , RawIdent (..)
  , RawConstraint (..)
  , RawConstructor (..)
  , RawData (..)
  )


-- | Names bound locally, innermost first.
type Local = [(String, Var)]

-- | The global names a written name may resolve to.
--
-- The definitions of the environment — not the constants, and not the inductive
-- records — plus, while a declaration is resolving its own constructors, the
-- datatype being declared, which is not in the environment yet and cannot be:
-- its own constructors mention it (see 'resolveData'). A 'Global' node names
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
type Globals = [GlobalName]

globalsOf :: GlobalEnv -> Globals
globalsOf e = map fst (definitions e) ++ map fst (primitives e)

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

-- | Resolve a raw tree as a core term. Holes, guesses and constraints are
-- rejected here: they live only in a development (§3.1).
resolve :: GlobalEnv -> Context -> Int -> Raw -> Either ResolveError (Core, Int)
resolve = resolveWith []

-- | 'resolve', with the template's splices filled (MS5 phase 81).
--
-- **Two entry points over one worker**, as 'Thena.Core.Unify' has @unify@ and
-- @unifyInto@ and 'Thena.Core.Convert' has @convert@ and @subsumes@: a term
-- with no @${…}@ in it resolves identically either way, so nothing that existed
-- before this phase can have changed meaning.
resolveWith
  :: Splices -> GlobalEnv -> Context -> Int -> Raw -> Either ResolveError (Core, Int)
resolveWith sp env ctx = core env (globalsOf env) sp ctx []


-- | Resolve a raw tree as a development, taking the LONGEST PREFIX (§2.7):
-- every leading binder becomes a chain link, so 'Trailing' ends up holding
-- something that is not a binder unless @⌜ ⌝@ says otherwise.
resolvePartial :: GlobalEnv -> Context -> Int -> Raw -> Either ResolveError (Partial, Int)
resolvePartial env ctx = partial env (globalsOf env) [] ctx []

-- --------------------------------------------------------------------------
-- Core terms
-- --------------------------------------------------------------------------

-- | @env@ answers "is @d@ a declared datatype, and what is its shape" for an
-- @elim@ (phase 7); @gs@ answers "is @s@ in scope as an ordinary name" for
-- everything else, and is not always @globalsOf env@ — see 'Globals'.
core
  :: GlobalEnv -> Globals -> Splices -> Context -> Local -> Int
  -> Raw -> Either ResolveError (Core, Int)
core env gs sp ctx local n raw = case raw of
  -- Local, then the ambient context, then the globals. A binder shadows a
  -- global of the same name, which is what one namespace (§3.6) requires: the
  -- names collide and the innermost wins.
  RawName s -> case lookup s local of
    Just v  -> Right (Free v, n)
    Nothing -> case lookupEntry s ctx of
      Just v  -> Right (Free v, n)
      Nothing
        | GlobalName s `elem` gs -> Right (Global (GlobalName s) [], n)
        | otherwise              -> Left (NotInScope s)

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
  RawAt i rls -> nameOf sp i >>= \s -> case lookup s local of
    Just _  -> Left (LevelArgumentsOnALocal s)
    Nothing -> case lookupEntry s ctx of
      Just _ -> Left (LevelArgumentsOnALocal s)
      Nothing
        | GlobalName s `elem` gs -> do
            let args = map levelOfNat rls
            Right (Global (GlobalName s) args, n)
        | otherwise -> Left (NotInScope s)

  RawApp f a -> do
    (f', n1) <- core env gs sp ctx local n f
    (a', n2) <- core env gs sp ctx local n1 a
    Right (App f' a', n2)

  -- A non-dependent arrow is a 'Pi' whose variable does not occur.
  RawArrow s b -> do
    (s', n1) <- core env gs sp ctx local n s
    (b', n2) <- core env gs sp ctx local n1 b
    let (v, n3) = fresh n2
    Right (Pi (Ident "_") s' (close v b'), n3)

  RawLam bs b -> binders env gs sp Lam ctx local n bs b
  RawPi bs b  -> binders env gs sp Pi ctx local n bs b

  RawLet i val ty b -> do
    x          <- nameOf sp i
    (val', n1) <- core env gs sp ctx local n val
    (ty', n2)  <- core env gs sp ctx local n1 ty
    let (v, n3) = fresh n2
    (b', n4)   <- core env gs sp ctx ((x, v) : local) n3 b
    Right (Let (Ident x) val' ty' (close v b'), n4)

  -- Transparent here: the corners only say something in a development
  -- position, where they stop the spine. A no-op rather than an error, because
  -- rejecting them would make the printer's own output fail to re-read in a
  -- nested position.
  RawQuote t -> core env gs sp ctx local n t

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
  RawElim di rls ps m ms is t -> do
    d         <- nameOf sp di
    dn        <- datatypeNamed env gs sp ctx local d
    def       <- maybe (Left (NotADatatype d)) Right (lookupInductive dn env)
    let dls = map levelOfNat rls
    (ps', n1) <- coreList env gs sp ctx local n ps
    (m', n2)  <- core env gs sp ctx local n1 m
    (ms', n3) <- coreList env gs sp ctx local n2 ms
    (is', n4) <- coreList env gs sp ctx local n3 is
    (t', n5)  <- core env gs sp ctx local n4 t
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

  RawClaim {}   -> Left (NotACoreTerm AHole)
  RawGuess {}   -> Left (NotACoreTerm AGuess)
  RawPending {} -> Left (NotACoreTerm AConstraint)

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
-- (@AGENDA.md@ item 28) — the constructors are checked in a context where the
-- type former exists but its eliminator does not, because the eliminator is
-- generated from the completed declaration.
datatypeNamed
  :: GlobalEnv -> Globals -> Splices -> Context -> Local -> String
  -> Either ResolveError GlobalName
datatypeNamed env gs sp ctx local d = case core env gs sp ctx local 0 (RawName d) of
  Right (Global g _, _) -> Right g
  _                   -> Left (NotADatatype d)

-- | A run of terms in the same local scope, left to right, threading the
-- counter — what @elim@\'s three list-valued fields need (§2.6).
coreList
  :: GlobalEnv -> Globals -> Splices -> Context -> Local -> Int
  -> [Raw] -> Either ResolveError ([Core], Int)
coreList _ _ _ _ _ n [] = Right ([], n)
coreList env gs sp ctx local n (r : rs) = do
  (t, n1)  <- core env gs sp ctx local n r
  (ts, n2) <- coreList env gs sp ctx local n1 rs
  Right (t : ts, n2)

-- | One binder group at a time, each nested inside the last.
binders
  :: GlobalEnv -> Globals -> Splices
  -> (Ident -> Core -> Scope Core -> Core)
  -> Context -> Local -> Int -> [RawBinder] -> Raw
  -> Either ResolveError (Core, Int)
binders env gs sp con ctx local n bs b = case bs of
  [] -> core env gs sp ctx local n b
  RawBinder i ty : rest -> do
    x         <- nameOf sp i
    (ty', n1) <- core env gs sp ctx local n ty
    let (v, n2) = fresh n1
    (b', n3) <- binders env gs sp con ctx ((x, v) : local) n2 rest b
    Right (con (Ident x) ty' (close v b'), n3)

-- --------------------------------------------------------------------------
-- Developments
-- --------------------------------------------------------------------------

partial
  :: GlobalEnv -> Globals -> Splices -> Context -> Local -> Int
  -> Raw -> Either ResolveError (Partial, Int)
partial env gs sp ctx local n raw = case raw of
  RawLam bs b -> binderLinks env gs sp Assume ctx local n bs b

  -- **A leading @∀@ run is components, exactly as a leading @λ@ run is** (MS4
  -- phase 41f). The fifth component is a ∀-binder, so the concrete syntax it
  -- needs is the one a core Π already has, and adding it here is the whole of
  -- what the DC's syntax owes it — no token, no production.
  --
  -- It costs what the @λ@ case has always cost: a development whose trailing
  -- term is a bare Π cannot be written without corners. @⌜ ∀ (x : A) -> B ⌝@
  -- is the escape, and 'RawQuote' below is where it stops the spine.
  RawPi bs b -> binderLinks env gs sp Quantify ctx local n bs b

  RawLet i val ty b -> do
    x          <- nameOf sp i
    (val', n1) <- core env gs sp ctx local n val
    (ty', n2)  <- core env gs sp ctx local n1 ty
    let (v, n3) = fresh n2
    (b', n4)   <- partial env gs sp ctx ((x, v) : local) n3 b
    Right (Under (Define v (Ident x) val' ty') b', n4)

  RawClaim i ty b -> do
    x         <- nameOf sp i
    (ty', n1) <- core env gs sp ctx local n ty
    let (v, n2) = fresh n1
    (b', n3)  <- partial env gs sp ctx ((x, v) : local) n2 b
    Right (Under (Claim v (Ident x) ty') b', n3)

  -- The guess body does NOT see the hole it fills: Γ_(?x ≐ P : S . p) = Γ_P
  -- (§4.5). Resolved with 'local' as it was; only the continuation gains @x@.
  RawGuess i ty g b -> do
    x         <- nameOf sp i
    (ty', n1) <- core env gs sp ctx local n ty
    (g', n2)  <- partial env gs sp ctx local n1 g
    let (v, n3) = fresh n2
    (b', n4)  <- partial env gs sp ctx ((x, v) : local) n3 b
    Right (Under (Guess v (Ident x) g' ty') b', n4)

  RawPending k b -> do
    (k', n1) <- constraint env gs sp ctx local n k
    (b', n2) <- partial env gs sp ctx local n1 b
    Right (Pending k' b', n2)

  -- The corners stop the spine: what is inside is a term, not a chain.
  RawQuote t -> do
    (t', n1) <- core env gs sp ctx local n t
    Right (Trailing t', n1)

  -- Everything else is the trailing term. This is the whole of longest prefix:
  -- the binder cases above consume as much as they can, and this catches the
  -- first thing that is not a binder.
  _ -> do
    (t', n1) <- core env gs sp ctx local n raw
    Right (Trailing t', n1)

-- | Each binder group in a @λ@ or a @∀@ becomes its own link.
--
-- Parameterised by which component it builds, the way 'binders' above is
-- parameterised by 'Thena.Core.Term.Lam' or 'Thena.Core.Term.Pi': the two runs
-- differ in exactly that and in nothing else.
binderLinks
  :: GlobalEnv -> Globals -> Splices -> (Var -> Ident -> Core -> Component)
  -> Context -> Local -> Int
  -> [RawBinder] -> Raw -> Either ResolveError (Partial, Int)
binderLinks env gs sp build ctx local n bs b = case bs of
  [] -> partial env gs sp ctx local n b
  RawBinder i ty : rest -> do
    x         <- nameOf sp i
    (ty', n1) <- core env gs sp ctx local n ty
    let (v, n2) = fresh n1
    (b', n3) <- binderLinks env gs sp build ctx ((x, v) : local) n2 rest b
    Right (Under (build v (Ident x) ty') b', n3)

-- | Ξ's binders scope over @s@, @t@ and @T@ and nothing else.
constraint
  :: GlobalEnv -> Globals -> Splices -> Context -> Local -> Int
  -> RawConstraint -> Either ResolveError (Constraint, Int)
constraint env gs sp ctx local n (RawConstraint bs s t ty) = do
  (xi, local', n1) <- telescope env gs ctx local n bs
  (s', n2)  <- core env gs sp ctx local' n1 s
  (t', n3)  <- core env gs sp ctx local' n2 t
  (ty', n4) <- core env gs sp ctx local' n3 ty
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
-- former's index binders name positions, not values (§3.7).
resolveData
  :: GlobalEnv -> Int -> RawData
  -> Either ResolveError (InductiveDefinition, Int)
resolveData env n (RawData name ps ty cs) = do
  -- **A declaration writes no level parameters** (MS3 phase 33c). It used to —
  -- @data D {ℓ}@, minted here as 'LRigid's and in scope throughout — and that
  -- was scaffolding, the only way to make a datatype polymorphic before metas
  -- existed. Now every written @Type@ mints a meta like any other, and
  -- "Thena.Global.Declare" computes the declared universe from the
  -- constructors' arguments and generalises whatever is left.
  (params, afterParams, n1)  <- telescope env gs [] [] n ps
  (indices, _, rest, n2)     <- prefix env gs afterParams n1 ty
  (level, n3) <- case rest of
    RawUniverse k   -> Right (levelOfNat k, n2)
    -- A bare @Type@: the level is worked out by the declaration path, which is
    -- where the constructors' arguments are known.
    RawUniverseOpen -> let (v, n') = freshLevelMeta n2 in Right (LVar v, n')
    _               -> Left (NotAUniverse name)
  -- The datatype being declared joins 'Globals' here, and only here: a
  -- constructor may recursively mention it (@succ : Nat -> Nat@), and
  -- 'lookupInductive' would find nothing for it in @env@ mid-declaration.
  (cs', n4) <- constructors env (dn : gs) dn params (length indices) afterParams n3 cs
  Right (InductiveDefinition dn [] params indices level cs', n4)
  where
    gs = globalsOf env
    dn = GlobalName name

constructors
  :: GlobalEnv -> Globals -> GlobalName -> Context -> Int -> Local
  -> Int -> [RawConstructor]
  -> Either ResolveError ([ConstructorDefinition], Int)
constructors _ _ _ _ _ _ n [] = Right ([], n)
constructors env gs dn params want local n (RawConstructor cn ty : rest) = do
  (args, inside, tgt, n1) <- prefix env gs local n ty
  (tgt', n2)              <- core env gs [] [] inside n1 tgt
  ixs                     <- targetIndices dn params want cn tgt'
  (rest', n3)             <- constructors env gs dn params want local n2 rest
  Right (ConstructorDefinition (GlobalName cn) args ixs (map (const Plain) args) : rest', n3)

-- --------------------------------------------------------------------------
-- Telescopes
-- --------------------------------------------------------------------------

-- | A binder group list, outermost first. Only 'Hypothesis' entries ever
-- appear (§3.3).
telescope
  :: GlobalEnv -> Globals -> Context -> Local -> Int
  -> [RawBinder] -> Either ResolveError (Context, Local, Int)
telescope _ _ _ local n [] = Right ([], local, n)
-- **No splices here** (MS5 phase 88): a telescope is a declaration's, read
-- from a file rather than built by a rule, so there is no environment for a
-- splice to be filled from — which is why 'core' is called with @[]@ below and
-- was before this phase too.
telescope env gs ctx local n (RawBinder i ty : rest) = do
  x         <- nameOf [] i
  (ty', n1) <- core env gs [] ctx local n ty
  let (v, n2) = fresh n1
  (xi, local', n3) <- telescope env gs ctx ((x, v) : local) n2 rest
  Right (Hypothesis v (Ident x) ty' : xi, local', n3)

-- | Peel the binder prefix of a declared type, and hand back what is left.
--
-- Used at the two places a declaration writes a telescope: the type former's
-- own type, whose prefix is the indices and whose tail must be a universe, and
-- a constructor's type, whose prefix is its arguments and whose tail is its
-- target. @∀@ groups and bare arrows both contribute — @succ : Nat -> Nat@ has
-- one argument and it happens to be nameless.
prefix
  :: GlobalEnv -> Globals -> Local -> Int -> Raw
  -> Either ResolveError (Context, Local, Raw, Int)
prefix env gs local n raw = case raw of
  RawPi bs b -> do
    (tel, local1, n1)        <- telescope env gs [] local n bs
    (tel', local2, rest, n2) <- prefix env gs local1 n1 b
    Right (tel ++ tel', local2, rest, n2)

  -- An arrow's argument has no written name, and unlike the @Ident "_"@ that
  -- 'core' puts on a non-dependent 'Pi' this one is visible: the generated
  -- wrapper abstracts it, and @λ (_ : Nat) -> ‹succ _›@ is not something to
  -- hand a student (§3.7 — the point of generating into the environment is that
  -- it can be read). The printer freshens a repeat to @x1@.
  RawArrow s b -> do
    (s', n1) <- core env gs [] [] local n s
    let (v, n2) = fresh n1
    (tel, local', rest, n3) <- prefix env gs local n2 b
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

