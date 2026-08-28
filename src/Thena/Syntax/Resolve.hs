-- | Turning the named tree the parser produces into 'Core', into a 'Partial',
-- or into an 'InductiveDefinition' (§2.5, §2.7, §3.7).
module Thena.Syntax.Resolve
  ( resolve
  , resolveAt
  , resolvePartial
  , resolveData
  ) where

import Thena.Core.Context (Context, Entry (..), entryIdent, entryVar)
import Thena.Core.Level (Level (..), LevelVar (..), levelOfNat)
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
import Thena.Global.Env
  ( ConstructorDefinition (..)
  , GlobalEnv
  , InductiveDefinition (..)
  , definitions
  , inductiveConstructors
  , inductiveIndices
  , inductiveParameters
  , lookupInductive
  )
import Thena.Syntax.Concrete
  ( Raw (..)
  , RawBinder (..)
  , RawConstraint (..)
  , RawConstructor (..)
  , RawData (..)
  , RawLevel (..)
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
globalsOf = map fst . definitions

-- | Resolve a raw tree as a core term. Holes, guesses and constraints are
-- rejected here: they live only in a development (§3.1).
resolve :: GlobalEnv -> Context -> Int -> Raw -> Either ResolveError (Core, Int)
resolve env ctx = core env (globalsOf env) ctx [] []

-- | 'resolve', with level parameters in scope (MS3 phase 30).
--
-- Only the theorem path supplies any: a statement declared @:theorem f {ℓ} : …@
-- resolves @ℓ@ inside its own type. Every other caller has none, which is why
-- 'resolve' stays the entry point it always was rather than every site growing
-- an empty list.
resolveAt
  :: [(String, LevelVar)] -> GlobalEnv -> Context -> Int -> Raw
  -> Either ResolveError (Core, Int)
resolveAt ls env ctx = core env (globalsOf env) ctx [] ls

-- | Resolve a raw tree as a development, taking the LONGEST PREFIX (§2.7):
-- every leading binder becomes a chain link, so 'Trailing' ends up holding
-- something that is not a binder unless @⌜ ⌝@ says otherwise.
resolvePartial :: GlobalEnv -> Context -> Int -> Raw -> Either ResolveError (Partial, Int)
resolvePartial env ctx = partial env (globalsOf env) ctx [] []

-- --------------------------------------------------------------------------
-- Core terms
-- --------------------------------------------------------------------------

-- | @env@ answers "is @d@ a declared datatype, and what is its shape" for an
-- @elim@ (phase 7); @gs@ answers "is @s@ in scope as an ordinary name" for
-- everything else, and is not always @globalsOf env@ — see 'Globals'.
core
  :: GlobalEnv -> Globals -> Context -> Local -> [(String, LevelVar)] -> Int
  -> Raw -> Either ResolveError (Core, Int)
core env gs ctx local lvs n raw = case raw of
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

  RawUniverse k -> Right (Universe (levelOfNat k), n)

  -- @Type {ℓ}@ — a universe at a written level (phase 30).
  RawUniverseAt rl -> do
    l <- levelArg lvs rl
    Right (Universe l, n)

  -- @foo {ℓ 0}@ — a global at level arguments. **Refused on a local**: only a
  -- definition has level parameters, and a λ-bound name has none to give.
  RawAt s rls -> case lookup s local of
    Just _  -> Left (LevelArgumentsOnALocal s)
    Nothing -> case lookupEntry s ctx of
      Just _ -> Left (LevelArgumentsOnALocal s)
      Nothing
        | GlobalName s `elem` gs -> do
            args <- mapM (levelArg lvs) rls
            Right (Global (GlobalName s) args, n)
        | otherwise -> Left (NotInScope s)

  RawApp f a -> do
    (f', n1) <- core env gs ctx local lvs n f
    (a', n2) <- core env gs ctx local lvs n1 a
    Right (App f' a', n2)

  -- A non-dependent arrow is a 'Pi' whose variable does not occur.
  RawArrow s b -> do
    (s', n1) <- core env gs ctx local lvs n s
    (b', n2) <- core env gs ctx local lvs n1 b
    let (v, n3) = fresh n2
    Right (Pi (Ident "_") s' (close v b'), n3)

  RawLam bs b -> binders env gs Lam ctx local lvs n bs b
  RawPi bs b  -> binders env gs Pi ctx local lvs n bs b

  RawLet x val ty b -> do
    (val', n1) <- core env gs ctx local lvs n val
    (ty', n2)  <- core env gs ctx local lvs n1 ty
    let (v, n3) = fresh n2
    (b', n4)   <- core env gs ctx ((x, v) : local) lvs n3 b
    Right (Let (Ident x) val' ty' (close v b'), n4)

  -- Transparent here: the corners only say something in a development
  -- position, where they stop the spine. A no-op rather than an error, because
  -- rejecting them would make the printer's own output fail to re-read in a
  -- nested position.
  RawQuote t -> core env gs ctx local lvs n t

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
  RawElim d ps m ms is t -> do
    dn        <- datatypeNamed env gs ctx local d
    def       <- maybe (Left (NotADatatype d)) Right (lookupInductive dn env)
    (ps', n1) <- coreList env gs ctx local lvs n ps
    (m', n2)  <- core env gs ctx local lvs n1 m
    (ms', n3) <- coreList env gs ctx local lvs n2 ms
    (is', n4) <- coreList env gs ctx local lvs n3 is
    (t', n5)  <- core env gs ctx local lvs n4 t
    let wantP = length (inductiveParameters def)
        wantM = length (inductiveConstructors def)
        wantI = length (inductiveIndices def)
    if length ps' /= wantP
      then Left (WrongNumberOfEliminationParameters d wantP (length ps'))
      else if length ms' /= wantM
        then Left (WrongNumberOfMethods d wantM (length ms'))
        else if length is' /= wantI
          then Left (WrongNumberOfEliminationIndices d wantI (length is'))
          else Right (Eliminate dn [] ps' m' ms' is' t', n5)

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
  :: GlobalEnv -> Globals -> Context -> Local -> String
  -> Either ResolveError GlobalName
datatypeNamed env gs ctx local d = case core env gs ctx local [] 0 (RawName d) of
  Right (Global g _, _) -> Right g
  _                   -> Left (NotADatatype d)

-- | A run of terms in the same local scope, left to right, threading the
-- counter — what @elim@\'s three list-valued fields need (§2.6).
coreList
  :: GlobalEnv -> Globals -> Context -> Local -> [(String, LevelVar)] -> Int
  -> [Raw] -> Either ResolveError ([Core], Int)
coreList _ _ _ _ _ n [] = Right ([], n)
coreList env gs ctx local lvs n (r : rs) = do
  (t, n1)  <- core env gs ctx local lvs n r
  (ts, n2) <- coreList env gs ctx local lvs n1 rs
  Right (t : ts, n2)

-- | One binder group at a time, each nested inside the last.
binders
  :: GlobalEnv -> Globals
  -> (Ident -> Core -> Scope Core -> Core)
  -> Context -> Local -> [(String, LevelVar)] -> Int -> [RawBinder] -> Raw
  -> Either ResolveError (Core, Int)
binders env gs con ctx local lvs n bs b = case bs of
  [] -> core env gs ctx local lvs n b
  RawBinder x ty : rest -> do
    (ty', n1) <- core env gs ctx local lvs n ty
    let (v, n2) = fresh n1
    (b', n3) <- binders env gs con ctx ((x, v) : local) lvs n2 rest b
    Right (con (Ident x) ty' (close v b'), n3)

-- --------------------------------------------------------------------------
-- Developments
-- --------------------------------------------------------------------------

partial
  :: GlobalEnv -> Globals -> Context -> Local -> [(String, LevelVar)] -> Int
  -> Raw -> Either ResolveError (Partial, Int)
partial env gs ctx local lvs n raw = case raw of
  RawLam bs b -> assumes env gs ctx local lvs n bs b

  RawLet x val ty b -> do
    (val', n1) <- core env gs ctx local lvs n val
    (ty', n2)  <- core env gs ctx local lvs n1 ty
    let (v, n3) = fresh n2
    (b', n4)   <- partial env gs ctx ((x, v) : local) lvs n3 b
    Right (Under (Define v (Ident x) val' ty') b', n4)

  RawClaim x ty b -> do
    (ty', n1) <- core env gs ctx local lvs n ty
    let (v, n2) = fresh n1
    (b', n3)  <- partial env gs ctx ((x, v) : local) lvs n2 b
    Right (Under (Claim v (Ident x) ty') b', n3)

  -- The guess body does NOT see the hole it fills: Γ_(?x ≐ P : S . p) = Γ_P
  -- (§4.5). Resolved with 'local' as it was; only the continuation gains @x@.
  RawGuess x ty g b -> do
    (ty', n1) <- core env gs ctx local lvs n ty
    (g', n2)  <- partial env gs ctx local lvs n1 g
    let (v, n3) = fresh n2
    (b', n4)  <- partial env gs ctx ((x, v) : local) lvs n3 b
    Right (Under (Guess v (Ident x) g' ty') b', n4)

  RawPending k b -> do
    (k', n1) <- constraint env gs ctx local lvs n k
    (b', n2) <- partial env gs ctx local lvs n1 b
    Right (Pending k' b', n2)

  -- The corners stop the spine: what is inside is a term, not a chain.
  RawQuote t -> do
    (t', n1) <- core env gs ctx local lvs n t
    Right (Trailing t', n1)

  -- Everything else is the trailing term. This is the whole of longest prefix:
  -- the binder cases above consume as much as they can, and this catches the
  -- first thing that is not a binder.
  _ -> do
    (t', n1) <- core env gs ctx local lvs n raw
    Right (Trailing t', n1)

-- | Each binder group in a @λ@ becomes its own 'Assume' link.
assumes
  :: GlobalEnv -> Globals -> Context -> Local -> [(String, LevelVar)] -> Int
  -> [RawBinder] -> Raw -> Either ResolveError (Partial, Int)
assumes env gs ctx local lvs n bs b = case bs of
  [] -> partial env gs ctx local lvs n b
  RawBinder x ty : rest -> do
    (ty', n1) <- core env gs ctx local lvs n ty
    let (v, n2) = fresh n1
    (b', n3) <- assumes env gs ctx ((x, v) : local) lvs n2 rest b
    Right (Under (Assume v (Ident x) ty') b', n3)

-- | Ξ's binders scope over @s@, @t@ and @T@ and nothing else.
constraint
  :: GlobalEnv -> Globals -> Context -> Local -> [(String, LevelVar)] -> Int
  -> RawConstraint -> Either ResolveError (Constraint, Int)
constraint env gs ctx local lvs n (RawConstraint bs s t ty) = do
  (xi, local', n1) <- telescope env gs ctx local lvs n bs
  (s', n2)  <- core env gs ctx local' lvs n1 s
  (t', n3)  <- core env gs ctx local' lvs n2 t
  (ty', n4) <- core env gs ctx local' lvs n3 ty
  Right (Equate xi s' t' ty', n4)

-- --------------------------------------------------------------------------
-- Declarations (§3.7)
-- --------------------------------------------------------------------------

-- | Resolve a @data@ declaration.
--
-- A declaration is closed: it is read in the empty context, not in the
-- development's, because what enters the global environment must mean the same
-- thing in every later proof (§3.3.1). Only the parameters, and the datatype's
-- own name, are added to the scope it is read in.
--
-- **The indices are not in scope in the constructors.** Each constructor
-- supplies its own index expressions and the record keeps those; the type
-- former's index binders name positions, not values (§3.7).
resolveData
  :: GlobalEnv -> Int -> RawData
  -> Either ResolveError (InductiveDefinition, Int)
resolveData env n (RawData name lps ps ty cs) = do
  -- **The level parameters are minted first and are in scope in everything
  -- that follows** (phase 31b) — the parameter telescope, the indices, the
  -- declared universe, and every constructor. They are 'LRigid': a declared
  -- parameter is universally quantified and unification may not solve it.
  let (lvars, n0) = mintLevelVars n lps
      lscope      = zip lps lvars
  (params, afterParams, n1)  <- telescope env gs [] [] lscope n0 ps
  (indices, _, rest, n2)     <- prefix env gs afterParams lscope n1 ty
  level <- case rest of
    RawUniverse k    -> Right (levelOfNat k)
    RawUniverseAt rl -> levelArg lscope rl
    _                -> Left (NotAUniverse name)
  -- The datatype being declared joins 'Globals' here, and only here: a
  -- constructor may recursively mention it (@succ : Nat -> Nat@), and
  -- 'lookupInductive' would find nothing for it in @env@ mid-declaration.
  (cs', n3) <- constructors env (dn : gs) dn params (length indices) afterParams lscope n2 cs
  Right (InductiveDefinition dn lvars params indices level cs', n3)
  where
    gs = globalsOf env
    dn = GlobalName name

constructors
  :: GlobalEnv -> Globals -> GlobalName -> Context -> Int -> Local
  -> [(String, LevelVar)] -> Int -> [RawConstructor]
  -> Either ResolveError ([ConstructorDefinition], Int)
constructors _ _ _ _ _ _ _ n [] = Right ([], n)
constructors env gs dn params want local lvs n (RawConstructor cn ty : rest) = do
  (args, inside, tgt, n1) <- prefix env gs local lvs n ty
  (tgt', n2)              <- core env gs [] inside lvs n1 tgt
  ixs                     <- targetIndices dn params want cn tgt'
  (rest', n3)             <- constructors env gs dn params want local lvs n2 rest
  Right (ConstructorDefinition (GlobalName cn) args ixs : rest', n3)

-- | Split a constructor's target into the index expressions the record keeps.
--
-- The parameters are not kept, because they are fixed for the whole definition
-- and a constructor must pass them through unchanged (§3.7, thesis §4.1.2).
-- Checking that here is what lets "Thena.Global.Declare" rebuild the target
-- from the record and get the same term back.
targetIndices
  :: GlobalName -> Context -> Int -> String -> Core
  -> Either ResolveError [Core]
targetIndices dn params want cn t = case spine t of
  (Global g _, as)
    | g == dn ->
        if length as /= length params + want
          then Left (TargetArgumentCount cn (length params + want) (length as))
          else passed params (take (length params) as)
                 >> Right (drop (length params) as)
  _ -> Left (TargetIsNotTheDatatype cn)
  where
    passed [] _ = Right ()
    passed (p : more) (a : as)
      | a == Free (entryVar p) = passed more as
      | otherwise              = Left (ParameterNotPassedThrough cn (entryIdent p))
    passed (p : _) []          = Left (ParameterNotPassedThrough cn (entryIdent p))

-- --------------------------------------------------------------------------
-- Telescopes
-- --------------------------------------------------------------------------

-- | A binder group list, outermost first. Only 'Hypothesis' entries ever
-- appear (§3.3).
telescope
  :: GlobalEnv -> Globals -> Context -> Local -> [(String, LevelVar)] -> Int
  -> [RawBinder] -> Either ResolveError (Context, Local, Int)
telescope _ _ _ local _ n [] = Right ([], local, n)
telescope env gs ctx local lvs n (RawBinder x ty : rest) = do
  (ty', n1) <- core env gs ctx local lvs n ty
  let (v, n2) = fresh n1
  (xi, local', n3) <- telescope env gs ctx ((x, v) : local) lvs n2 rest
  Right (Hypothesis v (Ident x) ty' : xi, local', n3)

-- | Peel the binder prefix of a declared type, and hand back what is left.
--
-- Used at the two places a declaration writes a telescope: the type former's
-- own type, whose prefix is the indices and whose tail must be a universe, and
-- a constructor's type, whose prefix is its arguments and whose tail is its
-- target. @∀@ groups and bare arrows both contribute — @succ : Nat -> Nat@ has
-- one argument and it happens to be nameless.
prefix
  :: GlobalEnv -> Globals -> Local -> [(String, LevelVar)] -> Int -> Raw
  -> Either ResolveError (Context, Local, Raw, Int)
prefix env gs local lvs n raw = case raw of
  RawPi bs b -> do
    (tel, local1, n1)        <- telescope env gs [] local lvs n bs
    (tel', local2, rest, n2) <- prefix env gs local1 lvs n1 b
    Right (tel ++ tel', local2, rest, n2)

  -- An arrow's argument has no written name, and unlike the @Ident "_"@ that
  -- 'core' puts on a non-dependent 'Pi' this one is visible: the generated
  -- wrapper abstracts it, and @λ (_ : Nat) -> ‹succ _›@ is not something to
  -- hand a student (§3.7 — the point of generating into the environment is that
  -- it can be read). The printer freshens a repeat to @x1@.
  RawArrow s b -> do
    (s', n1) <- core env gs [] local lvs n s
    let (v, n2) = fresh n1
    (tel, local', rest, n3) <- prefix env gs local lvs n2 b
    Right (Hypothesis v (Ident "x") s' : tel, local', rest, n3)

  _ -> Right ([], local, raw, n)

-- --------------------------------------------------------------------------
-- Odds and ends
-- --------------------------------------------------------------------------

-- | An application spine, head first.
spine :: Core -> (Core, [Core])
spine = go []
  where
    go as (App f a) = go (a : as) f
    go as t         = (t, as)

-- | The innermost entry wins, so the fold keeps the last match: a 'Context' is
-- outermost first (§3.2).
lookupEntry :: String -> Context -> Maybe Var
lookupEntry s = foldl pick Nothing
  where
    pick acc e
      | entryIdent e == Ident s = Just (entryVar e)
      | otherwise               = acc

-- | A level as written, against the level parameters in scope (phase 30).
--
-- **A numeral and a name are the whole of it.** There is no surface spelling
-- for @suc@ or @⊔@ yet: @⊔@ would have to become reserved, which narrows what
-- an identifier may contain (§2.6, his decision), and nothing needs to write
-- one until inference can get stuck.
levelArg :: [(String, LevelVar)] -> RawLevel -> Either ResolveError Level
levelArg lvs rl = case rl of
  RawLevelNum k -> Right (levelOfNat k)
  RawLevelVar s -> case lookup s lvs of
    Just v  -> Right (LVar v)
    Nothing -> Left (LevelNotInScope s)

-- | One 'LRigid' per declared level parameter, threading the counter.
--
-- Same counter as everything else (MS2 closeout 4f), so a datatype's level
-- parameters can never collide with a theorem's or with a metavariable.
mintLevelVars :: Int -> [String] -> ([LevelVar], Int)
mintLevelVars n []       = ([], n)
mintLevelVars n (_ : xs) = let (vs, n') = mintLevelVars (n + 1) xs in (LRigid n : vs, n')
