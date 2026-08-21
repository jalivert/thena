-- | Turning the named tree the parser produces into 'Core', into a 'Partial',
-- or into an 'InductiveDefinition' (§2.5, §2.7, §3.7).
module Thena.Syntax.Resolve
  ( ResolveError (..)
  , DevForm (..)
  , resolve
  , resolvePartial
  , resolveData
  ) where

import Thena.Core.Context (Context, Entry (..), entryIdent, entryVar)
import Thena.Core.Term
  ( Core (..)
  , GlobalName (..)
  , Ident (..)
  , Level (..)
  , Scope
  , Var
  , close
  , fresh
  )
import Thena.Development.Component (Component (..))
import Thena.Development.Partial (Constraint (..), Partial (..))
import Thena.Global.Env
  ( ConstructorDefinition (..)
  , GlobalEnv
  , InductiveDefinition (..)
  , definitions
  )
import Thena.Syntax.Concrete
  ( Raw (..)
  , RawBinder (..)
  , RawConstraint (..)
  , RawConstructor (..)
  , RawData (..)
  )

-- | Structured, per §12 invariant 2.
--
-- The last four are one shape of mistake — the declaration does not fit the
-- form — and they are here rather than in "Thena.Global.Declare" because this
-- is where "what you wrote does not fit" already lives. @Declare@ keeps the
-- judgements: positivity now, the universes at phase 8.
data ResolveError
  = NotInScope String
  | NotACoreTerm DevForm
    -- ^ a development-only form written where a term goes
  | NotAUniverse String
    -- ^ the datatype's declared type does not end in @Type_l@
  | TargetIsNotTheDatatype String
    -- ^ this constructor's result type is not the family being declared
  | TargetArgumentCount String Int Int
    -- ^ constructor, arguments its target should have, arguments it has
  | ParameterNotPassedThrough String Ident
    -- ^ a constructor's target changed a parameter; parameters are fixed (§3.7)
  deriving (Eq, Show)

-- | Which development-only form was met in a core position. An enum rather
-- than a message, per §12 invariant 2 — "Thena.Repl" turns it into English.
data DevForm = AHole | AGuess | AConstraint
  deriving (Eq, Show)

-- | Names bound locally, innermost first.
type Local = [(String, Var)]

-- | The global names a written name may resolve to.
--
-- The definitions of the environment — not the constants, and not the inductive
-- records. A 'Global' node names something with a body (§3.6), which is what
-- makes it the third form of δ; a constant with no body is reached from
-- 'Canonical' or 'Eliminate' instead, and neither is ever written.
--
-- Inside a @data@ declaration this list also carries the datatype being
-- declared, which is not in the environment yet and cannot be — its own
-- constructors mention it.
type Globals = [GlobalName]

globalsOf :: GlobalEnv -> Globals
globalsOf = map fst . definitions

-- | Resolve a raw tree as a core term. Holes, guesses and constraints are
-- rejected here: they live only in a development (§3.1).
resolve :: GlobalEnv -> Context -> Int -> Raw -> Either ResolveError (Core, Int)
resolve env ctx = core (globalsOf env) ctx []

-- | Resolve a raw tree as a development, taking the LONGEST PREFIX (§2.7):
-- every leading binder becomes a chain link, so 'Trailing' ends up holding
-- something that is not a binder unless @⌜ ⌝@ says otherwise.
resolvePartial :: GlobalEnv -> Context -> Int -> Raw -> Either ResolveError (Partial, Int)
resolvePartial env ctx = partial (globalsOf env) ctx []

-- --------------------------------------------------------------------------
-- Core terms
-- --------------------------------------------------------------------------

core :: Globals -> Context -> Local -> Int -> Raw -> Either ResolveError (Core, Int)
core gs ctx local n raw = case raw of
  -- Local, then the ambient context, then the globals. A binder shadows a
  -- global of the same name, which is what one namespace (§3.6) requires: the
  -- names collide and the innermost wins.
  RawName s -> case lookup s local of
    Just v  -> Right (Free v, n)
    Nothing -> case lookupEntry s ctx of
      Just v  -> Right (Free v, n)
      Nothing
        | GlobalName s `elem` gs -> Right (Global (GlobalName s), n)
        | otherwise              -> Left (NotInScope s)

  RawUniverse k -> Right (Universe (Level k), n)

  RawApp f a -> do
    (f', n1) <- core gs ctx local n f
    (a', n2) <- core gs ctx local n1 a
    Right (App f' a', n2)

  -- A non-dependent arrow is a 'Pi' whose variable does not occur.
  RawArrow s b -> do
    (s', n1) <- core gs ctx local n s
    (b', n2) <- core gs ctx local n1 b
    let (v, n3) = fresh n2
    Right (Pi (Ident "_") s' (close v b'), n3)

  RawLam bs b -> binders gs Lam ctx local n bs b
  RawPi bs b  -> binders gs Pi ctx local n bs b

  RawLet x val ty b -> do
    (val', n1) <- core gs ctx local n val
    (ty', n2)  <- core gs ctx local n1 ty
    let (v, n3) = fresh n2
    (b', n4)   <- core gs ctx ((x, v) : local) n3 b
    Right (Let (Ident x) val' ty' (close v b'), n4)

  -- Transparent here: the corners only say something in a development
  -- position, where they stop the spine. A no-op rather than an error, because
  -- rejecting them would make the printer's own output fail to re-read in a
  -- nested position.
  RawQuote t -> core gs ctx local n t

  RawClaim {}   -> Left (NotACoreTerm AHole)
  RawGuess {}   -> Left (NotACoreTerm AGuess)
  RawPending {} -> Left (NotACoreTerm AConstraint)

-- | One binder group at a time, each nested inside the last.
binders
  :: Globals
  -> (Ident -> Core -> Scope Core -> Core)
  -> Context -> Local -> Int -> [RawBinder] -> Raw
  -> Either ResolveError (Core, Int)
binders gs con ctx local n bs b = case bs of
  [] -> core gs ctx local n b
  RawBinder x ty : rest -> do
    (ty', n1) <- core gs ctx local n ty
    let (v, n2) = fresh n1
    (b', n3) <- binders gs con ctx ((x, v) : local) n2 rest b
    Right (con (Ident x) ty' (close v b'), n3)

-- --------------------------------------------------------------------------
-- Developments
-- --------------------------------------------------------------------------

partial :: Globals -> Context -> Local -> Int -> Raw -> Either ResolveError (Partial, Int)
partial gs ctx local n raw = case raw of
  RawLam bs b -> assumes gs ctx local n bs b

  RawLet x val ty b -> do
    (val', n1) <- core gs ctx local n val
    (ty', n2)  <- core gs ctx local n1 ty
    let (v, n3) = fresh n2
    (b', n4)   <- partial gs ctx ((x, v) : local) n3 b
    Right (Under (Define v (Ident x) val' ty') b', n4)

  RawClaim x ty b -> do
    (ty', n1) <- core gs ctx local n ty
    let (v, n2) = fresh n1
    (b', n3)  <- partial gs ctx ((x, v) : local) n2 b
    Right (Under (Claim v (Ident x) ty') b', n3)

  -- The guess body does NOT see the hole it fills: Γ_(?x ≐ P : S . p) = Γ_P
  -- (§4.5). Resolved with 'local' as it was; only the continuation gains @x@.
  RawGuess x ty g b -> do
    (ty', n1) <- core gs ctx local n ty
    (g', n2)  <- partial gs ctx local n1 g
    let (v, n3) = fresh n2
    (b', n4)  <- partial gs ctx ((x, v) : local) n3 b
    Right (Under (Guess v (Ident x) g' ty') b', n4)

  RawPending k b -> do
    (k', n1) <- constraint gs ctx local n k
    (b', n2) <- partial gs ctx local n1 b
    Right (Pending k' b', n2)

  -- The corners stop the spine: what is inside is a term, not a chain.
  RawQuote t -> do
    (t', n1) <- core gs ctx local n t
    Right (Trailing t', n1)

  -- Everything else is the trailing term. This is the whole of longest prefix:
  -- the binder cases above consume as much as they can, and this catches the
  -- first thing that is not a binder.
  _ -> do
    (t', n1) <- core gs ctx local n raw
    Right (Trailing t', n1)

-- | Each binder group in a @λ@ becomes its own 'Assume' link.
assumes
  :: Globals -> Context -> Local -> Int -> [RawBinder] -> Raw
  -> Either ResolveError (Partial, Int)
assumes gs ctx local n bs b = case bs of
  [] -> partial gs ctx local n b
  RawBinder x ty : rest -> do
    (ty', n1) <- core gs ctx local n ty
    let (v, n2) = fresh n1
    (b', n3) <- assumes gs ctx ((x, v) : local) n2 rest b
    Right (Under (Assume v (Ident x) ty') b', n3)

-- | Ξ's binders scope over @s@, @t@ and @T@ and nothing else.
constraint
  :: Globals -> Context -> Local -> Int -> RawConstraint
  -> Either ResolveError (Constraint, Int)
constraint gs ctx local n (RawConstraint bs s t ty) = do
  (xi, local', n1) <- telescope gs ctx local n bs
  (s', n2)  <- core gs ctx local' n1 s
  (t', n3)  <- core gs ctx local' n2 t
  (ty', n4) <- core gs ctx local' n3 ty
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
resolveData env n (RawData name ps ty cs) = do
  (params, afterParams, n1)  <- telescope gs [] [] n ps
  (indices, _, rest, n2)     <- prefix gs afterParams n1 ty
  level <- case rest of
    RawUniverse k -> Right (Level k)
    _             -> Left (NotAUniverse name)
  (cs', n3) <- constructors (dn : gs) dn params (length indices) afterParams n2 cs
  Right (InductiveDefinition dn params indices level cs', n3)
  where
    gs = globalsOf env
    dn = GlobalName name

constructors
  :: Globals -> GlobalName -> Context -> Int -> Local -> Int -> [RawConstructor]
  -> Either ResolveError ([ConstructorDefinition], Int)
constructors _ _ _ _ _ n [] = Right ([], n)
constructors gs dn params want local n (RawConstructor cn ty : rest) = do
  (args, inside, tgt, n1) <- prefix gs local n ty
  (tgt', n2)              <- core gs [] inside n1 tgt
  ixs                     <- targetIndices dn params want cn tgt'
  (rest', n3)             <- constructors gs dn params want local n2 rest
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
  (Global g, as)
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
  :: Globals -> Context -> Local -> Int -> [RawBinder]
  -> Either ResolveError (Context, Local, Int)
telescope _ _ local n [] = Right ([], local, n)
telescope gs ctx local n (RawBinder x ty : rest) = do
  (ty', n1) <- core gs ctx local n ty
  let (v, n2) = fresh n1
  (xi, local', n3) <- telescope gs ctx ((x, v) : local) n2 rest
  Right (Hypothesis v (Ident x) ty' : xi, local', n3)

-- | Peel the binder prefix of a declared type, and hand back what is left.
--
-- Used at the two places a declaration writes a telescope: the type former's
-- own type, whose prefix is the indices and whose tail must be a universe, and
-- a constructor's type, whose prefix is its arguments and whose tail is its
-- target. @∀@ groups and bare arrows both contribute — @succ : Nat -> Nat@ has
-- one argument and it happens to be nameless.
prefix
  :: Globals -> Local -> Int -> Raw
  -> Either ResolveError (Context, Local, Raw, Int)
prefix gs local n raw = case raw of
  RawPi bs b -> do
    (tel, local1, n1)        <- telescope gs [] local n bs
    (tel', local2, rest, n2) <- prefix gs local1 n1 b
    Right (tel ++ tel', local2, rest, n2)

  -- An arrow's argument has no written name, and unlike the @Ident "_"@ that
  -- 'core' puts on a non-dependent 'Pi' this one is visible: the generated
  -- wrapper abstracts it, and @λ (_ : Nat) -> ‹succ _›@ is not something to
  -- hand a student (§3.7 — the point of generating into the environment is that
  -- it can be read). The printer freshens a repeat to @x1@.
  RawArrow s b -> do
    (s', n1) <- core gs [] local n s
    let (v, n2) = fresh n1
    (tel, local', rest, n3) <- prefix gs local n2 b
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
