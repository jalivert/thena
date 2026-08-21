-- | Turning the named tree the parser produces into 'Core' or into a
-- 'Partial' (§2.5, §2.7).
module Thena.Syntax.Resolve
  ( ResolveError (..)
  , DevForm (..)
  , resolve
  , resolvePartial
  ) where

import Thena.Core.Context (Context, Entry (..))
import Thena.Core.Term
  ( Core (..)
  , Ident (..)
  , Level (..)
  , Scope
  , Var
  , close
  , fresh
  )
import Thena.Development.Component (Component (..))
import Thena.Development.Partial (Constraint (..), Partial (..))
import Thena.Syntax.Concrete (Raw (..), RawBinder (..), RawConstraint (..))

-- | Structured, per §12 invariant 2.
data ResolveError
  = NotInScope String
  | NotACoreTerm DevForm   -- ^ a development-only form written where a term goes
  deriving (Eq, Show)

-- | Which development-only form was met in a core position. An enum rather
-- than a message, per §12 invariant 2 — "Thena.Repl" turns it into English.
data DevForm = AHole | AGuess | AConstraint
  deriving (Eq, Show)

-- | Names bound locally, innermost first.
type Local = [(String, Var)]

-- | Resolve a raw tree as a core term. Holes, guesses and constraints are
-- rejected here: they live only in a development (§3.1).
resolve :: Context -> Int -> Raw -> Either ResolveError (Core, Int)
resolve ctx = core ctx []

-- | Resolve a raw tree as a development, taking the LONGEST PREFIX (§2.7):
-- every leading binder becomes a chain link, so 'Trailing' ends up holding
-- something that is not a binder unless @⌜ ⌝@ says otherwise.
resolvePartial :: Context -> Int -> Raw -> Either ResolveError (Partial, Int)
resolvePartial ctx = partial ctx []

-- --------------------------------------------------------------------------
-- Core terms
-- --------------------------------------------------------------------------

core :: Context -> Local -> Int -> Raw -> Either ResolveError (Core, Int)
core ctx local n raw = case raw of
  RawName s -> case lookup s local of
    Just v  -> Right (Free v, n)
    Nothing -> case lookupEntry s ctx of
      Just v  -> Right (Free v, n)
      Nothing -> Left (NotInScope s)

  RawUniverse k -> Right (Universe (Level k), n)

  RawApp f a -> do
    (f', n1) <- core ctx local n f
    (a', n2) <- core ctx local n1 a
    Right (App f' a', n2)

  -- A non-dependent arrow is a 'Pi' whose variable does not occur.
  RawArrow s b -> do
    (s', n1) <- core ctx local n s
    (b', n2) <- core ctx local n1 b
    let (v, n3) = fresh n2
    Right (Pi (Ident "_") s' (close v b'), n3)

  RawLam bs b -> binders Lam ctx local n bs b
  RawPi bs b  -> binders Pi ctx local n bs b

  RawLet x val ty b -> do
    (val', n1) <- core ctx local n val
    (ty', n2)  <- core ctx local n1 ty
    let (v, n3) = fresh n2
    (b', n4)   <- core ctx ((x, v) : local) n3 b
    Right (Let (Ident x) val' ty' (close v b'), n4)

  -- Transparent here: the corners only say something in a development
  -- position, where they stop the spine. A no-op rather than an error, because
  -- rejecting them would make the printer's own output fail to re-read in a
  -- nested position.
  RawQuote t -> core ctx local n t

  RawClaim {}   -> Left (NotACoreTerm AHole)
  RawGuess {}   -> Left (NotACoreTerm AGuess)
  RawPending {} -> Left (NotACoreTerm AConstraint)

-- | One binder group at a time, each nested inside the last.
binders
  :: (Ident -> Core -> Scope Core -> Core)
  -> Context -> Local -> Int -> [RawBinder] -> Raw
  -> Either ResolveError (Core, Int)
binders con ctx local n bs b = case bs of
  [] -> core ctx local n b
  RawBinder x ty : rest -> do
    (ty', n1) <- core ctx local n ty
    let (v, n2) = fresh n1
    (b', n3) <- binders con ctx ((x, v) : local) n2 rest b
    Right (con (Ident x) ty' (close v b'), n3)

-- --------------------------------------------------------------------------
-- Developments
-- --------------------------------------------------------------------------

partial :: Context -> Local -> Int -> Raw -> Either ResolveError (Partial, Int)
partial ctx local n raw = case raw of
  RawLam bs b -> assumes ctx local n bs b

  RawLet x val ty b -> do
    (val', n1) <- core ctx local n val
    (ty', n2)  <- core ctx local n1 ty
    let (v, n3) = fresh n2
    (b', n4)   <- partial ctx ((x, v) : local) n3 b
    Right (Under (Define v (Ident x) val' ty') b', n4)

  RawClaim x ty b -> do
    (ty', n1) <- core ctx local n ty
    let (v, n2) = fresh n1
    (b', n3)  <- partial ctx ((x, v) : local) n2 b
    Right (Under (Claim v (Ident x) ty') b', n3)

  -- The guess body does NOT see the hole it fills: Γ_(?x ≐ P : S . p) = Γ_P
  -- (§4.5). Resolved with 'local' as it was; only the continuation gains @x@.
  RawGuess x ty g b -> do
    (ty', n1) <- core ctx local n ty
    (g', n2)  <- partial ctx local n1 g
    let (v, n3) = fresh n2
    (b', n4)  <- partial ctx ((x, v) : local) n3 b
    Right (Under (Guess v (Ident x) g' ty') b', n4)

  RawPending k b -> do
    (k', n1) <- constraint ctx local n k
    (b', n2) <- partial ctx local n1 b
    Right (Pending k' b', n2)

  -- The corners stop the spine: what is inside is a term, not a chain.
  RawQuote t -> do
    (t', n1) <- core ctx local n t
    Right (Trailing t', n1)

  -- Everything else is the trailing term. This is the whole of longest prefix:
  -- the binder cases above consume as much as they can, and this catches the
  -- first thing that is not a binder.
  _ -> do
    (t', n1) <- core ctx local n raw
    Right (Trailing t', n1)

-- | Each binder group in a @λ@ becomes its own 'Assume' link.
assumes
  :: Context -> Local -> Int -> [RawBinder] -> Raw
  -> Either ResolveError (Partial, Int)
assumes ctx local n bs b = case bs of
  [] -> partial ctx local n b
  RawBinder x ty : rest -> do
    (ty', n1) <- core ctx local n ty
    let (v, n2) = fresh n1
    (b', n3) <- assumes ctx ((x, v) : local) n2 rest b
    Right (Under (Assume v (Ident x) ty') b', n3)

-- | Ξ's binders scope over @s@, @t@ and @T@ and nothing else.
constraint
  :: Context -> Local -> Int -> RawConstraint
  -> Either ResolveError (Constraint, Int)
constraint ctx local n (RawConstraint bs s t ty) = do
  (xi, local', n1) <- telescope ctx local n bs
  (s', n2)  <- core ctx local' n1 s
  (t', n3)  <- core ctx local' n2 t
  (ty', n4) <- core ctx local' n3 ty
  Right (Equate xi s' t' ty', n4)

-- | Ξ, outermost first. Only 'Hypothesis' entries ever appear (§3.3).
telescope
  :: Context -> Local -> Int -> [RawBinder]
  -> Either ResolveError (Context, Local, Int)
telescope _ local n [] = Right ([], local, n)
telescope ctx local n (RawBinder x ty : rest) = do
  (ty', n1) <- core ctx local n ty
  let (v, n2) = fresh n1
  (xi, local', n3) <- telescope ctx ((x, v) : local) n2 rest
  Right (Hypothesis v (Ident x) ty' : xi, local', n3)

-- | The innermost entry wins, so the fold keeps the last match: a 'Context' is
-- outermost first (§3.2).
lookupEntry :: String -> Context -> Maybe Var
lookupEntry s = foldl pick Nothing
  where
    pick acc e
      | identOf e == Ident s = Just (varOf e)
      | otherwise            = acc

    identOf e = case e of
      Hypothesis _ i _   -> i
      Definition _ i _ _ -> i

    varOf e = case e of
      Hypothesis v _ _   -> v
      Definition v _ _ _ -> v
