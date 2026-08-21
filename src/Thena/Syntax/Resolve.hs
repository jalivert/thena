-- | Turning the named tree the parser produces into 'Core' (§2.5).
--
-- This is where a written name becomes a 'Bound' index, a 'Free' variable or a
-- scope error, and it is the only place that decision is made.
module Thena.Syntax.Resolve
  ( ResolveError (..)
  , resolve
  ) where

import Thena.Core.Context (Context, Entry (..))
import Thena.Core.Term
  ( Core (..)
  , Ident (..)
  , Level (..)
  , Var
  , close
  , fresh
  )
import Thena.Syntax.Concrete (Raw (..), RawBinder (..))

-- | Structured, per §12 invariant 2.
newtype ResolveError = NotInScope String
  deriving (Eq, Show)

-- | Resolve a raw tree against the working context, threading the session's
-- name counter.
--
-- There is no 'GlobalEnv' argument yet — that type arrives at phase 6, and the
-- parameter arrives with it. Until then a name that is neither locally bound nor
-- a context entry is a scope error, which is exactly what §9 asks of this phase.
resolve :: Context -> Int -> Raw -> Either ResolveError (Core, Int)
resolve ctx = go []
  where
    go :: [(String, Var)] -> Int -> Raw -> Either ResolveError (Core, Int)
    go local n raw = case raw of
      RawName s -> case lookup s local of
        Just v  -> Right (Free v, n)
        Nothing -> case lookupEntry s ctx of
          Just v  -> Right (Free v, n)
          Nothing -> Left (NotInScope s)

      RawUniverse k -> Right (Universe (Level k), n)

      RawApp f a -> do
        (f', n1) <- go local n f
        (a', n2) <- go local n1 a
        Right (App f' a', n2)

      -- A non-dependent arrow is a 'Pi' whose variable does not occur. The
      -- identifier is never seen: the printer restores the arrow by asking
      -- whether the variable occurs (§2.6).
      RawArrow s b -> do
        (s', n1) <- go local n s
        (b', n2) <- go local n1 b
        let (v, n3) = fresh n2
        Right (Pi (Ident "_") s' (close v b'), n3)

      RawLam bs b -> binders Lam local n bs b
      RawPi bs b  -> binders Pi local n bs b

      RawLet x val ty b -> do
        (val', n1) <- go local n val
        (ty', n2)  <- go local n1 ty
        let (v, n3) = fresh n2
        (b', n4)   <- go ((x, v) : local) n3 b
        Right (Let (Ident x) val' ty' (close v b'), n4)

    -- One binder group at a time, each nested inside the last. Consing onto
    -- 'local' is what makes an inner binder shadow an outer one of the same
    -- name — 'lookup' finds the most recent.
    binders con local n bs b = case bs of
      [] -> go local n b
      RawBinder x ty : rest -> do
        (ty', n1) <- go local n ty
        let (v, n2) = fresh n1
        (b', n3) <- binders con ((x, v) : local) n2 rest b
        Right (con (Ident x) ty' (close v b'), n3)

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
