-- | The working context — what a core judgment can see (§3.2).
--
-- Imports "Thena.Core.Term" and must never be imported by it.
module Thena.Core.Context
  ( Entry (..)
  , Context
  , entryVar
  , entryIdent
  , entryType
  , piOver
  , lamOver
  ) where

import Thena.Core.Term (Core (..), Ident, Scope, Var, close)

-- | An entry in a working context: a name with a type, or a name with a type
-- and a value.
--
-- **Provenance-free by design.** An entry may have come from a development
-- component read forgetfully, or from opening a core 'Thena.Core.Term.Scope',
-- and nothing downstream may ask which. That is what makes it honest: the
-- alternative carries hole-ness and guess bodies into the context, so a consumer
-- /can/ ask, and sooner or later one would (§3.2).
--
-- The type is always the last field, as in 'Thena.Development.Component' — the
-- shape reads like the notation.
--
-- 'Eq' is derived and so compares 'Ident's, unlike 'Eq' on
-- 'Thena.Core.Term.Core'. That is deliberate: a context is named (§3.5), and two
-- entries differing only in display name are two different entries.
data Entry
  = Hypothesis Var Ident      Core   -- ^ @x     : S@
  | Definition Var Ident Core Core   -- ^ @x = s : S@
  deriving (Eq, Show)

-- | Outermost first.
type Context = [Entry]

entryVar :: Entry -> Var
entryVar e = case e of
  Hypothesis v _ _   -> v
  Definition v _ _ _ -> v

entryIdent :: Entry -> Ident
entryIdent e = case e of
  Hypothesis _ i _   -> i
  Definition _ i _ _ -> i

entryType :: Entry -> Core
entryType e = case e of
  Hypothesis _ _ t   -> t
  Definition _ _ _ t -> t

-- | @∀ Γ -> T@: bind a whole context over a term.
--
-- A context is a telescope, and this is the type it stands for. Phase 6's
-- declarations are what want it — an inductive definition's parameters and a
-- constructor's arguments are both contexts, and both are printed and stored as
-- the Π-type they bind (§3.7). A 'Definition' entry becomes a @let@, which is
-- what it means; only 'Hypothesis' entries arise in practice.
piOver :: Context -> Core -> Core
piOver = bindOver Pi

-- | @λ Γ -> t@. The same fold with the other binder: it is what a generated
-- former wrapper abstracts (§3.7 item 2).
lamOver :: Context -> Core -> Core
lamOver = bindOver Lam

bindOver :: (Ident -> Core -> Scope Core -> Core) -> Context -> Core -> Core
bindOver con tel body = foldr bind body tel
  where
    bind (Hypothesis v i t)   b = con i t (close v b)
    bind (Definition v i s t) b = Let i s t (close v b)
