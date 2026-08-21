-- | The working context — what a core judgment can see (§3.2).
--
-- Imports "Thena.Core.Term" and must never be imported by it.
module Thena.Core.Context
  ( Entry (..)
  , Context
  ) where

import Thena.Core.Term (Core, Ident, Var)

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
