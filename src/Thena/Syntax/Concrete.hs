-- | The named, unresolved tree the parser produces (§2.5).
--
-- It is not 'Thena.Core.Term.Core' and cannot be: which of @Bound@, @Free@ and
-- @Global@ a written name denotes depends on the context it is written in, and
-- that is "Thena.Syntax.Resolve"'s job.
--
-- The constructors are prefixed @Raw@ so that a module importing this and
-- "Thena.Core.Term" together — 'Thena.Syntax.Resolve' does — needs no qualified
-- import, and so that "a raw lam" and "a core lam" are distinguishable said out
-- loud.
module Thena.Syntax.Concrete
  ( Raw (..)
  , RawBinder (..)
  ) where

data Raw
  = RawName String
  | RawUniverse Int
  | RawLam [RawBinder] Raw       -- ^ @λ (x : S) (y : T) -> b@
  | RawPi [RawBinder] Raw        -- ^ @∀ (x : S) (y : T) -> B@
  | RawArrow Raw Raw             -- ^ @S -> B@, the non-dependent case
  | RawApp Raw Raw
  | RawLet String Raw Raw Raw    -- ^ @let x = s : S in t@
  deriving (Eq, Show)

data RawBinder = RawBinder String Raw
  deriving (Eq, Show)
