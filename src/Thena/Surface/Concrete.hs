-- | The surface language's own tree (MS4).
--
-- **This is not "Thena.Syntax.Concrete".** That module's 'Thena.Syntax.Concrete.Raw'
-- is a concrete syntax for the /development/ language — components, holes,
-- guesses, @let@ — and turning one into a 'Thena.Core.Term.Core' is name
-- resolution. This is the language a user writes a program in, and turning one
-- of these into a @Core@ is **elaboration**, which is a different thing
-- entirely and is the whole of what MS4 is about.
--
-- The two exist side by side and neither becomes the other. The user's
-- correction, three times over: /"Raw is not Surface. Absolutely not the same
-- thing. Can not be further from the same thing."/
--
-- Constructors are prefixed @Surface@ for "Thena.Syntax.Concrete"'s own reason:
-- a module importing this, that one and "Thena.Core.Term" together needs no
-- qualified import, and "a surface lam", "a raw lam" and "a core lam" are three
-- different things that have to be distinguishable said out loud.
module Thena.Surface.Concrete
  ( Surface (..)
  , SurfaceArg (..)
  , SurfaceBinder (..)
  , Plicity (..)
  ) where

import Data.List.NonEmpty (NonEmpty)

-- | Whether the elaborator supplies an argument or the user writes it.
--
-- **Icity lives here and never in "Thena.Core.Term"** — the user's decision,
-- 2026-09-01: /"I am convinced that the DC does not need implicits. I think
-- implicit arguments and placeholders and implicit level arguments are all only
-- part of the surface syntax."/ That is Brady's arrangement too: TT's @∀@ has
-- no flag, and the system state records which positions of which name are
-- implicit.
--
-- **Parsed and inert in phase 39.** Nothing reads it until phase 44.
data Plicity = Explicit | Implicit
  deriving (Eq, Show)

-- | A written surface term.
data Surface
  = SurfaceName String
    -- ^ what a name denotes is elaboration's answer, not the tree's
  | SurfaceUniverse Int          -- ^ @Type₀@
  | SurfaceUniverseOpen          -- ^ @Type@, whose level is inferred

  | SurfacePlaceholder
    -- ^ @_@ — /"those elaborate just by not elaborating"/ (the user,
    -- 2026-09-01). Unification is expected to find it, and if it does not, the
    -- hole is simply still there. Brady's @UNFOCUS@ exists because his focus
    -- /is/ the head of a hole queue; ours is a cursor, so there is no head to
    -- clear and nothing to build.
  | SurfaceHole String
    -- ^ @?foo@ — a **named placeholder**, which becomes a real hole. What
    -- happens at one is expressed in the rules and not decided by the system:
    -- a clause may run automatically, ask the user, offer a choice, or hand
    -- control over.

  | SurfaceApp Surface (NonEmpty SurfaceArg)
    -- ^ **a spine, and there is exactly one application constructor.** The
    -- head is any 'Surface' and the argument list is never empty — the user,
    -- 2026-09-01: /"I don't think @App@ should be able to have an empty
    -- application list. That doesn't make sense."/
    --
    -- Three reasons it is a spine: juxtaposition is n-ary in the grammar, so a
    -- binary tree throws that away for every consumer to rebuild; the printer
    -- and the zipper both want it (@into-arg 2@ is a move on a spine and
    -- /left, left, right/ on a chain); and phase 44's @EXPAND@ needs the whole
    -- argument list at once to know where the implicit positions fall.
    --
    -- **Two constructors were rejected**: they would make @f a b@ and
    -- @(f a) b@ two representable forms of one term. The /two clauses/ live in
    -- the elaborator — head-is-a-name, and anything else — which is Brady's own
    -- split.
    --
    -- 'Thena.Core.Term.Core' stays binary. Elaboration flattens on the way in
    -- and nests on the way out.

  | SurfaceLam (NonEmpty SurfaceBinder) Surface
    -- ^ @\\ x (y : A) -> b@ — **a lambda's binder need not be annotated**, and
    -- that is the main thing the surface has that the development calculus does
    -- not. @let@, @∀@ and a top-level signature all still carry their types.
  | SurfacePi (NonEmpty SurfaceBinder) Surface   -- ^ @∀ (x : A) -> B@
  | SurfaceArrow Surface Surface                 -- ^ @A -> B@

  | SurfaceLet String (Maybe Surface) Surface Surface
    -- ^ @let x [: T] = s in t@. The annotation is optional here where
    -- 'Thena.Syntax.Concrete.RawLet' requires one, because in the development
    -- calculus there is nothing to infer it with.
  | SurfaceAnnot Surface Surface                 -- ^ @e : T@

  | SurfaceElim String [Surface] Surface [Surface] [Surface] Surface
    -- ^ @elim d (params) motive (methods) (indices) target@ — the same
    -- positional shape 'Thena.Syntax.Concrete.RawElim' has, because there is no
    -- pattern matching in the surface language yet and this is how a proof by
    -- induction is written. The user, 2026-09-01: /"yes, for now we use
    -- eliminators in the surface too."/
    --
    -- **No level arguments.** A use writes them in the development calculus and
    -- phase 44 decides how, or whether, they are written here.
  deriving (Eq, Show)

-- | One argument of a spine, and whether it was written in braces.
data SurfaceArg = SurfaceArg Plicity Surface
  deriving (Eq, Show)

-- | One bound name, its plicity, and its type if it was written.
--
-- A binder group binds **one** name. @\\ (x y : A) -> b@ parses to two of
-- these sharing a type, which is where the grouping stops mattering: nothing
-- downstream needs to know two names were written inside one pair of
-- parentheses, and a group would be a second way to say the same thing.
data SurfaceBinder = SurfaceBinder Plicity String (Maybe Surface)
  deriving (Eq, Show)
