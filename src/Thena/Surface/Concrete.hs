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
  , SurfaceDecl (..)
  , SurfaceModule (..)
  , SurfaceData (..)
  , SurfaceConstructor (..)
  , PairingError (..)
  , paired
  , SurfaceArg (..)
  , SurfaceBinder (..)
  , Plicity (..)
  ) where

import Data.List.NonEmpty (NonEmpty)

-- | **The instruction language is shared, and it is term-free**, which is what
-- makes sharing it possible: a 'Thena.Syntax.Concrete.RawOperand' is an
-- identifier, a number or a string, and mentions neither 'Surface' nor
-- 'Thena.Syntax.Concrete.Raw'. So this import crosses no language boundary —
-- it is the machine's own syntax, which belongs to neither term language.
import Thena.Syntax.Concrete (RawInstr)

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

  | SurfaceDo [RawInstr]
    -- ^ @do { ‹instruction› ; … }@ (MS4 phase 45) — **a block of the
    -- instruction language, written down and never computed.** Its elaboration
    -- is to play it, which is why it holds the block as a field rather than
    -- anything to be evaluated: the same shape 'Thena.Ops.DefineData' has, and
    -- for the same reason.
    --
    -- **It holds @RawInstr@, not @Instr@**, because parsing precedes
    -- resolution here as it does everywhere: which word names an op is
    -- "Thena.Rules"' question, and a grammar that answered it would be a
    -- second place the op vocabulary is written.
    --
    -- His proposal, and it is what removes the need for a surface term meaning
    -- /no proof given, search for one/: the user writes @do { prove }@, and a
    -- search strategy is then a rule name rather than syntax.
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

-- | A proof module: a name and the declarations under it (MS4 phase 43).
--
-- **The header is real syntax**, not a textual pre-pass like the rule base's
-- @rule base ‹name› where@ — his call, 2026-09-02. So @module@ is a reserved
-- word in the shared lexer and identifiers narrow project-wide, exactly as they
-- did for @data@ at 42b.
--
-- **The name is recorded and not yet used for anything.** Nothing imports a
-- proof module until after MS4, and a module whose name disagreed with its path
-- would be a rule this phase has no reason to invent. What the header buys now
-- is that the file says what it is, which is how @:load@ tells a proof module
-- from a script without opening it further than the first line.
data SurfaceModule = SurfaceModule
  { surfaceModuleName  :: String
  , surfaceModuleDecls :: [SurfaceDecl]
  }
  deriving (Eq, Show)

-- | One line of a surface module (MS4 phase 42).
--
-- **Agda\/Haskell-style, so a declaration is two of these** — his choice at
-- phase 39. The signature and the equation are separate items and 'paired'
-- puts them together, which is what those languages do and why a signature
-- with no equation is a diagnosable mistake rather than an unparseable one.
data SurfaceDecl
  = SurfaceSignature String Surface   -- ^ @foo : T@
  | SurfaceEquation  String Surface   -- ^ @foo = e@
  | SurfaceDatatype  SurfaceData      -- ^ @data D … where { … }@ (phase 42b)
  | SurfaceBlock     [RawInstr]
    -- ^ a top-level @do@ block (MS4 phase 45) — **his, 2026-09-03**. At the top
    -- of a module a block is not an expression but an /item/: it plays where
    -- the others declare, so a module can define most of itself in the
    -- functional language and drop into the instruction language for the parts
    -- that want it.
    --
    -- **It needs no mechanism of its own.** A module is already one instruction
    -- program ('Thena.Driver.surfaceProgram'), so a top-level block is spliced
    -- into it — no frame, no op, and nothing that could tell it from
    -- instructions the elaborator emitted.
  deriving (Eq, Show)

-- | A datatype declaration, in the shape §3.7 requires disambiguated.
--
-- **The same split 'Thena.Syntax.Concrete.RawData' makes**: the parameters are
-- the binder groups left of the @:@ and the indices are the arrow prefix of the
-- type right of it. Keeping it syntactic is what lets the elaborated form be
-- taken apart again by /counting/ — 'Thena.Global.Declare.buildInductive'.
data SurfaceData = SurfaceData
  { surfaceDataName         :: String
  , surfaceDataParameters   :: [(String, Surface)]
  , surfaceDataType         :: Surface   -- ^ the part right of the @:@
  , surfaceDataConstructors :: [SurfaceConstructor]
  }
  deriving (Eq, Show)

data SurfaceConstructor = SurfaceConstructor String Surface
  deriving (Eq, Show)

-- | What went wrong pairing them.
data PairingError
  = SignatureWithNoEquation String
  | EquationWithNoSignature String
  | DatatypeInATheoremList
  | BlockInATheoremList
    -- ^ and neither is a top-level @do@ block (MS4 phase 45), for the same
    -- reason: 'paired' is about theorems.
    -- ^ 'paired' is about theorems; a caller that can also take a datatype
    -- splits the list first. Phase 43's loader does; phase 42b's @declare@
    -- keeps them apart at the command.
  deriving (Eq, Show)

-- | Pair each signature with the equation that follows it.
--
-- **Adjacent and in that order**, which is the rule Haskell and Agda both use;
-- nothing here searches, so a declaration cannot pick up an equation from the
-- far end of a module.
paired :: [SurfaceDecl] -> Either PairingError [(String, Surface, Surface)]
paired ds = case ds of
  [] -> Right []
  SurfaceSignature x ty : SurfaceEquation y body : rest
    | x == y -> ((x, ty, body) :) <$> paired rest
  SurfaceSignature x _ : _ -> Left (SignatureWithNoEquation x)
  SurfaceEquation  x _ : _ -> Left (EquationWithNoSignature x)
  SurfaceDatatype _    : _ -> Left DatatypeInATheoremList
  SurfaceBlock _       : _ -> Left BlockInATheoremList
