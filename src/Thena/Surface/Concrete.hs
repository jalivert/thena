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
  , ObjectPiece (..)
  , SurfaceDecl (..)
  , SurfaceOpenSpec (..)
  , SurfaceModule (..)
  , SurfaceData (..)
  , SurfaceConstructor (..)
  , PairingError (..)
  , SurfaceArg (..)
  , SurfaceBinder (..)
  , SurfacePattern (..)
  , SurfaceArm (..)
  , Analysis (..)
  , Plicity (..)
  , blocksIn
  , surfaceName
  ) where

import Data.List.NonEmpty (NonEmpty, toList)

import Thena.Core.Term (GlobalName (..), Literal (..))

-- | **`instral` is shared, and it is term-free**, which is what makes sharing it
-- possible: a 'Thena.Instral.Concrete.RawOperand' is an identifier, a number or
-- a string, and mentions neither 'Surface' nor 'Thena.Syntax.Concrete.Raw'. So
-- this import crosses no language boundary — it is the machinery's own syntax,
-- and a @do@ block in a surface program is `instral` written in place
-- (@discussion\/the-five-languages.md@ §0b, table F).
import Thena.Instral.Concrete (RawInstr (..))
import Thena.Syntax.Lexer (BlockKind)
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
  = SurfaceName [String] String
    -- ^ what a name denotes is elaboration's answer, not the tree's
  | SurfaceUniverse Int          -- ^ @Type₀@
  | SurfaceLiteral Literal
    -- ^ @"ab"@, @'c'@, @3@ (MS6 phase 97c). A leaf, and the only surface node
    -- whose elaboration is settled by the node alone: its 'Thena.Core.Term.Core'
    -- is itself and its type is fixed, so the clause is @fill@ then @solve@ like
    -- a written universe's.
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

  | SurfaceObject String (Maybe String) [ObjectPiece]
    -- ^ @LC\`( \955 x : \953 . x )\`@ — **a tagged term literal** (MS6 phase
    -- 104, @ms6\/SPEC.md@ §8): the language, the production to start at if one
    -- was written, and the region's text split at its splices.
    --
    -- **It denotes an ordinary value of an ordinary datatype.** Its
    -- elaboration parses the text with that language's installed grammar and
    -- elaborates the constructor application the reading denotes — so
    -- @LC\`( \955 x : \953 . x )\`@ /is/ @abs "x" base (var "x")@, with no branded
    -- type and no coercion.
    --
    -- **The text cannot be parsed when it is read**: a module is parsed whole
    -- before its own @language@ block is installed, so what survives to here is
    -- the region, and the grammar is asked for at elaboration.
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
    -- **This is not the same question as 'SurfacePi'\'s binder group**, which
    -- /does/ make one term representable two ways and was accepted anyway
    -- (2026-09-09). The difference is elaboration, not representability: both
    -- @∀@ spellings elaborate identically, because that clause peels one binder
    -- and recurses, while both application spellings would not — this one needs
    -- the head and the whole argument list at once.
    --
    -- The fallback, if a flat spine ever stops being something every producer
    -- guarantees, is written up as @application-representation.md@ in the
    -- project's design notes. Do not re-derive it.
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
    -- anything to be evaluated: the same shape 'Thena.Instral.Ops.DefineData' has, and
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
  | SurfaceElim [String] String [Surface] Surface [Surface] [Surface] Surface
    -- ^ @elim d (params) motive (methods) (indices) target@ — the same
    -- positional shape 'Thena.Syntax.Concrete.RawElim' has, because there is no
    -- pattern matching in the surface language yet and this is how a proof by
    -- induction is written. The user, 2026-09-01: /"yes, for now we use
    -- eliminators in the surface too."/
    --
    -- **No level arguments.** A use writes them in the development calculus and
    -- phase 44 decides how, or whether, they are written here.
  | SurfaceSplit Analysis Surface [SurfaceArm]
    -- ^ @induction t of { p -> e ; … }@ and @case t of { p -> e ; … }@ (MS9
    -- phase 179) — __the target, and one arm per written pattern__.
    --
    -- __One node for both words, and the 'Analysis' says which was written.__
    -- They differ in one thing only: whether an arm is handed the induction
    -- hypotheses of the constructor it matched. Everything else — the target,
    -- the patterns, how an arm is printed, where the zipper may go — is the
    -- same, so two constructors would be two identical cases in every consumer
    -- that is not elaboration. **And @by ‹eliminator›@ is a third value of that
    -- field** rather than a third node, which is what settles it: the field is
    -- /which scheme analyses the target/, and the node is the analysis.
    --
    -- __It is self-delimiting, so it is an atom__ — @of@ opens a block, which
    -- the offside rule closes, exactly as @do@ and @where@ already do. So it
    -- stands where a name stands and needs no parentheses to be an argument.
    --
    -- __No arms is legal and useful__: @case t of { }@ is the whole of a case
    -- analysis on @Empty@. The same reason 'SurfaceData' admits a datatype with
    -- no constructors.
  | SurfaceTrusted Surface Surface
    -- ^ @trusted T e@ (MS8 phase 150) — **two operands, where
    -- 'Thena.Core.Term.Trusted' has three.** The third is the type @e@ was
    -- actually checked at, and **the user neither knows nor writes it**: it is
    -- derived, so elaboration claims a hole for it and the body's own
    -- elaboration solves it. His ruling, 2026-10-05, and the house pattern — a
    -- surface lambda's annotation is optional where @Core@'s 'Lam' always
    -- carries its domain.
    --
    -- **@trusted _ e@ needs nothing special.** The type position takes an
    -- ordinary 'SurfacePlaceholder', and elaboration solves it from the goal or
    -- leaves the hole standing, exactly as everywhere else — **treating that
    -- position as special would be the special case**, and he settled it by not
    -- treating it as a question.
  deriving (Eq, Show)

-- | A piece of a tagged term literal (MS6 phase 104).
--
-- **A splice holds a whole 'Surface' term**, not a name: §7.6 says a splice
-- supplies the slot's value and its type is the slot's, so what stands there is
-- an ordinary term elaborated at the slot\'s type. Nothing about the slot is
-- recorded here — which slot it is is the parser\'s answer, from where the
-- splice fell in the text.
data ObjectPiece
  = ObjectText String     -- ^ text, with its escapes already undone
  | ObjectSplice Surface  -- ^ @${ e }@
  deriving (Eq, Show)

-- | One argument of a spine, and whether it was written in braces.
data SurfaceArg = SurfaceArg Plicity Surface
  deriving (Eq, Show)

-- | Which scheme a 'SurfaceSplit' analyses its target with (MS9 phase 179).
--
-- __It is the word the user wrote and nothing more.__ What each one means is
-- elaboration's: @induction@ reaches for the generated eliminator, whose methods
-- carry an inductive hypothesis per recursive argument, and @case@ reaches for
-- the generated @caseD@, whose methods carry none.
--
-- __@by ‹eliminator›@ belongs here when it arrives__, as a third case carrying
-- the term that is to do the eliminating — a non-default induction principle,
-- which is what POPLMark 1A's nested induction needs and cannot say today. That
-- it fits as a case of this type rather than as a node of its own is why
-- 'SurfaceSplit' is one constructor.
data Analysis
  = ByInduction   -- ^ @induction t of …@
  | ByCases       -- ^ @case t of …@
  deriving (Eq, Show)

-- | One arm of a 'SurfaceSplit': the pattern, and what to do when it matches —
-- or __nothing at all__, which is how a case that cannot arise is written.
--
-- __@->@ and not @=@ — his ruling, 2026-10-18__: /"obviously @->@ for case and
-- induction syntax"/. @=@ stays for a clause, which is a declaration and not an
-- arm.
--
-- __AN EMPTY BODY IS THE VANISHED CASE — his ruling, 2026-10-20__, and it is why
-- there is no @impossible@ keyword. Splitting a @Vec A (succ n)@ leaves no @vnil@
-- case, @succ n = zero@ being a conflict, so there is no method and nothing to
-- prove: the user writes @vnil ->@ and stops. The whole split may be written with
-- no arms at all — @induction d of { }@ — and an empty arm is that same notion for
-- one case rather than for all of them, which is why no word was reserved for it.
-- @DECISIONS.md@ carries the decision and the reason.
data SurfaceArm = SurfaceArm SurfacePattern (Maybe Surface)
  deriving (Eq, Show)

-- | A written pattern (MS9 phase 179).
--
-- __A bare name does not say whether it is a variable or a nullary
-- constructor, and the tree must not pretend otherwise.__ @nil@ and @n@ are the
-- same shape written down; which one is which is a question about the globals,
-- so elaboration answers it with @constructor-datatype@ and the tree carries
-- the name. **This is the opposite of 'Thena.Instral.Pattern'**, whose decision
-- 1 is that a bare identifier /is/ a variable and a named constructor cannot be
-- matched — that is a pattern over @instral@'s own values, and it is not this.
--
-- __Nested patterns are parenthesised__, so an argument of a pattern is itself
-- one and @cons n a (cons m b nil)@ is three of these deep.
--
-- __An inaccessible pattern carries a term__ (MS9 phase 228), which is what
-- makes it the one pattern with something to elaborate. __What is deliberately
-- not here yet__ is a literal pattern; it is additive, a case of this type, and
-- not foreclosed.
data SurfacePattern
  = PatternName String [SurfacePattern]
    -- ^ @c p₁ … pₙ@, and with no arguments a bare name
  | PatternWildcard
    -- ^ @_@ — a variable the user did not care to name. **Not
    -- 'SurfacePlaceholder'**, which is a term that elaborates by not
    -- elaborating; a pattern binds, and there is nothing here to solve.
  | PatternDot Surface
    -- ^ @.e@ — an __inaccessible pattern__ (MS9 phase 228, on his ruling of
    -- 2026-10-19). It binds nothing and __asserts__: this position is
    -- determined, and by this term.
    --
    -- **It is optional and may never be made mandatory**, which is the whole of
    -- the ruling — naming a forced position binds the name as a definition and
    -- goes on working. Thena has no left-hand side to keep linear, so the
    -- constraint that makes Agda demand the dot does not reach here; the dot is
    -- kept because it __says more than a name can__.
    --
    -- **The term is a 'Surface' and not a 'SurfacePattern'**: @.(succ n)@ is an
    -- ordinary term that elaborates in the arm's own context, and an
    -- inaccessible position binds nothing, so there is nothing in it to
    -- destructure and no sub-pattern to carry.
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
-- **The name is qualified, and it is checked against the path when the file is
-- reached by name** — his ruling of 2026-11-05, @~r58qh@. So the shape is
-- 'SurfaceImport'\'s: the steps are the directories and the last is the file, and
-- @module Stlc.Terms where@ is legal where it was one word before (MS11 phase
-- 278). The check is only on the way in: a file @:load@ed by path, or typed at
-- the prompt, is never asked to agree with anything.
data SurfaceModule = SurfaceModule
  { surfaceModuleSteps :: [String]
  , surfaceModuleWord  :: String
  , surfaceModuleExporting :: Maybe [([String], String)]
    -- ^ @exporting ( … )@ on the header, as written (MS11 phase 285, @~jmw4k@).
    --
    -- **'Nothing' and @Just []@ are different modules.** No clause at all is a
    -- file that states no interface and exports everything it declares, which
    -- is every file written before this phase; @exporting ( )@ is a file that
    -- deliberately exports nothing.
  , surfaceModuleDecls :: [SurfaceDecl]
  }
  deriving (Eq, Show)

-- | One line of a surface module (MS4 phase 42).
--
-- **Agda\/Haskell-style, so a declaration is two of these** — his choice at
-- phase 39. The signature and the equation are separate items and 'paired'
-- puts them together, which is what those languages do and why a signature
-- with no equation is a diagnosable mistake rather than an unparseable one.
-- **What a declaration names may be written with a path** (MS10 phase 243):
-- the steps, then the base word, exactly as 'SurfaceName' carries a written
-- name. @Ty.subst-X : …@ declares into @Ty@'s namespace, and a name with no
-- steps is every declaration anything wrote before MS10. **It is the written
-- pieces and not a resolved 'Thena.Core.Term.GlobalName'**, because a
-- declaration inside an enclosing namespace will be relative to it.
-- | What an @open@ said about which of a namespace's names it brings in (MS10
-- phase 254).
--
-- **Only one of these at a time**, which is his ruling's shape: the forms are
-- @open X@, @open X ( a b )@, @open X hiding ( … )@ and
-- @open X renaming ( e -> c )@, and nothing combines two. A combination would
-- have to say which applied first, and nothing wants it yet.
data SurfaceOpenSpec
  = OpenWhole                      -- ^ @open X@, and @open X Y Z@
  | OpenOnly [String]              -- ^ @open X ( a b )@
  | OpenHiding [String]            -- ^ @open X hiding ( a b )@
  | OpenRenaming [(String, String)]
    -- ^ @open X renaming ( e -> c )@ — @(original, as written)@
    --
    -- **@-\>@ and not @→@**, which is a legal identifier character here: making
    -- the glyph a token would narrow what a name may contain, and that is a
    -- decision about identifiers rather than about @open@.
  deriving (Eq, Show)

data SurfaceDecl
  = SurfaceSignature [String] String Surface   -- ^ @foo : T@, @Ns.foo : T@
  | SurfaceEquation  [String] String Surface   -- ^ @foo = e@, @Ns.foo = e@
  | SurfaceDatatype  SurfaceData      -- ^ @data D … where { … }@ (phase 42b)
  | SurfaceOpen      [([String], String)] SurfaceOpenSpec
    -- ^ @open ‹namespace›@ — **bring namespaces into view** (MS10 phase 247,
    -- all five forms at 254).
    --
    -- The steps and the last word of each namespace's own path, so @open A.B@
    -- is @[(["A"], "B")]@ and the namespace is @A.B@. **A namespace is a prefix
    -- and not a thing that is declared**, so there is nothing here but the
    -- path: what it contains is whatever keys the environment has under it.
    --
    -- **Several paths, because @open X Y Z@ is one line and three opens** — it
    -- is pulled apart by 'Thena.Driver.regroup', so nothing below this carries
    -- the plural.
    --
    -- **Its effect runs from where it is written to the end of the enclosing
    -- namespace**, which for a file with no @namespace@ block is the rest of
    -- the file — so a declaration above it does not see it.
  | SurfacePrivate SurfaceDecl
    -- ^ @private ‹declaration›@ — **the declaration is the file's own and no
    -- importer may name it** (MS11 phase 286, his ruling of 2026-10-30, the
    -- fine-grained escape from the header's @exporting@ list).
    --
    -- **It takes a declaration, not a block**, which is 'SurfaceOpenIn'\'s shape
    -- and for its reason: a signature and its equation are two of these and one
    -- declaration, so the pass that pairs them is the one that can say how far
    -- a @private@ in front of the signature reaches.
    --
    -- **A mark and not a scope.** Where the declaration lands, what it may see
    -- and what it generates are all exactly what they are without the word; the
    -- only thing that changes is whether another file may write the names.
  | SurfaceOpenIn [([String], String)] SurfaceOpenSpec SurfaceDecl
    -- ^ @open X in ‹one declaration›@ — **the open reaches that declaration and
    -- stops** (MS10 phase 254), which is his *"one local let-like"*.
    --
    -- **One declaration means the signature and the equation**, because that is
    -- what a declaration is in this language — 'SurfaceDecl' is half of one.
    -- 'Thena.Driver.regroup' takes the pair, so
    --
    -- > open Nat in two : Nat.Nat
    -- > two = succ zero
    --
    -- is one declaration under one @open@, and @succ@ resolves in both lines.
  | SurfaceConsult [String] String
    -- ^ @consult ‹module›@ — **what this file's proofs are searched against**
    -- (MS11 phase 273, his ruling of 2026-11-03).
    --
    -- The steps and the last word of a **file's** name, the same shape
    -- 'SurfaceOpen' uses for a namespace's and meaning something different by
    -- it: here the steps are directories under the project's source root, and
    -- @consult Stlc.Tactics@ reaches @Stlc\/Tactics.thena.rules@. **A file's
    -- name and a namespace are different spaces** — his model of 2026-10-29 —
    -- which is why the two constructors share a shape and not a type.
    --
    -- **Its effect is the file's, not the session's**: a consult applies
    -- whenever this module is elaborated and does not leak to whoever loaded
    -- it, which is what makes a module that type-checks in isolation type-check
    -- for whoever imports it.
  | SurfaceImport [String] String
    -- ^ @import ‹module›@ — **which surface modules this file depends on**
    -- (MS11 phase 274, his ruling of 2026-11-03).
    --
    -- 'SurfaceConsult'\'s shape and 'SurfaceConsult'\'s meaning of it: the steps
    -- are directories, so @import Stlc.Terms@ reaches @Stlc\/Terms.thena@ — the
    -- act supplies the extension, which is the only thing that tells the two
    -- apart on disk.
    --
    -- **What it does is load**, and that is all it does today: the module it
    -- names is elaborated before this one, so a file states what it refers to
    -- rather than relying on the session having loaded it. **Which of the
    -- module's names the importer may then write is not settled** — that is
    -- @exporting ( … )@ and @public import@, and until they are built
    -- everything the imported module declared is reachable.
  | SurfaceNamespace [String] String [SurfaceDecl]
    -- ^ @namespace ‹name› where { … }@ — **declare a namespace and put these
    -- declarations in it** (MS10 phase 254).
    --
    -- **A namespace is a prefix, so nesting is a longer prefix and needs no
    -- mechanism of its own**: @namespace A where { namespace B where { … } }@
    -- puts a @foo@ inside at @A.B.foo@. Written with a path, @namespace A.B@ is
    -- the same thing said in one line.
    --
    -- **Open-ended, like Lean's and unlike a Haskell module** — his ruling of
    -- 2026-10-30: two files may both add to @A@, because the environment is
    -- keyed by a qualified name and two keys sharing a prefix is not a conflict.
    -- A check would have to be /added/ to forbid it.
    --
    -- **What the declarations inside can see is the walk, not an @open@**: a
    -- written word is tried in @A.B@, then in @A@, then at the root, and a
    -- nearer rung wins outright. 'Thena.Core.Term.InScope' carries the two
    -- apart.
  | SurfaceGrammar   BlockKind Int String
    -- ^ a @language@ or @context@ block (MS6 phase 101): its kind, the line of
    -- its keyword, and its text, raw. "Thena.Driver.regroup" reads it.
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
  { surfaceDataSteps        :: [String]   -- ^ the path written before the name
  , surfaceDataName         :: String
  , surfaceDataParameters   :: [(String, Surface)]
  , surfaceDataType         :: Surface   -- ^ the part right of the @:@
  , surfaceDataConstructors :: [SurfaceConstructor]
  }
  deriving (Eq, Show)

data SurfaceConstructor = SurfaceConstructor [String] String Surface
  deriving (Eq, Show)

-- | What went wrong pairing a signature with its equation
-- ("Thena.Driver.regroup").
data PairingError
  = SignatureWithNoEquation String
  | EquationWithNoSignature String
  deriving (Eq, Show)

-- | Every @do@ block written inside a surface term, outermost first.
--
-- **The one walk over 'Surface' that is not elaboration** (MS5 phase 79). It
-- exists so a block can be resolved and type-checked when the term is /read/,
-- where until then 'Thena.Instral.Ops.Play' resolved it as it ran — so @say 3@ in one
-- halted the machine mid-proof rather than being refused at load
-- (@ms5\/CLOSEOUT.md@ 20).
--
-- **A nested block is found too**: a block\'s instructions can hold a surface
-- literal of their own, and that literal can hold a block. The recursion goes
-- through 'RawInstr' without this module knowing what an operand is, because
-- it cannot — @instral@ is term-free and a surface literal reaches an operand
-- only after resolution. So nesting is picked up on the next pass instead, by
-- the caller, which walks resolved instructions.
blocksIn :: Surface -> [[RawInstr]]
blocksIn t = case t of
  SurfaceDo is        -> [is]
  SurfaceSplit _ tg as -> blocksIn tg ++ concatMap (\(SurfaceArm _ b) -> foldMap blocksIn b) as
  SurfaceApp f as     -> blocksIn f ++ concatMap (\(SurfaceArg _ a) -> blocksIn a) (toList as)
  SurfaceLam bs b     -> concatMap binder (toList bs) ++ blocksIn b
  SurfacePi bs b      -> concatMap binder (toList bs) ++ blocksIn b
  SurfaceArrow a b    -> blocksIn a ++ blocksIn b
  SurfaceLet _ mt v b -> maybe [] blocksIn mt ++ blocksIn v ++ blocksIn b
  SurfaceAnnot e ty   -> blocksIn e ++ blocksIn ty
  SurfaceTrusted ty e -> blocksIn ty ++ blocksIn e
  SurfaceElim _ _ ls m is ms tg ->
    concatMap blocksIn ls ++ blocksIn m ++ concatMap blocksIn is
      ++ concatMap blocksIn ms ++ blocksIn tg
  -- A splice is a term like any other, so a block inside one is found here.
  SurfaceObject _ _ ps -> concatMap piece ps
  SurfaceName _ _     -> []
  SurfaceUniverse _   -> []
  SurfaceLiteral _    -> []
  SurfaceUniverseOpen -> []
  SurfacePlaceholder  -> []
  SurfaceHole _       -> []
  where
    binder (SurfaceBinder _ _ mt) = maybe [] blocksIn mt
    piece pc = case pc of
      ObjectText _   -> []
      ObjectSplice e -> blocksIn e

-- | A global's name, written out as a name (MS10 phase 244).
--
-- **For a generator**: what the substitution family and a reading of an object
-- term write is a name that is already resolved, and a reference to one in a
-- namespace has to carry its path or the context would be searched for its base
-- word first. Writing it is the same thing a user does with @Ty.subst-X@.
surfaceName :: GlobalName -> Surface
surfaceName n = SurfaceName (nameSteps n) (nameWord n)
