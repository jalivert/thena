-- | A zipper over the surface language — a focused tree carried as a /value/
-- (MS4 phase 46).
--
-- **His design, and shape D of @discussion\/surface-and-elaboration.md@ §1.**
-- The alternatives were named there and dismissed: a bare subterm (shape A) is
-- /"D with the path thrown away"/, and a second ambient cursor (shape B) would
-- either give every move op a mode — the first design principle's own example
-- of a wrong design — or duplicate the op vocabulary.
--
-- == Why the path is worth carrying
--
-- A zipper that is a value costs the machine nothing: it backtracks by living
-- in @env@, which a 'Thena.Engine.Choice' frame already restores, and no op has
-- to ask which cursor it is moving. That is the Ξ precedent — unification
-- decomposes into rules /because/ Ξ is a field of the constraint and therefore
-- data, where Γ is ambient and @infer@ does not.
--
-- What the path buys, and neither is built here:
--
--   * **a hole can record where in the user's program it came from**, which is
--     the hook Agda-style refinement needs (§2.4.1). §2.4's last line is the
--     scope: /"Direction 2 is what §1's zipper keeps open at no extra cost.
--     That is an argument for D and not an argument for building refinement
--     now."/
--   * **observability** — the machine can say where in the surface it is
--     standing, from data it is already holding.
--
-- == What is here, and what is deliberately not
--
-- **Only the moves the clauses of @elaborate@ perform**, because §12 invariant
-- 5 says the vocabulary is discovered by writing the thing that needs it. So
-- there is no @up@ — nothing goes up, since each nested @elaborate@ is a fresh
-- call carrying its own zipper — and there is no way to /replace/ the focus,
-- which
-- is refinement's operation (§2.4.1) and not this phase's.
--
-- **There are no ops over this yet.** His ruling, 2026-09-03: phase 46 is the
-- representation, and the op vocabulary arrives at phase 49 with the clauses
-- that call it.
--
-- == The one law, and it is what the tests check
--
-- Every move preserves the root: @root (into… z) == root z@, up to the way the
-- surface tree spells a Π binder group (see 'intoPiTail'). 'root' goes through
-- 'rebuild', which is written per frame and is not the code any move uses —
-- the standing testing lesson's /"look for the invariant that is checked by
-- different code from the code that maintains it"/.
module Thena.Surface.Zipper
  ( SurfaceZipper
  , rootedAt
  , focus
  , root
    -- * Moves — one per descent a clause of @elaborate@ performs
  , intoFun
  , intoArg
  , intoHead
  , intoAppTail
  , intoLamBody
  , intoLamTail
  , intoLamAnnot
  , intoPiDomain
  , intoPiTail
  , intoArrowDomain
  , intoArrowCodomain
  , intoLetType
  , intoLetValue
  , intoLetBody
  , intoAnnotType
  , intoAnnotTerm
  , intoTrustedType
  , intoTrustedTerm
  , intoElimField
  , intoSplitTarget
  , intoSplitArmBody
  , intoSplitTail
  ) where

import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE

import Thena.Surface.Concrete
  ( Analysis, Plicity, Surface (..), SurfaceArg (..), SurfaceArm (..)
  , SurfaceBinder (..), SurfacePattern
  )

-- | A surface term, and where it sits in the one it came from.
--
-- The constructor is hidden, as 'Thena.Development.Cursor.Cursor'\'s is: the
-- frames are in child-to-root order and nothing outside this module has any
-- business assembling one.
data SurfaceZipper = SurfaceZipper Surface [Frame]
  deriving (Eq, Show)

-- | One step of the path — a node with a hole where the focus is.
--
-- **Structural, which is the obvious first answer and nothing argues against
-- it** (§1's second @[open]@).
--
-- **A frame holds its node's other fields as they were**, including the one
-- the focus replaced, and 'rebuild' puts the focus back by position. That is
-- one field of redundancy per frame, bought deliberately: the alternative
-- spellings — a flat sibling list re-split on the way out, or a @Maybe@ no
-- caller could see — both need a branch that cannot be reached, and an
-- unreachable branch is what the next reader has to reason about.
data Frame
  = InFun SurfaceArg
    -- ^ the focus is a spine minus its last argument
  | InArg Surface (NonEmpty SurfaceArg) Int
    -- ^ the focus is the @k@th argument of a spine
  | InHead (NonEmpty SurfaceArg)
    -- ^ the focus is the head a whole spine is applied to
  | InAppTail SurfaceArg
    -- ^ the focus is the spine that is left once its first argument is taken
    -- — 'InLamTail' one node over, and merged on the way out for 'InFun'\'s
    -- reason
  | InLamBody (NonEmpty SurfaceBinder)
  | InLamTail SurfaceBinder
    -- ^ the focus is what the λ abstracts once its first binder is peeled off
    -- — 'InPiTail' for a λ, and merged on the way out for the same reason
  | InLamAnnot Plicity String [SurfaceBinder] Surface
    -- ^ the focus is a λ binder's written type: its plicity and name, the rest
    -- of the group, and the body. **'InPiDomain' for a λ**, and it exists
    -- because an annotated λ binder elaborates — the written type has to be
    -- reachable to be elaborated at all
  | InPiDomain Plicity String [SurfaceBinder] Surface
    -- ^ the focus is the first binder's annotation: its plicity and name, the
    -- rest of the group, and the body
  | InPiTail SurfaceBinder
    -- ^ the focus is what the Π quantifies over once its first binder is
    -- peeled off — see 'intoPiTail'
  | InArrowDomain Surface
  | InArrowCodomain Surface
  | InLetType String Surface Surface          -- ^ name, value, body
  | InLetValue String (Maybe Surface) Surface -- ^ name, annotation, body
  | InLetBody String (Maybe Surface) Surface  -- ^ name, annotation, value
  | InAnnotType Surface                       -- ^ the ascribed term
  | InAnnotTerm Surface                       -- ^ the type ascribed
  | InTrustedType Surface                     -- ^ the trusted term
  | InTrustedTerm Surface                     -- ^ the type claimed
  | InElimField String [Surface] Surface [Surface] [Surface] Surface Int
    -- ^ the focus is one field of an @elim@, at flat position @k@ in the order
    -- the elaborator walks them: parameters, motive, methods, indices, target
  | InSplitTarget Analysis [SurfaceArm]
    -- ^ the focus is the term a split analyses (MS9 phase 181)
  | InSplitArmBody Analysis Surface SurfacePattern [SurfaceArm]
    -- ^ the focus is the __first__ arm's right-hand side: the analysis, the
    -- target, that arm's own pattern, and the arms after it.
    --
    -- **Only the first**, because that is the only one a clause descends into
    -- — 'intoSplitTail' peels an arm and the clause recurses, exactly as
    -- @E\u27e6x \u20d7a\u27e7@ walks a spine with 'InAppTail'. An indexed frame like
    -- 'InElimField' would buy a move nothing performs.
  | InSplitTail Analysis Surface SurfaceArm
    -- ^ the focus is the split that is left once its first arm is taken —
    -- 'InAppTail' for a split, and merged on the way out for the same reason
  deriving (Eq, Show)

-- | The whole term, focused at its root.
rootedAt :: Surface -> SurfaceZipper
rootedAt s = SurfaceZipper s []

-- | The subterm the zipper stands at.
focus :: SurfaceZipper -> Surface
focus (SurfaceZipper s _) = s

-- | The term the zipper came from, rebuilt.
root :: SurfaceZipper -> Surface
root (SurfaceZipper s fs) = foldl rebuild s fs

-- | Put the focus back into the node its frame came from.
rebuild :: Surface -> Frame -> Surface
rebuild s f = case f of
  -- **Flattened, not nested**, matching the parser's own @spine@: the head of
  -- a 'SurfaceApp' may be anything, so nesting one inside another would make
  -- @f a b@ representable twice over, which is what having one application
  -- constructor exists to prevent.
  InFun a -> case s of
    SurfaceApp g as -> SurfaceApp g (as <> (a :| []))
    _               -> SurfaceApp s (a :| [])
  InArg h as k ->
    SurfaceApp h (NE.zipWith (at k) (0 :| [1 ..]) as)
  -- **Flattened, exactly as 'InFun' is**: a head that is itself a spine joins
  -- the argument runs rather than nesting, which is what keeps @f a b@
  -- representable one way only.
  InHead as -> case s of
    SurfaceApp g bs -> SurfaceApp g (bs <> as)
    _               -> SurfaceApp s as
  InAppTail a -> case s of
    SurfaceApp h as -> SurfaceApp h (a NE.<| as)
    _               -> SurfaceApp s (a :| [])
  InLamBody bs -> SurfaceLam bs s
  InPiDomain p x rest body ->
    SurfacePi (SurfaceBinder p x (Just s) :| rest) body
  InLamAnnot p x rest body ->
    SurfaceLam (SurfaceBinder p x (Just s) :| rest) body
  -- **Merged, for 'InFun'\'s reason**, and it is the one place the law in the
  -- header is up to spelling: @∀ (A : S) (a : A) -> B@ comes back exactly, and
  -- @∀ (A : S) -> ∀ (a : A) -> B@ comes back as the first — the same term,
  -- written the other way. The surface tree admits both, which is a wart of
  -- the AST and not of the zipper; @ms4\/CLOSEOUT.md@ 18 carries it.
  InLamTail b -> case s of
    SurfaceLam bs body -> SurfaceLam (b NE.<| bs) body
    _                  -> SurfaceLam (b :| []) s
  InPiTail b -> case s of
    SurfacePi bs body -> SurfacePi (b NE.<| bs) body
    _                 -> SurfacePi (b :| []) s
  InArrowDomain cod -> SurfaceArrow s cod
  InArrowCodomain dom -> SurfaceArrow dom s
  InLetType x v body -> SurfaceLet x (Just s) v body
  InLetValue x ann body -> SurfaceLet x ann s body
  InLetBody x ann v -> SurfaceLet x ann v s
  InSplitTarget a arms -> SurfaceSplit a s arms
  -- **@Just@ and not a 'Maybe' in the frame**: you can only be inside a body
  -- that was written, so an arm rebuilt from here always has one.
  InSplitArmBody a tgt p rest -> SurfaceSplit a tgt (SurfaceArm p (Just s) : rest)
  -- **Merged, for 'InAppTail'\'s reason**: the arm goes back on the front of
  -- whatever arms the focus has. The analysis and the target come from the
  -- frame, which holds them as they were.
  InSplitTail a tgt arm -> case s of
    SurfaceSplit _ _ arms -> SurfaceSplit a tgt (arm : arms)
    _                     -> SurfaceSplit a tgt [arm]
  InAnnotType e -> SurfaceAnnot e s
  InAnnotTerm ty -> SurfaceAnnot s ty
  InTrustedType e -> SurfaceTrusted s e
  InTrustedTerm ty -> SurfaceTrusted ty s
  -- The flat order is the parameters, the motive, the methods, the indices and
  -- the target, so each group starts where the one before it ended — which is
  -- the arithmetic, and where an off-by-one in this frame would live.
  InElimField d ps mot ms is tgt k ->
    let np = length ps
        nm = length ms
        put i old = if i == k then s else old
     in SurfaceElim d
          (zipWith put [0 ..] ps)
          (put np mot)
          (zipWith put [np + 1 ..] ms)
          (zipWith put [np + 1 + nm ..] is)
          (put (np + 1 + nm + length is) tgt)
  where
    at k i (SurfaceArg p a) = SurfaceArg p (if i == (k :: Int) then s else a)

-- | Focus a spine minus its last argument — @f a b@ becomes @f a@, and @f a@
-- becomes @f@.
--
-- **A move takes the pieces its caller has already destructured**, rather than
-- re-matching the focus and handing back a 'Maybe' that nothing could ever
-- see. Passing a piece that did not come from the focus is representable and
-- not well formed — @.claude\/spec\/representation.md@ §3.4's line — and the law in this
-- module's header is what checks it.
intoFun :: SurfaceArg -> Surface -> SurfaceZipper -> SurfaceZipper
intoFun a fun = push fun (InFun a)

-- | Focus the @k@th argument of a spine, counting from zero.
intoArg
  :: Surface -> NonEmpty SurfaceArg -> Int -> Surface -> SurfaceZipper
  -> SurfaceZipper
intoArg h as k a = push a (InArg h as k)

-- | Focus the head a whole spine is applied to — @f a b@ gives @f@.
--
-- 'intoFun' peels one argument off the right; this reaches all the way in,
-- because @E⟦x ⃗a⟧@ needs the head before it has walked any argument.
intoHead :: NonEmpty SurfaceArg -> Surface -> SurfaceZipper -> SurfaceZipper
intoHead as h = push h (InHead as)

-- | Focus what is left of a spine once its **first** argument is taken.
--
-- **This is how a rule loops over a spine** (MS4 phase 49f), and it is
-- 'intoLamTail' one node over: a clause takes the first argument, claims a hole
-- for it and calls itself on the tail, so the surface term is the counter.
--
-- The exhausted case is the bare head, not a failure, which is what gives the
-- recursion its base case: @f a@ answers with @f@.
intoAppTail :: SurfaceArg -> Surface -> SurfaceZipper -> SurfaceZipper
intoAppTail a rest = push rest (InAppTail a)

intoLamBody
  :: NonEmpty SurfaceBinder -> Surface -> SurfaceZipper -> SurfaceZipper
intoLamBody bs body = push body (InLamBody bs)

-- | Focus the annotation on a Π's first binder.
intoPiDomain
  :: Plicity -> String -> [SurfaceBinder] -> Surface -> Surface -> SurfaceZipper
  -> SurfaceZipper
intoPiDomain p x rest body ty = push ty (InPiDomain p x rest body)

-- | Focus the type written on a λ's first binder.
--
-- 'intoPiDomain' for a λ, and the group is carried the same way: the move holds
-- the binders it did not descend into, so the way back is the only place that
-- has to know the group was ever split.
intoLamAnnot
  :: Plicity -> String -> [SurfaceBinder] -> Surface -> Surface -> SurfaceZipper
  -> SurfaceZipper
intoLamAnnot p x rest body ty = push ty (InLamAnnot p x rest body)

-- | Focus what a Π quantifies over once its first binder is peeled off.
--
-- **The group is peeled by the move and not in the tree**, which is what phase
-- 46 changed about the Π case: it used to rewrite @∀ (A : S) (a : A) -> B@
-- into @∀ (A : S) -> ∀ (a : A) -> B@ and call @compile@ again on a node that
-- was never in the user's program. The instruction stream is identical either
-- way — the codomain has always gone through a nested @Elaborate@ — so the
-- move costs nothing and the path stays real.
--
-- The focus is @∀ ‹rest› -> body@ when the group had more binders and @body@
-- when it did not; the caller passes whichever it has.
intoPiTail :: SurfaceBinder -> Surface -> SurfaceZipper -> SurfaceZipper
intoPiTail b rest = push rest (InPiTail b)

-- | Focus what a λ abstracts once its first binder is peeled off — the rest of
-- the group if there was one, otherwise the body.
--
-- **This is how a rule loops over a binder group** (MS4 phase 49c): a clause
-- peels one binder and calls itself on the tail, so the surface term is the
-- counter and the rule language needs no iteration of its own.
intoLamTail :: SurfaceBinder -> Surface -> SurfaceZipper -> SurfaceZipper
intoLamTail b rest = push rest (InLamTail b)

intoArrowDomain :: Surface -> Surface -> SurfaceZipper -> SurfaceZipper
intoArrowDomain cod dom = push dom (InArrowDomain cod)

intoArrowCodomain :: Surface -> Surface -> SurfaceZipper -> SurfaceZipper
intoArrowCodomain dom cod = push cod (InArrowCodomain dom)

-- | Focus a @let@\'s written type annotation.
intoLetType
  :: String -> Surface -> Surface -> Surface -> SurfaceZipper -> SurfaceZipper
intoLetType x v body ty = push ty (InLetType x v body)

intoLetValue
  :: String -> Maybe Surface -> Surface -> Surface -> SurfaceZipper
  -> SurfaceZipper
intoLetValue x ann body v = push v (InLetValue x ann body)

intoLetBody
  :: String -> Maybe Surface -> Surface -> Surface -> SurfaceZipper
  -> SurfaceZipper
intoLetBody x ann v body = push body (InLetBody x ann v)

intoAnnotType :: Surface -> Surface -> SurfaceZipper -> SurfaceZipper
intoAnnotType e ty = push ty (InAnnotType e)

intoAnnotTerm :: Surface -> Surface -> SurfaceZipper -> SurfaceZipper
intoAnnotTerm ty e = push e (InAnnotTerm ty)

-- | Focus the claimed type of a @trusted T e@ (MS8 phase 150).
intoTrustedType :: Surface -> Surface -> SurfaceZipper -> SurfaceZipper
intoTrustedType e ty = push ty (InTrustedType e)

-- | … and its body.
intoTrustedTerm :: Surface -> Surface -> SurfaceZipper -> SurfaceZipper
intoTrustedTerm ty e = push e (InTrustedTerm ty)

-- | Focus one field of an @elim@, at flat position @k@ in the order the
-- elaborator walks them: the parameters, the motive, the methods, the indices,
-- the target.
intoElimField
  :: String -> [Surface] -> Surface -> [Surface] -> [Surface] -> Surface
  -> Int -> Surface -> SurfaceZipper -> SurfaceZipper
intoElimField d ps mot ms is tgt k fld =
  push fld (InElimField d ps mot ms is tgt k)

-- | Focus the term a split analyses.
intoSplitTarget
  :: Analysis -> [SurfaceArm] -> Surface -> SurfaceZipper -> SurfaceZipper
intoSplitTarget a arms tgt = push tgt (InSplitTarget a arms)

-- | Focus the first arm's right-hand side.
intoSplitArmBody
  :: Analysis -> Surface -> SurfacePattern -> [SurfaceArm] -> Surface
  -> SurfaceZipper -> SurfaceZipper
intoSplitArmBody a tgt p rest body = push body (InSplitArmBody a tgt p rest)

-- | Focus the split that is left once its first arm is taken.
--
-- **The analysis and the target are carried over unchanged**, so the tail is a
-- split of the same thing with one fewer arm — and a split with /no/ arms is a
-- legal node, which is what makes this recursion need no special base case.
intoSplitTail
  :: Analysis -> Surface -> SurfaceArm -> [SurfaceArm]
  -> SurfaceZipper -> SurfaceZipper
intoSplitTail a tgt arm rest =
  push (SurfaceSplit a tgt rest) (InSplitTail a tgt arm)

push :: Surface -> Frame -> SurfaceZipper -> SurfaceZipper
push s f (SurfaceZipper _ fs) = SurfaceZipper s (f : fs)
