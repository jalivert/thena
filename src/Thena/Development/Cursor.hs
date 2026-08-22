-- | The cursor: focus and navigation over a development (§4).
--
-- The cursor /is/ the development, not a pointer into one (§4.2). There is
-- exactly one focus, always; rendering the whole state means 'rebuild'ing,
-- which is O(depth) with most structure shared.
--
-- One module, deliberately, and a long one. 'Path', 'Step', 'Slot', 'Crossing',
-- 'TermStep' and 'Cursor' cooperate to maintain one invariant — that the
-- variable a binder step carries is the variable its 'Scope' was opened with —
-- and §2.5's principle is that such a set lives together.
--
-- This is the third and last place the project spends Level 1 (§3.4):
-- 'Cursor'\'s constructors are not exported, so 'enter' and the moves are the
-- only ways to build one. Everything else here is transparent, because the
-- terminal has to render a path and cannot do it through a keyhole.
module Thena.Development.Cursor
  ( -- * The path
    Path (..)
  , Step (..)
  , Slot (..)
  , Crossing (..)
  , TermStep (..)
  , Part (..)
  , fill

    -- * The cursor
  , Cursor  -- NB: the type only. Hiding the constructors is the point (§4.4).
  , Focus (..)
  , enter
  , rebuild
  , prefix
  , focus

    -- * Moving (§4.3)
  , along
  , into
  , crossType
  , crossValue
  , down
  , back

    -- * Reading the position (§4.5)
  , context
  , expectedType

    -- * Changing the development
  , insertAbove
  , replaceFocus
  , replaceCore

    -- * The root-down pass (§4.0 G1)
  , overComponents
  , overConstraints
  , postConstraint
  , below
  ) where

import Data.Foldable (toList)
import Data.List ((\\))
import Data.Maybe (mapMaybe)

import Thena.Core.Context (Context, Entry (..))
import Thena.Core.Term
  ( Core (..)
  , GlobalName
  , Ident
  , Scope
  , Var
  , close
  , freeVars
  , fresh
  , open
  )
import Thena.Development.Component (Component (..), forget)
import Thena.Development.Partial (Constraint (..), Partial (..), freeVarsPartial)
import Thena.Errors (MoveError (..))

-- --------------------------------------------------------------------------
-- The path
-- --------------------------------------------------------------------------

-- | A path, root first, O(1) to extend at the focus end. Pronounce @(:>)@
-- \"then\".
--
-- A snoc list rather than a reversed cons list, so that it both pushes at the
-- focus end in O(1) /and/ reads root first — there is no \"remember to
-- reverse\" convention anywhere (§4.2, §4.0 I3). 'Foldable' walks it root
-- first, which is the order 'context' and the breadcrumb both want.
data Path a = Here | Path a :> a
  deriving (Eq, Show, Functor, Foldable)

infixl 5 :>

-- | A step within the partial fragment. There are exactly three (§4.2).
data Step
  = Along     Component                 -- ^ @c . □@ — passed a component
  | Past      Constraint                -- ^ @κ . □@ — passed a constraint
  | IntoGuess Var Ident Core Partial    -- ^ @?x ≐ □ : S . p@ — entered a guess
  deriving (Eq, Show)

-- | A component with one core field deleted.
--
-- Component kind and deleted field are chosen by one constructor, so no slot
-- exists that its kind does not have — an assumption has no value slot, and
-- that is true rather than merely checked (§4.4).
data Slot
  = TypeOfAssume  Var Ident            -- ^ @λ x     : □@
  | TypeOfDefine  Var Ident Core       -- ^ @x  = s  : □@ — the value is kept
  | ValueOfDefine Var Ident Core       -- ^ @x  = □  : S@ — the type is kept
  | TypeOfClaim   Var Ident            -- ^ @? x     : □@
  | TypeOfGuess   Var Ident Partial    -- ^ @? x ≐ g : □@ — the body is kept
  deriving (Eq, Show)

-- | Put a core term back in the field a 'Slot' deleted.
fill :: Slot -> Core -> Component
fill slot t = case slot of
  TypeOfAssume  x i   -> Assume x i t
  TypeOfDefine  x i v -> Define x i v t
  ValueOfDefine x i s -> Define x i t s
  TypeOfClaim   x i   -> Claim  x i t
  TypeOfGuess   x i g -> Guess  x i g t

-- | The one move out of the partial fragment. It happens once, or not at all
-- (§4.2).
--
-- There is deliberately no crossing into a constraint — no @Gap@ beside 'Slot'
-- and no @InEquate@ here. DECIDED 2026-08-18 by the user; §4.2 has the
-- argument, and §4.5's \"a 'Crossing' contributes nothing\" depends on it.
data Crossing
  = TrailingTerm          -- ^ □ is the partial construction's trailing term
  | InSlot Slot Partial   -- ^ □ is a core field; @p@ is what followed the component
  deriving (Eq, Show)

-- | A 'Core' constructor with one 'Core' field deleted: one constructor per
-- field, carrying every sibling field, with list fields split into before and
-- after.
--
-- 'Bound', 'Free', 'Global' and 'Universe' have no 'Core' fields and generate
-- no steps. 'Eliminate' has six fields and generates five. This type is
-- /derived/ from 'Core': if 'Core' changes, this changes with it (§4.2).
--
-- **The three binder steps inline an 'Entry' rather than carrying one.**
-- §4.2 writes them as @IntoPiCod Entry@; they are spelled out here because
-- @IntoLetBody@ needs a 'Definition' and the other two need a 'Hypothesis',
-- and an 'Entry' field admits both. Choosing the entry's kind by the
-- constructor is exactly 'Slot'\'s own technique, and the same inlining
-- 'Cursor' does to @Under@ — see the plan for phase 5 §10. The close-on-ascent
-- record is still entirely here and nowhere else.
data TermStep
  = IntoFun      Core                          -- ^ @□ a@
  | IntoArg      Core                          -- ^ @f □@
  | IntoPiDom    Ident      (Scope Core)       -- ^ @Π x : □ . B@
  | IntoPiCod    Var Ident Core                -- ^ @Π x : S . □@ — the opened binder
  | IntoLamDom   Ident      (Scope Core)       -- ^ @λ x : □ . b@
  | IntoLamBody  Var Ident Core                -- ^ @λ x : S . □@ — the opened binder
  | IntoLetValue Ident      Core (Scope Core)  -- ^ @x = □ : S . t@
  | IntoLetType  Ident Core      (Scope Core)  -- ^ @x = s : □ . t@
  | IntoLetBody  Var Ident Core Core           -- ^ @x = s : S . □@ — the opened binder
  | IntoCanonArg GlobalName [Core] [Core]      -- ^ @c a₁ … □ … aₙ@
  | IntoElimParam  GlobalName [Core] [Core] Core [Core] [Core] Core
  | IntoElimMotive GlobalName [Core]            [Core] [Core] Core
  | IntoElimMethod GlobalName [Core] Core [Core] [Core] [Core] Core
  | IntoElimIndex  GlobalName [Core] Core [Core] [Core] [Core] Core
  | IntoElimTarget GlobalName [Core] Core [Core] [Core]
  deriving (Eq, Show)

-- | Which core field a descent names — one per 'TermStep', so that no word
-- means a different thing depending on what is in focus (§4.0 C1).
--
-- 'Dom' serves Π and λ and 'Body' serves λ and @let@ because in each pair the
-- field plays the same role; they are one word for one idea, not one word for
-- two.
data Part
  = Fun | Arg
  | Dom | Cod
  | Val | Type | Body
  | Motive | Target
  | Param Int | Method Int | Index Int | CanonArg Int
  deriving (Eq, Show)

-- --------------------------------------------------------------------------
-- The cursor
-- --------------------------------------------------------------------------

-- | The development, focused.
--
-- @InPartial p c rest@ is one field with its constructor inlined — @Under c
-- rest@ — exactly as @NonEmpty a = a :| [a]@ inlines @(:)@. It has to be known
-- non-'Trailing', because a trailing term /is/ a core focus and that is
-- 'InCore'\'s job; allowing both would give one position two cursors and
-- 'rebuild' would stop being injective (§4.2).
data Cursor
  = InPartial    (Path Step) Component  Partial
  | AtConstraint (Path Step) Constraint Partial
  | InCore       (Path Step) Crossing (Path TermStep) Core
  deriving (Eq, Show)

-- | The focused form, read-only: 'Cursor'\'s constructors are hidden, and this
-- is how the terminal asks what it is standing on.
--
-- It is not a second copy of 'Cursor'. It carries the focus side only — the
-- prefix is 'prefix' and the development is 'rebuild', each with one meaning
-- and each available on its own.
data Focus
  = OnComponent  Component
  | OnConstraint Constraint
  | OnTerm       Crossing (Path TermStep) Core
  deriving (Eq, Show)

-- | Focus the root of a development. Total: every 'Partial' has a root focus.
enter :: Partial -> Cursor
enter = focusAt Here

-- | Focus the head of a partial construction, under a given prefix. The one
-- helper behind 'enter', 'along' and 'into' — \"what it means to arrive at a
-- partial construction\" is written once.
focusAt :: Path Step -> Partial -> Cursor
focusAt p q = case q of
  Under   c rest -> InPartial p c rest
  Pending k rest -> AtConstraint p k rest
  Trailing t     -> InCore p TrailingTerm Here t

-- | Rebuild the development. One fold, and the whole specification of the
-- structure (§4.3).
rebuild :: Cursor -> Partial
rebuild cur = case cur of
  InPartial    p c rest -> unwind p (Under   c rest)
  AtConstraint p k rest -> unwind p (Pending k rest)
  InCore p x ts t       -> unwind p (cross x (unwindTerm ts t))

unwind :: Path Step -> Partial -> Partial
unwind Here        q = q
unwind (p :> s)    q = unwind p (step s q)

step :: Step -> Partial -> Partial
step s q = case s of
  Along     c            -> Under c q
  Past      k            -> Pending k q
  IntoGuess x i ty rest  -> Under (Guess x i q ty) rest

cross :: Crossing -> Core -> Partial
cross TrailingTerm     t = Trailing t
cross (InSlot slot rest) t = Under (fill slot t) rest

unwindTerm :: Path TermStep -> Core -> Core
unwindTerm Here      t = t
unwindTerm (ts :> s) t = unwindTerm ts (termStep s t)

termStep :: TermStep -> Core -> Core
termStep s t = case s of
  IntoFun      a          -> App t a
  IntoArg      f          -> App f t
  IntoPiDom    i b        -> Pi i t b
  IntoPiCod    x i dom    -> Pi i dom (close x t)
  IntoLamDom   i b        -> Lam i t b
  IntoLamBody  x i dom    -> Lam i dom (close x t)
  IntoLetValue i ty b     -> Let i t ty b
  IntoLetType  i v b      -> Let i v t b
  IntoLetBody  x i v ty   -> Let i v ty (close x t)
  IntoCanonArg f bs as    -> Canonical f (bs ++ t : as)
  IntoElimParam  d bs as m ms is tgt -> Eliminate d (bs ++ t : as) m ms is tgt
  IntoElimMotive d ps      ms is tgt -> Eliminate d ps t ms is tgt
  IntoElimMethod d ps m bs as is tgt -> Eliminate d ps m (bs ++ t : as) is tgt
  IntoElimIndex  d ps m ms bs as tgt -> Eliminate d ps m ms (bs ++ t : as) tgt
  IntoElimTarget d ps m ms is        -> Eliminate d ps m ms is t

-- | The prefix: everything above the focus, root first. Always meaningful,
-- whichever fragment the focus is in — §4.0 A4's \"the prefix spans both
-- fragments\" is this field being the same field in all three cases.
prefix :: Cursor -> Path Step
prefix cur = case cur of
  InPartial    p _ _ -> p
  AtConstraint p _ _ -> p
  InCore       p _ _ _ -> p

-- | What is in focus.
focus :: Cursor -> Focus
focus cur = case cur of
  InPartial    _ c _   -> OnComponent c
  AtConstraint _ k _   -> OnConstraint k
  InCore       _ x ts t -> OnTerm x ts t

-- --------------------------------------------------------------------------
-- Moving
-- --------------------------------------------------------------------------

-- | Go past the head of the focus.
--
-- One meaning throughout, and it covers §4.0 B4: 'along' from the last
-- component of a chain lands on the trailing term, which is how a
-- 'TrailingTerm' crossing is ever reached. 'back' undoes it, popping the
-- 'Along' step it pushed.
along :: Cursor -> Either MoveError Cursor
along cur = case cur of
  InPartial    p c rest -> Right (focusAt (p :> Along c) rest)
  AtConstraint p k rest -> Right (focusAt (p :> Past  k) rest)
  InCore {}             -> Left NotOnTheSpine

-- | Enter a guess's body, which stays inside the partial fragment (§4.2).
--
-- Unchanged by the constraint form: a 'Constraint' has no 'Partial' field, so
-- there is nothing to enter.
into :: Cursor -> Either MoveError Cursor
into cur = case cur of
  InPartial p (Guess x i g ty) rest -> Right (focusAt (p :> IntoGuess x i ty rest) g)
  InPartial {}                      -> Left NotAGuess
  AtConstraint {}                   -> Left NotAGuess
  InCore {}                         -> Left NotOnTheSpine

-- | Cross into the focused component's type. The fragment change, and it
-- happens once.
crossType :: Cursor -> Either MoveError Cursor
crossType cur = case cur of
  InPartial p c rest -> Right $ case c of
    Assume x i   s -> InCore p (InSlot (TypeOfAssume x i)   rest) Here s
    Define x i v s -> InCore p (InSlot (TypeOfDefine x i v) rest) Here s
    Claim  x i   s -> InCore p (InSlot (TypeOfClaim  x i)   rest) Here s
    Guess  x i g s -> InCore p (InSlot (TypeOfGuess  x i g) rest) Here s
  AtConstraint {} -> Left NoCrossingIntoAConstraint
  InCore {}       -> Left NotOnTheSpine

-- | Cross into a definition's value. Only a 'Define' has one.
crossValue :: Cursor -> Either MoveError Cursor
crossValue cur = case cur of
  InPartial p (Define x i v s) rest ->
    Right (InCore p (InSlot (ValueOfDefine x i s) rest) Here v)
  InPartial {}    -> Left NotADefinition
  AtConstraint {} -> Left NoCrossingIntoAConstraint
  InCore {}       -> Left NotOnTheSpine

-- | Descend into a core subterm (§4.7).
--
-- Takes the name counter because descending under a binder must 'open' its
-- 'Scope' with a fresh 'Var' (§4.0 D3), and only 'fresh' mints one. The three
-- moves that do so are the three that record an opened binder; every other
-- descent gives the counter straight back.
down :: Part -> Int -> Cursor -> Either MoveError (Cursor, Int)
down part n cur = case cur of
  InCore p x ts t -> case (part, t) of
    (Fun,  App f a)     -> here n (IntoFun a) f
    (Arg,  App f a)     -> here n (IntoArg f) a
    (Dom,  Pi  i s b)   -> here n (IntoPiDom i b) s
    (Dom,  Lam i s b)   -> here n (IntoLamDom i b) s
    (Cod,  Pi  i s b)   -> opened (IntoPiCod   ) i s b
    (Body, Lam i s b)   -> opened (IntoLamBody ) i s b
    (Val,  Let i v s b) -> here n (IntoLetValue i s b) v
    (Type, Let i v s b) -> here n (IntoLetType  i v b) s
    (Body, Let i v s b) ->
      let (w, n1) = fresh n
       in Right (InCore p x (ts :> IntoLetBody w i v s) (open w b), n1)

    (CanonArg k, Canonical f as) -> do
      (bs, a, as') <- pick k as
      here n (IntoCanonArg f bs as') a
    (Param k, Eliminate d ps m ms is tgt) -> do
      (bs, a, as) <- pick k ps
      here n (IntoElimParam d bs as m ms is tgt) a
    (Motive, Eliminate d ps m ms is tgt) ->
      here n (IntoElimMotive d ps ms is tgt) m
    (Method k, Eliminate d ps m ms is tgt) -> do
      (bs, a, as) <- pick k ms
      here n (IntoElimMethod d ps m bs as is tgt) a
    (Index k, Eliminate d ps m ms is tgt) -> do
      (bs, a, as) <- pick k is
      here n (IntoElimIndex d ps m ms bs as tgt) a
    (Target, Eliminate d ps m ms is tgt) ->
      here n (IntoElimTarget d ps m ms is) tgt

    _ -> Left NoSuchPart
    where
      here n' s' t' = Right (InCore p x (ts :> s') t', n')
      opened con i s b =
        let (w, n1) = fresh n
         in Right (InCore p x (ts :> con w i s) (open w b), n1)
  _ -> Left NotInCore

-- | Split a list at a one-based position: what is before, the element, what is
-- after. The @n@ the user typed is one-based because the printer numbers from
-- one; nothing else here counts.
pick :: Int -> [a] -> Either MoveError ([a], a, [a])
pick k xs = case splitAt (k - 1) xs of
  (bs, a : as) | k >= 1 -> Right (bs, a, as)
  _                     -> Left NoSuchPart

-- | Undo the last move: pop the innermost step of the path, whatever it was.
--
-- One inverse for every descent, and one rule to state (§4.0 C3). It restores
-- exactly what was there, including closing a core binder on ascent —
-- @close x (open x sc) == sc@ holds because @x@ was fresh when the step was
-- pushed, and the step is the only record of which @x@ that was.
back :: Cursor -> Either MoveError Cursor
back cur = case cur of
  InCore p x (ts :> s) t -> Right (InCore p x ts (termStep s t))

  -- At the top of a core term, the crossing is what is popped — except for a
  -- trailing term, which was never crossed into: 'along' put us there, so an
  -- 'Along' step is what comes off.
  InCore p (InSlot slot rest) Here t -> Right (InPartial p (fill slot t) rest)
  InCore Here TrailingTerm    Here _ -> Left AtRoot
  InCore (p :> s) TrailingTerm Here t -> Right (unstep p s (Trailing t))

  InPartial Here _ _              -> Left AtRoot
  InPartial (p :> s) c rest       -> Right (unstep p s (Under c rest))
  AtConstraint Here _ _           -> Left AtRoot
  AtConstraint (p :> s) k rest    -> Right (unstep p s (Pending k rest))

-- | 'step', inverted: put the tail back under the step and focus what the step
-- passed.
unstep :: Path Step -> Step -> Partial -> Cursor
unstep p s q = case s of
  Along     c           -> InPartial p c q
  Past      k           -> AtConstraint p k q
  IntoGuess x i ty rest -> InPartial p (Guess x i q ty) rest

-- --------------------------------------------------------------------------
-- Reading the position
-- --------------------------------------------------------------------------

-- | Γ, derived from the prefix (§4.5). Outermost first.
--
-- It is exactly the 'Along' steps, forgotten, plus the binder each core step
-- opened. Everything else contributes nothing, each for its own reason, and by
-- construction rather than by a filter:
--
--   * 'Past' — a constraint binds nothing, and does not match 'Along'.
--   * 'IntoGuess' — §2.2.1's @Γ_(?x ≐ P : S . p) = Γ_P@: a guessed term cannot
--     refer to its own hole.
--   * a 'Crossing' — a hole's type may not mention it and a definition's value
--     is not recursive. There is no crossing into a constraint, so Ξ never
--     enters Γ at all.
--   * the focused component — you are /on/ it, not past it.
--
-- Expensive, and allowed to be (§4.0 D4). **Display must not use this**: a
-- printer that seeds its names from Γ shows a guess body the wrong scope, which
-- is invisible until a body binds its own hole's identifier (phase 3 §7.2).
context :: Cursor -> Context
context cur = spine ++ opened
  where
    spine = [ forget c | Along c <- toList (prefix cur) ]

    opened = case cur of
      InCore _ _ ts _ -> mapMaybe binder (toList ts)
      _               -> []

    binder s = case s of
      IntoPiCod   x i ty   -> Just (Hypothesis x i ty)
      IntoLamBody x i ty   -> Just (Hypothesis x i ty)
      IntoLetBody x i v ty -> Just (Definition x i v ty)
      _                    -> Nothing

-- | The type the structure knows the focus must have, where it knows one.
--
-- 'Nothing' means the structure does not carry it — not that the focus is
-- untyped. Deriving a type for an arbitrary core subterm is @infer@\'s job and
-- arrives at phase 8; until then this reports only what is written down:
--
--   * a component's own type, and a constraint's;
--   * the type beside a definition's value;
--   * the type of the innermost guess we have descended into, which is what a
--     guess body's trailing term must have (§4.5, §4.0 D2).
--
-- A focus that /is/ a type — anything crossed into through a @TypeOf…@ slot —
-- has a universe for its type, and MS1 has no level inference until phase 8,
-- so its level is not known here.
expectedType :: Cursor -> Maybe Core
expectedType cur = case cur of
  InPartial    _ c _ -> Just (componentType c)
  AtConstraint _ (Equate _ _ _ ty) _ -> Just ty
  InCore p x Here _ -> case x of
    InSlot (ValueOfDefine _ _ ty) _ -> Just ty
    InSlot _ _                      -> Nothing
    TrailingTerm                    -> innermostGuess p
  InCore {} -> Nothing

componentType :: Component -> Core
componentType c = case c of
  Assume _ _   s -> s
  Define _ _ _ s -> s
  Claim  _ _   s -> s
  Guess  _ _ _ s -> s

-- | The type carried by the innermost 'IntoGuess' step, walking up from the
-- focus.
innermostGuess :: Path Step -> Maybe Core
innermostGuess Here = Nothing
innermostGuess (p :> s) = case s of
  IntoGuess _ _ ty _ -> Just ty
  _                  -> innermostGuess p

-- --------------------------------------------------------------------------
-- Changing the development
-- --------------------------------------------------------------------------

-- | Add a component to the prefix immediately above the focus. The focus does
-- not move.
--
-- This is §4.0 B's answer to table 2.7's @Θ Θ' ⟹ Θ (λx:S) Θ'@, which looks like
-- an insertion at an unnamed split: under A1 there is no position between
-- components, so the operation is \"above the focus\" and nothing else.
--
-- Total, in the core fragment too: the prefix is the same prefix there (A4), so
-- @assume@ standing inside a component's type adds a binder above that
-- component. There is no other reading of \"above\" available, and refusing it
-- would be an extra rule with nothing behind it.
insertAbove :: Component -> Cursor -> Cursor
insertAbove c cur = case cur of
  InPartial    p f rest    -> InPartial    (p :> Along c) f rest
  AtConstraint p k rest    -> AtConstraint (p :> Along c) k rest
  InCore       p x ts t    -> InCore       (p :> Along c) x ts t

-- | Replace the focus — the focused form and everything below it — with
-- another partial construction, and land on its head (§4.0 F6).
--
-- Structural only. Nothing here checks that the replacement has the type the
-- old focus had; that is @check@, phase 8, and the operations that will use
-- this properly — @solve@, @abandon@, @cut@ — are later phases still. Its one
-- caller now is @:goal@, which throws a proof away and starts it again.
--
-- A core focus has to be replaced by a 'Core', not by a chain, so this is a
-- partial-fragment operation and says so.
replaceFocus :: Partial -> Cursor -> Either MoveError Cursor
replaceFocus q cur = case cur of
  InPartial    p _ _ -> Right (focusAt p q)
  AtConstraint p _ _ -> Right (focusAt p q)
  InCore {}          -> Left NotOnTheSpine

-- | Replace a focused core term with another, in place — what a committed
-- reduction does (§4.7). The caller decides what the replacement is; this
-- function is the zipper mechanics and the orphan check, nothing about
-- reduction itself, which is why "Thena.Core.Reduce" is not imported here —
-- @whnf@ is called by 'Thena.Engine', which already has the 'Context' this
-- position's Γ is and the 'Thena.Global.Env.GlobalEnv' @whnf@ needs.
--
-- Reports which of the prefix's HOLES — a 'Claim' or a 'Guess', never a plain
-- 'Assume' — no longer occur anywhere in the resulting development. A
-- variable that vanished from the reduced subterm might still be referenced
-- somewhere else below the focus, so the check rebuilds and asks
-- 'freeVarsPartial' rather than trusting the one subterm's own free variables
-- (§4.7's own example, @(λ_. Nat) ?h ⟶ Nat@, only orphans @?h@ because that
-- was its one and only occurrence).
replaceCore :: Core -> Cursor -> Either MoveError (Cursor, [Ident])
replaceCore t' cur = case cur of
  InCore p x ts t ->
    let cur'      = InCore p x ts t'
        vanished  = freeVars t \\ freeVars t'
        remaining = freeVarsPartial (rebuild cur')
        holes     = mapMaybe holeBinding [ c | Along c <- toList p ]
        orphaned  = [ i | (v, i) <- holes, v `elem` vanished, v `notElem` remaining ]
     in Right (cur', orphaned)
  _ -> Left NotInCore

-- | The variable and identifier a hole binds — a 'Claim' or a 'Guess' — or
-- 'Nothing' for an 'Assume' or a 'Define', which are not holes and whose
-- variables becoming unused is unremarkable.
holeBinding :: Component -> Maybe (Var, Ident)
holeBinding c = case c of
  Claim v i _   -> Just (v, i)
  Guess v i _ _ -> Just (v, i)
  _             -> Nothing

-- --------------------------------------------------------------------------
-- The root-down pass (§4.0 G1)
-- --------------------------------------------------------------------------
--
-- §4.0 G1 asks for "a focus-independent pass that walks from the root,
-- rewrites, and rebuilds — with the focus intact", and says unification's
-- substitutions are applied this way: it would be insane to make unification
-- zip around hunting for holes. These four are that pass, split by what they
-- edit. They are the only operations here that touch the development without
-- being a move, and they exist because the moves cannot do this job — a move
-- takes the focus with it, and this pass must not.
--
-- **Policy lives in the caller.** None of these knows what a hole is or where a
-- constraint belongs; 'postConstraint' takes the position as a number and
-- "Thena.Core.Unify" computes it.

-- | Rewrite every component of the development in place, above the focus, at
-- it, and below it. What unification's hole-solving uses: promoting @? x : S@
-- to @x = t : S@ is exactly a component rewritten in place (§4.0 G2).
--
-- **In place only, and at a core focus the focused component is skipped.** The
-- focus's 'Slot' has the component's kind built into its constructor, so a
-- rewrite that turned that component's 'Claim' into a 'Define' would leave a
-- 'TypeOfClaim' slot describing a component that no longer exists. Standing
-- inside a hole's own type while something solves that hole is an odd place to
-- be, and the answer is that the equation defers rather than that the focus
-- moves — G1 is explicit that the focus stays put.
overComponents :: (Component -> Component) -> Cursor -> Cursor
overComponents f cur = case cur of
  InPartial p c rest    -> InPartial (fmap onStep p) (f c) (onPartial rest)
  AtConstraint p k rest -> AtConstraint (fmap onStep p) k (onPartial rest)
  InCore p x ts t       -> InCore (fmap onStep p) (onCrossing x) ts t
  where
    onStep s = case s of
      Along c               -> Along (f c)
      Past  k               -> Past k
      IntoGuess x i ty rest -> IntoGuess x i ty (onPartial rest)

    onCrossing x = case x of
      TrailingTerm     -> TrailingTerm
      InSlot slot rest -> InSlot slot (onPartial rest)   -- the slot's own component is skipped

    onPartial q = case q of
      Trailing t     -> Trailing t
      Under c rest   -> Under (f c) (onPartial rest)
      Pending k rest -> Pending k (onPartial rest)

-- | Rewrite the chain's constraint links; 'Nothing' removes one. What
-- unification's wake-up uses: a constraint that has become solvable stops being
-- a link, and one that has not stays where it is.
--
-- **The focused constraint is left alone**, for 'overComponents'\' reason: a
-- focus standing on a constraint cannot survive that constraint being deleted,
-- and the pass may not move the focus.
overConstraints :: (Constraint -> Maybe Constraint) -> Cursor -> Cursor
overConstraints f cur = case cur of
  InPartial p c rest    -> InPartial (onPath p) c (onPartial rest)
  AtConstraint p k rest -> AtConstraint (onPath p) k (onPartial rest)
  InCore p x ts t       -> InCore (onPath p) (onCrossing x) ts t
  where
    onPath Here     = Here
    onPath (p :> s) = case s of
      Past k -> case f k of
        Nothing -> onPath p
        Just k' -> onPath p :> Past k'
      Along c               -> onPath p :> Along c
      IntoGuess x i ty rest -> onPath p :> IntoGuess x i ty (onPartial rest)

    onCrossing x = case x of
      TrailingTerm     -> TrailingTerm
      InSlot slot rest -> InSlot slot (onPartial rest)

    onPartial q = case q of
      Trailing t     -> Trailing t
      Under c rest   -> Under c (onPartial rest)
      Pending k rest -> case f k of
        Nothing -> onPartial rest
        Just k' -> Pending k' (onPartial rest)

-- | Splice a constraint into the path, keeping the given number of steps above
-- it and pushing the rest down. @0@ puts it at the root; the path's own length
-- puts it immediately above the focus, which is what 'insertAbove' does for a
-- component.
--
-- The position is a number rather than a policy because §6.4 makes position
-- real information and `AGENDA.md` item 16 q1 makes choosing it a /tactic/
-- question. "Thena.Core.Unify" answers it — the minimal legal position,
-- decided by the user 2026-08-22 — and this function does as it is told.
--
-- **It reaches below the focus as well as above it**, which the first draft did
-- not: it spliced into the path only, on the argument that a constraint's
-- variables are all in scope where it was built and so never below. That is
-- true of a term typed at the REPL and false in general — a tactic that has
-- moved the focus upwards can defer an equation about components under it, and
-- parking that above them would name a variable that is not bound yet. The
-- numbering is continuous across the focus so the caller does not have to know
-- which side it landed on.
postConstraint :: Int -> Constraint -> Cursor -> Cursor
postConstraint n k cur = case cur of
  InPartial    p c rest -> place p (\p' -> InPartial    p' c) rest
  AtConstraint p j rest -> place p (\p' -> AtConstraint p' j) rest
  InCore       p x ts t -> case x of
    TrailingTerm     -> InCore (splice p (depth p)) TrailingTerm ts t
    InSlot slot rest ->
      let d = depth p
       in if n <= d
            then InCore (splice p d) x ts t
            else InCore p (InSlot slot (spliceUnder (n - d - 1) rest)) ts t
  where
    -- Above the focus the constraint becomes a step in the path; below it, a
    -- link in the chain. One index numbers both — the path's steps are 0 to
    -- d-1, the focus is d, and what is under it carries on from d+1 — which is
    -- the same numbering "Thena.Core.Unify" computes positions in.
    place p rebuildAt rest
      | n <= depth p = rebuildAt (splice p (depth p)) rest
      | otherwise    = rebuildAt p (spliceUnder (n - depth p - 1) rest)

    depth = length . toList

    splice p d = foldl (:>) Here (insertAt (clamp d) (toList p))

    clamp d = max 0 (min n d)

    insertAt _ []       = [Past k]
    insertAt 0 ss       = Past k : ss
    insertAt m (s : ss) = s : insertAt (m - 1) ss

    spliceUnder m q
      | m <= 0 = Pending k q
      | otherwise = case q of
          Trailing t     -> Pending k (Trailing t)
          Under c rest   -> Under c (spliceUnder (m - 1) rest)
          Pending j rest -> Pending j (spliceUnder (m - 1) rest)

-- | The chain strictly below the focus, where there is one.
--
-- 'Nothing' at a trailing term and at a core term inside one: a chain ends
-- there, so there is nothing under it. Read-only — 'overComponents' and
-- 'overConstraints' are how the part below the focus is written.
below :: Cursor -> Maybe Partial
below cur = case cur of
  InPartial    _ _ rest          -> Just rest
  AtConstraint _ _ rest          -> Just rest
  InCore _ (InSlot _ rest) _ _   -> Just rest
  InCore _ TrailingTerm    _ _   -> Nothing
