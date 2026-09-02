-- | Elaboration — turning a surface term into a development (MS4 phase 41).
--
-- **Step 1 of a two-step, and his design** (2026-09-02): the elaborator is
-- written in Haskell behind one large instruction first, and then broken into
-- the clauses of a rule named @elaborate@. `PLAN-machine.md` §7.2's /large and
-- small instructions coexist/ is the licence, and "Thena.Tactics.Eliminate" is
-- the precedent. §12 invariant 5 is the argument: **writing it here is how step
-- 2 finds out which ops it wants**, rather than having them guessed into a
-- phase up front.
--
-- == It emits instructions; it does not do the work
--
-- Every case compiles to a short program of ops that **already exist**, and to
-- an @Elaborate@ of each sub-term — so the op recurses through itself and each
-- case stays a line or two. Three things follow, and the first is why the shape
-- was chosen:
--
--   * **step 2 is a decomposition, not a rewrite.** The rule clauses that
--     replace this will emit the same instructions from a body instead of from
--     Haskell. Nothing about /what runs/ changes.
--   * **it is observable**: @:step@ shows an elaboration as ordinary
--     instructions, which is the whole of what the machine is for.
--   * **it cannot cheat.** A case that wanted something the op vocabulary does
--     not have cannot quietly reach past it — it has to fail, and that failure
--     is the list step 2 works from.
--
-- == What is here, and what is not
--
-- Phase 41 compiles the **leaves**: a name, a universe, and the two
-- placeholders. Lambdas, Π, application, @let@, ascription and @elim@ are
-- phase 41b, and each of them needs something the vocabulary does not yet have
-- — see 'NoElaborationRule'.
module Thena.Elaborate
  ( compile
  ) where

import Thena.Core.Context (Context, entryIdent, entryVar)

import Thena.Core.Level (Level (..), freshLevelMeta, levelOfNat)
import Thena.Core.Term (Core (..), GlobalName (..), Ident (..), Var)
import qualified Data.List.NonEmpty as NE

import Thena.Development.Partial (Partial (..))
import Thena.Errors (FailReason (..), ResolveError (..), SyntaxError (..))
import Thena.Global.Env (GlobalEnv, isDeclared)
import Thena.Ops (Instr (..), Op (..), Operand (..), Value (..))
import Thena.Surface.Concrete
  (Plicity (..), Surface (..), SurfaceArg (..), SurfaceBinder (..))

-- | The program that elaborates one surface node into the focused hole.
--
-- Takes Γ at the focus and the name counter, exactly as the ops it emits do,
-- and hands back the counter it advanced — a universe whose level is left open
-- mints a meta.
--
-- **A node it cannot yet elaborate is a failure and not a silence.** That list
-- is phase 41b's specification.
-- | The names one compiled node binds, all carrying its own number.
--
-- **A fixed name is a bug and this is the fix** (MS4 phase 41e). A nested
-- @Elaborate@ runs in the /same/ body environment, so an inner node that binds
-- @here@ shadows the outer node's — and the outer @goto here@ then lands on the
-- inner component. @elaborate (\ A -> \ y -> y)@ failed exactly that way with
-- /"that names no hole or guess"/, from the moment @here@ was introduced.
--
-- The number comes from the machine's own counter, which only ever grows, so
-- two nodes can never share one. Each 'compile' consumes a tick for it — the
-- same thing 'Thena.Core.Term.fresh' does with the same counter.
data Names = Names
  { hereName, domName, codName, arrName, funName, argName
  , appName, refName, tyName, goalName :: String }

namesFor :: Int -> Names
namesFor n =
  Names (w "here") (w "dom") (w "cod") (w "arr") (w "fun") (w "arg")
        (w "app") (w "ref") (w "ty") (w "goal")
  where w x = x ++ show n

compile :: GlobalEnv -> Context -> Int -> Surface -> Either FailReason ([Instr], Int)
compile env ctx n0 s = case s of
  -- @E⟦x⟧ = FILL x; SOLVE@ — Brady's variable case, and the one clause of his
  -- elaborator that has run in this system since phase 17b. What was
  -- @elab-var@'s body is now these two instructions.
  --
  -- Local names first, then the globals: a binder shadows a global of the same
  -- name, which is what one namespace (§3.6) requires. The same order
  -- "Thena.Syntax.Resolve" uses, for the same reason.
  SurfaceName x -> case inContext x of
    Just v -> attach (Free v)
    Nothing
      | isDeclared (GlobalName x) env -> attach (Global (GlobalName x) [])
      | otherwise -> Left (CannotRead (ResolveFailed (NotInScope x)))

  SurfaceUniverse k  -> attach (Universe (levelOfNat k))

  -- Typical ambiguity: the level is a meta and conversion decides it (phase
  -- 33). Writing @Typeₙ@ is always available and is the recovery.
  SurfaceUniverseOpen ->
    let (v, n1) = freshLevelMeta n
     in Right ([Do (Try (lit (Universe (LVar v)))), Do Solve], n1)

  -- @E⟦_⟧@ — **elaborate by not elaborating.** His words, 2026-09-01. Brady's
  -- @UNFOCUS@ exists because his focus /is/ the head of a hole queue and he has
  -- to move something off it; ours is a cursor, so leaving the hole alone is
  -- the whole of it. Unification is expected to find it, and if it does not,
  -- the hole is simply still there.
  SurfacePlaceholder -> Right ([], n)

  -- A **named** placeholder becomes a real hole, which is what the focused hole
  -- already is. Giving it the written name, and the clauses that ask the user
  -- or hand control over, are phase 44's.
  SurfaceHole _ -> Right ([], n)

  -- @E⟦e a⟧@ — Brady's application case with his own correction to the printed
  -- rule (the missing @FILL@ and @SOLVE@, @IDRIS.md@):
  --
  -- > CLAIM (A : Type); CLAIM (B : Type); CLAIM (f : A → B); CLAIM (s : A)
  -- > FILL (f s); FOCUS f; E⟦e⟧; FOCUS s; E⟦a⟧; SOLVE
  --
  -- **A spine is folded right to left**: @h a₁ … aₙ@ is @(h a₁ … aₙ₋₁) aₙ@, so
  -- one clause covers every arity and the head of the recursion is an ordinary
  -- 'Surface'. Brady's other rule, @E⟦x ⃗a⟧@, is the one that expands implicits
  -- and needs the whole list at once — phase 44's.
  --
  -- **@prim-apply@ is not involved.** It claims holes and yields only the
  -- spine, so a body cannot reach them; here each claim is emitted and named,
  -- and @goto@ reaches it. Brady's arrangement rather than ours.
  --
  -- **@FILL@ is written out rather than reached through @unify-refine-core@**,
  -- which is @elaboration-in-rules.md@'s **gap 4** — /"Brady needs @FILL@ and
  -- @SOLVE@ separated, with the two @FOCUS@es between them"/. Splitting the
  -- rule turns out not to be needed to get it: the pieces are all ops, so the
  -- filling half is emitted here and the @prim-solve@ after the arguments.
  SurfaceApp h as
    | SurfaceArg Implicit _ <- NE.last as ->
        Left (NoElaborationRule "an implicit argument")
    | otherwise ->
        let front = NE.init as
            fun   = case front of
                      [] -> h
                      _  -> SurfaceApp h (NE.fromList front)
            SurfaceArg _ arg = NE.last as
            (l1, n1) = freshLevelMeta n
            (l2, n2) = freshLevelMeta n1
            nm k w   = Bind k (FreshName (lit' w))
         in Right
              ( concat
                  [ [ Bind (hereName names) Here
                    , nm (domName names ++ "n") "A"
                    , Bind (domName names)
                        (Claim (Ref (domName names ++ "n")) (lit (Universe (LVar l1))))
                    , nm (codName names ++ "n") "B"
                    , Bind (codName names)
                        (Claim (Ref (codName names ++ "n")) (lit (Universe (LVar l2))))
                    , Bind (arrName names) (Arrow (Ref (domName names)) (Ref (codName names)))
                    , nm (funName names ++ "n") "f"
                    , Bind (funName names)
                        (Claim (Ref (funName names ++ "n")) (Ref (arrName names)))
                    , nm (argName names ++ "n") "s"
                    , Bind (argName names)
                        (Claim (Ref (argName names ++ "n")) (Ref (domName names)))
                    , Bind (appName names)
                        (ApplyTo (Ref (funName names)) (Ref (argName names)))
                    ]
                    -- @FILL@: park it in a definition, unify its type with the
                    -- goal's, attach it. Thesis §2.7's @=@-binding, and the
                    -- reason it is a definition rather than a direct @try@ is
                    -- that @f s@'s type is @B@, a hole, and not yet the goal's.
                  , fill (Ref (appName names))
                    -- The two @FOCUS@es, and only then the @SOLVE@.
                  , [ Do (Goto (Ref (funName names)))
                    , Do (Elaborate (Lit (VSurface fun)))
                    , Do (Goto (Ref (argName names)))
                    , Do (Elaborate (Lit (VSurface arg)))
                    , Do (Goto (Ref (hereName names)))
                    , Do Solve
                    ]
                  ]
              , n2
              )

  -- @E⟦\ x => e⟧ = ATTACK; LAMBDA x; E⟦e⟧; SOLVE@ — Brady's λ case, and the
  -- first structural one this elaborator can do (MS4 phase 41b).
  --
  -- **One @prim-intro@ per binder, and each is given the SURFACE name.** That
  -- is what @prim-intro@'s optional operand is for: without it the binder keeps
  -- the identifier written in the /type/, so @\ y -> y@ at a goal
  -- @∀ (x : A) -> A@ would bind @x@ and the body's @y@ would resolve to
  -- nothing.
  --
  -- **Then @into@, then one @along@ per binder** — the navigation the phase-26
  -- mockup established and tested. It is counting structure rather than holding
  -- a handle, which is @elaboration-in-rules.md@'s gap 1; it is exact here
  -- because this clause knows how many binders it introduced.
  --
  -- **And the moves are undone before @prim-solve@**, which is the invariant
  -- every later case will lean on: **an @Elaborate@ leaves the focus where it
  -- found it.** The leaves do it by not moving at all — @prim-try@ and
  -- @prim-solve@ rewrite the focused component in place — and this clause does
  -- it by balancing its own moves.
  SurfaceLam bs body ->
    let names' = [ x | SurfaceBinder _ x _ <- NE.toList bs ]
     in case [ () | SurfaceBinder p _ ty <- NE.toList bs
             , p == Implicit || ty /= Nothing ] of
          _ : _ -> Left (NoElaborationRule "a lambda binder with a type or braces")
          []    -> Right
            ( concat
                [ [Bind (hereName names) Here, Do Attack]
                , [ Do (Intro (Just (lit' x))) | x <- names' ]
                , [Do Into]
                , replicate (length names') (Do Along)
                , [Do (Elaborate (Lit (VSurface body)))]
                , [Do (Goto (Ref (hereName names))), Do Solve]
                ]
            , n
            )
  SurfacePi {}    -> unsupported "a ∀"
  SurfaceArrow {} -> unsupported "an arrow"
  SurfaceLet {}   -> unsupported "a let"
  SurfaceAnnot {} -> unsupported "an ascription"
  SurfaceElim {}  -> unsupported "an elim"
  where
    -- Each node takes one tick of the counter for the names it binds.
    n     = n0 + 1
    names = namesFor n0

    -- @E⟦x⟧ = FILL x; SOLVE@ — and **@FILL@ is not @try@**.
    --
    -- @try@ /checks/ the term against the goal, so it needs the two types to
    -- match already; Brady's @FILL@ *"UNIFYs its type with the goal's"*. That
    -- is the difference between a leaf at a concrete goal — which is all
    -- @elab-var@ ever met — and one at a goal that is still a hole, which is
    -- exactly what the application case claims for its function and argument.
    -- So every leaf goes through the same filling sequence the application
    -- case does.
    attach t = Right (fill (lit t) ++ [Do Solve], n)

    -- Thesis §2.7's @=@-binding: park the term in a definition, unify the type
    -- it has with the type the hole wants, and only then attach it. What
    -- @unify-refine-core@'s body does, emitted rather than called, so that the
    -- application case can put its two @FOCUS@es before the @prim-solve@
    -- (@elaboration-in-rules.md@'s gap 4).
    fill t =
      [ Bind (refName names ++ "n") (FreshName (lit' "refined"))
      , Bind (refName names) (Define (Ref (refName names ++ "n")) t)
      , Bind (tyName names) (Typing (Ref (refName names)))
      , Bind (goalName names) Goal
      , Do (Unify (Ref (tyName names)) (Ref (goalName names)))
      , Do (Try (Ref (refName names)))
      ]
    lit' x   = Lit (VText x)

    -- The innermost binding of that name, if the context has one. The same
    -- reading "Thena.Syntax.Resolve" gives it, kept here rather than shared:
    -- that module is about @Raw@, and the two languages must not acquire a
    -- function in common.
    inContext :: String -> Maybe Var
    inContext x = foldl pick Nothing ctx
      where
        pick acc e
          | entryIdent e == Ident x = Just (entryVar e)
          | otherwise               = acc
    lit t    = Lit (VTerm (Trailing t))
    unsupported what = Left (NoElaborationRule what)
