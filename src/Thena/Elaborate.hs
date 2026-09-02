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
import Thena.Development.Partial (Partial (..))
import Thena.Errors (FailReason (..), ResolveError (..), SyntaxError (..))
import Thena.Global.Env (GlobalEnv, isDeclared)
import Thena.Ops (Instr (..), Op (..), Operand (..), Value (..))
import Thena.Surface.Concrete (Surface (..))

-- | The program that elaborates one surface node into the focused hole.
--
-- Takes Γ at the focus and the name counter, exactly as the ops it emits do,
-- and hands back the counter it advanced — a universe whose level is left open
-- mints a meta.
--
-- **A node it cannot yet elaborate is a failure and not a silence.** That list
-- is phase 41b's specification.
compile :: GlobalEnv -> Context -> Int -> Surface -> Either FailReason ([Instr], Int)
compile env ctx n s = case s of
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

  SurfaceApp {}   -> unsupported "an application"
  SurfaceLam {}   -> unsupported "a lambda"
  SurfacePi {}    -> unsupported "a ∀"
  SurfaceArrow {} -> unsupported "an arrow"
  SurfaceLet {}   -> unsupported "a let"
  SurfaceAnnot {} -> unsupported "an ascription"
  SurfaceElim {}  -> unsupported "an elim"
  where
    attach t = Right ([Do (Try (lit t)), Do Solve], n)

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
