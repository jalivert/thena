-- | The kernel: re-check a closed, pure core term against its stated type
-- (§5.3).
--
-- **Outside the layer stack.** Nothing in the project imports this module
-- except the driver, and this module imports only the core. It is called at
-- @qed@, before a theorem is admitted, and by the @certify@ command.
--
-- **It shares the core's reduction, conversion and typing** — decided by the
-- user 2026-08-22, and explicitly provisional: /"For now, kernel can share just
-- fine. Later, in future milestone when I need to, I will reimplement it."/ So
-- the body below is short, and the module boundary is what matters: the
-- signature and 'Thena.Errors.KernelError' are what a later reimplementation
-- must keep, and every caller already goes through them. **Do not inline this
-- into "Thena.Core.Typing" on the grounds that it is short.**
--
-- Be clear about what it buys, because "independent re-checker" overclaims
-- (§5.3). It gives independence from the **elaborator** — the tactic engine,
-- unification, the rule engine, every hole solution and every postponed
-- constraint — which is where the complexity and the bugs are. It does not
-- give independence from a bug in β, in conversion or in @infer@, because it
-- calls the same ones.
--
-- The global environment is **inside** the trust boundary (§5.3): @certify@
-- performs ι and δ unfolds globals, so it uses the generated eliminators and
-- the inductive declarations rather than re-deriving them.
module Thena.Kernel
  ( certify
  ) where

import Thena.Core.Level (Level, LevelVar, Obligation, solveLevels)
import Thena.Core.Term (Core, Var, beyond, freeVars, substLevelsIn)
import Thena.Core.Typing (check)
import Thena.Errors (KernelError (..), Position (..))
import Thena.Global.Env (GlobalEnv, varsInEnv)

-- | @certify env t ty@ — does @t@ really have type @ty@, trusting nothing the
-- elaborator produced?
--
-- **No 'Thena.Core.Context.Context' in the signature, because the term is
-- closed** (§5.3), and 'closed' below is what earns that: a 'Free' the caller
-- forgot to abstract would otherwise be reported by @infer@ as an unknown
-- variable, which is true but says nothing about /whose/ mistake it is. The
-- context reappears the moment @check@ descends under a Π or a λ, which is why
-- §3.2's type exists in the kernel whether or not the elaborator uses one.
--
-- **No counter in the signature either**, though @check@ threads one (§7.4).
-- A closed term is checked in an empty context, so the only variables minted
-- are @check@'s own and they cannot collide with anything the caller holds —
-- and unlike @infer@ at the REPL, nothing here is handed back to a session
-- that has to keep numbering monotonically. Starting from the term's own
-- highest variable is belt and braces for a term that has none.
-- **What it returns is the level solutions the check forced** (MS3 phase 33),
-- and they are the caller's to write back: the development the term was
-- extracted from still mentions the metas, and @qed@'s definition is stored
-- from that development, and the **residue** — the obligations that are neither
-- valid nor false, which are true of some levels and not others.
--
-- **The residue is not a refusal** (MS3 phase 33b). It is what the caller
-- generalises: @qed@ turns the term's remaining metas into the definition's
-- prenex level parameters and stores the residue as the scheme's constraints,
-- which every use site then instantiates and owes again. Both lists are empty
-- whenever no bare @Type@ was involved, which is every use of the kernel before
-- phase 33.
certify
  :: GlobalEnv -> Core -> Core
  -> Either KernelError ([(LevelVar, Level)], [Obligation])
certify env t ty = do
  closed t
  closed ty

  -- **Start the counter above every variable the environment holds**, not at
  -- zero (MS3 phase 31d).
  --
  -- Zero looks safe because 'closed' has just rejected a term with any free
  -- variable — but the **global environment is inside the trust boundary**
  -- (see this module's header), and a datatype's telescopes carry variables
  -- minted when it was declared. 'Thena.Global.Env.eliminatorType' reuses
  -- those *and* mints fresh ones beside them, so a checker counting from zero
  -- mints a variable a prelude datatype already owns, and 'close' captures it.
  --
  -- **This was a live bug**, found 2026-08-28: @fst@'s proof over @Sigma@ was
  -- accepted by @:infer@ (which counts from the machine's live counter) and
  -- refused by @qed@, with the motive substituted where a parameter belonged.
  -- It had nothing to do with levels — making the prelude's @Eq@ polymorphic
  -- shifted the numbering one place and moved @Sigma@'s parameters into range,
  -- which is all that changed.
  --
  -- **And the level obligations the check owed are collected here** (phase
  -- 33), for @revalidate@'s reason: re-checking regenerates precisely the ones
  -- the finished term owes, so there is nothing to have carried along.
  case check env [] (beyond (varsInEnv env)) t ty of
    (Left e,   _,    _) -> Left (Ill TheTerm e)
    (Right (), owed, _) -> case solveLevels owed of
      Left u                -> Left (Levels u)
      Right ([], residue)   -> Right ([], residue)

      -- **Something was solved, so the term is re-checked with it in place**
      -- rather than the check being argued to survive substitution. It is one
      -- extra pass, only when a bare @Type@ was written, and it terminates
      -- because every solution removes a meta.
      Right (sub, _) -> do
        (rest, residue) <- certify env (substLevelsIn sub t) (substLevelsIn sub ty)
        Right (sub ++ rest, residue)

-- | Nothing free, in either the term or its stated type.
closed :: Core -> Either KernelError ()
closed t = case freeVars t of
  x : _ -> Left (NotClosed (x :: Var))
  []    -> Right ()
