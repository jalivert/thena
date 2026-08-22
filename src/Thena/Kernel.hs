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

import Thena.Core.Term (Core, Var, freeVars)
import Thena.Core.Typing (check)
import Thena.Errors (KernelError (..), Position (..))
import Thena.Global.Env (GlobalEnv)

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
certify :: GlobalEnv -> Core -> Core -> Either KernelError ()
certify env t ty = do
  closed t
  closed ty
  case fst (check env [] 0 t ty) of
    Left e   -> Left (Ill TheTerm e)
    Right () -> Right ()

-- | Nothing free, in either the term or its stated type.
closed :: Core -> Either KernelError ()
closed t = case freeVars t of
  x : _ -> Left (NotClosed (x :: Var))
  []    -> Right ()
