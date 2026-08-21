-- | Hand-built developments, shared by the tests.
--
-- **Built in Haskell, deliberately, not by parsing a string.** These are what
-- the parser and printer are tested against, so building them with the parser
-- would make the tests agree with themselves — the failure mode phase 2's §7
-- measured. Phases 5, 7 and 9 reuse them (`PREPLAN.md` phase 3).
module Thena.Fixtures
  ( idMidway
  , withConstraint
  , allFour
  , shadowedBinders
  , guessShadowing
  , trailingLam
  , richTypes
  ) where

import Thena.Core.Context (Entry (..))
import Thena.Core.Term
  ( Core (..)
  , Ident (..)
  , Level (..)
  , Var
  , close
  , fresh
  )
import Thena.Development.Component (Component (..))
import Thena.Development.Partial (Constraint (..), Partial (..))

type0 :: Core
type0 = Universe (Level 0)

-- | @A -> A@, a non-dependent 'Pi' over the given domain.
arrow :: Var -> Core -> Core
arrow spare dom = Pi (Ident "_") dom (close spare dom)

-- | The running example of §2.7.
idMidway :: Partial
idMidway =
  let (vA, n1)   = fresh 0
      (vId, n2)  = fresh n1
      (va, n3)   = fresh n2
      (vh, n4)   = fresh n3
      (spare, _) = fresh n4
      body =
        Under (Assume va (Ident "a") (Free vA))
          (Under (Claim vh (Ident "h") (Free vA))
            (Trailing (Free vh)))
   in Under (Assume vA (Ident "A") type0)
        (Under (Guess vId (Ident "id'") body (arrow spare (Free vA)))
          (Trailing (Free vId)))

-- | A chain carrying an undischarged constraint with a non-empty Ξ.
withConstraint :: Partial
withConstraint =
  let (vA, n1) = fresh 0
      (va, n2) = fresh n1
      (vh, n3) = fresh n2
      (vx, _)  = fresh n3
      xi       = [Hypothesis vx (Ident "x") (Free vA)]
   in Under (Assume vA (Ident "A") type0)
        (Under (Assume va (Ident "a") (Free vA))
          (Under (Claim vh (Ident "h") (Free vA))
            (Pending (Equate xi (Free vh) (Free vx) (Free vA))
              (Trailing (Free vh)))))

-- | One link of each kind, so the four-case display is exercised at once.
allFour :: Partial
allFour =
  let (vA, n1) = fresh 0
      (vd, n2) = fresh n1
      (vh, n3) = fresh n2
      (vg, _)  = fresh n3
   in Under (Assume vA (Ident "A") type0)
        (Under (Define vd (Ident "d") (Free vA) type0)
          (Under (Claim vh (Ident "h") (Free vA))
            (Under (Guess vg (Ident "g") (Trailing (Free vh)) (Free vA))
              (Trailing (Free vg)))))

-- | Two chain links with the same identifier, the body naming the OUTER one.
-- Unreachable from concrete syntax, and the case the printer must freshen.
shadowedBinders :: Partial
shadowedBinders =
  let (v1, n1) = fresh 0
      (v2, _)  = fresh n1
   in Under (Assume v1 (Ident "x") type0)
        (Under (Assume v2 (Ident "x") type0)
          (Trailing (Free v1)))

-- | A guess whose BODY binds the same identifier as the hole itself.
--
-- The hole is not in scope inside its own body (§4.5), so the body's binder
-- must NOT be freshened. Nothing else in this module can see that: it takes a
-- name collision across exactly that boundary to make the mistake observable,
-- and a printer that wrongly puts the hole in scope prints @x1@ here.
guessShadowing :: Partial
guessShadowing =
  let (vHole, n1) = fresh 0
      (vLam, _)   = fresh n1
   in Under (Guess vHole (Ident "x")
               (Under (Assume vLam (Ident "x") type0) (Trailing (Free vLam)))
               type0)
        (Trailing (Free vHole))

-- | A development whose component types have something in every core field.
--
-- Phase 5's core navigation needs one: a /dependent/ Π (so @cod@ opens a
-- binder), a @let@ (all three of @val@, @type@, @body@), an application (@fun@
-- and @arg@), and a λ in a definition's value, which is the only way to reach
-- one through @cross val@.
--
--   > λ (A : Type₀) ->
--   > λ (f : A -> A) ->
--   > let d = λ (z : A) -> z : A -> A in
--   > let ? h : ∀ (x : A) -> let y = x : A in f y in
--   > h
richTypes :: Partial
richTypes =
  let (vA, n1) = fresh 0
      (vf, n2) = fresh n1
      (vd, n3) = fresh n2
      (vz, n4) = fresh n3
      (vh, n5) = fresh n4
      (vx, n6) = fresh n5
      (vy, n7) = fresh n6
      (spare, _) = fresh n7
      a        = Free vA
      endo     = arrow spare a
      lamZ     = Lam (Ident "z") a (close vz (Free vz))
      letY     = Let (Ident "y") (Free vx) a (close vy (App (Free vf) (Free vy)))
      holeTy   = Pi (Ident "x") a (close vx letY)
   in Under (Assume vA (Ident "A") type0)
        (Under (Assume vf (Ident "f") endo)
          (Under (Define vd (Ident "d") lamZ endo)
            (Under (Claim vh (Ident "h") holeTy)
              (Trailing (Free vh)))))

-- | A 'Trailing' holding a binder. Without the corners this re-reads as a
-- chain link and print-then-read is not stable (§2.7).
trailingLam :: Partial
trailingLam =
  let (v, _) = fresh 0
   in Trailing (Lam (Ident "A") type0 (close v (Free v)))
