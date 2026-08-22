-- | The datatypes the core tests share, declared through the real front end.
--
-- Separate from "Thena.Fixtures", whose whole point is that its developments
-- are hand-built rather than parsed. These go the other way on purpose: they
-- are read with 'parseDeclaration' and admitted with 'declare', exactly as a
-- user would type them, so a mistake in the grammar, the resolver's arity
-- checks or phase 8's universe check shows up in whichever suite is running
-- rather than only in a hand-built record.
--
-- **One copy, because three suites need the same two datatypes.** Reduction,
-- conversion and typing must all agree about what @Nat@ and @Vec@ /are/; three
-- transcriptions of the same declaration could drift, and a drifting fixture
-- makes two suites pass about two different datatypes.
module Thena.Declared
  ( natDecl
  , vecDecl
  , finDecl
  , emptyDecl
  , eqDecl
  , taplDecl
  , nat
  , natVec
  , natVecCounter
  , natFin
  , natFinCounter
  , eqNat
  , eqNatCounter
  , eqTapl
  , eqTaplCounter
  , declared
  ) where

import Thena.Driver (parseDeclaration)
import Thena.Global.Declare (declare)
import Thena.Global.Env (GlobalEnv, emptyGlobals)

natDecl, vecDecl, finDecl, emptyDecl :: String
natDecl = "Nat : Type\8320 { zero : Nat ; succ : Nat -> Nat }"
vecDecl =
  "Vec (A : Type\8320) : Nat -> Type\8320 \
  \{ nil : Vec A zero \
  \; cons : forall (n : Nat) (a : A) (as : Vec A n) -> Vec A (succ n) }"

-- | Thesis §4.1.4's own example, and phase 10's reason for existing.
--
-- **Not a substitute for @Vec@ and not covered by it.** @Vec@ is a family of
-- datatypes with a parameter; @Fin@ is an inductive family with /no/ parameter
-- and an index that varies between a constructor's argument and its target —
-- @fs : Fin n -> Fin (succ n)@. So @Fin@ is what distinguishes an eliminator
-- that carries a recursive argument\'s /own/ indices into the inductive
-- hypothesis and the recursive call from one that reuses the target\'s
-- (`PREPLAN.md` phase 10: "@Nat@ alone will not catch it").
finDecl =
  "Fin : Nat -> Type\8320 \
  \{ fz : forall (n : Nat) -> Fin (succ n) \
  \; fs : forall (n : Nat) (i : Fin n) -> Fin (succ n) }"

-- | No constructors at all — the eliminator with no methods, which every other
-- fixture has at least one of.
emptyDecl = "Empty : Type\8320 { }"

-- | The prelude's propositional equality, spelled out here rather than loaded.
--
-- Phase 14 needs it: no-confusion is generated only where an equation can be
-- stated, and these fixtures are prelude-free on purpose (phase 11). Declaring
-- it in a fixture is what lets a suite have both worlds — the environments
-- above have no @Eq@ and therefore no no-confusion, the ones below do.
eqDecl, taplDecl :: String
eqDecl =
  "Eq (A : Type\8320) : A -> A -> Type\8320 \
  \{ refl : \8704 (a : A) -> Eq A a a }"

-- | MS1's target language: TAPL chapter 3, the seven constructors determinacy
-- of evaluation is proved about (§9). @ifthen@ is the one with three arguments,
-- which is the case no other fixture has.
taplDecl =
  "Term : Type\8320 \
  \{ true : Term \
  \; false : Term \
  \; ifthen : Term -> Term -> Term -> Term \
  \; zero : Term \
  \; succ : Term -> Term \
  \; pred : Term -> Term \
  \; iszero : Term -> Term }"

-- | Declare a list of datatypes in order, threading the environment and the
-- name counter. A refusal is a fixture bug, not a test result, so it errors
-- loudly rather than quietly becoming an unrelated assertion failure.
declared :: [String] -> (GlobalEnv, Int)
declared = foldl one (emptyGlobals, 0)
  where
    one (env, n) src = case parseDeclaration env n src of
      Left e -> error ("fixture does not parse: " ++ show e)
      Right (d, n1) -> case declare env n1 d of
        Left e              -> error ("fixture refused: " ++ show e)
        Right (env', n2, _) -> (env', n2)

nat, natVec, natFin :: GlobalEnv
nat    = fst (declared [natDecl])
natVec = fst (declared [natDecl, vecDecl])

-- | Its own environment rather than a third entry in 'natVec', because
-- 'natVecCounter' is what every hand-built context in the core suites starts
-- from: adding a declaration to that list shifts the counter and each of those
-- contexts silently starts numbering somewhere else.
natFin = fst (declared [natDecl, finDecl, emptyDecl])

-- | The counter after both declarations. Every hand-built context in the core
-- suites must start from this and never from 0: a declaration mints its own
-- formal variables, and a context numbered from scratch can collide with one by
-- coincidence and silently substitute the wrong occurrence (the incident is
-- recorded in "Thena.Core.ReduceTests").
natVecCounter :: Int
natVecCounter = snd (declared [natDecl, vecDecl])

-- | The same for 'natFin'.
natFinCounter :: Int
natFinCounter = snd (declared [natDecl, finDecl, emptyDecl])

-- | @Eq@ and then @Nat@ — so @Nat@ arrives with @NoConfusionNat@ and
-- @noConfusionNat@ beside it (phase 14).
eqNat :: GlobalEnv
eqNat = fst (declared [eqDecl, natDecl])

eqNatCounter :: Int
eqNatCounter = snd (declared [eqDecl, natDecl])

-- | @Eq@ and then MS1's target language.
eqTapl :: GlobalEnv
eqTapl = fst (declared [eqDecl, taplDecl])

eqTaplCounter :: Int
eqTaplCounter = snd (declared [eqDecl, taplDecl])
