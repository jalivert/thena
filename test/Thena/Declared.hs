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
  , packDecl
  , spanDecl
  , allDecl
  , afterDecl
  , beforeDecl
  , bothDecl
  , apartDecl
  , emptyDecl
  , eqDecl
  , unitDecl
  , andDecl
  , dpairDecl
  , preludeDecls
  , taplDecl
  , stepDecl
  , nat
  , natVec
  , natVecCounter
  , natFin
  , natFinCounter
  , natAnd
  , natAndCounter
  , eqNat
  , eqNatVec
  , eqNatVecCounter
  , eqNatFin
  , eqNatFinCounter
  , eqNatFinPack
  , eqNatFinPackCounter
  , eqNatVecSpan
  , eqNatVecSpanCounter
  , eqNatVecAll
  , eqNatVecAfter
  , eqNatVecBefore
  , eqNatVecBoth
  , eqNatVecApart
  , eqNatCounter
  , eqTapl
  , eqTaplCounter
  , eqStep
  , eqStepCounter
  , declared
  ) where

import Thena.Driver (parseDeclaration)
import Thena.Global.Declare (declare)
import Thena.Global.Env (GlobalEnv, emptyGlobals)

natDecl, vecDecl, finDecl, packDecl, spanDecl, emptyDecl :: String
allDecl, afterDecl, beforeDecl, bothDecl, apartDecl :: String
natDecl = "Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
vecDecl =
  "Vec (A : Type\8320) : Nat -> Type\8320 \
  \where { nil : Vec A zero \
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
  \where { fz : forall (n : Nat) -> Fin (succ n) \
  \; fs : forall (n : Nat) (i : Fin n) -> Fin (succ n) }"

-- | A constructor whose argument telescope is DEPENDENT — @i@'s type mentions
-- @n@ — over a datatype with __no indices__ (MS9 phase 215).
--
-- **The missing index is the whole point.** @fs@'s telescope is dependent too,
-- but its result type @Fin (succ n)@ pins its first argument, so an equation
-- between two @fs@ applications is well typed only when both name the same @n@
-- and injectivity's first equation is then a /deletion/ over a transported
-- chain, which is UIP. @Pack@ pins nothing, so the two sides may differ in the
-- first argument and the first equation is a solution — which is the case
-- "Thena.Tactics.Specialise" can discharge.
packDecl =
  "Pack : Type\8320 \
  \where { pack : forall (n : Nat) (i : Fin n) -> Pack }"

-- | A constructor argument that reaches back PAST another argument (MS9 phase
-- 216) — @e@'s type mentions @n@ and @as@, with @a@ sitting between @as@ and
-- @e@.
--
-- **The gap is the whole point.** The chain's package is a contiguous span, so
-- it holds @as; a; e@ and @a@ is /interior/ to it: the rest of the package is
-- transported along @a@'s own equation while nothing at all mentions @a@. A
-- no-confusion generator that decided the pair from the telescope — is this
-- argument mentioned later? — answered @And@ there and left @a@'s proof free in
-- the second conjunct, and the kernel refused the family it had built.
-- @Pack@ has no gap, which is why it was not enough to catch this.
spanDecl =
  "Span (A : Type\8320) : Type\8320 \
  \where { span : forall (n : Nat) (as : Vec A n) (a : A) \
  \(e : Eq {0} (Vec A n) as as) -> Span A }"

-- | 'spanDecl'\'s gap, over a family with an INDEX TELESCOPE and a RECURSIVE
-- argument (MS9 phase 223) — @examples\/vector-families.thena@\'s @All@, which
-- is where the gap was found.
--
-- **@Span@ does not cover it.** @Span@ has no recursive argument, so acyclicity
-- for it is trivial and the nested J has nothing to cross; @acons@ has one, and
-- its own argument @ps@ is what the acyclicity equipment is about. The package
-- is @as; ps@ with @a@ interior to it, and before phase 223 that withheld
-- @noCycleAll@ and with it the cycle transition for every family of the shape.
allDecl =
  "All (A : Type\8320) : forall (n : Nat) -> Vec A n -> Type\8320 \
  \where { anil : All A zero (nil A) \
  \; acons : forall (n : Nat) (as : Vec A n) (a : A) (ps : All A n as) \
  \-> All A (succ n) (cons A n a as) }"

-- | An index AFTER a dependent one (MS9 phase 223).
--
-- **The chain's package has to be moved by an equation stated after it was
-- built.** @as@ reaches back to @n@ and the family\'s own element reaches back
-- to @as@, so the two travel packaged; @m@ is quantified after them and the
-- element mentions it, so the package must be transported along @m@\'s equation
-- when the element is read out of it and not before. Every family of this shape
-- had its declaration refused — @noConfusionAfter does not typecheck@ — until
-- the package was moved lazily, one component at a time.
afterDecl =
  "After (A : Type\8320) : forall (n : Nat) -> Vec A n -> Nat -> Type\8320 \
  \where { amk : forall (n : Nat) (as : Vec A n) (m : Nat) -> After A n as m }"

-- | An index BEFORE the dependent one (MS9 phase 225).
--
-- **The smallest telescope the projections defect showed on**, and smaller than
-- the two-vector shape it was found next to: @as@ reaches back to @n@ with the
-- independent @m@ sitting between them, so the chain's package has a component
-- read out of it and is then transported again. The motive of that second
-- transport substituted the equations but not the component already projected,
-- which left @as@ bare at its old index.
beforeDecl =
  "Before (A : Type\8320) : forall (n : Nat) -> Nat -> Vec A n -> Type\8320 \
  \where { bmk : forall (n : Nat) (m : Nat) (as : Vec A n) -> Before A n m as }"

-- | TWO indices reaching back to the SAME earlier one (MS9 phase 226) — the
-- shape a family indexed by two vectors of one length has, and
-- @examples\/vector-families.thena@\'s @Pairwise@ is the same shape split on.
--
-- **Two components are read out of one package, and each one\'s projection
-- mentions the other\'s argument**: a projection names the package and the
-- package names every argument in it. So the chain\'s substitution is not a
-- fold in any order — abstracting @bs@ captured the @bs@ inside @as@\'s
-- projection, and the pack\'s type stood at the wrong index. Every family of
-- this shape was refused with @noConfusionDiv does not typecheck@.
bothDecl =
  "Both (A : Type\8320) : forall (n : Nat) -> Vec A n -> Vec A n -> Type\8320 \
  \where { tmk : forall (n : Nat) (as : Vec A n) (bs : Vec A n) \
  \-> Both A n as bs }"

-- | Two indices reaching back to one EACH (MS9 phase 226), which the same defect
-- refused for its second reason: the package is transported along @m@\'s
-- equation while @as@\'s projection, which mentions @bs@, is already in flight.
apartDecl =
  "Apart (A : Type\8320) : forall (n : Nat) (m : Nat) -> Vec A n -> Vec A m \
  \-> Type\8320 \
  \where { pmk : forall (n : Nat) (m : Nat) (as : Vec A n) (bs : Vec A m) \
  \-> Apart A n m as bs }"

-- | No constructors at all — the eliminator with no methods, which every other
-- fixture has at least one of.
emptyDecl = "Empty : Type where { }"

-- | The prelude's propositional equality, spelled out here rather than loaded.
--
-- Phase 14 needs it: no-confusion is generated only where an equation can be
-- stated, and these fixtures are prelude-free on purpose (phase 11). Declaring
-- it in a fixture is what lets a suite have both worlds — the environments
-- above have no @Eq@ and therefore no no-confusion, the ones below do.
eqDecl, unitDecl, andDecl, dpairDecl, taplDecl :: String
eqDecl =
  "Eq (A : Type) : A -> A -> Type \
  \where { refl : \8704 (a : A) -> Eq A a a }"

-- | The other two prelude types no-confusion is written out of (phase 20).
--
-- @Empty@ is 'emptyDecl' above, which predates them and is shared.
unitDecl = "Unit : Type where { unit : Unit }"
andDecl =
  "And (A : Type) (B : Type) : Type \
  \where { both : \8704 (a : A) (b : B) -> And A B }"

-- | The dependent pair the generated family pairs its equations in (MS9 phase
-- 212). Level-polymorphic in both components, which is what writing @Type@
-- twice gets.
dpairDecl =
  "DPair (A : Type) (B : A -> Type) : Type \
  \where { dpair : \8704 (a : A) (b : B a) -> DPair A B }"

-- | Everything 'Thena.Global.NoConfusion' can need, in the prelude's own order.
--
-- **@Eq@ first, then @DPair@, and @And@ after both**, because each one's own
-- no-confusion needs what precedes it: @And@ states equations, so it needs the
-- equality, and @both@ takes two arguments, so it needs the pair. The reverse
-- order costs @NoConfusionAnd@ silently.
preludeDecls :: [String]
preludeDecls = [eqDecl, dpairDecl, unitDecl, emptyDecl, andDecl]

-- | MS1's target language: TAPL chapter 3, the seven constructors determinacy
-- of evaluation is proved about (§9). @ifthen@ is the one with three arguments,
-- which is the case no other fixture has.
taplDecl =
  "Term : Type\8320 \
  \where { true : Term \
  \; false : Term \
  \; ifthen : Term -> Term -> Term -> Term \
  \; zero : Term \
  \; succ : Term -> Term \
  \; pred : Term -> Term \
  \; iszero : Term -> Term }"

-- | The @if@ fragment of TAPL\'s one-step evaluation relation (3.5.3), as an
-- inductively defined relation over 'taplDecl'\'s @Term@.
--
-- **Three rules, not the whole relation.** These are the ones @PLAN.md@ §3.7
-- works its elimination example on, and eliminating them at specific term
-- shapes is what phase 17 exists to do. The @succ@/@pred@/@iszero@ rules need
-- a numeric-value predicate and belong with phase 18, which declares the
-- relation for real; a fixture that guessed at them now would be a second
-- transcription to drift.
stepDecl :: String
stepDecl =
  "Step : Term -> Term -> Type\8320 \
  \where { eIfTrue : \8704 (t2 : Term) (t3 : Term) -> Step (ifthen true t2 t3) t2 \
  \; eIfFalse : \8704 (t2 : Term) (t3 : Term) -> Step (ifthen false t2 t3) t3 \
  \; eIf : \8704 (t1 : Term) (t1' : Term) (t2 : Term) (t3 : Term) (s : Step t1 t1') \
  \-> Step (ifthen t1 t2 t3) (ifthen t1' t2 t3) }"

-- | Declare a list of datatypes in order, threading the environment and the
-- name counter. A refusal is a fixture bug, not a test result, so it errors
-- loudly rather than quietly becoming an unrelated assertion failure.
declared :: [String] -> (GlobalEnv, Int)
declared = foldl one (emptyGlobals, 0)
  where
    one (env, n) src = case parseDeclaration [] env n src of
      Left e -> error ("fixture does not parse: " ++ show e)
      Right (d, n1) -> case declare env n1 d of
        Left e              -> error ("fixture refused: " ++ show e)
        Right (env', n2)    -> (env', n2)

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

-- | @Nat@ beside 'andDecl' — a datatype with two parameters and no index, which
-- is what it takes to instantiate a parameter with the datatype itself (MS9).
--
-- Prelude-free like the three above, so it carries no no-confusion: this one is
-- about ι and nothing else.
natAnd :: GlobalEnv
natAnd = fst (declared [natDecl, andDecl])

-- | Its counter, for the reason 'natVecCounter' gives.
natAndCounter :: Int
natAndCounter = snd (declared [natDecl, andDecl])

-- | The prelude and then @Nat@ — so @Nat@ arrives with @NoConfusionNat@ and
-- @noConfusionNat@ beside it (phase 14).
eqNat :: GlobalEnv
eqNat = fst (declared (preludeDecls ++ [natDecl]))

eqNatCounter :: Int
eqNatCounter = snd (declared (preludeDecls ++ [natDecl]))

-- | The prelude, @Nat@ and @Vec@ — @noConfusionNat@ beside an indexed family
-- whose index is a @Nat@, which is what specialisation by unification is worked
-- on (MS9 phase 177).
eqNatVec :: GlobalEnv
eqNatVec = fst (declared (preludeDecls ++ [natDecl, vecDecl]))

eqNatVecCounter :: Int
eqNatVecCounter = snd (declared (preludeDecls ++ [natDecl, vecDecl]))

-- | The prelude, @Nat@ and @Fin@ — a dependent argument telescope, which got no
-- no-confusion equipment at all before MS9 phase 212.
eqNatFin :: GlobalEnv
eqNatFin = fst (declared (preludeDecls ++ [natDecl, finDecl]))

eqNatFinCounter :: Int
eqNatFinCounter = snd (declared (preludeDecls ++ [natDecl, finDecl]))

-- | The prelude, @Nat@, @Fin@ and 'packDecl' — the environment injectivity over
-- a dependent argument telescope is worked on (MS9 phase 215). @Pack@ needs
-- @Fin@ to be a dependent telescope at all.
eqNatFinPack :: GlobalEnv
eqNatFinPack = fst (declared (preludeDecls ++ [natDecl, finDecl, packDecl]))

eqNatFinPackCounter :: Int
eqNatFinPackCounter = snd (declared (preludeDecls ++ [natDecl, finDecl, packDecl]))

-- | The prelude, @Nat@, @Vec@ and 'spanDecl' — a chain with an argument
-- /interior/ to its package, which generated a no-confusion family the kernel
-- refused until MS9 phase 216. @Span@ needs @Vec@ for an argument type that
-- mentions two earlier arguments at once.
eqNatVecSpan :: GlobalEnv
eqNatVecSpan = fst (declared (preludeDecls ++ [natDecl, vecDecl, spanDecl]))

eqNatVecSpanCounter :: Int
eqNatVecSpanCounter = snd (declared (preludeDecls ++ [natDecl, vecDecl, spanDecl]))

-- | The prelude, @Nat@, @Vec@ and 'allDecl' — 'spanDecl'\'s interior argument
-- over an indexed family with a recursive argument.
eqNatVecAll :: GlobalEnv
eqNatVecAll = fst (declared (preludeDecls ++ [natDecl, vecDecl, allDecl]))

-- | The prelude, @Nat@, @Vec@ and 'afterDecl' — an index after a dependent one.
eqNatVecAfter :: GlobalEnv
eqNatVecAfter = fst (declared (preludeDecls ++ [natDecl, vecDecl, afterDecl]))

-- | The prelude, @Nat@, @Vec@ and 'beforeDecl' — an index before a dependent one.
eqNatVecBefore :: GlobalEnv
eqNatVecBefore = fst (declared (preludeDecls ++ [natDecl, vecDecl, beforeDecl]))

-- | The prelude, @Nat@, @Vec@ and 'bothDecl' — two indices over one length.
eqNatVecBoth :: GlobalEnv
eqNatVecBoth = fst (declared (preludeDecls ++ [natDecl, vecDecl, bothDecl]))

-- | The prelude, @Nat@, @Vec@ and 'apartDecl' — two indices over one length each.
eqNatVecApart :: GlobalEnv
eqNatVecApart = fst (declared (preludeDecls ++ [natDecl, vecDecl, apartDecl]))

-- | The prelude and then MS1's target language.
eqTapl :: GlobalEnv
eqTapl = fst (declared (preludeDecls ++ [taplDecl]))

eqTaplCounter :: Int
eqTaplCounter = snd (declared (preludeDecls ++ [taplDecl]))

-- | The prelude, MS1's target language, and its evaluation relation — what
-- phase 17's elimination tactic is aimed at.
eqStep :: GlobalEnv
eqStep = fst (declared (preludeDecls ++ [taplDecl, stepDecl]))

eqStepCounter :: Int
eqStepCounter = snd (declared (preludeDecls ++ [taplDecl, stepDecl]))
