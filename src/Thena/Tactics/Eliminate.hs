-- | The elimination tactic — §3.7's index-generalising motive (phase 17).
--
-- Given a goal @G@ and a term to eliminate, this builds the three things
-- thesis §3.6 calls a scheme, its subgoals and the proof: a motive that
-- generalises the target's indices and carries the equations that recover
-- their specificity, one method type per constructor, and the @Eliminate@ node
-- that proves @G@ from methods still to be filled in.
--
-- **It is one coarse operation, deliberately — decided by the user
-- 2026-08-23** (@AGENDA.md@ item 35). §7.2 grants MS1 the liberty of leaving a
-- whole tactic behind one 'Thena.Instral.Ops.Op', and this is the case it was granted
-- for: everything here is term construction over an 'InductiveDefinition', the
-- same kind of thing as 'Thena.Global.Env.eliminatorType' and
-- "Thena.Global.NoConfusion". A granular rule body would need a term-building
-- sub-vocabulary — motive assembly, telescope walking, @Eq@ application —
-- designed up front with nothing else asking for it, and §12 invariant 5
-- forbids exactly that.
--
-- **The limit on a dependent index telescope binds only a /tied/ index —
-- narrowed at phase 19.** An index whose type mentions an earlier one cannot be
-- equated, because the two sides of @Eq@ would be at two different types. But a
-- /friendly/ index states no equation at all, so it is abstracted and its type
-- is free to depend; the motive's own telescope carries the dependency, which
-- is what 'scheme' substitutes the earlier fresh index variables to build.
--
-- **AND A TIED ONE IS NOW STATED BY TRANSPORTING IT — MS9 phase 213.** §3.2 of
-- Cockx, Devriese and Piessens, /Pattern Matching Without K/, states a
-- telescopic equality homogeneously: @s; s̄ ≡ t; t̄@ is @(e : s ≡ t) (ē : e∗ s̄ ≡
-- t̄)@, each equation stated after transporting along the one before it. So the
-- carrier is the __actual__ earlier index rather than the generalised one, the
-- __actual side is left bare__ — it is where a copy or a constructor argument
-- stands, and @solution@ has to reach it — and the generalised side is carried
-- there by one J per earlier position its type mentions. Nothing heterogeneous
-- is declared and K is not assumed: @RULINGS.md@'s /Ruling of 2026-10-26/ is
-- why, and @DECISIONS.md@ has the public statement.
--
-- **For a family whose index telescope is not dependent the chain is empty**,
-- and every term this module generates for one is the term it generated before
-- the phase, byte for byte.
--
-- **A SPLIT ALSO GENERALISES THE AMBIENT ENTRIES ITS INDICES MENTION — MS9
-- phase 191.** A motive abstracts the target's /indices/, so a variable bound
-- before the target was never refined by a split and the equation about it was
-- handed to the user: @case e of { evs n en -> … }@ on @e : Ev (s m)@ got
-- @Eq N (s n) m@ instead of a goal with @m := s n@ in it, because @m@ is rigid
-- and no transition of "Thena.Tactics.Specialise" may move a rigid variable.
--
-- **The construction is to prove the more general thing and apply it to the
-- variable in hand.** The motive quantifies a /fresh copy/ of each such entry,
-- __placed after the target__, and states its equations about the copy; the use
-- site passes the real entry and @refl@. The copy is then one of the method's
-- own binders, which is the one place @solution@ can reach, so the four
-- existing transitions do the whole of the refinement and nothing in the kernel
-- or the development calculus changes.
--
-- **It is thesis §2.8, @Discharge@ and the permutations** — /"components may be
-- permuted in any way preserving dependencies; where dependency exists, reorder
-- anyway and account for it by introducing functional behaviour"/. The reorder
-- is the entry moving past the target, and the functional behaviour that
-- accounts for the dependency is the equation, discharged by @refl@ at the use
-- site. It is __not__ @raise@, which moves a binding the other way and hands
-- back the statement one started with.
--
-- **AND IT IS ONE OF TWO CONSTRUCTIONS THE CALLER ASKS FOR BY NAME — MS9 phase
-- 211, @~84x46@.** 'Premises' says whether the ambient entries are copied or
-- every premise stays fixed, and it is a parameter for the reason 'Scheme' is:
-- a method written by hand has no specialiser to solve the copies away, so it
-- asks for §3.7 and pays nothing. 'Premises' has the argument.
--
-- **The cheap case is subsumed rather than special-cased.** Where nothing the
-- arm needs mentions the entry the equation is pure noise — the thesis's
-- @delete-unused@ — and generalising gets that for free: the copy is
-- quantified, @solution@ fires, the binder is dropped and the goal never
-- mentioned it. One mechanism with a cheap case, not two that have to agree on
-- which applies.
--
-- **It computes; it does not touch the development.** What comes back is a list
-- of holes to claim and a term to attach, and "Thena.Engine" does both. That is
-- §7.4's rule about which operations take a 'Context' and which take the
-- development, applied: this one needs only what a core judgment can see.
--
-- Where it sits in §2.5: above "Thena.Core.Typing" and "Thena.Global.Env",
-- below "Thena.Engine" — the same slot as "Thena.Global.NoConfusion", which is
-- also a generator that has to typecheck what it builds. §2.5 gains the line.
module Thena.Tactics.Eliminate
  ( Elimination (..)
  , MethodShape (..)
  , Premises (..)
  , eliminate
  , spineOf
  ) where

import Data.List (nub)

import Thena.Core.Level (Level, instantiateLevels)
import Thena.Core.Context
  ( Context
  , Entry (..)
  , entryIdent
  , entryType
  , entryVar
  , lamOver
  , piOver
  )
import Thena.Core.Reduce (whnf)
import Thena.Core.Term
  ( Core (..)
  , substLevelsIn
  , GlobalName (..)
  , Ident (..)
  , Var
  , close
  , freeVars
  , fresh
  , instantiate
  , open
  )
import Thena.Core.Typing (check, infer, sortOf)
import Thena.Errors (ElimError (..))
import Thena.Global.Env
  ( GlobalEnv
  , ConstructorDefinition (..)
  , Definition (..)
  , InductiveDefinition (..)
  , Scheme (..)
  , caseName
  , eliminatorType
  , isDeclared
  , lookupConstructor
  , lookupDefinition
  , lookupInductive
  )

-- | What the tactic worked out: the subgoals, and the refinement.
--
-- 'elimMethods' is one entry per constructor, **in declaration order**, which
-- is the order 'Thena.Core.Term.Eliminate' expects its methods in. Each is a
-- hole the caller must put into the development /above/ the goal, so that the
-- goal can see it — the same placement 'Thena.Instral.Ops.Claim' already uses.
--
-- 'elimTerm' mentions those holes as @'Free' v@, so it is well typed only in a
-- context extended by them. 'eliminate' has already checked it there.
data Elimination = Elimination
  { elimMethods   :: [(Var, Ident, Core)]
  , elimTerm      :: Core
  , elimShape     :: MethodShape
    -- ^ what the motive added to every method of this elimination, and what the
    -- target was — see 'MethodShape'.
  }
  deriving (Eq, Show)

-- | **What the motive added to every method, and what the target was** — one
-- fact about every method of one elimination (MS9 phases 191, 192, 196).
--
-- __It is a type and not a tuple because nothing between the two ops reads
-- it.__ "Thena.Tactics.Specialise" is the only consumer; a rule takes
-- 'Elimination'\'s pair apart and threads this half whole. Five components
-- spelled out at every row of the signature table, and in three rule
-- signatures, said nothing a reader could use.
--
-- __Every component is something a method type cannot say.__ A method type is Π
-- binders all the way down: nothing in it marks where the constructor's own
-- telescope ends, which binders are the copies, which indices were abstracted
-- outright, or what the family's parameters were.
data MethodShape = MethodShape
  { shapeGeneralised :: [Ident]
    -- ^ the ambient entries this elimination __generalised__, in context order
    -- and under the names they already had (MS9 phase 191).
    --
    -- __Each is a further binder of every method__, standing before the
    -- equations, and the names are here because the caller binds them: an arm
    -- shadows the ambient entry with its own refined copy, which is how the
    -- body comes to be written against the refinement rather than against the
    -- equation. See the note on 'generalised' below.
  , shapeEquations :: Int
    -- ^ how many equations __each__ method carries — the number of /tied/
    -- indices, and the same for every method of one elimination (MS9 phase
    -- 177).
    --
    -- __It is here because nothing else can work it out.__ A method type is Π
    -- binders all the way down and does not say which of them are the
    -- equations; the count is what 'friendlyAt' decided, and
    -- "Thena.Tactics.Specialise" is the caller that needs it. So the op that
    -- /states/ the equations is what answers with how many it stated.
  , shapeFriendly :: [(Ident, Int)]
    -- ^ the ambient entries a /friendly/ index abstracted outright, each with
    -- the index position that abstracted it (MS9 phase 196).
    --
    -- __An arm has to bind these under the ambient names, exactly as it binds a
    -- solved copy__ (@~8v3pg@). A friendly index needs no equation because
    -- abstracting it already generalises everything that mentions it — but the
    -- entry it abstracted is still in the context under its own name, and the
    -- arm's goal is about the abstracted variable, so the name means the
    -- unrefined thing unless something binds it. There is no /copy/ on this
    -- path, so phase 195's two clauses have nothing to work from and this is
    -- what tells them.
    --
    -- __The position and not the term__: the term is the constructor's own
    -- index expression and differs per method, so only
    -- "Thena.Tactics.Specialise" — which has that method's binders — can write
    -- it down.
    --
    -- __And it may not be recomputed from the context later.__ 'friendlyAt'
    -- asks whether any /other/ entry mentions the variable, and by the time a
    -- method is being specialised the method holes are entries of that context
    -- and their types mention it through the motive. So the answer is recorded
    -- here, where it was decided.
  , shapeParameters :: [Core]
    -- ^ the family's parameters as the target supplied them (MS9 phase 196).
    --
    -- __Here for 'shapeFriendly' and the target's own rebinding__: a
    -- constructor's index expression is stated in the declaration's parameter
    -- variables, so writing one out at a method needs the substitution the
    -- scheme already made, and a method type does not carry it; and a
    -- saturated constructor application takes the parameters first.
  , shapeTargetNames :: [Ident]
    -- ^ every ambient name the __target__ is known by (MS9 phase 202,
    -- @~hc4ps@).
    --
    -- __The target is the other thing a split refines that is not a binder of
    -- the method.__ Inside a method it is the constructor applied to that
    -- method's arguments, so the entry the author named it by goes on being its
    -- old self at the old index and writing it in the arm was refused at the
    -- arm's own goal. The arm binds this name exactly as it binds a solved copy
    -- or a friendly index, and "Thena.Tactics.Specialise" writes the term,
    -- being the only thing that has this method's binders.
    --
    -- __It is a list because the split writes its own name for the target__ —
    -- @xsplit := d@ — and the author's @d@ is one step further out, so one
    -- name is never enough. It is 'targetVars', which is already the chain the
    -- scheme treats as the target, and it is empty where the target is not a
    -- bare variable: a compound target names no ambient entry.
  , shapeLevels :: [Level]
    -- ^ the family's level arguments as the target supplied them (MS9 phase
    -- 202). __Here for 'shapeTarget' and nothing else__: a saturated
    -- constructor application states them and a method type does not carry
    -- them.
  }
  deriving (Eq, Show)

-- | Whether the motive generalises the ambient entries, or leaves every premise
-- __fixed__ (MS9 phase 211, @~84x46@).
--
-- __The two are two constructions and not one with a preference.__ 'Fixed' is
-- §3.7 exactly — the motive abstracts the target and its indices, every premise
-- stays where it is, and an equation about a variable bound before the target is
-- stated and kept. 'Generalised' is that plus §2.8's permutation: the entries a
-- tied index mentions are copied after the target, the equations are about the
-- copies, and the use site discharges them with the entries themselves. The
-- module header has the construction.
--
-- __Which one a caller wants is decided by whether anything will solve the
-- copies.__ A surface split runs "Thena.Tactics.Specialise" over every method,
-- which solves each copy and drops its binder, so generalising costs the author
-- nothing and buys the refinement. A method written __by hand__ has no
-- specialiser behind it, so every copy is a binder its author has to take and
-- write the arm about — the cost @~84x46@ measured over 1190 lines of
-- @examples\/determinacy-tactics.thena.script@.
--
-- __It is a parameter for 'Scheme'\'s reason__, and not a mode: nothing
-- downstream can tell the results apart. Both build an ordinary
-- 'Thena.Core.Term.Eliminate' over an ordinary motive, both answer the same
-- pair, and the specialiser reads what the motive did from 'MethodShape' rather
-- than from which construction made it — under 'Fixed' 'shapeGeneralised' is
-- empty and every transition behaves as it did before phase 191.
data Premises
  = Fixed
    -- ^ §3.7's own scheme: the target and its indices, and nothing else
  | Generalised
    -- ^ … and a fresh copy, after the target, of every ambient entry a tied
    -- index mentions
  deriving (Eq, Show)

-- | Eliminate @target@ in service of @goal@ (§3.7).
--
-- The scheme is exactly §3.7's:
--
-- > P := λ i⃗ (x : D p⃗ i⃗) . Eq I₁ i₁ a₁ → … → Eq Iₙ iₙ aₙ → G[target := x, a⃗ := i⃗]
--
-- and the use site discharges the equations reflexively, so that @P a⃗ target@
-- applied to @refl …@ is @G@ again.
--
-- **The abstraction is what makes the induction worth doing**, and it is the
-- half of §3.7 that its displayed formula leaves implicit. Eliminating
-- @n : Nat@ in a goal that mentions @n@ is the case that forces it: @Nat@ has
-- no indices, so the equations are empty and abstracting the /target/ is the
-- only generalisation there is. Without it the motive is constant and each
-- method's induction hypothesis says nothing.
--
-- **A 'Scheme' says which eliminator, and that is the ONLY thing the two words
-- differ by** (MS9 phase 188). @induction … of@ builds an 'Eliminate' node;
-- @case … of@ applies the generated @caseD@ global, whose methods are the same
-- ones minus their inductive hypotheses. Everything above — the motive, the
-- equations, which indices are tied, the reflexivity at the use site — is
-- shared, because none of it has anything to do with hypotheses. So this is a
-- parameter rather than a second tactic, for the reason
-- 'Thena.Global.Env.Scheme' is a parameter rather than a second
-- @eliminatorParts@.
--
-- **The target is abstracted before the indices**, which is a real choice and
-- not an accident of order. If an occurrence of the target contains an index
-- expression, abstracting indices first rewrites inside it, and the occurrence
-- then no longer matches the target. Both orders are sound — the use site
-- substitutes everything back — but this one generalises more.
eliminate
  :: GlobalEnv -> Context -> Scheme -> Premises -> Int -> Core -> Core
  -> (Either ElimError Elimination, Int)
eliminate env ctx sch prem n0 goal tgt =
  -- **Level obligations are dropped here**, as everywhere outside the checking
  -- pass: "Thena.Core.Typing"'s header says why once, and @qed@ re-collects.
  case infer env ctx n0 tgt of
    (Left e, _, n1)    -> (Left (TargetNotTypeable e), n1)
    (Right tty, _, n1) -> case saturated (whnf env ctx tty) of
      Just (d, ls, ps, as) -> build d ls ps as n1
      Nothing          -> (Left (TargetNotInductive ctx tgt (whnf env ctx tty)), n1)
  where
    -- @D p⃗ a⃗@ for a declared @D@, with every parameter and index supplied.
    -- Under-application is not an elimination target: the eliminator is
    -- saturated (§3.6) and so is the family it eliminates.
    saturated ty = case spineOf ty of
      Just (dn, ls, args) -> do
        d <- lookupInductive dn env
        let np = length (inductiveParameters d)
            ni = length (inductiveIndices d)
        if length args == np + ni
          then let (ps, as) = splitAt np args in Just (d, ls, ps, as)
          else Nothing
      Nothing -> Nothing

    build d ls ps as n1
      | not (null as), Just missing <- undeclared = (Left (NoEquality missing), n1)
      | Just e <- dependentTied = (Left e, n1)
      -- **The level of each tied index's type** (phase 31d). @Eq@ is
      -- level-polymorphic, so @Eq Iₖ iₖ aₖ@ has to say which level @Iₖ@ lives
      -- at.
      --
      -- Read **here** and not inside 'scheme': here the type is read at the
      -- /actual/ indices, which are terms of @ctx@, where inside 'scheme' the
      -- same type also carries the motive's fresh binders, which are in no
      -- context at all. **It is the actual indices and not the parameters
      -- alone** (MS9 phase 213): a tied index's type may now mention an earlier
      -- index, and the declaration's own index variable is in no context either.
      | otherwise = case tiedLevels n1 of
          (Left e,    n) -> (Left (IndexTypeIllTyped e), n)
          (Right lvls, n) -> scheme d ls ps as tiedIx generalised lvls n
      where
        tiedLevels k0 = go tiedIx k0
          where
            go []       k = (Right [], k)
            go (i : is) k =
              case sortOf env ctx k (actualIxType i) of
                (Left e,  _, k1) -> (Left e, k1)
                (Right v, _, k1) -> case go is k1 of
                  (Left e,   k2) -> (Left e, k2)
                  (Right vs, k2) -> (Right (v : vs), k2)

        -- §3.7, decided 2026-08-11: @Eq@ and @refl@ are referred to **by
        -- name**. No designation table, no pragma, no shape check — they are
        -- expected to be there, and elimination fails if they are not. A name
        -- check gives a message worth reading; leaving it to the typechecker
        -- would report a missing global from inside a generated term.
        undeclared
          | not (isDeclared equality env) = Just equality
          | not (isDeclared reflexivity env) = Just reflexivity
          | otherwise = Nothing

        -- Thesis §3.5.2's "what to fix, what to abstract", answered one index
        -- at a time. An index the target supplies as a plain context
        -- /variable/ needs no equation: replacing its occurrences already
        -- generalises everything that mentions it, and applying the motive
        -- back at that very variable recovers the goal. Emitting one anyway
        -- is what killed the induction hypothesis — see the header.
        --
        -- Three conditions, each a case that breaks without it. The variable
        -- must be a 'Hypothesis', since a 'Definition' has a value that would
        -- be left behind. It must occur nowhere else in the family's own
        -- spine, or two abstractions race for the same occurrences —
        -- @e : Eq Nat a a@ is the case, and it must keep both equations. And
        -- no /other/ entry of the context may mention it: every premise stays
        -- fixed (§3.7), and a fixed premise still constraining the abstracted
        -- variable is exactly the specificity the equation existed to carry.
        --
        -- Decided here rather than in 'scheme' because it needs no fresh
        -- names, and the dependent-index refusal below is about /these/
        -- indices only.
        friendlyAt k a = case a of
          Free v ->
            isHypothesisOf v
              && not (any (\b -> v `elem` freeVars b) (ps ++ others k))
              && all (unmentioned v) ctx
          _ -> False
        others k = [ b | (j, b) <- zip [(0 :: Int) ..] as, j /= k ]
        isHypothesisOf v = or [ True | Hypothesis w _ _ <- ctx, w == v ]
        -- **An ALIAS of the index is not a premise about it** (MS9 phase 208,
        -- @~5kcb4@). Elaborating a name binds a copy of it, so a goal the user
        -- wrote in an argument position — @idT (R a c) (case q of …)@ — arrives
        -- as @R a2 a3@ over @a2 := a@ and @a3 := c@, and those two definitions
        -- mention the indices. Counting them as fixed premises tied every index
        -- the goal names: with two of them the specialiser solves one equation
        -- by the method's own binder and the second is left between two ambient
        -- variables, which is rigid and reaches every arm. 'namesFor' is the
        -- same walk 'targetChain' is, in both directions, because an alias is
        -- not a premise constraining the index — it IS the index.
        unmentioned v e =
          entryVar e == v
            || entryVar e `elem` targetVars
            || entryVar e `elem` namesFor v
            || v `notElem` entryUses e

        -- Which indices keep an equation, and which are simply abstracted.
        tiedIx = [ k | (k, a) <- zip [(0 :: Int) ..] as, not (friendlyAt k a) ]

        -- **Which ambient entries this split generalises** (MS9 phase 191,
        -- `~6dpg5`) — the entries whose fresh copies the motive quantifies, in
        -- context order, which is the order their types depend on each other
        -- in. The module header has the construction and why it is §2.8.
        --
        -- __The seeds are the ambient variables a TIED index mentions__, and
        -- only a tied one: a friendly index is a variable abstracted outright
        -- and there is nothing left to refine. Then the __forward closure__,
        -- which is the thesis's own dependency-preservation condition read as a
        -- rule: an entry whose type mentions a generalised variable is itself
        -- generalised, or its copy would be about a variable that no longer
        -- means what it meant. @usesHyp@ is the case — generalising @m@ without
        -- @h : Ev m@ leaves the arm a hypothesis it cannot use.
        --
        -- __IT IS UNCONDITIONAL UNDER 'Generalised', AND THAT IS WHY THERE IS A
        -- 'Fixed' — `~6dpg5`'s measurement, and `~84x46`'s answer to it.__ A copy
        -- is made for every seed, including one whose refinement nothing but the
        -- equation reads: making it is what turns a stuck equation into a solved
        -- one, so there is no seed this closure is free to skip. What is not free
        -- is the caller with no specialiser behind it. In a split
        -- "Thena.Tactics.Specialise" solves the copy and drops the binder, so the
        -- arm never sees it; a method written __by hand__ pays for every copy in
        -- binders, which is what @eliminate-core@ asks 'Fixed' for.
        --
        -- __TWO QUESTIONS, AND THEY ARE ASKED IN TWO PLACES — MS9 phase 197,
        -- `~k54hh`.__ /Which/ ambient entries may be copied is 'generalisable',
        -- which skips the ones that may not; /whether the scheme can state the
        -- copies it found/ is 'viable', and a failure there cancels the lot,
        -- leaving the split behaving exactly as it did before phase 191 — the
        -- equation stated and kept. They were one all-or-nothing test until
        -- phase 197, and that is what shut `~k54hh`: a definition the split did
        -- not put in the context cancelled every copy.
        generalised = case prem of
          Fixed       -> []
          Generalised -> if viable then closed else []
          where
            -- A friendly index's variable is abstracted outright, so it is
            -- neither a seed nor a reader nor part of the closure.
            friendlies = [ v | (k, a) <- zip [(0 :: Int) ..] as
                             , friendlyAt k a
                             , Free v <- [a] ]

            -- __WHAT THIS SPLIT MAY GENERALISE AT ALL, and it is the ONE
            -- place that decides it — MS9 phase 197, `~k54hh`.__ The target and
            -- a friendly index's variable are already abstracted, so a copy of
            -- either would be a second abstraction of the same occurrences; and
            -- only a 'Hypothesis' can be copied, since a 'Definition' has a
            -- value its copy would lose.
            --
            -- __A 'Definition' is SKIPPED here and does not cancel the
            -- generalisation, which is the whole of `~k54hh`.__ The condition
            -- used to be tested after the fact, in @viable@, so one definition
            -- anywhere in the forward closure cancelled every copy. The
            -- context is full of definitions this split did not put there —
            -- the arm's rebinding of an ambient name (@~8v3pg@), the target's
            -- own @xsplit@, and __the solved components of the ARM BEFORE this
            -- one__ — and the measurement is that the last of those is what
            -- shut `~k54hh`: at the inner split of
            --
            -- > p8 = \ n x u -> induction x of
            -- >   { az -> \ f -> case f of { }
            -- >   ; as k p -> \ f -> case f of { fs j m r -> m } }
            --
            -- the ambient @u@ /is/ a hypothesis, /is/ a seed and /is/ in the
            -- closure. What failed was @azMethod@ and @azCase@, the @az@ arm's
            -- own solved definitions, whose types mention @u@ because the
            -- statement's @f : F n u@ is in them. Nothing a later arm proves is
            -- a premise of this one, and skipping a definition leaves it exactly
            -- as it was — the pre-phase-191 behaviour for that entry, and no
            -- worse for anything else.
            generalisable e =
              isHypothesis e
                && entryVar e `notElem` targetVars
                && entryVar e `notElem` friendlies

            -- __A VARIABLE THAT SITS INSIDE A TIED INDEX, which the closure may
            -- not drag in — MS9 phase 210, @~5kcb4@.__ The equation for a tied index is stated at the
            -- index with the generalised entries replaced, so copying something
            -- the index /mentions/ states the equation about a copy — and a copy
            -- is quantified after the constructor's telescope, so the only
            -- solution left points forwards and @~cq5mt@ is what that costs.
            --
            -- @d1 : sub G S ‹Z›@ is the case. @Z@ is not the index; the index is
            -- @tvar Z@, and @Z@ arrives in the closure backwards, from
            -- @d2 : sub G ‹Z› T@ which phase 209 seeds. Copying it turns
            -- @SA-Trans-TVar@'s equation into @Eq Ty T1 (tvar Z')@ over a copy
            -- bound after @T1@, where before it was @Eq Ty T1 (tvar Z)@ over an
            -- ambient variable and @T1 := tvar Z@ fired —
            -- @stuck: T1 and Ty`${a6}` cannot be made equal@.
            --
            -- __An index that IS a bare variable is not in question__, and
            -- generalising that one is the whole of phase 191: there the copy is
            -- the only thing a solution can reach. The distinction is therefore
            -- between being an index and being inside one, which is the same
            -- line 'demandedAt' already draws position by position.
            --
            -- __A SEED OVERRIDES IT, and that is measured.__ The same variable
            -- can be bare at one index position and inside a term at another —
            -- @examples\/determinacy-patterns.thena@ splits a step whose indices
            -- are @p@ and @ifthen p p2 p3@ — and there the demand test has
            -- already said the copy is the only thing a solution can reach.
            -- Without the override that file loses two arms:
            -- @stuck: p and true cannot be made equal@.
            insideTied =
              nub [ v | k <- tiedIx
                      , Just a <- [atIx k as]
                      , not (bareVar a)
                      , v <- freeVars a ]
            bareVar a = case a of
              Free _ -> True
              _      -> False
            atIx k xs = case drop k xs of
              x : _ -> Just x
              []    -> Nothing

            isHypothesis e = case e of
              Hypothesis {} -> True
              Definition {} -> False

            -- __THE SEEDS ARE THE ENTRIES SOME METHOD CANNOT DO WITHOUT, not
            -- every ambient variable a tied index mentions.__ His question,
            -- 2026-10-20: only prove the stronger thing where it has to be
            -- proved. Position by position, the constructor's own index against
            -- the target's:
            --
            --   * the constructor's side is one of ITS OWN argument variables —
            --     @ePred c1@ against @pred (succ v)@ — and @solution@ removes
            --     that binder with no copy in sight. __Nothing is demanded__,
            --     and demanding it is what cost two arms of
            --     @examples\/determinacy-patterns.thena@: the copy is bound
            --     after @c1@, so @c1 := succ v9@ points backwards.
            --   * the target's side is a bare ambient variable facing anything
            --     else — @true@ against @p@ — and __the copy is the only thing
            --     a solution can reach__, which is the whole reason copies
            --     exist. That position demands it.
            --   * both are constructor applications: the same former recurses,
            --     different formers is a conflict and demands nothing.
            --
            -- __Erring narrow is the safe direction.__ Generalising something no
            -- method needed is what broke working proofs; failing to generalise
            -- something a method did need leaves the equation standing, which is
            -- exactly the behaviour that preceded this phase.
            -- __AND THE TARGET IS ALWAYS A SEED — MS9 phase 206, @~pmpqg@,
            -- his ruling of 2026-10-22.__ A premise whose type mentions the
            -- target has to be refined with it, exactly as a premise mentioning
            -- an index is, or the arm holds a fact about a subject it can no
            -- longer even name — the arm rebinds the author's name for the
            -- target to the constructor (@~hc4ps@). It is what matching a
            -- pattern means: @l := ln@ reaches the goal and every premise after
            -- it.
            --
            -- __It is UNCONDITIONAL where an index's is demand-tested, and the
            -- asymmetry is not an oversight.__ The demand test exists because a
            -- copy for an index carries an @Eq@ the specialiser may be unable to
            -- reach, and a copy made for nothing is bound after the constructor's
            -- own arguments where a solution would point backwards. The target
            -- carries no equation at all: it is the eliminator's own final
            -- argument, abstracted outright, and each method simply /is/ the
            -- constructor. So there is nothing to state an equation about and
            -- nothing for a copy about it to point backwards at.
            --
            -- __The chain and not 'targetVars'__, for 'tgtSubst''s reason: a
            -- copy is what carries a premise whose bare type is the target.
            -- 'generalisable' still refuses a copy of the target's own entries,
            -- which are abstracted outright and would otherwise be abstracted
            -- twice.
            --
            -- __AND IT IS THE PREMISES THAT ARE SEEDED, NOT THE TARGET
            -- ITSELF — measured, and seeding the target broke 16 assertions.__
            -- 'grow' closes backward as well as forward (@~754m3@), and
            -- backward from the target is wrong for the reason the target is
            -- not copied at all: @d : Step (ifthen true t2 t3) u@ would drag
            -- @t2@, @t3@ and @u@ into the closure because the TARGET's type
            -- mentions them, which is §3.7's own worked example and generalises
            -- what no method asked for. A copy's backward closure exists so a
            -- copy is not pinned to an entry that stayed behind; the target
            -- stays behind on purpose.
            aboutTarget = [ entryVar e
                          | e <- ctx
                          , generalisable e
                          , any (`elem` freeVars (entryType e)) targetChain
                          ]

            -- __AND A PREMISE ABOUT AN INDEX IS REFINED WITH IT, FOR THE
            -- SAME REASON — MS9 phase 208, @~5kcb4@.__ @~pmpqg@'s ruling was
            -- about the target; the index half of it was still open, and
            -- 'demandedAt' does not answer it. That test asks what a /method/
            -- cannot do without, which is a question about the index's own copy;
            -- whether an ARM can use a premise stated about the index is a
            -- different question, and the answer is the same as for the target.
            --
            -- @\ a c dq q -> case q of { refl u -> … dq … }@ over
            -- @dq : Eq Comparison (eqString a c) different@ is the case: nothing
            -- demands @a@ or @c@, because @refl@'s index is its own argument at
            -- both positions, so @dq@ stayed at @eqString a c@ while the arm's
            -- own subject is @u@ — @stuck: c and a cannot be made equal@, and
            -- the lemma cannot be written at all.
            --
            -- __It seeds the premise and not the index__, exactly as
            -- 'aboutTarget' does, and for the same measured reason. The index's
            -- own copy then comes from the backward closure where the equation
            -- needs it and from 'friendlies' where it does not, so the two cases
            -- sort themselves out rather than being told apart here.
            aboutIndex = [ entryVar e
                         | e <- ctx
                         , generalisable e
                         , any (`elem` indexVars) (freeVars (entryType e))
                         ]
            indexVars = [ v | Free v <- as ]

            seeds = nub (aboutTarget
                      ++ aboutIndex
                      ++ [ v | k <- tiedIx
                             , c <- inductiveConstructors d
                             , v <- demandedAt c k ++ recursionDemandsAt c k
                             , v `notElem` targetVars
                             , v `notElem` friendlies ])

            -- __AND THE RECURSION DEMANDS WHAT NO ARM DOES — MS9 phase 205,
            -- `~wk9qh`.__ 'demandedAt' above asks what a /method/ cannot do
            -- without, and that is not the whole of the question: the induction
            -- hypothesis is the motive applied at a recursive premise's indices,
            -- so where a constructor's recursive premise sits at a /different/
            -- index than its own conclusion, the hypothesis is stated at a term
            -- the ambient entry cannot be, and only a copy can carry it.
            --
            -- @tl : forall (g : N) (p : T (s g)) -> T g@ is the case: the
            -- premise is at @s g@ and the conclusion at @g@, so a recursion
            -- gets @Eq N (s g0) g -> …@, which nothing can discharge. Three
            -- probes and a four-declaration fixture are in `~wk9qh`'s brief.
            --
            -- __It is the SAME positional test, asked of the premise's indices
            -- instead of the conclusion's__, and that is what keeps it from
            -- demanding a copy where the hypothesis is usable without one:
            -- @vcons@'s premise sits at its own argument @n@, so @vtail@ demands
            -- nothing and @EliminateTests@ still says so.
            --
            -- __It is asked per position, only of a recursive premise, and only
            -- under @induction@__: a case analysis offers no hypothesis at all,
            -- so there is nothing for a copy to let vary, and demanding one there
            -- is what broke @examples\/normal.thena@ when this was first
            -- measured. A family that does not recurse at that index demands
            -- nothing new either, and the narrow rule stands unchanged.
            recursionDemandsAt c k
              | CaseAnalysis <- sch = []
              | otherwise = concat [ walkAt c i (as !! k)
                                   | is <- recursivePremiseIndices c
                                   , i  <- take 1 (drop k is) ]

            -- The index expressions of each argument of @c@ whose type is this
            -- same family — the premises an induction hypothesis is offered for
            -- — with the family's parameters replaced by the target's, which is
            -- the substitution 'conIndex' makes for the conclusion's.
            -- Parameters dropped, as everywhere else here.
            recursivePremiseIndices c =
              [ map (substVars psub) (drop (length (inductiveParameters d)) args)
              | e <- constructorArguments c
              , Just (g, _, args) <- [spineOf (whnf env ctx (entryType e))]
              , g == inductiveName d
              ]
              where psub = zip (map entryVar (inductiveParameters d)) ps

            demandedAt c k = walkAt c (conIndex c k) (as !! k)

            -- __ONE POSITIONAL TEST, TWO SOURCES OF INDEX EXPRESSION.__ The
            -- constructor's side against the target's: where the constructor's
            -- side is one of its own argument variables a @solution@ removes
            -- that binder and nothing is demanded; where the target's side is a
            -- bare ambient variable only a copy is something a solution can
            -- reach; the same former recurses and different formers conflict.
            -- 'demandedAt' asks it of the constructor's /conclusion/ and
            -- 'recursionDemandsAt' of each recursive /premise/ — see the note
            -- on the latter for why both are needed.
            walkAt c = walk
              where
                argv = map entryVar (constructorArguments c)
                walk ic it
                  | Free w <- whnf env ctx ic, w `elem` argv = []
                  | Free v <- whnf env ctx it                = [v]
                  | Just (gc, acs) <- constructed ic
                  , Just (gt, ats) <- constructed it
                  , gc == gt = concat (zipWith walk acs ats)
                  | otherwise = []

            -- The constructor's own index expression for position @k@, with the
            -- family's parameters replaced by the target's — the same
            -- substitution 'tiedIndexTypes' makes.
            conIndex c k =
              substVars (zip (map entryVar (inductiveParameters d)) ps)
                        (constructorIndices c !! k)

            -- A saturated constructor application, __parameters dropped__,
            -- because they are the same on both sides and comparing them would
            -- demand a copy for nothing.
            constructed t = case spineOf (whnf env ctx t) of
              Just (g, _, args) -> case lookupConstructor g env of
                Just (dd, _) -> Just (g, drop (length (inductiveParameters dd)) args)
                Nothing      -> Nothing
              Nothing -> Nothing

            -- In context order, whatever order the closure found them in.
            closed = [ entryVar e
                     | e <- ctx
                     , generalisable e
                     , entryVar e `elem` grow seeds
                     , entryVar e `elem` seeds
                         || entryVar e `notElem` insideTied
                     ]


            -- __AND IT CLOSES BOTH WAYS — MS9 phase 199, `~754m3`.__ Forward
            -- is the thesis's dependency-preservation condition: an entry whose
            -- type mentions a generalised variable is generalised too, or its
            -- copy would be a hypothesis about a subject that no longer means
            -- what it meant. __Backward is the same condition read from the
            -- other end__, and leaving it out is what made a recursion
            -- impossible to write: a copy whose type mentions an ambient entry
            -- that was /not/ copied is pinned to that entry, so the induction is
            -- over something less general than the entries describe.
            --
            -- @p12@ is the case, and it is measured:
            --
            -- > p12 = \ n x u f -> induction x of
            -- >   { az -> case f of { }
            -- >   ; as k p -> case f of { fs j m r -> p12 k p m r } }
            --
            -- The tied index seeds @n@; forward from @n@ takes @f : F n u@; and
            -- @u@ is left behind, so the hypothesis is @∀ n' (f' : F n' u) -> …@
            -- about the ambient @u@ — which the inner split has refined to
            -- @s m@, while the recursion needs the hypothesis at @m@. **The
            -- hypothesis the proof needs does not exist in the arm**, and no
            -- amount of work at the call could have found it. With @u@ copied it
            -- does, and @nvNoStep@ with its four premises written at the top is
            -- the same shape in @examples\/determinacy-patterns.thena@.
            --
            -- __What makes it the right rule rather than a wider one__: the
            -- copies are a sub-telescope the motive moves (§2.8), and a
            -- telescope that mentions what it did not take is not a telescope
            -- you can instantiate on its own. Generalising /everything/
            -- generalisable is the wider rule, and @~cq5mt@ measured what it
            -- costs. The closure is the smallest set that is closed under
            -- dependency, which is what @~6dpg5@ asked for in the first place.
            --
            -- __THE CLOSURE TESTS AN ENTRY'S TYPE AND NOT ITS VALUE — MS9
            -- phase 196.__ The condition it stands for is about types: an
            -- entry whose /type/ mentions a generalised variable would be a
            -- hypothesis about a subject that no longer means what it meant. A
            -- 'Definition' whose /value/ mentions one is a different thing —
            -- its type does not move, so the motive has nothing to preserve
            -- about it, and it stays itself.
            --
            -- __And testing the value made a split undo the one around it.__
            -- An arm binds the ambient names a split refined (@~8v3pg@), which
            -- puts definitions in the context; the first of those to mention a
            -- seed pulled itself into the closure, failed the 'Hypothesis' test
            -- and so cancelled the generalisation outright.
            -- @examples\/determinacy-patterns.thena@ measured it: @p@ stopped
            -- being refined to @true@ the moment the outer split bound @t@.
            -- Testing the type instead fixed /that/ shape; what was left is the
            -- definition whose own TYPE mentions a seed, and 'generalisable' is
            -- where that one stops cancelling.
            grow vs =
              let vs' = nub (vs ++ reads' ++ read')
               in if length vs' == length vs then vs else grow vs'
              where
                -- An entry whose type mentions one of these.
                reads' = [ entryVar e
                         | e <- ctx
                         , generalisable e
                         , any (`elem` freeVars (entryType e)) vs
                         ]
                -- An entry one of these mentions in its type.
                read' = [ entryVar e
                        | e <- ctx
                        , generalisable e
                        , f <- ctx
                        , entryVar f `elem` vs
                        , entryVar e `elem` freeVars (entryType f)
                        ]

            -- __WHETHER THE SCHEME CAN STATE THE COPIES, and nothing about
            -- which entries they are__ — that is 'generalisable''s, and the two
            -- were one test until MS9 phase 197. Both of these are ways the
            -- motive would not typecheck rather than preferences: a generalised
            -- variable may not occur in the family's /parameters/, which the
            -- scheme fixes, nor in the /type/ of a tied index, or @Eq Iₖ iₖ aₖ@
            -- would have its two sides at two different types — the same limit
            -- 'dependentTied' states one step over. Where one fails, nothing is
            -- generalised and the split behaves as it did before phase 191.
            viable =
              not (null closed)
                && not (any (`elem` concatMap freeVars ps) closed)
                && not (any (`elem` concatMap freeVars tiedIndexTypes) closed)

            tiedIndexTypes =
              [ substVars (zip (map entryVar (inductiveParameters d)) ps)
                          (entryType (inductiveIndices d !! k))
              | k <- tiedIx
              ]

        -- The declaration's own index variables, and one index's type with the
        -- family's parameters replaced by the target's — the two things every
        -- question about the index telescope is asked in terms of.
        ixVars = map entryVar (inductiveIndices d)
        paramSub = zip (map entryVar (inductiveParameters d)) ps
        ixType j = substVars paramSub (entryType (inductiveIndices d !! j))
        -- … and the same with the /earlier actual/ indices put in, which is
        -- where a tied index's equation is carried and so where its level is
        -- read.
        actualIxType j =
          substVars (paramSub ++ zip (take j ixVars) (take j as))
                    (entryType (inductiveIndices d !! j))
        -- Which earlier index positions a tied index's type mentions.
        mentionedBy k = [ j | j <- [0 .. k - 1], (ixVars !! j) `elem` freeVars (ixType k) ]

        -- §3.7's limit, and __it is now the limit of a TRANSPORTED equation__
        -- (MS9 phase 213, @~7gmvr@ step two). @Eq Iₖ iₖ aₖ@ is homogeneous, so
        -- where @Iₖ@ mentions an earlier index the two sides stand at two
        -- different types — and the remedy is §3.2 of /Pattern Matching Without
        -- K/ rather than \"John Major\" equality: state the equation at the
        -- __actual__ earlier indices and carry the generalised side there along
        -- the earlier equations. 'scheme' builds that chain; a /friendly/ index
        -- still states no equation at all, and its type was always free to
        -- depend.
        --
        -- __Two shapes are left, and both are a missing step of the chain
        -- rather than a missing equality.__
        --
        --   * the mentioned index is __friendly__ — abstracted outright, with no
        --     equation to transport along. @b : Below n (fz m)@ is the case:
        --     @n@ is a bare variable, so index 1 is abstracted, and
        --     @Eq (Fin i₁) i₂ (fz m)@ would ask @fz m@ to inhabit @Fin i₁@ for
        --     an @i₁@ nothing constrains.
        --   * two mentioned indices are __chained__ — @Iₖ@ mentions both @j@ and
        --     @m@ while @Iₘ@ mentions @j@ — and then transporting past @j@
        --     leaves the binder at @m@ typed at the old @j@. The paper's answer
        --     is a motive that abstracts the /proof/ as well as the endpoint,
        --     which is the packaged telescopic equality these phases do without.
        dependentTied = firstJust [ dependent k | k <- tiedIx ]
        dependent k
          | null untransportable = Nothing
          | otherwise = Just (IndexTypeDepends (k + 1) (entryIdent (inductiveIndices d !! k)))
          where
            ms = mentionedBy k
            untransportable =
              [ j | j <- ms, j `notElem` tiedIx ]
                ++ [ j | j <- ms, i <- ms, i < j, (ixVars !! i) `elem` freeVars (ixType j) ]
        firstJust xs = case [ x | Just x <- xs ] of
          x : _ -> Just x
          []    -> Nothing

    scheme d ls ps as tiedIx gen tiedLvs n1 =
      let ni = length as

          -- One fresh variable per index, plus the motive's own target binder.
          (ivs, n2) = freshen ni n1
          (xv,  n3) = fresh n2

          -- One fresh copy per generalised ambient entry (MS9 phase 191).
          (gvs, n3') = freshen (length gen) n3

          -- What the motive says about an ambient entry, it says about the
          -- copy: the goal, and the index expressions the equations are stated
          -- at. The use site undoes it by passing the entry itself.
          genSubst = [ (v, Free gv) | (v, gv) <- zip gen gvs ]

          -- The copies as a telescope, each one's type carrying the __earlier__
          -- copies, which is what makes a chain like
          -- @(p' : Term) (s' : Step p' q)@ expressible — the same reason
          -- 'indexTys' substitutes the earlier index binders below.
          --
          -- __Under the entry's own 'Ident'__, because the caller binds an arm's
          -- copy by that name and so shadows the entry it came from.
          genEntries =
            [ Hypothesis gv (entryIdent e)
                           (substVars (tgtSubst ++ take j genSubst) (entryType e))
            | (j, (v, gv)) <- zip [(0 :: Int) ..] (zip gen gvs)
            , e            <- [ x | x <- ctx, entryVar x == v ]
            ]

          -- __Every ambient name the target is known by becomes the motive's
          -- own target binder — MS9 phase 206, @~pmpqg@, his ruling of
          -- 2026-10-22.__ 'replaceTerm' below abstracts the /term/ this was
          -- handed, and that term is the hole @induction … of@ elaborated the
          -- written target into, so a goal or a premise written in the author's
          -- own name for the target held no occurrence of it and was left
          -- unrefined. It is @~hc4ps@'s lesson — one name is never enough —
          -- for the scheme instead of the arm.
          --
          -- __It is 'targetChain' and not 'targetVars'__: only a variable the
          -- target /is/ may become @xv@, where an entry whose bare /type/ is
          -- the target is a premise ABOUT it and is carried by a copy instead.
          -- Substituting there would put a term where a type stood.
          tgtSubst = [ (v, Free xv) | v <- targetChain ]

          -- The type each index is generalised at: the family's parameters
          -- replaced by the target's, and each /earlier/ index binder by this
          -- motive's own fresh variable. The second substitution is what makes
          -- a dependent index telescope expressible — the motive's binder for
          -- @Below@'s second index must read @Fin i₁@, naming the first binder
          -- of this motive and not the one in the declaration, which is not in
          -- scope here at all.
          paramSubst = zip (map entryVar (inductiveParameters d)) ps
          earlierIx  = map entryVar (inductiveIndices d)
          indexTys =
            [ substVars (paramSubst ++ zip (take k earlierIx) (map Free (take k ivs)))
                        (entryType e)
            | (k, e) <- zip [(0 :: Int) ..] (inductiveIndices d)
            ]

          -- The actual indices with the generalised entries replaced by their
          -- copies — the side the equations are stated at, so that the equation
          -- constrains the method's own binder (MS9 phase 191).
          asG = map (substVars genSubst) as

          -- __The type a tied index's equation is CARRIED at, and it is the
          -- actual earlier indices — MS9 phase 213, @~7gmvr@ step two.__ §3.2 of
          -- /Pattern Matching Without K/: for two instances of one telescope,
          -- @s; s̄ ≡ t; t̄@ is @(e : s ≡ t) (ē : e∗ s̄ ≡ t̄)@ — a later equation is
          -- stated after transporting the earlier one, which keeps every
          -- equation inside the @Eq@ we already have.
          --
          -- So the carrier names @aⱼ@ where 'indexTys' names @iⱼ@, and it is the
          -- __actual__ side that is left bare: @aₖ@ is where a copy or a
          -- constructor argument stands, and burying it under a transport is
          -- what would put it out of @solution@'s reach.
          --
          -- __For an index telescope that is not dependent these are the very
          -- same terms as 'indexTys'__, so nothing a family without the shape
          -- generates moves by a byte.
          carrierTys =
            [ substVars (paramSubst ++ zip (take k earlierIx) (take k asG)) (entryType e)
            | (k, e) <- zip [(0 :: Int) ..] (inductiveIndices d)
            ]

          -- … and the same with the entries themselves rather than their
          -- copies, which is the type the use site's @refl@ is at.
          actualTys =
            [ substVars (paramSubst ++ zip (take k earlierIx) (take k as)) (entryType e)
            | (k, e) <- zip [(0 :: Int) ..] (inductiveIndices d)
            ]

          -- **At the target's own level arguments** (phase 31c): the family
          -- the motive abstracts is the same family the target inhabits.
          familyAt is = foldl App (Global (inductiveName d) ls) (ps ++ is)

          -- The generalised goal. Target first; see the note above.
          --
          -- **The indices are abstracted before the copies are substituted**,
          -- and that order generalises more: an occurrence of @aₖ@ in the goal
          -- becomes the index binder outright, where substituting first would
          -- have left it as @aₖ@ about a copy. The two agree on the arm's goal
          -- either way, because the equation ties the binder to the copy.
          -- **Every name the target is known by is abstracted, not only the
          -- term handed here** — 'tgtSubst' above, @~pmpqg@. Abstracting the
          -- goal alone would trade one failure for another, a premise ABOUT the
          -- target being left unrefined beside a refined goal; the seeds carry
          -- that half.
          (goalT,  n4) = replaceTerm tgt xv n3' (goalType as)
          goalX        = substVars tgtSubst goalT
          (goalIx, n5) = foldl abstractIndex (goalX, n4) (zip ivs as)
          abstractIndex (g, n) (iv, a) = replaceTerm a iv n g
          goalGen = substVars genSubst goalIx

          -- __One binder per tied equation, minted BEFORE the equations are
          -- built__ (MS9 phase 213). It used to be one fresh variable per Π that
          -- nothing referred to; a transported equation names the proof of each
          -- earlier one, so the binders have to exist before any equation can
          -- be stated. In @tiedIx@ order, which is the order the Π chain binds
          -- them in, so a later equation only ever names an __outer__ binder.
          (qvs, n5') = freshen (length tiedIx) n5

          -- Which positions a tied index's type mentions, read off the motive's
          -- own binders rather than the declaration's, because 'indexTys' is
          -- what the transport walks.
          mentionedBy k =
            [ j | j <- [0 .. k - 1], (ivs !! j) `elem` freeVars (indexTys !! k) ]

          -- __The generalised side, carried to the equation's carrier along the
          -- earlier equations — MS9 phase 213, @~7gmvr@ step two.__ One J per
          -- earlier index position the type mentions, in increasing order, each
          -- replacing that position's generalised binder by its actual index.
          -- The shape is "Thena.Tactics.Specialise"'s @coerce@ exactly — motive
          -- @λ l r q -> residue l -> residue r@, method @λ a at -> at@ — because
          -- it is the same construction: a value wanted at one end of an
          -- equation and held at the other.
          --
          -- __An empty chain is the identity and that is the common case__: a
          -- tied index whose type mentions no earlier index gets @Free iv@ back
          -- unchanged, which is what every family before this phase generated.
          --
          -- 'dependentTied' has already refused the two shapes this walk cannot
          -- state — a mentioned index that is friendly, and two mentioned
          -- indices that are chained — so every position it reaches has a proof
          -- to transport along and leaves the binders after it well typed.
          -- Each tied position with what the transport needs from it: the level
          -- its carrier lives at, the binder of its own equation, and the side
          -- that equation's left is. A position the walk cannot find is
          -- impossible after 'dependentTied' — and if it ever were not, the
          -- chain stops and the motive is refused by 'sortOf' below rather than
          -- crashing, which is how 'SchemeIllTyped' already treats the tactic
          -- being wrong about its own construction.
          (lefts, n5'') = foldl carried ([], n5') tiedIx
          carried (acc, m) k = (acc ++ [(k, t)], m')
            where
              (t, m') = walk (mentionedBy k) (Free (ivs !! k)) (indexTys !! k) m
              walk []       u _  p = (u, p)
              walk (j : js) u ty p
                | [(lv, qv, lj)] <- [ (lv, qv, lj)
                                    | ((i, lv), qv) <- zip (zip tiedIx tiedLvs) qvs
                                    , i == j
                                    , (i', lj) <- acc
                                    , i' == j
                                    ] =
                let cj      = carrierTys !! j
                    resid z = substVars [(ivs !! j, z)] ty
                    (zl, p1) = fresh p
                    (zr, p2) = fresh p1
                    (zq, p3) = fresh p2
                    (zf, p4) = fresh p3
                    (za, p5) = fresh p4
                    (zb, p6) = fresh p5
                    motiveT =
                      Lam (Ident "left") cj (close zl
                        (Lam (Ident "right") cj (close zr
                          (Lam (Ident "q") (equationOf lv cj (Free zl) (Free zr)) (close zq
                            (Pi (Ident "at") (resid (Free zl))
                                (close zf (resid (Free zr)))))))))
                    methodT =
                      Lam (Ident "same") cj (close za
                        (Lam (Ident "at") (resid (Free za)) (close zb (Free zb))))
                    carry = Eliminate
                      { eliminated = equality
                      , levels     = [lv]
                      , parameters = [cj]
                      , motive     = motiveT
                      , methods    = [methodT]
                      , indices    = [lj, asG !! j]
                      , target     = Free qv
                      }
                 in walk js (App carry u) (resid (asG !! j)) p6
                | otherwise = (u, p)

          -- Each tied index with **the level its type lives at**, the equation
          -- the motive states about it, and the @refl@ the use site discharges
          -- it with — in @tiedIx@ order, which is the order 'tiedLevels'
          -- produced the levels in.
          tied =
            [ ( lv
              , equationOf lv (carrierTys !! k) l (asG !! k)
              , Canonical reflexivity [lv] [actualTys !! k, as !! k]
              )
            | (lv, (k, l)) <- zip tiedLvs lefts
            ]

          -- __Which ambient entry each FRIENDLY index abstracted, by
          -- position__ (MS9 phase 196, @~8v3pg@). A position is friendly
          -- exactly when it is not tied, and 'friendlyAt' admitted only a
          -- @'Free' v@ that is a 'Hypothesis' of the context, so there is
          -- always a name to find. 'elimFriendly' says what the arm does with
          -- it.
          friendlyEntries =
            [ (i, k)
            | (k, a) <- zip [(0 :: Int) ..] as
            , k `notElem` tiedIx
            , Free v <- [a]
            , Hypothesis w i _ <- ctx
            , w == v
            ]

          -- @Eq Iₖ iₖ aₖ → …@, one Π per *tied* index, in @tiedIx@ order so that
          -- a transported equation's proof is bound before the equation that
          -- names it.
          --
          -- **Stated about the copy** (MS9 phase 191): @aₖ@ with the
          -- generalised entries replaced, so that the equation constrains the
          -- method's own binder and @solution@ can reach it. @tied@ keeps the
          -- original @aₖ@, which is what the use site's @refl@ is at.
          --
          -- **The Π is no longer always non-dependent** (MS9 phase 213): an
          -- equation whose generalised side was transported names an earlier
          -- one's proof, which is exactly the dependency §3.2's telescopic
          -- equality introduces.
          (equations, n6) = (constrain (zip qvs tied) goalGen, n5'')
          constrain []                   b = b
          constrain ((qv, (_, eq, _)) : cs) b =
            Pi (Ident "q") eq (close qv (constrain cs b))

          -- The context the motive's body lives in, which is also where its
          -- universe is read.
          indexEntries =
            [ Hypothesis iv (entryIdent e) ity
            | (iv, e, ity) <- zip3 ivs (inductiveIndices d) indexTys
            ]
          bodyCtx =
            ctx ++ indexEntries ++ [Hypothesis xv (Ident "target") (familyAt (map Free ivs))]

          -- @∀ y⃗' -> eqs -> G'@. **The copies stand outside the equations**
          -- because the equations are stated about them, and after the target
          -- because that is the one side of it @solution@ can reach.
          motiveBody = piOver genEntries equations

          motiveTerm =
            lamOver indexEntries
              (Lam (Ident "target") (familyAt (map Free ivs)) (close xv motiveBody))
       in
          -- Reading the universe **is** the check that the abstraction was
          -- type-preserving; the level is needed anyway, so it costs nothing
          -- extra (thesis §3.5.3, and see this module's header).
          case sortOf env bodyCtx n6 motiveBody of
            (Left e, _, n7)  -> (Left (MotiveIllTyped e), n7)
            (Right l, _, n7) -> assemble d ls ps as gen genEntries tied friendlyEntries motiveTerm l n7

    -- **Which scheme's type the methods are read off, and at which levels.**
    -- One of exactly two places the scheme is read.
    --
    -- For 'Inductive' the type is computed, as it has been since phase 8. For
    -- 'CaseAnalysis' it is the type @declare@ installed for @caseD@, looked up
    -- rather than rebuilt: @caseD@ is an ordinary definition, and recomputing
    -- its type here would be the second encoding §3.7 refuses for the ι-rules.
    -- Its level parameters are the datatype's plus its own motive level, in
    -- that order (phase 178), which is why the two answer with their own list.
    --
    -- The @Nothing@ case is unreachable — @declare@ installs @caseD@ with the
    -- datatype, and 'build' has already found the datatype. It falls back to the
    -- eliminator's type, which has a hypothesis per recursive argument that
    -- @caseD@'s head does not take, so the scheme is refused by 'check' rather
    -- than quietly handing an arm an extra binder.
    schemeType d l n = case sch of
      Inductive    -> inductive
      CaseAnalysis -> case lookupDefinition (caseName (inductiveName d)) env of
        Just cd -> (definitionType cd, definitionLevels cd, n)
        Nothing -> inductive
      where inductive = let (t, n') = eliminatorType d l n
                         in (t, inductiveLevels d, n')

    -- The level arguments that scheme's head is taken at. @caseD@ takes the
    -- motive's level as a further argument; an @Eliminate@ node carries the
    -- motive itself and needs none.
    schemeLevels ls l = case sch of
      Inductive    -> ls
      CaseAnalysis -> ls ++ [l]

    -- **The head the methods are attached to** — the other place the scheme is
    -- read. An 'Eliminate' node for induction; an application of the @caseD@
    -- global for case analysis, which δ-unfolds to an elimination whose methods
    -- discard the hypotheses, so the kernel sees one kind of thing either way.
    schemeHead d ls ps motiveTerm mvs as elargs = case sch of
      Inductive -> Eliminate
        { eliminated = inductiveName d
        , levels     = ls
        , parameters = ps
        , motive     = motiveTerm
        , methods    = map Free mvs
        , indices    = as
        , target     = tgt
        }
      CaseAnalysis ->
        foldl App (Global (caseName (inductiveName d)) elargs)
          (ps ++ [motiveTerm] ++ map Free mvs ++ as ++ [tgt])

    assemble d ls ps as gen genEntries tied friendlyEntries motiveTerm l n7 =
      let (ety0, elvs, n8) = schemeType d l n7
          -- **Instantiated at the target's level arguments** (phase 31d).
          -- 'Thena.Core.Typing' does the same for a written @elim@; the tactic
          -- builds its own scheme and has to do it too, or the eliminator's
          -- type keeps the datatype's rigid parameters and nothing matches.
          elargs = schemeLevels ls l
          ety = case instantiateLevels elvs elargs of
            Just sub -> substLevelsIn sub ety0
            Nothing  -> ety0
          -- Walk the eliminator's type past the parameters and the motive, then
          -- read one method type off per constructor. This is phase 8's "the
          -- ordinary application rule walked down the eliminator's type", used
          -- to *ask* for the types rather than to check against them.
          afterArgs = applyTo ety (ps ++ [motiveTerm])
          (raw, n9)  = peel (length (inductiveConstructors d)) afterArgs n8
          (methodTys, n9') = tidyAll raw n9
          (mvs, n10)      = freshen (length methodTys) n9'

          -- Named after the constructor each stands for, so that @:show@ and
          -- @:where@ say which case you are in. The suffix is what keeps the
          -- name out of the way of the constructor itself, which the proof of
          -- that very case is going to want to write.
          holes =
            [ (mv, Ident (cn ++ "Method"), mty)
            | (mv, mty, c) <- zip3 mvs methodTys (inductiveConstructors d)
            , let GlobalName cn = constructorName c
            ]
          methodEntries = [ Hypothesis mv i mty | (mv, i, mty) <- holes ]

          node = schemeHead d ls ps motiveTerm mvs as elargs
          -- The equations are reflexive at the use site, which is the whole
          -- point of the scheme (§3.7, thesis §3.5). Only the tied indices have
          -- one; a friendly index was abstracted outright and carries none.
          --
          -- **And each generalised entry is passed as itself** (MS9 phase 191),
          -- before the equations, in the order the motive quantified the copies.
          -- That application is what §2.8 calls discharging the dependency: the
          -- copy becomes the entry again, @aₖ@ becomes @aₖ@, and the @refl@
          -- below is at the index the target really has.
          --
          -- **A transported equation is discharged by the same @refl@** (MS9
          -- phase 213): the motive is applied at the actual indices, so each
          -- transport is a J over @refl@ and ι-contracts to the identity, and
          -- the generalised side is @aₖ@ again. 'check' below is what says so.
          proof = foldl App node
            ([ Free v | v <- gen ] ++ [ r | (_, _, r) <- tied ])
       in case check env (ctx ++ methodEntries) n10 proof goal of
            (Left e, _, n11)   -> (Left (SchemeIllTyped e), n11)
            (Right (), _, n11) ->
              ( Right (Elimination holes proof
                         (MethodShape (map entryIdent genEntries) (length tied)
                                      friendlyEntries ps targetIdents ls))
              , n11 )

    -- Peel @k@ Π domains off a type, instantiating each binder with itself is
    -- not possible — nothing refers to a method — so a method type is read
    -- under a variable that is thrown away.
    peel k ty n
      | k <= (0 :: Int) = ([], n)
      | otherwise = case whnf env ctx ty of
          Pi _ dom sc ->
            let (v, n1)    = fresh n
                (rest, n2) = peel (k - 1) (open v sc) n1
             in (dom : rest, n2)
          _ -> ([], n)   -- unreachable: the eliminator type has k method binders

    applyTo = foldl (\ty a -> case whnf env ctx ty of
                                Pi _ _ sc -> instantiate a sc
                                other     -> other)

    -- A generated method type says @P ī (c Δ)@ with @P@ instantiated to the
    -- motive, so every mention of the goal is a β-redex sitting under the
    -- constructor's own telescope: @(λ target . Eq Nat target target) zero@.
    -- Contracting them is what thesis §3.6.3 means by \"the type of |app can
    -- then reduce\", and it is what the user reads when they walk to the
    -- subgoal.
    --
    -- 'whnf' does the β; the recursion is only into Π domains and bodies,
    -- because that is where the motive's applications are and MS1 has no
    -- normal form to reach for (§5.1, §11 — normalisation by evaluation was
    -- considered and rejected). The stated type stays /convertible/ with the
    -- generated one, which is why 'check' below still passes.
    tidyAll ts n = case ts of
      []      -> ([], n)
      t : tss -> let (t', n1)  = tidy t n
                     (rest, n2) = tidyAll tss n1
                  in (t' : rest, n2)

    tidy t n = case whnf env ctx t of
      Pi i dom sc ->
        let (dom', n1) = tidy dom n
            (v,    n2) = fresh n1
            (body, n3) = tidy (open v sc) n2
         in (Pi i dom' (close v body), n3)
      other -> (other, n)

    -- @Eq {ℓ} I l r@ — instantiated at the level its carrier type lives at
    -- (phase 31d). Before this it was @Global equality []@, and @Eq@ was stuck
    -- at @Type₀@: §2 item 1, and why @Box1@ could not be eliminated.
    equationOf lv ity l r = foldl App (Global equality [lv]) [ity, l, r]

    -- The entries the target /is/, when it is a variable. They are the entries
    -- allowed to mention a friendly index — the whole point is that the target
    -- follows the index into the motive.
    --
    -- __It is a chain and not one entry__ (MS9 phase 186). @induction … of@
    -- cannot know the target's type before elaborating it, so its clause claims
    -- a hole of its own, elaborates the written target into it and eliminates
    -- /that/: the hole is a 'Definition' whose value is the user's own
    -- hypothesis, and both entries mention the index. Counting the second as a
    -- fixed premise tied every index of every split, so
    -- @\ t T d -> induction d of …@ handed each arm an equation over an ambient
    -- variable, which is rigid and which no specialiser transition can touch.
    --
    -- __The exception is "the entry the target denotes", not "the entry whose
    -- variable the target is"__, and the two were the same thing until a caller
    -- elaborated its target into a hole. That the wider reading is right is not
    -- a judgement call: @examples\/progress.thena@ writes the same elimination by
    -- hand, over a context holding @d : HasType t T@, with no equations — and
    -- the kernel accepts it.
    --
    -- A value that is not a variable stops the walk, and then only the hole is
    -- excepted: a compound target really does leave the user's hypothesis as a
    -- separate premise constraining the index.
    -- | __Every ambient name the target is known by__ (MS9 phase 202,
    -- @~hc4ps@), which the arm rebinds to the constructor applied to that
    -- method's arguments. The split defines @xsplit := d@ and eliminates
    -- @xsplit@, so the author's own name is one step out and both mean the same
    -- thing in the arm — one name is never enough.
    --
    -- __It follows a definition's VALUE and nothing else__, which is where it
    -- differs from 'targetVars': that walk also follows a bare /type/, because
    -- an entry whose type is the abstracted variable is a premise about the
    -- target and has to be fixed with it. Such a name is not a name for the
    -- target, and rebinding it would put a term where a type stood.
    targetIdents = [ entryIdent e | e <- ctx, entryVar e `elem` targetChain ]

    -- | __Every variable the target IS__, following a definition's value and
    -- nothing else (MS9 phase 202). 'targetIdents' names them in the arm.
    -- __'scheme' does NOT abstract them in the goal__, and @~pmpqg@ is that.
    targetChain = case tgt of
      Free w -> walk [] [w]
      _      -> []
      where
        walk seen []       = seen
        walk seen (w : ws)
          | w `elem` seen = walk seen ws
          | otherwise     = walk (w : seen) (ws ++ concatMap (valueOf w) ctx)
        valueOf w e
          | entryVar e /= w                = []
          | Definition _ _ (Free y) _ <- e = [y]
          | otherwise                      = []

    -- | __The goal, read through the names it is bound to__ (MS9 phase 208,
    -- @~5kcb4@).
    --
    -- A split in an argument position is handed its goal as a /variable/: the
    -- expected type is one of the @let@s elaboration binds, so
    -- @idT (R a c) (case q of …)@ eliminates against @a1@, where
    -- @a1 := refined2@ and @refined2 := R a c@. Abstracting the target and the
    -- indices in @a1@ abstracts nothing at all, the motive comes out constant,
    -- and the arm is handed the goal unrefined — @~pmpqg@'s failure one level
    -- over, and the reason it was not found with it is that a goal written in a
    -- declaration's type is no such name.
    --
    -- __Only the copies that HIDE something the motive must abstract are
    -- unfolded__, which is what 'hiding' collects. A definition is
    -- definitionally its value, so unfolding one changes nothing about what the
    -- motive means; unfolding every one would, in effect, δ-normalise the goal
    -- and leave the motive's body a term the author would not recognise. So the
    -- rule is the narrowest one that works: a copy goes only if the target or an
    -- index is somewhere underneath it.
    goalType as = unfold (0 :: Int) goal
      where
        unfold depth t
          | depth >= 64 = t
          | otherwise   =
              case [ (v, s) | v <- freeVars t, v `elem` hiding as, s <- valueIn v ] of
                [] -> t
                vs -> unfold (depth + 1) (substVars vs t)
        valueIn v = take 1 [ s | Definition w _ s _ <- ctx, w == v ]

    -- | __The local definitions a goal can reach the target or an index
    -- through__ (MS9 phase 208, @~5kcb4@).
    --
    -- Elaborating a name binds a copy of it, and a copy of a /compound/ term is
    -- where this bites: @isSame (eqString a c)@ in an argument position arrives
    -- as @a2 a3@ over @a3 := eqString a4 a5@, @a4 := a@ and @a5 := c@, so
    -- neither index occurs in the goal at all and no amount of renaming reaches
    -- them. The set is therefore grown rather than walked: a definition is in it
    -- when its value mentions something already in it, starting from the target's
    -- chain and the indices.
    hiding as = grow [] (targetChain ++ [ v | Free v <- as ])
      where
        grow acc seen =
          let more = [ w | Definition w _ s _ <- ctx
                         , w `notElem` acc
                         , any (`elem` seen) (freeVars s) ]
           in if null more then acc else grow (acc ++ more) (seen ++ more)

    -- | __Every ambient name a variable is known by__ (MS9 phase 208,
    -- @~5kcb4@), following the alias definitions elaboration binds __in both
    -- directions__.
    --
    -- 'targetChain' walks forward only, from the hole the split eliminates to
    -- the author's own name, because that is the direction the scaffolding
    -- builds. A goal names its indices the other way round: the author wrote
    -- @a@, elaboration bound @a2 := a@, and the goal mentions @a2@. Both ways
    -- along a chain of @z := y@ is therefore the same relation read without a
    -- preferred end, and every name in the class is definitionally the one
    -- term, which is what makes substituting any of them for the index binder
    -- sound.
    namesFor v0 = walk [] [v0]
      where
        walk seen []       = seen
        walk seen (w : ws)
          | w `elem` seen = walk seen ws
          | otherwise     = walk (w : seen) (ws ++ step w)
        step w =
          [ y | Definition z _ (Free y) _ <- ctx, z == w ]
            ++ [ z | Definition z _ (Free y) _ <- ctx, y == w ]

    targetVars = case tgt of
      Free w -> walk [] [w]
      _      -> []
      where
        walk seen []       = seen
        walk seen (w : ws)
          | w `elem` seen = walk seen ws
          | otherwise     = walk (w : seen) (ws ++ concatMap (standsFor w) ctx)

        -- One step: the variable an entry's value is, and the variable its type
        -- is. Only a bare variable continues the walk — a compound value or a
        -- written-out type is the end of the chain, and then the entries beyond
        -- it really are separate premises.
        standsFor w e
          | entryVar e /= w = []
          | otherwise = bare (entryType e) ++ case e of
              Definition _ _ val _ -> bare val
              Hypothesis {}        -> []

        bare (Free y) = [y]
        bare _        = []

    entryUses e = case e of
      Hypothesis _ _ t   -> freeVars t
      Definition _ _ s t -> freeVars s ++ freeVars t

equality :: GlobalName
equality = GlobalName "Eq"

reflexivity :: GlobalName
reflexivity = GlobalName "refl"

-- | The head and arguments of a type former application.
--
-- **A whnf\'d family application is a 'Canonical', not an @App@ spine over a
-- 'Global'** — §12 invariant 6, and it is easy to forget: the user writes
-- @Vec A n@, which resolves to nested @App@s over @'Global' \"Vec\"@, and then
-- δ unfolds the generated former wrapper and β saturates it into the one
-- spelling the representation admits. Both forms are read here because this is
-- asked of a reduced type, and reading only the second is a bug that shows up
-- as \"Nat is not a datatype\".
-- | The head of an application spine, **its level arguments**, and its
-- ordinary arguments.
--
-- The levels come back because an elimination has to record the ones its target
-- was at (phase 31c) — the node carries them and 'Thena.Core.Typing'
-- instantiates the eliminator with them.
spineOf :: Core -> Maybe (GlobalName, [Level], [Core])
spineOf = go []
  where
    go acc t = case t of
      App f a          -> go (a : acc) f
      Global g ls      -> Just (g, ls, acc)
      Canonical g ls as -> Just (g, ls, as ++ acc)
      _                -> Nothing

-- | Replace parameter variables by the terms the target supplied for them.
--
-- 'close' then 'instantiate' rather than a substitution function: those two are
-- the only way in and out of a 'Thena.Core.Term.Scope' (§3.4), and going
-- through them keeps this honest about binding.
substVars :: [(Var, Core)] -> Core -> Core
substVars subst t = foldl (\acc (v, a) -> instantiate a (close v acc)) t subst

-- | Replace every occurrence of @needle@ by @'Free' v@ — thesis §3.5.3's
-- \"abstracting patterns from the goal\", which §3.7 writes as @G[i⃗]@.
--
-- Equality on 'Core' is alpha-equivalence (§3.5), so this matches up to binder
-- names and nothing else. The counter is threaded because going under a scope
-- means opening it, and only 'Thena.Core.Term.fresh' mints the variable to open
-- it with.
--
-- @needle@ comes from the ambient context and so contains no 'Bound' index;
-- that is why opening a scope cannot make a spurious match.
replaceTerm :: Core -> Var -> Int -> Core -> (Core, Int)
replaceTerm needle v = go
  where
    go n t
      | t == needle = (Free v, n)
      | otherwise = case t of
          Pi  i s sc    -> binder Pi i s sc n
          Lam i s sc    -> binder Lam i s sc n
          Let i s ty sc ->
            let (s',  n1) = go n s
                (ty', n2) = go n1 ty
                (x,   n3) = fresh n2
                (b,   n4) = go n3 (open x sc)
             in (Let i s' ty' (close x b), n4)
          App f a ->
            let (f', n1) = go n f
                (a', n2) = go n1 a
             in (App f' a', n2)
          -- **The level arguments go back unchanged** (MS6 phase 109c). They
          -- were rebuilt as @[]@ from MS3 phase 29 on, which the kernel then
          -- refused as a use of a polymorphic family at no levels — found
          -- when a goal first held an unfolded definition over @List@.
          Canonical g ls as ->
            let (as', n1) = list n as in (Canonical g ls as', n1)
          Eliminate d ls ps m ms is tg ->
            let (ps', n1) = list n ps
                (m',  n2) = go n1 m
                (ms', n3) = list n2 ms
                (is', n4) = list n3 is
                (tg', n5) = go n4 tg
             in (Eliminate d ls ps' m' ms' is' tg', n5)
          _ -> (t, n)

    binder con i s sc n =
      let (s', n1) = go n s
          (x,  n2) = fresh n1
          (b,  n3) = go n2 (open x sc)
       in (con i s' (close x b), n3)

    list n []       = ([], n)
    list n (t : ts) =
      let (t',  n1) = go n t
          (ts', n2) = list n1 ts
       in (t' : ts', n2)

-- | @k@ fresh variables.
freshen :: Int -> Int -> ([Var], Int)
freshen k n
  | k <= 0    = ([], n)
  | otherwise = let (v, n1)  = fresh n
                    (vs, n2) = freshen (k - 1) n1
                 in (v : vs, n2)
