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
  :: GlobalEnv -> Context -> Scheme -> Int -> Core -> Core
  -> (Either ElimError Elimination, Int)
eliminate env ctx sch n0 goal tgt =
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
      -- Read **here** and not inside 'scheme': here the type is
      -- @substVars paramSubst (entryType e)@ and nothing more, and
      -- 'dependentTied' has already refused a tied index whose type mentions an
      -- earlier index — so it mentions only what @ctx@ already has. Inside
      -- 'scheme' the same type also carries the motive's fresh binders, which
      -- are in no context at all.
      | otherwise = case tiedLevels n1 of
          (Left e,    n) -> (Left (IndexTypeIllTyped e), n)
          (Right lvls, n) -> scheme d ls ps as tiedIx generalised lvls n
      where
        tiedLevels k0 = go tiedIx k0
          where
            psub = zip (map entryVar (inductiveParameters d)) ps
            go []       k = (Right [], k)
            go (i : is) k =
              case sortOf env ctx k (substVars psub (entryType (inductiveIndices d !! i))) of
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
        unmentioned v e =
          entryVar e == v
            || entryVar e `elem` targetVars
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
        -- __IT IS UNCONDITIONAL, AND THAT HAS A MEASURED COST — this phase's
        -- measurement, which `~6dpg5` asked for.__ A copy is made for every seed,
        -- including one whose refinement nothing but the equation reads: making
        -- it is what turns a stuck equation into a solved one, so there is no
        -- seed it is free to skip. What is not free is the other caller. In a
        -- split "Thena.Tactics.Specialise" solves the copy and drops the binder,
        -- so the arm never sees it; under @eliminate-core@ the methods are
        -- written __by hand__ and every copy is a binder the author has to take.
        -- @examples\/dependent-index.thena.script@ and
        -- @examples\/determinacy-tactics.thena.script@ both had to be rewritten
        -- for that, and the item's claim that generalising \"always gets that case
        -- for free\" holds only on the specialised side.
        --
        -- __TWO QUESTIONS, AND THEY ARE ASKED IN TWO PLACES — MS9 phase 197,
        -- `~k54hh`.__ /Which/ ambient entries may be copied is 'generalisable',
        -- which skips the ones that may not; /whether the scheme can state the
        -- copies it found/ is 'viable', and a failure there cancels the lot,
        -- leaving the split behaving exactly as it did before phase 191 — the
        -- equation stated and kept. They were one all-or-nothing test until
        -- phase 197, and that is what shut `~k54hh`: a definition the split did
        -- not put in the context cancelled every copy.
        generalised = if viable then closed else []
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
            seeds = nub [ v | k <- tiedIx
                            , c <- inductiveConstructors d
                            , v <- demandedAt c k
                            , v `notElem` targetVars
                            , v `notElem` friendlies ]

            demandedAt c k = walk (conIndex c k) (as !! k)
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

        -- §3.7's limit, and it binds a *tied* index only. @Eq Iₖ iₖ aₖ@ is
        -- homogeneous, and @iₖ@ is the generalised index while @aₖ@ is the
        -- actual one, so @Iₖ@ may not mention an earlier index: instantiated
        -- for the two sides it would be two different types, which is what
        -- \"John Major\" equality exists to relate. A /friendly/ index states no
        -- equation at all, so its type is free to depend on an earlier one —
        -- only the motive's own telescope has to carry the dependency, and
        -- 'scheme' builds it so that it does.
        dependentTied = firstJust [ dependent k | k <- tiedIx ]
        dependent k =
          let e     = inductiveIndices d !! k
              subst = zip (map entryVar (inductiveParameters d)) ps
              ty    = substVars subst (entryType e)
              taken = take k (map entryVar (inductiveIndices d))
           in if any (`elem` freeVars ty) taken
                then Just (IndexTypeDepends (k + 1) (entryIdent e))
                else Nothing
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
            [ Hypothesis gv (entryIdent e) (substVars (take j genSubst) (entryType e))
            | (j, (v, gv)) <- zip [(0 :: Int) ..] (zip gen gvs)
            , e            <- [ x | x <- ctx, entryVar x == v ]
            ]

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
          -- **Only the target term handed here is abstracted, and a goal
          -- written in the author's own name for it keeps that name** —
          -- @~pmpqg@, which is his: abstracting the whole chain alone trades
          -- the failure for another, because a premise ABOUT the target is not
          -- refined either and the two used to agree by both being unrefined.
          (goalX,  n4) = replaceTerm tgt xv n3' goal
          (goalIx, n5) = foldl abstractIndex (goalX, n4) (zip ivs as)
          abstractIndex (g, n) (iv, a) = replaceTerm a iv n g
          goalGen = substVars genSubst goalIx

          -- Which indices keep an equation. Decided by 'build'; see the note
          -- on 'friendlyAt' there.
          -- Each tied index with **the level its type lives at**, in @tiedIx@
          -- order — which is the order 'tiedLevels' produced them in.
          tied = zip tiedLvs
                     [ (ity, iv, a)
                     | (k, (ity, iv, a)) <- zip [(0 :: Int) ..] (zip3 indexTys ivs as)
                     , k `elem` tiedIx
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

          -- @Eq Iₖ iₖ aₖ → …@, one non-dependent Π per *tied* index. A Π still
          -- needs a variable to close over even when nothing refers to it,
          -- exactly as 'Thena.Global.Env.eliminatorType' mints one per
          -- induction hypothesis.
          --
          -- **Stated about the copy** (MS9 phase 191): @aₖ@ with the
          -- generalised entries replaced, so that the equation constrains the
          -- method's own binder and @solution@ can reach it. @tied@ keeps the
          -- original @aₖ@, which is what the use site's @refl@ is at.
          (equations, n6) = constrain tied n5 goalGen
          constrain []                  n b = (b, n)
          constrain ((lv, (ity, iv, a)) : cs) n b =
            let (body, na) = constrain cs n b
                (qv,   nb) = fresh na
             in ( Pi (Ident "q")
                     (equationOf lv ity (Free iv) (substVars genSubst a))
                     (close qv body)
                , nb )

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
          proof = foldl App node
            ([ Free v | v <- gen ]
             ++ [ Canonical reflexivity [lv] [ity, a] | (lv, (ity, _, a)) <- tied ])
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
