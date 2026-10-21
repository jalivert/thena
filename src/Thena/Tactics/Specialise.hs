-- | Specialisation by unification — the four transitions, in one coarse
-- operation (MS9 phase 177).
--
-- "Thena.Tactics.Eliminate" stops where the equations are produced. A method of
-- an elimination at specific indices reads
--
-- @
-- ∀ Δc -> IHs -> y⃗' -> Eq I₁ u₁ v₁ -> … -> Eq Iₖ uₖ vₖ -> T
-- @
--
-- where @y⃗'@ are the fresh copies the motive generalised the ambient entries
-- its indices mention to (MS9 phase 191). **They are pattern variables here and
-- that is the whole of why they exist**: @solution@ may move a binder of the
-- method and may not move a rigid ambient variable, so a copy is the one thing
-- an equation about an outer variable can be solved against.
--
-- and the user discharges every equation by hand. Across @examples\/@ that is
-- 519 uses of a generated @noConfusion@, 79 eliminations of @Empty@ and 29
-- transports — about one every seven lines of a development. __This module does
-- that work instead__: it rewrites such a method type to the one its equations
-- imply, and emits the term that recovers the original from the rewritten one.
--
-- == The four transitions
--
-- Each applies to one equation, and applying one leaves a smaller problem.
--
-- * __deletion__ — @Eq I t t@ constrains nothing, so the binder goes and the
--   term ignores the argument.
-- * __conflict__ — @Eq I (c s⃗) (c' t⃗)@ for two different constructors cannot be
--   inhabited, so there is __no subgoal at all__: what is left of the method is
--   proved by eliminating the @Empty@ the generated @noConfusion@ gives. This is
--   the impossible case vanishing.
-- * __injectivity__ — @Eq I (c s⃗) (c t⃗)@ becomes one equation per argument, out
--   of the same lemma, and those are transformed in their turn.
-- * __solution__ — @Eq I t x@ (or @Eq I x t@) where @x@ is one of the method's
--   own binders substitutes @x := t@ and __drops the binder__. This is the one
--   that removes a coercion from what the user writes rather than a line.
--
-- __There is no cycle transition__, because @noCycle@ exists nowhere in Thena.
-- Its absence is sound and it is not silent: an equation no transition applies
-- to is __kept__, exactly as it is handed over today, so the worst case here is
-- the behaviour that preceded it.
--
-- __So this never fails for want of a transition.__ @eliminating.pdf@
-- Definition 19 makes "no transition applies" a /failure/; here it is a
-- residual hypothesis, because refusing would withdraw a split the user can
-- still do by hand.
--
-- == Where the risk sits
--
-- __One coarse op, and the splitting tree is rules — his ruling, 2026-10-18__,
-- with the argument that decided it: a wrong tree is a failed elaboration,
-- while a wrong proof term is caught by @check@. Everything built here is
-- therefore checked against the method type it claims to inhabit before it is
-- handed back — the bargain "Thena.Tactics.Eliminate" and
-- "Thena.Global.NoConfusion" already struck.
--
-- __Termination__ is the lexicographic measure (binders in @Δ@, then the size
-- of the equations): solution drops a binder, and deletion, conflict and
-- injectivity keep @Δ@ and shrink the equations. Nothing here is bounded by a
-- fuel count because nothing here needs to be.
--
-- Where it sits in §2.5: beside "Thena.Tactics.Eliminate" — above
-- "Thena.Core.Typing" and "Thena.Global.Env", below "Thena.Engine".
module Thena.Tactics.Specialise
  ( Specialisation (..)
  , Binder (..)
  , Role (..)
  , binderWord
  , specialise
  ) where

import Thena.Core.Context (Context, Entry (..), entryIdent, entryType, entryVar, lamOver, piOver)
import Thena.Core.Level (Level, instantiateLevels, substLevel)
import Thena.Core.Reduce (whnf)
import Thena.Core.Term
  ( Core (..)
  , GlobalName (..)
  , Ident (..)
  , Var
  , close
  , freeVars
  , fresh
  , instantiate
  , open
  , substLevelsIn
  )
import Thena.Core.Typing (check)
import Thena.Errors (SpecialiseError (..))
import Thena.Global.Env
  ( ConstructorDefinition (..)
  , GlobalEnv
  , InductiveDefinition (..)
  , isDeclared
  , lookupConstructor
  , lookupInductive
  )
import Thena.Global.NoConfusion (noConfusionNames)
import Thena.Tactics.Eliminate (MethodShape (..), spineOf)

-- | What specialisation worked out: the subgoal, and __one ordered report of
-- what each binder of the method is__.
--
-- 'specialisedGoal' is __zero or one__ hole, and a list rather than a 'Maybe'
-- so that it is exactly 'Thena.Tactics.Eliminate.Elimination'\'s shape —
-- "Thena.Engine" claims them with the same fold, and the empty case is a
-- conflict closing the method outright.
--
-- 'specialisedTerm' mentions that hole as @'Free' v@, so it is well typed only
-- in a context extended by it. 'specialise' has already checked it there.
--
-- 'specialisedBinders' is __one entry per binder of the method's telescope, in
-- the order the method binds them__ — the constructor's arguments, then the
-- hypotheses this method carries, then the copies the motive generalised. Each
-- says what the binder /is/ and whether an equation determined it:
-- @'Nothing'@ for one that survived as a binder of the subgoal, and @'Just' t@
-- for one a solution removed, @t@ being a function from the binders that
-- survived before it to what it was solved to. __Only the solution transition
-- removes a binder__, so only it writes a @'Just'@ here.
--
-- __IT REPLACED THREE WALKS THAT AGREED BY CONVENTION — his ruling of
-- 2026-10-20, fourth session.__ Until MS9 phase 192 this was two positional
-- slices, @specialisedForced@ over the arguments and @specialisedRefined@ over
-- the copies, and the caller rebuilt the third group — the hypotheses — from
-- the declaration. Three rules then introduced one group each, in an order each
-- of them had to know and none of them stated. That convention is what made the
-- binder order load-bearing when the copies arrived (@~bq3rn@, @~2d9xj@), and
-- the case for keeping it was only that fewer goldens move, which is a cost and
-- not a side. __So there is one list and one place that consumes it.__
--
-- __What the caller does with an entry is decided by its 'Role', and the three
-- are genuinely three.__ An argument is named by the arm's /pattern/, so the
-- walk consumes one there and nowhere else; a hypothesis is bound under a
-- __freshened__ name, because the argument it is about is already in the
-- development and shadowing it would silently build the proof out of the wrong
-- variable; a copy is bound under the ambient name it already had, because
-- shadowing the entry is the whole of the refinement.
--
-- __A SOLVED BINDER'S TERM IS ABSTRACTED OVER THE BINDERS THAT SURVIVED BEFORE
-- IT — MS9 phase 195__, so @'Just' t@ is @λ ‹those› -> ‹the term›@ and the
-- caller applies it to what it bound for them, in order. @report@'s comment has
-- why, and the short of it is that the term is written in variables @peel@
-- minted here: the caller's binders are its own, so a raw term is out of scope
-- wherever the caller could use it.
--
-- __This is the only thing that knows.__ The subgoal is a type with fewer
-- binders than the method's telescope has and nothing in it says which ones are
-- missing, so a clause introducing an arm's binders cannot work it out — which
-- is why phase 184's clause failed on @vtail@.
--
-- __A SOLVED COPY'S TERM IS NOT AMBIENT, AND THAT IS WHY EVERY SOLVED TERM IS
-- ABSTRACTED.__ A forced constructor /argument/ is solved from the target's
-- index, which lives where the elimination was written, so its term mentions no
-- binder of the method; a /copy/ is solved from the __constructor's__ index, so
-- @p'@ comes out as @c1@ — a binder of this very method. Reporting the first
-- raw worked only because of a property the second does not have, and relying
-- on it is what @~tzwjk@ measured. Abstracted, both are in scope wherever the
-- caller has bound the surviving binders, which is what lets it bind either one
-- with @define@ above the hole.
data Specialisation = Specialisation
  { specialisedGoal    :: [(Var, Ident, Core)]
  , specialisedTerm    :: Core
  , specialisedBinders :: [(Binder, Maybe Core)]
  , specialisedRebound :: [(Ident, Core)]
    -- ^ **the names bound OUTSIDE the split that this method makes something
    -- else of** — each with a function from the binders that survived to what
    -- it now means (MS9 phase 196, @~8v3pg@).
    --
    -- __One of them today__: an ambient entry a /friendly/ index abstracted
    -- outright.
    --
    -- __The TARGET is the other thing a split refines that is not a binder of
    -- the method, and it is not here — measured, not overlooked.__ Inside a
    -- method the target is the constructor applied to that method's arguments,
    -- and the entry the author named it by goes on being its old self, so
    -- writing it in the arm is refused at the arm's own goal. Binding it is
    -- what cannot be done yet: a rebinding is a
    -- 'Thena.Core.Context.Definition', and the target's one has a /type/ that
    -- mentions what the split refined — @s1 := eIf p p' a b sr@ is a
    -- @Step (ifthen p a b) (ifthen p' a b)@. A split nested in that arm then
    -- meets it in the forward closure of its own seeds, where
    -- @Thena.Tactics.Eliminate@'s @viable@ may not carry a definition, so it
    -- cancels the generalisation and the arm loses the refinement it had:
    -- @examples\/determinacy-patterns.thena@ measures it, @p@ stopping being
    -- refined to @true@. An index's rebinding has a type that mentions nothing,
    -- which is why that half is here and this one is not.
    --
    -- __It is not in 'specialisedBinders' because it is not a binder of the
    -- method__, and that list says one entry per binder in the order the method
    -- binds them. A friendly index states no equation and quantifies no copy,
    -- so it has nowhere in that list to go — which is why the arm used to bind
    -- nothing for it and the name went on meaning the unrefined thing.
    --
    -- __Abstracted over /every/ surviving binder, where a solved binder's term
    -- is abstracted over the ones before it.__ Nothing orders a friendly index
    -- against the constructor's arguments — @fs@'s second index is @s m@ and
    -- @m@ is its last argument — so the caller applies these once the whole
    -- telescope is bound, which is also where they have to be /bound/, for the
    -- λ-chain reason @bind-solved@ carries.
  }
  deriving (Eq, Show)

-- | One binder of a specialised method: what it is, and the name it is bound
-- under (MS9 phase 192).
--
-- __The name is here because the three roles take it from three different
-- places__ and only the caller of 'specialise' knows two of them: an argument's
-- is the method type's own binder, a hypothesis's is the recursive argument it
-- is about, and a copy's is the ambient entry it copies. The first is read off
-- the telescope; the other two are told to 'specialise', which is also how it
-- learns how many there are.
data Binder = Binder Role Ident
  deriving (Eq, Show)

-- | Which of a method's three groups a binder belongs to (MS9 phase 192).
--
-- __Three and not two__: the hypotheses were never in the specialiser's report
-- at all, and that is precisely why a caller had to count. A method of @caseD@
-- carries none, so the group can be empty — it is not a case that stops
-- existing.
data Role
  = AnArgument
    -- ^ an argument of the constructor, named by the arm's pattern
  | AnHypothesis
    -- ^ an induction hypothesis this method carries, one per recursive
    -- argument and __none under @case … of@__
  | ACopy
    -- ^ a fresh copy of an ambient entry the motive generalised (MS9 phase
    -- 191), standing after the target
  deriving (Eq, Show)

-- | What a binder is, in words — @argument n@, @hypothesis m@, @copy s0@ (MS9
-- phase 192).
--
-- __Here and not in a printer__, because there is nothing to print /back/: a
-- role is this module's own vocabulary and has no written form, so a printer
-- that spelled it itself would be a second authority on what the three groups
-- are called. "Thena.Render" and "Thena.View.Instral" both read this one.
binderWord :: Binder -> String
binderWord (Binder r (Ident w)) = word r ++ " " ++ w
  where
    word AnArgument   = "argument"
    word AnHypothesis = "hypothesis"
    word ACopy        = "copy"

-- | Specialise the method of @c@ whose last @k@ binders before the body are the
-- equations the elimination stated.
--
-- __All of those are facts the caller has and the type does not.__ A method
-- type is Π binders all the way down, and nothing in it marks where the
-- constructor's own telescope ends and the equations begin — a constructor may
-- itself take a proof of an equation, and the body after the equations may be a
-- Π of its own, so counting binders settles nothing. So @c@ gives the
-- constructor's own arguments, @hyps@ names the induction hypotheses this
-- method carries, @gens@ names the copies the motive generalised, and @k@ is
-- how many indices were tied.
--
-- __THE HYPOTHESES ARE NAMED AND NOT COUNTED — MS9 phase 192__, and the
-- generalised copies with them. Their count used to be all that came in, and
-- that is what forced the caller to rebuild each group by position:
-- 'specialisedBinders' carries the names, and a name a method type does not have
-- has to be told. A hypothesis's binder is @ih@ in
-- 'Thena.Global.Env.eliminatorType' for every recursive argument of every
-- constructor, so the recursive argument's own name — which is the name the arm
-- freshens — exists nowhere in the type at all.
--
-- __And the count still may not be read off the declaration — MS9 phase 188.__
-- It used to be, as one per recursive constructor argument, and that silently
-- assumed the caller was eliminating: @caseD@'s methods carry none, so the
-- assumption made @case … of@ refuse its own methods as misshapen. The caller
-- knows which scheme it asked for; this does not, and no longer guesses. The
-- copies join @Δc@ and the hypotheses as __pattern variables__, which is the
-- only change the four transitions need.
specialise
  :: GlobalEnv -> Context -> Int -> GlobalName -> [Ident] -> MethodShape -> Core
  -> (Either SpecialiseError Specialisation, Int)
specialise env ctx n0 cn hyps shape mty = case lookupConstructor cn env of
  Nothing -> (Left (NotThatConstructor cn), n0)
  Just (d, c)
    | k < 0 -> (Left (MethodNotShaped (arity d c) k mty), n0)
    | otherwise -> case peel (arity d c + gc + k) mty n0 of
        Nothing -> (Left (MethodNotShaped (arity d c) k mty), n0)
        Just (tel, body, n1) ->
          let (delta, raw) = splitAt (arity d c + gc) tel
           in case mapM equationOf raw of
                Nothing -> (Left (NotAnEquation (map entryType raw)), n1)
                Just es ->
                  let (hv, n2) = fresh n1
                   in case solve hv delta es body n2 of
                        (Left e, n3) -> (Left e, n3)
                        (Right (want, tm, sol), n3) ->
                          verify hv want tm (report c delta sol)
                                 (reboundTerms d c delta sol) n3
  where
    MethodShape gens k friendly pars = shape

    h  = length hyps
    gc = length gens

    -- One binder per constructor argument, plus the hypotheses the caller says
    -- this method carries. 'Thena.Global.Env.eliminatorType'\'s @methodType@
    -- read backwards for 'Thena.Global.Env.Inductive', and @caseD@'s for
    -- 'Thena.Global.Env.CaseAnalysis', where @h@ is zero.
    arity _ c = length (constructorArguments c) + h

    -- __THE REPORT: one entry per binder, in the order the method binds them.__
    -- 'Thena.Global.Env.eliminatorType' states the constructor's arguments and
    -- then its hypotheses, and 'Thena.Tactics.Eliminate' quantifies the copies
    -- after the target, so the three groups are the three stretches of @delta@
    -- in that order and @zip3@ is the whole of finding them. Nothing downstream
    -- counts anything: an entry says which group it is in.
    --
    -- __An argument's name is the method type's own binder__, kept by @peel@,
    -- which is what makes the subgoal read like the method it came from. A
    -- hypothesis's and a copy's are the caller's, for the reason the header
    -- above gives.
    --
    -- __A hypothesis is never solved__ — an equation is over the datatype's
    -- indices and a hypothesis is a proof of the motive — so its entry is
    -- always 'Nothing'. It is looked up anyway rather than asserted, because an
    -- assertion here would be a claim about the transitions that nothing checks.
    report c telescope sol =
      [ (Binder role i, abstractOver (entryVar e) <$> lookup (entryVar e) sol)
      | (role, i, e) <- zip3 roles idents telescope
      ]
      where
        nargs  = length (constructorArguments c)
        roles  = replicate nargs AnArgument
                   ++ replicate h AnHypothesis
                   ++ replicate gc ACopy
        idents = map entryIdent (take nargs telescope) ++ hyps ++ gens

        -- __A SOLVED BINDER'S TERM IS ANSWERED ABSTRACTED OVER THE BINDERS THAT
        -- SURVIVED BEFORE IT — MS9 phase 195.__ It is written in /this module's/
        -- variables, which @peel@ minted and which exist nowhere else: the
        -- caller binds the surviving binders itself, so the two sets of
        -- variables are different and a term handed over raw is out of scope
        -- wherever the caller could use it. @‹Var 3853› is not in scope@ was the
        -- measured failure (@~tzwjk@).
        --
        -- __A λ is the translation, and applying it performs it.__ The surviving
        -- entries in order are exactly the subgoal's own binders, which is what
        -- the caller introduces and in that order, so the function this answers
        -- is total on what it needs: 'solvable' refuses a solution whose term
        -- mentions a binder __at or after__ the one being solved, so nothing
        -- here can be abstracted over a binder the caller has not bound yet.
        --
        -- __The same shape for all three roles__, and that is the point. Until
        -- this phase a forced /argument/ was reported raw, on the strength of
        -- its term being ambient, and a solved /copy/ could not be reported
        -- usefully at all — one group's report being well scoped by a property
        -- of that group is the special case that cost @~tzwjk@. An argument's
        -- abstraction is usually empty, which costs nothing.
        --
        -- The types are substituted because @telescope@ is the problem as it
        -- __arrived__: a surviving entry's type may mention a binder a later
        -- solution removed, and the subgoal's own binders carry the substituted
        -- types.
        abstractOver v = lamOver
          [ Hypothesis (entryVar e) (entryIdent e) (substituteAll sol (entryType e))
          | e <- takeWhile ((/= v) . entryVar) telescope
          , entryVar e `notElem` map fst sol
          ]

    -- __WHAT THIS METHOD MAKES OF EACH FRIENDLY INDEX'S AMBIENT NAME — MS9
    -- phase 196, @~8v3pg@.__ The motive abstracted the index outright, so the
    -- arm's goal is about the abstracted variable while the entry is still in
    -- the context under its own name meaning the unrefined thing. What the name
    -- now denotes is this constructor's own index expression at that position,
    -- and it is written here because nowhere else has both the expression and
    -- this method's binders.
    --
    -- __Two substitutions, and each is the same one the scheme made.__ The
    -- declaration states an index in the family's /parameter/ variables, so
    -- those become the target's — 'Thena.Tactics.Eliminate' hands them over for
    -- this — and in the constructor's own /argument/ variables, so those become
    -- @delta@'s, positionally, which is the correspondence @report@ already
    -- relies on for the names. Then the solutions, because a forced argument
    -- the expression mentions no longer has a binder.
    --
    -- __Abstracted over every surviving binder__, where a solved binder is
    -- abstracted over the ones before it: an index expression may mention any
    -- of the constructor's arguments, so there is no prefix to stop at. The
    -- caller applies it once the telescope is bound.
    reboundTerms d c delta sol = map (fmap (lamOver survivors)) indices
      where
        -- An ambient entry a friendly index abstracted now means this
        -- constructor's own index expression at that position.
        indices =
          [ (i, substituteAll sol (substituteAll argSub (substituteAll paramSub ix)))
          | (i, pos) <- friendly
          , ix <- take 1 (drop pos (constructorIndices c))
          ]

        conArgs  = take (length (constructorArguments c)) delta
        paramSub = zip (map entryVar (inductiveParameters d)) pars
        argSub   = zip (map entryVar (constructorArguments c)) (map (Free . entryVar) conArgs)
        survivors =
          [ Hypothesis (entryVar e) (entryIdent e) (substituteAll sol (entryType e))
          | e <- delta
          , entryVar e `notElem` map fst sol
          ]

    -- The hole and the term that uses it, checked in the context that will hold
    -- both. Checking here is the whole of §7.2's bargain for a coarse op: a
    -- wrong proof term is caught, so only the caller's /choice/ of what to
    -- specialise is unguarded.
    verify hv want tm bs fs n =
      let hole = [ (hv, Ident (nameOf cn ++ "Case"), w) | Just w <- [want] ]
          with = ctx ++ [ Hypothesis v i t | (v, i, t) <- hole ]
       in case check env with n tm mty of
            (Left e, _, n1)   -> (Left (SpecialisedIllTyped e), n1)
            (Right (), _, n1) -> (Right (Specialisation hole tm bs fs), n1)

    nameOf (GlobalName w) = w

    -- @j@ Π binders as a telescope, each opened at a fresh variable so that it
    -- is an ordinary 'Context' entry. The binder's 'Ident' is kept, which is
    -- what makes the simplified goal read like the method it came from.
    --
    -- Reduced at the ambient context, as "Thena.Tactics.Eliminate"\'s own @peel@
    -- is: what comes in is a method type whose binders are already exposed, so
    -- this is a guard rather than a walk.
    peel j ty n
      | j <= (0 :: Int) = Just ([], ty, n)
      | otherwise = case whnf env ctx ty of
          Pi i dom sc ->
            let (v, n1) = fresh n
             in case peel (j - 1) (open v sc) n1 of
                  Nothing          -> Nothing
                  Just (es, b, n2) -> Just (Hypothesis v i dom : es, b, n2)
          _ -> Nothing

    -- An entry whose type is @Eq {l} I u v@, read apart. The binder is kept: a
    -- residual equation is still a hypothesis the method takes, and a
    -- transition that fires needs the variable to name its proof with.
    equationOf e = case spineOf (whnf env ctx (entryType e)) of
      Just (GlobalName "Eq", [l], [i, u, v]) ->
        Just (Eqn (entryVar e) (entryIdent e) (entryType e) l i u v)
      _ -> Nothing

    -- ------------------------------------------------------------------
    -- The loop
    -- ------------------------------------------------------------------

    -- __The invariant, and it is what lets the recursion compose__: the term
    -- handed back always inhabits @∀ Δ -> eqs -> t@, the problem as it stands
    -- at this call, and the type handed back is what the single remaining hole
    -- must be given. 'Nothing' there means the term does not mention the hole —
    -- a conflict closed the method.
    --
    -- __And it answers with what the solution transitions removed__, as
    -- @(binder, the term it was solved to)@, which is what 'specialisedBinders'
    -- is read off @delta@ with. Every term in it is already resolved, because a
    -- solution applies the sub-problem's own pairs to its term before recording
    -- it, so nothing there mentions a binder the list removes.
    --
    -- Equations are tried left to right; one no transition applies to is moved
    -- into the accumulator and stays a binder.
    solve hv delta eqs t = go [] eqs
      where
        go bfr [] n = (Right (Just (problem (reverse bfr) t), Free hv, []), n)

        go bfr (e : after) n = case transition delta e of
          NoTransition -> go (e : bfr) after n
          Delete       -> deletion  bfr e after n
          Conflict dn  -> conflict  bfr e after n dn
          Inject dn c  -> injection bfr e after n dn c
          Solve x left -> solution  bfr e after n x left

        -- @∀ Δ -> eqs -> t@, the type of every term this function builds.
        problem es body = piOver (delta ++ map entry es) body

        -- Everything bound to the left of, and including, the equation a
        -- transition fired on. The body under it is @after -> t@, which is what
        -- each case below has to produce.
        prefix before e = delta ++ map entry (before ++ [e])

        -- __deletion.__ The equation says nothing, so it is bound and ignored.
        deletion bfr e after n =
          let before = reverse bfr
           in continue (before ++ after) t n $ \g ->
                lamOver (prefix before e)
                        (applyTo g (varsOf delta ++ eqnVars before))

        -- __conflict.__ @noConfusion@ at two different constructors is an
        -- @Empty@, and eliminating it proves whatever is left. __Nothing is
        -- claimed.__
        conflict bfr e after n dn = case confusion dn e of
          Nothing -> go (e : bfr) after n
          Just (lv, absurd) ->
            let before   = reverse bfr
                rest     = piOver (map entry after) t
                (v, n1)  = fresh n
                node = Eliminate
                  { eliminated = emptiness
                  , levels     = [lv]
                  , parameters = []
                  , motive     = Lam (Ident "impossible") (Global emptiness [lv])
                                     (close v rest)
                  , methods    = []
                  , indices    = []
                  , target     = absurd
                  }
             in (Right (Nothing, lamOver (prefix before e) node, []), n1)

        -- __injectivity.__ One equation per constructor argument, each proved by
        -- a projection out of the @And@ chain the lemma answers with, and the
        -- whole lot handed to the sub-problem in this equation's place.
        injection bfr e after n dn c = case conjuncts dn c e n of
          (Nothing, n1) -> go (e : bfr) after n1
          (Just (news, ps), n1) ->
            let before = reverse bfr
             in continue (before ++ news ++ after) t n1 $ \g ->
                  lamOver (prefix before e)
                          (applyTo g (varsOf delta ++ eqnVars before ++ ps))

        -- __solution.__ The binder goes and everything to its right is
        -- substituted. What the sub-problem then proves is this method at the
        -- /term/ where this one wants it at the /binder/, so one J-elimination
        -- coerces between the two.
        solution bfr e after n x onLeft =
          let before    = reverse bfr
              (d1, d2)  = break ((== x) . entryVar) delta
              d2'       = drop 1 d2
              other     = if onLeft then eqnRight e else eqnLeft e
              -- @∀ Δ₂ -> before -> after -> t@ with @z@ for the binder being
              -- removed: at @x@ the type this term must end at, at @other@ the
              -- sub-problem's.
              residueAt z =
                substituting x z (piOver (d2' ++ map entry (before ++ after)) t)
           in case solve hv (d1 ++ substIn x other d2')
                            (map (substEqn x other) (before ++ after))
                            (substituting x other t) n of
                (Left err, n1) -> (Left err, n1)
                (Right (want, g, sol), n1) ->
                  let (co, n2) = coerce e onLeft residueAt n1
                   in ( Right ( want
                              , lamOver (prefix before e)
                                  (applyTo (App co (applyTo g (varsOf d1)))
                                           (varsOf d2' ++ eqnVars before))
                              -- __Resolved before it is recorded.__ A deeper
                              -- solution may have removed a binder that @other@
                              -- mentions, so the pairs it answered with are
                              -- applied here; the invariant above is what makes
                              -- one pass enough.
                              , (x, substituteAll sol other) : sol )
                      , n2 )

        -- Solve the sub-problem, then shape this one's term out of its.
        continue es body n f = case solve hv delta es body n of
          (Left err, n1)             -> (Left err, n1)
          (Right (want, g, sol), n1) -> (Right (want, f g, sol), n1)

    -- ------------------------------------------------------------------
    -- Which transition applies
    -- ------------------------------------------------------------------

    -- __Deletion first, then discrimination, then solution__, and the order is
    -- not arbitrary: @Eq I x x@ for a pattern variable @x@ admits both deletion
    -- and solution, and deletion is the one that leaves the binder alone.
    transition delta e
      | whnf env ctx (eqnLeft e) == whnf env ctx (eqnRight e) = Delete
      | Just (dn, cu, _) <- former (eqnLeft e)
      , Just (_,  cv, _) <- former (eqnRight e)
      , Just _ <- confusionOf dn =
          if cu == cv then Inject dn cu else Conflict dn
      | Just x <- solvable (eqnRight e) (eqnLeft e)  = Solve x False
      | Just x <- solvable (eqnLeft e)  (eqnRight e) = Solve x True
      | otherwise = NoTransition
      where
        -- A pattern variable is one of __this method's own binders__ — @delta@,
        -- never the ambient context, whose variables are rigid. §6.2 is the note
        -- that matters: a rigid variable against a term would want @raise@,
        -- which is deliberately not in the op vocabulary, so this is the only
        -- transition that may move a binding at all.
        --
        -- Two conditions beyond that, each a case that breaks without it. @x@
        -- may not occur in the term that solves it — that is the cycle
        -- transition, and @noCycle@ does not exist — and the term may mention
        -- __no binder at or after @x@__, or substituting it leftwards would be
        -- ill-scoped.
        solvable candidate by = case whnf env ctx candidate of
          Free x
            | any ((== x) . entryVar) delta
            , x `notElem` freeVars by
            , not (any (`elem` freeVars by) (atOrAfter x)) -> Just x
          _ -> Nothing

        atOrAfter x = map entryVar (dropWhile ((/= x) . entryVar) delta)

    -- The datatype, the constructor and its arguments, for a term that is a
    -- saturated constructor application. __The parameters are dropped__: a
    -- constructor passes them through unchanged, so the equations injectivity
    -- states are over the arguments alone.
    former t = case spineOf (whnf env ctx t) of
      Just (g, _, as) -> case lookupConstructor g env of
        Just (d, _) ->
          Just (inductiveName d, g, drop (length (inductiveParameters d)) as)
        Nothing -> Nothing
      Nothing -> Nothing

    -- @noConfusion‹D›@, if it was generated at all. It is declined for a
    -- datatype with a dependent argument telescope
    -- ("Thena.Global.NoConfusion"), and without it neither discrimination
    -- transition can fire — so the equation is kept.
    confusionOf dn
      | isDeclared lem env = Just lem
      | otherwise          = Nothing
      where lem = snd (noConfusionNames dn)

    -- @noConfusion‹D› p⃗ i⃗ u v q@ — the lemma applied, and the level its @Empty@
    -- and its equations are stated at, which is the datatype's own (phase 31g)
    -- __instantiated at the carrier's level arguments__. Left rigid it would be
    -- a level parameter of the declaration appearing in a term, which is the
    -- bug phase 31c fixed one level up.
    confusion dn e = do
      lem        <- confusionOf dn
      d          <- lookupInductive dn env
      (_, ls, as) <- spineOf (whnf env ctx (eqnCarrier e))
      let sub = maybe [] id (instantiateLevels (inductiveLevels d) ls)
      pure ( substLevel sub (inductiveLevel d)
           , foldl App (Global lem ls)
                   (as ++ [eqnLeft e, eqnRight e, Free (eqnVar e)])
           )

    -- One equation per argument, with its proof.
    --
    -- __The chain's own types are rebuilt here rather than read back__, because
    -- what the lemma answers with is @NoConfusion‹D› …@ and seeing the
    -- conjunction in it means reducing two eliminations. The two spellings are
    -- convertible and 'verify' is what holds this honest.
    conjuncts dn c e n = case (confusion dn e, lookupConstructor c env) of
      (Just (lv, p), Just (d, kc))
        | Just (_, _, us) <- former (eqnLeft e)
        , Just (_, _, vs) <- former (eqnRight e)
        , length us == length (constructorArguments kc)
        , length vs == length (constructorArguments kc) ->
            chain lv [ (argType d kc j, s, u) | (j, s, u) <- zip3 [0 ..] us vs ] p n
      _ -> (Nothing, n)
      where
        -- A constructor argument's type with the __actual__ parameters and level
        -- arguments in it. It mentions no earlier argument:
        -- 'Thena.Global.NoConfusion' declines a telescope where one does, which
        -- is why this substitution is the whole of it.
        argType d kc j =
          substituteAll (zip (map entryVar (inductiveParameters d)) (actuals d))
            (substLevelsIn (levelSub d) (entryType (constructorArguments kc !! j)))

        spine = spineOf (whnf env ctx (eqnCarrier e))
        actuals d = case spine of
          Just (_, _, as) -> take (length (inductiveParameters d)) as
          Nothing         -> []
        levelSub d = case spine of
          Just (_, ls, _) -> maybe [] id (instantiateLevels (inductiveLevels d) ls)
          Nothing         -> []

    -- The right-nested @And@ chain, projected: the equations in argument order
    -- and a proof of each.
    chain lv pieces p n = case pieces of
      [] -> (Just ([], []), n)   -- a nullary constructor, so @Unit@ — and the
                                 -- two sides were α-equal, so deletion fired
      [(i, a, b)] ->
        let (v, n1) = fresh n
         in (Just ([equationEqn v lv i a b], [p]), n1)
      (i, a, b) : rest ->
        let (v,  n1) = fresh n
            this     = equation lv i a b
            tail'    = conjoin lv [ equation lv i' a' b' | (i', a', b') <- rest ]
            (l, n2)  = andProject lv this tail' p True n1
            (r, n3)  = andProject lv this tail' p False n2
         in case chain lv rest r n3 of
              (Nothing, n4)       -> (Nothing, n4)
              (Just (es, ps), n4) ->
                (Just (equationEqn v lv i a b : es, l : ps), n4)

    equationEqn v lv i a b = Eqn v (Ident "q") (equation lv i a b) lv i a b

    -- ------------------------------------------------------------------
    -- Terms
    -- ------------------------------------------------------------------

    -- @elim Eq (I) (λ l r q -> residue ‹other› -> residue ‹solved›)
    -- ((λ a f -> f)) (u, v) q@ — J, used for the one thing it is needed for
    -- here: the method is wanted at the binder and the sub-problem proves it at
    -- the term.
    --
    -- __Which way the arrow goes is the orientation__, and that is the whole of
    -- the difference between @Eq I t x@ and @Eq I x t@: the domain is the
    -- residue at whichever side is /not/ the pattern variable, so that the
    -- motive at the equation's own two sides is always @residue t -> residue x@.
    coerce e onLeft residueAt n0' =
      ( Eliminate
          { eliminated = equality
          , levels     = [eqnLevel e]
          , parameters = [eqnCarrier e]
          , motive     = motiveTerm
          , methods    = [methodTerm]
          , indices    = [eqnLeft e, eqnRight e]
          , target     = Free (eqnVar e)
          }
      , n6 )
      where
        i = eqnCarrier e
        (zl, n1) = fresh n0'
        (zr, n2) = fresh n1
        (zq, n3) = fresh n2
        (zf, n4) = fresh n3
        (za, n5) = fresh n4
        (zb, n6) = fresh n5

        (from, to) | onLeft    = (zr, zl)
                   | otherwise = (zl, zr)

        motiveTerm =
          Lam (Ident "left") i (close zl
            (Lam (Ident "right") i (close zr
              (Lam (Ident "q") (equation (eqnLevel e) i (Free zl) (Free zr)) (close zq
                (Pi (Ident "at") (residueAt (Free from))
                    (close zf (residueAt (Free to)))))))))

        methodTerm =
          Lam (Ident "same") i (close za
            (Lam (Ident "at") (residueAt (Free za)) (close zb (Free zb))))

    -- @elim And (A B) (λ p -> A) ((λ l r -> l)) () q@, and the mirror image.
    -- Built rather than named, because @andLeft@ and @andRight@ are prelude
    -- /definitions/ and this module already depends on the prelude's
    -- constructors alone — the same line "Thena.Global.NoConfusion" draws.
    andProject lv a b q wantLeft n0' =
      ( Eliminate
          { eliminated = conjunction
          , levels     = [lv, lv]
          , parameters = [a, b]
          , motive     = Lam (Ident "p") pair (close pv (if wantLeft then a else b))
          , methods    = [ Lam (Ident "l") a (close av
                             (Lam (Ident "r") b
                                (close bv (Free (if wantLeft then av else bv))))) ]
          , indices    = []
          , target     = q
          }
      , n3 )
      where
        pair     = foldl App (Global conjunction [lv, lv]) [a, b]
        (pv, n1) = fresh n0'
        (av, n2) = fresh n1
        (bv, n3) = fresh n2

    -- @Eq {l} I a b@.
    equation l i a b = foldl App (Global equality [l]) [i, a, b]

    -- @And@ right-nested, which is the shape "Thena.Global.NoConfusion"
    -- conjoins its equations in.
    conjoin lv ts = case ts of
      []       -> Global (GlobalName "Unit") [lv]
      [t]      -> t
      t : rest -> foldl App (Global conjunction [lv, lv]) [t, conjoin lv rest]

    emptiness   = GlobalName "Empty"
    equality    = GlobalName "Eq"
    conjunction = GlobalName "And"

-- | One equation of a method, read apart.
--
-- It carries its binder, because a residual equation stays a hypothesis the
-- method takes and a transition that fires needs a variable to name its proof.
data Eqn = Eqn
  { eqnVar     :: Var
  , eqnIdent   :: Ident
  , eqnType    :: Core
  , eqnLevel   :: Level
  , eqnCarrier :: Core
  , eqnLeft    :: Core
  , eqnRight   :: Core
  }

-- | The hypothesis an equation is, so that a run of them is an ordinary
-- 'Context' and 'piOver' and 'lamOver' work over both halves of a problem.
entry :: Eqn -> Entry
entry e = Hypothesis (eqnVar e) (eqnIdent e) (eqnType e)

-- | Which transition applies to an equation.
data Transition
  = Delete
  | Conflict GlobalName
  | Inject GlobalName GlobalName   -- ^ the datatype, and the shared constructor
  | Solve Var Bool                 -- ^ the binder, and whether it is on the left
  | NoTransition

varsOf :: Context -> [Core]
varsOf = map (Free . entryVar)

eqnVars :: [Eqn] -> [Core]
eqnVars = map (Free . eqnVar)

applyTo :: Core -> [Core] -> Core
applyTo = foldl App

-- | 'close' then 'instantiate', which is the only way in and out of a
-- 'Thena.Core.Term.Scope' (§3.4) — the same reason
-- 'Thena.Tactics.Eliminate.substVars' is written this way.
substituting :: Var -> Core -> Core -> Core
substituting v t body = instantiate t (close v body)

substituteAll :: [(Var, Core)] -> Core -> Core
substituteAll s t = foldl (\acc (v, a) -> substituting v a acc) t s

substIn :: Var -> Core -> Context -> Context
substIn v t = map one
  where
    one (Hypothesis w i ty)   = Hypothesis w i (substituting v t ty)
    one (Definition w i s ty) = Definition w i (substituting v t s) (substituting v t ty)

substEqn :: Var -> Core -> Eqn -> Eqn
substEqn v t e = e
  { eqnType    = substituting v t (eqnType e)
  , eqnCarrier = substituting v t (eqnCarrier e)
  , eqnLeft    = substituting v t (eqnLeft e)
  , eqnRight   = substituting v t (eqnRight e)
  }
