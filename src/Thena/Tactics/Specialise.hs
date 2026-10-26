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
  )
import Thena.Core.Typing (check, sortOf)
import Thena.Errors (ChainBlocker (..), SpecialiseError (..))
import Thena.Global.Env
  ( ConstructorDefinition (..)
  , GlobalEnv
  , InductiveDefinition (..)
  , isDeclared
  , lookupConstructor
  , lookupInductive
  )
import Thena.Global.NoConfusion
  ( dependentPairInScope
  , noConfusionNames
  )
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
    -- __Two kinds__: an ambient entry a /friendly/ index abstracted outright,
    -- and __the target itself__ (MS9 phase 202, @~hc4ps@) — every ambient name
    -- it is known by, bound to this constructor applied to this method's
    -- arguments, which is what the method's conclusion already says its subject
    -- is.
    --
    -- __The target waited for phase 197.__ A rebinding is a
    -- 'Thena.Core.Context.Definition', and the target's one has a /type/ that
    -- mentions what the split refined — @s1 := eIf p p' a b sr@ is a
    -- @Step (ifthen p a b) (ifthen p' a b)@. While one definition anywhere in a
    -- nested split's forward closure cancelled every copy, binding it broke
    -- @examples\/determinacy-patterns.thena@ outright, @p@ stopping being
    -- refined to @true@. @Thena.Tactics.Eliminate@'s @generalisable@ skips a
    -- definition instead, so the entry stays exactly what it was and nothing is
    -- cancelled.
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
    MethodShape gens k friendly pars tgtNames lvls = shape

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
    reboundTerms d c delta sol = map (fmap (lamOver survivors)) (indices ++ scrutinee)
      where
        -- An ambient entry a friendly index abstracted now means this
        -- constructor's own index expression at that position.
        indices =
          [ (i, substituteAll sol (substituteAll argSub (substituteAll paramSub ix)))
          | (i, pos) <- friendly
          , ix <- take 1 (drop pos (constructorIndices c))
          ]

        -- __And the target means this constructor applied to this method's own
        -- arguments__ (MS9 phase 202, @~hc4ps@) — @mk V@ where the author wrote
        -- @d@, which is what the method's conclusion already says its subject
        -- is. It is the same rebinding as a friendly index's and it is written
        -- here for the same reason: the arguments are binders of this method.
        -- The solutions go through it because a forced argument has no binder
        -- left to name.
        scrutinee =
          [ (i, substituteAll sol
                  (Canonical cn lvls
                     (pars ++ map (Free . entryVar) conArgs)))
          | i <- tgtNames
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

    -- __An equation whose sides are re-read after a proof was substituted
    -- into them — MS9 phase 214.__ 'solution' supplies @refl@ for its own
    -- proof, so a later side that was @e* s@ is a transport along @refl@ and
    -- ι-contracts; reducing here is what lets the next transition match it, and
    -- what keeps a /residual/ equation readable instead of printing the spent J.
    --
    -- __The equation is restated rather than read back__, which is 'conjuncts'\'
    -- bargain one transition over: the two spellings are convertible and
    -- 'verify' is what holds it honest. Reduced at the ambient context for the
    -- same reason 'transition' is — the sides mention this method's own binders,
    -- which 'whnf' never needs to look up.
    reduceEqn e =
      let u = whnf env ctx (eqnLeft e)
          v = whnf env ctx (eqnRight e)
       in e { eqnLeft  = u
            , eqnRight = v
            , eqnType  = equation (eqnLevel e) (eqnCarrier e) u v
            }

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

        -- __THREE OF THE FOUR DECLINE WHERE A LATER EQUATION NAMES THIS
        -- ONE'S PROOF, AND THE EQUATION IS KEPT RATHER THAN THE SPLIT REFUSED
        -- — MS9 phase 214.__ A dependent index telescope states a later
        -- equation after transporting its side along an earlier one (§3.2 of
        -- /Pattern Matching Without K/), so firing a transition that /removes/
        -- that earlier binder leaves the later equation about a variable that
        -- is gone — a 'SpecialisedIllTyped' naming two generated variables,
        -- which is the error reserved for this module being wrong about its own
        -- construction.
        --
        -- __@conflict@ is the one that carries a chain, and it does so for
        -- free__: it claims nothing and binds the equation it fired on, so
        -- everything after that equation — transports included — stays in scope
        -- under the @Empty@ elimination. The other three each want something
        -- Thena does not have:
        --
        --   * __deletion__ would need @q ≃ refl@ for an arbitrary proof of
        --     @Eq I t t@, which is UIP, and that is the one place the paper
        --     says the K axiom actually enters. It is not coming.
        --   * __injectivity__ would need @noConfusion@ /backwards/ and its
        --     round-trip law — the paper's @noConfD⁻¹@ and @isLeftInvD@, §3.5 —
        --     to restate the later transport along the new proof. Neither is
        --     generated.
        --   * __solution__ would need the paper's own @solution@, which is
        --     @J A x₀ Φ m x e@ with @Φ@ abstracting the /varying/ end and the
        --     proof while the fixed end stays fixed — __based path induction__.
        --     @Eq@ is declared with both ends as indices, so what Thena derives
        --     is Martin-Löf's J, whose motive abstracts both; and the residue
        --     cannot be abstracted in the fixed end, because a later equation's
        --     right side inhabits its carrier by computation and not by its
        --     spelling. 'coerce' is the non-dependent J this leaves in place.
        --
        -- __So they keep the equation, and that is this module's own law rather
        -- than a new concession__: an equation no transition applies to stays a
        -- hypothesis the method takes, because refusing would withdraw a split
        -- the user can still do by hand. The split now goes through with a
        -- residual equation where it refused outright, and a family with a
        -- dependent index telescope splits for the first time.
        go bfr (e : after) n =
          let keep     = go (e : bfr) after n
              -- Counting from 1, which is how 'NotAnEquation' and the
              -- declaration readers count a position the user can see.
              blocked why =
                ( Left (TransportedEquation why
                          (length eqs - length after) (eqnType e))
                , n )
           in case transition delta e of
                NoTransition -> keep
                Conflict dn  -> conflict bfr e after n dn
                Delete
                  | namedLater e after -> blocked ByDeletion
                  | otherwise          -> deletion bfr e after n
                Inject dn c
                  | namedLater e after -> blocked ByInjectivity
                  | otherwise          -> injection bfr e after n dn c
                Solve x left
                  | not (namedLater e after) -> solution bfr e after n x left
                  | singletonInScope env     -> solution bfr e after n x left
                  | otherwise                -> blocked BySolution

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
        --
        -- __AND IT SUPPLIES @refl@ FOR ITS OWN PROOF WHERE A LATER EQUATION WAS
        -- TRANSPORTED ALONG IT — MS9 phase 214, @~7gmvr@ step three.__ The
        -- sub-problem is then taken at @q := refl@ as well as at @x := other@,
        -- every such transport ι-contracts, and what is left is an ordinary
        -- homogeneous equation the transitions can match. 'coerceChained' is
        -- what makes that honest and 'reduceEqn' is what lets the next
        -- transition see it.
        --
        -- __A flat index telescope takes neither__: @carries@ is false, the
        -- substitution is the identity, and 'coerce' builds exactly the term it
        -- always did, down to the variables minted.
        solution bfr e after n x onLeft =
          let before    = reverse bfr
              (d1, d2)  = break ((== x) . entryVar) delta
              d2'       = drop 1 d2
              other     = if onLeft then eqnRight e else eqnLeft e
              carries   = namedLater e after
              reflHere  = reflAt (eqnLevel e) (eqnCarrier e) other
              -- @∀ Δ₂ -> before -> after -> t@ with @z@ for the binder being
              -- removed and @q@ for this equation's proof: at @(x, its own
              -- proof)@ the type this term must end at, at @(other, refl)@ the
              -- sub-problem's. A flat telescope mentions @q@ nowhere, so the
              -- second argument does nothing there.
              base      = piOver (d2' ++ map entry (before ++ after)) t
              residueAt z q =
                substituting (eqnVar e) q (substituting x z base)
              carry | carries   = substEqn (eqnVar e) reflHere
                    | otherwise = id
              -- Where the residue's universe is read, which 'coerceChained'
              -- needs for the motive that states @Φ@ as a type. @base@ binds
              -- @Δ₂@ and every equation itself, so only @Δ₁@, the binder being
              -- removed and this equation stand outside it.
              lvlCtx = ctx ++ d1 ++ take 1 d2 ++ [entry e]
           in case solve hv (d1 ++ substIn x other d2')
                            (map (reduceEqn . carry . substEqn x other)
                                 (before ++ after))
                            (substituting (eqnVar e) reflHere
                               (substituting x other t)) n of
                (Left err, n1) -> (Left err, n1)
                (Right (want, g, sol), n1) ->
                  case built e onLeft x residueAt carries lvlCtx n1 of
                   (Left err, n2) -> (Left err, n2)
                   (Right co, n2) ->
                     ( Right ( want
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

        -- Which coercion a solution needs: the plain J where nothing was
        -- transported along this equation, and the singleton construction where
        -- something was. Split here so that the common case cannot pay for the
        -- rare one, in term size or in minted variables.
        built e onLeft x residueAt carries lvlCtx n
          | not carries =
              let (co, n1) = coerce e onLeft (\z -> residueAt z (Free (eqnVar e))) n
               in (Right co, n1)
          | otherwise = case sortOf env lvlCtx n (residueAt (Free x) (Free (eqnVar e))) of
              (Left te, _, n1) -> (Left (SpecialisedIllTyped te), n1)
              (Right l, _, n1) ->
                let (co, n2) = coerceChained e onLeft x residueAt l n1
                 in (Right co, n2)

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

    -- @noConfusion‹D›@, if it was generated at all — it is declined for a
    -- datatype whose prelude is missing a piece ("Thena.Global.NoConfusion"),
    -- and without it neither discrimination transition can fire, so the
    -- equation is kept.
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

    -- @NoConfusion‹D› p⃗ i⃗ u v@ — the family at the same arguments, which /is/
    -- the chain: the lemma's result type, before anything is projected out of
    -- it. 'conjuncts' reduces this rather than restating what the generator
    -- wrote.
    confusionFamily dn e = do
      fam         <- family
      (_, ls, as) <- spineOf (whnf env ctx (eqnCarrier e))
      pure (foldl App (Global fam ls) (as ++ [eqnLeft e, eqnRight e]))
      where
        nm = fst (noConfusionNames dn)
        family | isDeclared nm env = Just nm
               | otherwise         = Nothing

    -- One equation per argument, with its proof.
    --
    -- __The chain is read apart rather than restated.__ Its shape is equation 18
    -- of §3.2 of /Pattern Matching Without K/, and
    -- "Thena.Global.NoConfusion" is where that equation is written: for a
    -- dependent argument telescope a later equation is stated about an earlier
    -- argument /transported along the earlier equation/, which only the
    -- generator knows how to build. So this reduces the family to the chain and
    -- walks down it, and the two cannot drift apart because there is one
    -- statement of the nesting. Until MS9 phase 215 the types were rebuilt here
    -- and a dependent telescope was declined for want of the transports.
    --
    -- __Two tracks of the same shape, and that is the whole of the
    -- bookkeeping.__ @tyH@ carries, for each earlier equation, the /binder/ this
    -- method will bind for its proof, which is what the sub-problem's
    -- hypotheses have to say; @tyP@ carries the /projection/, which is what the
    -- proof terms are actually typed at. They are destructured together, so a
    -- shape they disagree on is a decline rather than an ill-typed method.
    conjuncts dn c e n = case (confusion dn e, confusionFamily dn e) of
      (Just (_, p), Just ty)
        | Just _ <- lookupConstructor c env -> chain ty ty p n
      _ -> (Nothing, n)
      where
        -- The chain, walked: one equation per constructor argument in argument
        -- order, each with a projection out of @p@ that proves it.
        --
        -- The proofs are applied to the sub-problem in this order, so the type
        -- of the @j@th is the @j@th equation with the earlier /projections/ in
        -- it — which is exactly what applying the earlier proofs to the
        -- sub-problem's Π type instantiates it to.
        chain tyH tyP p n0' = case (linkOf env ctx tyH, linkOf env ctx tyP) of
          -- A nullary constructor, so @Unit@ — and the two sides were α-equal,
          -- so deletion fired rather than injectivity.
          (LinkUnit, LinkUnit) -> (Just ([], []), n0')
          (LinkLast, LinkLast) ->
            let (v, n1) = fresh n0'
             in case eqnAt v tyH of
                  Nothing -> (Nothing, n1)
                  Just q  -> (Just ([q], [p]), n1)
          -- No later equation names this one's proof, so the generator held the
          -- pair in @And@ and the rest of the chain is independent of it.
          (LinkAnd _ aH bH, LinkAnd ls aP bP) ->
            let (v, n1) = fresh n0'
                (l, n2) = andProject ls aP bP p True n1
                (r, n3) = andProject ls aP bP p False n2
             in step v aH bH bP l r n3
          -- One does, so the pair is @DPair@ and the rest of the chain is a
          -- function of this equation's proof.
          (LinkPair _ aH bH, LinkPair ls aP bP) ->
            let (v,  n1) = fresh n0'
                (hd, n2) = firstOf ls aP bP p n1
                (tl, n3) = secondOf ls aP bP p n2
             in step v aH (App bH (Free v)) (App bP hd) hd tl n3
          _ -> (Nothing, n0')
          where
            -- This equation, bound at @v@, and then the rest of the chain.
            step v aH restH restP prf rest n1 = case eqnAt v aH of
              Nothing -> (Nothing, n1)
              Just q  -> case chain restH restP rest n1 of
                (Nothing, n2)       -> (Nothing, n2)
                (Just (es, ps), n2) -> (Just (q : es, prf : ps), n2)

    -- One equation of the chain, as the hypothesis the method will bind for it.
    -- 'equationOf' is the same reading one level out, over a binder the method
    -- already has.
    --
    -- __Only the @Eq@ application is restated; its three arguments are kept as
    -- the chain states them__, transports and all. The head has to be restated
    -- because the chain's last link may still be the family application itself
    -- — a one-argument constructor's chain /is/ its only equation, so nothing
    -- was projected and nothing reduced on the way. 'reduceEqn' is what
    -- contracts the transports in the arguments, once a solution has supplied
    -- @refl@ for the proof they are along.
    eqnAt v ty = case spineOf (whnf env ctx ty) of
      Just (GlobalName "Eq", [l], [i, a, b]) ->
        Just (Eqn v (Ident "q") (equation l i a b) l i a b)
      _ -> Nothing

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
    --
    -- __The levels are the pair's own, read off the chain__ rather than assumed
    -- to be the datatype's: the generator states every equation at one level
    -- today, and nothing here has to know that.
    andProject ls a b q wantLeft n0' =
      ( Eliminate
          { eliminated = conjunction
          , levels     = ls
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
        pair     = foldl App (Global conjunction ls) [a, b]
        (pv, n1) = fresh n0'
        (av, n2) = fresh n1
        (bv, n3) = fresh n2

    -- @elim DPair (A B) (λ p -> A) ((λ x y -> x)) () p@ — the first projection,
    -- which is the equation a @DPair@ link of the chain heads, and
    -- @λ p -> B (fst p)@ for the second, which is the rest of the chain at that
    -- proof. 'andProject'\'s reason for building rather than naming them: @fst@
    -- and @snd@ are prelude /definitions/.
    firstOf ls a b p n0' =
      ( Eliminate
          { eliminated = dependentPair
          , levels     = ls
          , parameters = [a, b]
          , motive     = Lam (Ident "p") (pairOf ls a b) (close zv a)
          , methods    = [ Lam (Ident "x") a (close xv
                             (Lam (Ident "y") (App b (Free xv))
                                (close yv (Free xv)))) ]
          , indices    = []
          , target     = p
          }
      , n3 )
      where
        (zv, n1) = fresh n0'
        (xv, n2) = fresh n1
        (yv, n3) = fresh n2

    secondOf ls a b p n0' =
      let (zv, n1)  = fresh n0'
          (fp, n2)  = firstOf ls a b (Free zv) n1
          (xv, n3)  = fresh n2
          (yv, n4)  = fresh n3
       in ( Eliminate
              { eliminated = dependentPair
              , levels     = ls
              , parameters = [a, b]
              , motive     = Lam (Ident "p") (pairOf ls a b) (close zv (App b fp))
              , methods    = [ Lam (Ident "x") a (close xv
                                 (Lam (Ident "y") (App b (Free xv))
                                    (close yv (Free yv)))) ]
              , indices    = []
              , target     = p
              }
          , n4 )

    pairOf ls a b = foldl App (Global dependentPair ls) [a, b]

    -- @Φ (fixed, refl) -> Φ (‹the binder›, its own proof)@, where @Φ z q@ is
    -- the residue at @z@ for the binder being removed and @q@ for this
    -- equation's proof.
    --
    -- __THIS IS THE PAPER'S @solution@ AND IT IS WHAT A TRANSPORTED CHAIN
    -- NEEDS — MS9 phase 214, @~7gmvr@ step three.__ §3.5 states it as
    --
    -- @
    -- solution : (Φ : (x : A) (e : x₀ ≡ x) -> Set) -> Φ x₀ refl
    --              -> (x : A) (e : x₀ ≡ x) -> Φ x e
    -- @
    --
    -- — __based path induction__, whose motive abstracts the end that varies
    -- and the proof while the other end stays the term it is. 'coerce''s plain
    -- J cannot do it: @Eq@ is declared with both ends as indices, so what Thena
    -- derives abstracts both, and __the residue cannot be abstracted in the
    -- fixed end__ — a later equation's right side inhabits its carrier by
    -- computation and not by its spelling, so @fz m : Fin (s m)@ does not
    -- follow @s m@ to a motive binder. That was measured, not reasoned.
    --
    -- __So based path induction is derived, by the singleton that is
    -- contractible__, and the derivation costs no universe: @Σ (y : I). I y ≡
    -- fixed@ has one inhabitant up to @Eq@, the ordinary J proves it
    -- (@contract@ below, whose motive is an equation and so stays at the
    -- carrier's own level), and transporting @Φ@ along that equation is the
    -- second J. The alternative — quantifying over the family, @∀ (P : …) ->
    -- P x₀ refl -> P x e@ — is one universe up, which is the cost @~7gmvr@
    -- named for the route not taken.
    --
    -- __@Φ@ is written once__, as the method of a @DPair@ elimination whose
    -- motive is @λ _ -> Type ℓ@, so @Φ (z, p)@ ι-contracts to the residue and
    -- the residue is not copied per occurrence. @ℓ@ is why 'built' reads the
    -- universe.
    coerceChained e onLeft x residueAt lvl n0' = (carry, n9)
      where
        i  = eqnCarrier e
        lv = eqnLevel e

        -- The end that does not vary. A residual equation after this one is
        -- stated about a transport whose other index is this term, which is
        -- precisely why it may not move.
        fixed = if onLeft then eqnRight e else eqnLeft e

        -- @λ y . Eq I y fixed@, or its mirror — the family whose total space is
        -- the singleton. Which side @y@ falls on is the orientation, the same
        -- one 'coerce' reads.
        sideways z f | onLeft    = equation lv i z f
                     | otherwise = equation lv i f z
        famOf f    = Lam (Ident "y") i (close yv (sideways (Free yv) f))
        singOf f   = foldl App (Global dependentPair [lv, lv]) [i, famOf f]
        ptOf f z p = Canonical dependentPairMk [lv, lv] [i, famOf f, z, p]

        sing     = singOf fixed
        ptFixed  = ptOf fixed fixed (reflAt lv i fixed)
        ptBinder = ptOf fixed (Free x) (Free (eqnVar e))

        (yv, n1) = fresh n0'
        (sv, n2) = fresh n1
        (mv, n3) = fresh n2
        (zv, n4) = fresh n3
        (pv, n5) = fresh n4

        -- @Φ@ as a function of the pair: @elim DPair (I, fam) (λ _ . Type ℓ)
        -- ((λ z p . residue)) () s@, under one λ so the residue is written once.
        psi = Lam (Ident "s") sing (close sv (Eliminate
                { eliminated = dependentPair
                , levels     = [lv, lv]
                , parameters = [i, famOf fixed]
                , motive     = Lam (Ident "p") sing (close mv (Universe lvl))
                , methods    = [ Lam (Ident "z") i (close zv
                                   (Lam (Ident "q") (sideways (Free zv) fixed) (close pv
                                      (residueAt (Free zv) (Free pv))))) ]
                , indices    = []
                , target     = Free sv
                }))

        -- @(fixed, refl) ≡ (x, q)@ — the singleton is contractible, and the
        -- ordinary J is all it takes: at @refl@ the two pairs are the same pair.
        (ca, n6) = freshThree n5
        contract = Eliminate
          { eliminated = equality
          , levels     = [lv]
          , parameters = [i]
          , motive     = contractMotive
          , methods    = [contractMethod]
          , indices    = [eqnLeft e, eqnRight e]
          , target     = Free (eqnVar e)
          }
        (cl, cr, ce) = ca
        contractMotive =
          Lam (Ident "left") i (close cl
            (Lam (Ident "right") i (close cr
              (Lam (Ident "q") (equation lv i (Free cl) (Free cr)) (close ce
                (let f  = if onLeft then Free cr else Free cl
                     vy = if onLeft then Free cl else Free cr
                  in equation lv (singOf f)
                       (ptOf f f (reflAt lv i f))
                       (ptOf f vy (Free ce))))))))
        contractMethod =
          Lam (Ident "same") i (close cm
            (Canonical reflexivity [lv]
               [ singOf (Free cm)
               , ptOf (Free cm) (Free cm) (reflAt lv i (Free cm)) ]))

        -- … and @Φ@ carried along it, which is the prelude's @transport@ at the
        -- singleton: motive @λ u v w . Φ u -> Φ v@, method the identity.
        (cm, n7) = fresh n6
        (tu, n8) = freshThree n7
        (tl, tr, tw) = tu
        (td, n9) = freshTwo n8
        (ta, tz) = td
        carry = Eliminate
          { eliminated = equality
          , levels     = [lv]
          , parameters = [sing]
          , motive     = Lam (Ident "u") sing (close tl
              (Lam (Ident "v") sing (close tr
                (Lam (Ident "w") (equation lv sing (Free tl) (Free tr)) (close tw
                  (Pi (Ident "at") (App psi (Free tl))
                      (close ta (App psi (Free tr)))))))))
          , methods    = [ Lam (Ident "same") sing (close tz
                             (Lam (Ident "at") (App psi (Free tz)) (close ta (Free ta)))) ]
          , indices    = [ptFixed, ptBinder]
          , target     = contract
          }

    -- @Eq {l} I a b@.
    equation l i a b = foldl App (Global equality [l]) [i, a, b]

    -- @refl {l} I a@ — the spelling "Thena.Tactics.Eliminate" discharges a tied
    -- index's equation with at the use site, which is why a transport along one
    -- of these ι-contracts the moment 'solution' supplies it.
    reflAt l i a = Canonical reflexivity [l] [i, a]

    emptiness        = GlobalName "Empty"
    equality         = GlobalName "Eq"
    reflexivity      = GlobalName "refl"
    conjunction      = GlobalName "And"
    dependentPair    = GlobalName "DPair"
    dependentPairMk  = GlobalName "dpair"

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

-- | One link of the chain @noConfusion‹D›@ answers with, as
-- "Thena.Global.NoConfusion" nests it.
--
-- __@DPair@ against @And@ is the one distinction that matters__, and it is not a
-- choice this module makes: the generator holds an equation in a dependent pair
-- exactly where a later equation is stated about its proof, and in @And@ where
-- one is not. Reading the nesting back is how the two stay in step.
data Link
  = LinkUnit                    -- ^ @Unit@, so the constructor takes no arguments
  | LinkAnd [Level] Core Core   -- ^ @And A B@ — the rest of the chain is independent
  | LinkPair [Level] Core Core  -- ^ @DPair A B@ — it is a function of this proof
  | LinkLast                    -- ^ anything else, which must be the final equation

-- | The chain's head, reduced far enough to see which link it is.
--
-- Reducing is unfolding the family and taking two ι-steps, one per side; both
-- sides of an injectivity are saturated applications of the same constructor, so
-- what comes out is the diagonal case. __Only the head reduces__, so the
-- equations inside are left spelled as the generator wrote them.
linkOf :: GlobalEnv -> Context -> Core -> Link
linkOf env ctx t = case spineOf (whnf env ctx t) of
  Just (GlobalName "Unit",  _,  [])     -> LinkUnit
  Just (GlobalName "And",   ls, [a, b]) -> LinkAnd ls a b
  Just (GlobalName "DPair", ls, [a, b]) -> LinkPair ls a b
  _                                     -> LinkLast

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

-- | Does a later equation of the block mention this one's proof?
--
-- __It is the one question a dependent index telescope forces on the
-- transitions__ (MS9 phase 214, @~7gmvr@ step three). §3.2 of /Pattern Matching
-- Without K/ states a later equation after transporting its side along the
-- earlier ones, so the answer is @True@ exactly where removing this equation's
-- binder would leave a later one about a variable that is gone. @solve@'s @go@
-- is where it decides something, and the module header says what each
-- transition does about it.
namedLater :: Eqn -> [Eqn] -> Bool
namedLater e after = any ((eqnVar e `elem`) . freeVars . eqnType) after

-- | Is the contractible singleton 'coerceChained' is built from available?
--
-- __It is @DPair@ of the prelude's own shape, matched structurally rather than
-- by name__ — "Thena.Global.NoConfusion" draws that line and this is the same
-- one, for the same reason: a user may declare something else called @DPair@,
-- and the cost of not looking would be a type error from a term they never
-- wrote. A session without the prelude has none, and then the solution
-- transition declines a transported chain and the equation is kept.
singletonInScope :: GlobalEnv -> Bool
singletonInScope env = dependentPairInScope env && isDeclared (GlobalName "dpair") env

-- | Three fresh variables, and two — @coerceChained@ mints eleven and a
-- run of @let@ pairs for them is unreadable.
freshThree :: Int -> ((Var, Var, Var), Int)
freshThree n =
  let (a, n1) = fresh n
      (b, n2) = fresh n1
      (c, n3) = fresh n2
   in ((a, b, c), n3)

freshTwo :: Int -> ((Var, Var), Int)
freshTwo n =
  let (a, n1) = fresh n
      (b, n2) = fresh n1
   in ((a, b), n2)

substEqn :: Var -> Core -> Eqn -> Eqn
substEqn v t e = e
  { eqnType    = substituting v t (eqnType e)
  , eqnCarrier = substituting v t (eqnCarrier e)
  , eqnLeft    = substituting v t (eqnLeft e)
  , eqnRight   = substituting v t (eqnRight e)
  }
