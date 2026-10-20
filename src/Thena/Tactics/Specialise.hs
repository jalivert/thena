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
import Thena.Tactics.Eliminate (spineOf)

-- | What specialisation worked out: the subgoal, and the refinement.
--
-- 'specialisedGoal' is __zero or one__ hole, and a list rather than a 'Maybe'
-- so that it is exactly 'Thena.Tactics.Eliminate.Elimination'\'s shape —
-- "Thena.Engine" claims them with the same fold, and the empty case is a
-- conflict closing the method outright.
--
-- 'specialisedTerm' mentions that hole as @'Free' v@, so it is well typed only
-- in a context extended by it. 'specialise' has already checked it there.
--
-- 'specialisedForced' is __one entry per constructor argument__, in declaration
-- order: 'Nothing' where the argument survived as a binder of the subgoal, and
-- @'Just' t@ where an equation determined it to be @t@ and the binder went.
-- __Only the solution transition removes a binder__, so only it writes an entry
-- here (MS9 phase 185).
--
-- 'specialisedRefined' is __the same report for the generalised copies__, in the
-- order the motive quantified them (MS9 phase 191). @'Just' t@ is a copy an
-- equation solved, which is how an index position bound outside the split comes
-- to be refined; 'Nothing' is one that survived as a binder, which is how a
-- /hypothesis/ about such a position reaches the arm with its type refined.
-- __The caller binds both under the ambient entry's own name__, so the arm's
-- body is written against the refinement — a @define@ for the first and a
-- @prim-lambda@ for the second, which is 'specialisedForced'\'s own treatment
-- and deliberately the same mechanism.
--
-- __And unlike a forced constructor argument, a solved copy MAY mention the
-- method's own binders.__ The solving side of an equation about a copy is the
-- /constructor's/ index, so @a'@ comes out as @c1@ rather than as a term of the
-- ambient context. Those binders are @Δc@ and the hypotheses, which stand
-- before the copies, so the @define@ is well scoped exactly where the caller
-- puts it — after the pattern's binders and after the hypotheses, never before.
--
-- __This is the only thing that knows.__ The subgoal is a type with fewer
-- binders than the constructor has arguments and nothing in it says which ones
-- are missing, so a clause introducing an arm's pattern variables cannot work it
-- out — which is why phase 184's clause failed on @vtail@.
--
-- __A forced term is written in the ambient context__ and mentions no binder of
-- the method, forced or surviving. The solving side of an equation is always the
-- /target/'s index, which lives where the elimination was written; injectivity
-- decomposes both sides in step and so preserves that split, and a solution
-- substitutes into the equations that follow, never into the target. So the
-- entries here are in scope wherever the subgoal is, which is what lets the
-- caller bind one with @define@ above the hole.
data Specialisation = Specialisation
  { specialisedGoal    :: [(Var, Ident, Core)]
  , specialisedTerm    :: Core
  , specialisedForced  :: [Maybe Core]
  , specialisedRefined :: [Maybe Core]
  }
  deriving (Eq, Show)

-- | Specialise the method of @c@ whose last @k@ binders before the body are the
-- equations the elimination stated.
--
-- __All three of those are facts the caller has and the type does not.__ A
-- method type is Π binders all the way down, and nothing in it marks where the
-- constructor's own telescope ends and the equations begin — a constructor may
-- itself take a proof of an equation, and the body after the equations may be a
-- Π of its own, so counting binders settles nothing. So @c@ gives the
-- constructor's own arguments, @h@ is how many induction hypotheses this
-- method carries, and @k@ is how many indices were tied.
--
-- __@h@ IS AN ARGUMENT AND NOT READ OFF THE DECLARATION — MS9 phase 188.__ It
-- used to be counted here, as one per recursive constructor argument, which is
-- 'Thena.Global.Env.eliminatorType'\'s method shape — and that silently assumed
-- the caller was eliminating. @caseD@'s methods carry none, so the assumption
-- made @case … of@ refuse its own methods as misshapen. The caller knows which
-- scheme it asked for; this does not, and no longer guesses.
--
-- __@g@ is how many copies the motive generalised__ (MS9 phase 191), and the
-- same argument applies to it: nothing in the type marks where the copies end
-- and the equations begin, and the caller is the one that knows. They join
-- @Δc@ and the hypotheses as __pattern variables__, which is the only change
-- the four transitions need.
specialise
  :: GlobalEnv -> Context -> Int -> GlobalName -> Int -> Int -> Int -> Core
  -> (Either SpecialiseError Specialisation, Int)
specialise env ctx n0 cn h g k mty = case lookupConstructor cn env of
  Nothing -> (Left (NotThatConstructor cn), n0)
  Just (d, c)
    | k < 0 || g < 0 -> (Left (MethodNotShaped (arity d c) k mty), n0)
    | otherwise -> case peel (arity d c + g + k) mty n0 of
        Nothing -> (Left (MethodNotShaped (arity d c) k mty), n0)
        Just (tel, body, n1) ->
          let (delta, raw) = splitAt (arity d c + g) tel
           in case mapM equationOf raw of
                Nothing -> (Left (NotAnEquation (map entryType raw)), n1)
                Just es ->
                  let (hv, n2) = fresh n1
                   in case solve hv delta es body n2 of
                        (Left e, n3) -> (Left e, n3)
                        (Right (want, tm, sol), n3) ->
                          verify hv want tm (forced c delta sol)
                                 (refined d c delta sol) n3
  where
    -- One binder per constructor argument, plus the hypotheses the caller says
    -- this method carries. 'Thena.Global.Env.eliminatorType'\'s @methodType@
    -- read backwards for 'Thena.Global.Env.Inductive', and @caseD@'s for
    -- 'Thena.Global.Env.CaseAnalysis', where @h@ is zero.
    arity _ c = length (constructorArguments c) + h

    -- One entry per constructor argument, which is the __first__ stretch of the
    -- telescope: 'Thena.Global.Env.eliminatorType' states the arguments and then
    -- the induction hypotheses, so the arguments are a prefix of @delta@ and no
    -- count has to be carried alongside. A hypothesis is never solved — an
    -- equation is over the datatype's indices and a hypothesis is a proof of the
    -- motive — and if one ever were, it would simply not be reported here.
    forced c telescope sol =
      [ lookup (entryVar e) sol
      | e <- take (length (constructorArguments c)) telescope
      ]

    -- The same report for the generalised copies, which are the __last__ @g@
    -- entries of the telescope: 'Thena.Tactics.Eliminate' quantifies them after
    -- the target, so the motive puts them after the constructor's arguments and
    -- after the hypotheses. Nothing has to be carried to find them — @arity@ is
    -- where they begin.
    refined d c telescope sol =
      [ lookup (entryVar e) sol | e <- drop (arity d c) telescope ]

    -- The hole and the term that uses it, checked in the context that will hold
    -- both. Checking here is the whole of §7.2's bargain for a coarse op: a
    -- wrong proof term is caught, so only the caller's /choice/ of what to
    -- specialise is unguarded.
    verify hv want tm fs gs n =
      let hole = [ (hv, Ident (nameOf cn ++ "Case"), w) | Just w <- [want] ]
          with = ctx ++ [ Hypothesis v i t | (v, i, t) <- hole ]
       in case check env with n tm mty of
            (Left e, _, n1)   -> (Left (SpecialisedIllTyped e), n1)
            (Right (), _, n1) -> (Right (Specialisation hole tm fs gs), n1)

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
    -- @(binder, the term it was solved to)@ — 'specialisedForced' read off
    -- @delta@. Every term in that list is already resolved, because a solution
    -- applies the sub-problem's own pairs to its term before recording it, so
    -- nothing in the list mentions a binder the list removes.
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
