-- | Tying a recursive call to the induction hypothesis it is (MS9 phase 186).
--
-- A definition's body is elaborated with the name being defined bound as an
-- ordinary assumption, so @double@ resolves inside @double@'s own body and no
-- rule has to know that a call is recursive. What
-- 'Thena.Development.Partial.extract' then hands back is
--
-- @
-- λ double -> λ n -> elim Nat … (λ m ih -> succ (double m)) … n
-- @
--
-- and this module replaces each application of that assumption by the
-- hypothesis it denotes, answering the body with the assumption gone.
--
-- == Why it is a pass over the term and not a lookup at the call site
--
-- __His ruling of 2026-10-19__; @.claude\/RULINGS.md@ carries it with what the
-- literature does instead. The short form: the usual translation resolves a
-- call where it is written, by searching the context for a hypothesis whose
-- type carries a /label/ saying which call it answers — and that label is an
-- extension of the core syntax, which this milestone does not make. Nothing
-- else tells a hypothesis from an ordinary assumption: where the motive does
-- not depend on the target, @m : Nat@ and the hypothesis about @m@ have the
-- same type, so a search by type picks the wrong one and still typechecks.
--
-- __What this does instead is read the hypotheses off the declaration.__
-- 'Thena.Global.Env.eliminatorType' states a method's binders as the
-- constructor's arguments and then one hypothesis per /recursive/ argument, in
-- argument order, so a method that is a λ-chain exposes them at positions the
-- datatype already fixes. No marker is needed because nothing was ever
-- ambiguous about the shape.
--
-- == The two things that make the walk less obvious than it sounds
--
-- __A method is reached through the names elaboration bound it to.__ The term
-- is a chain of @let@s and the 'Eliminate' node is handed /variables/, so the
-- λ-chain a method is cannot be recognised where it is written — only where it
-- is used, which is further in. So the walk reports upwards: it answers, beside
-- the rewritten term, which free variables were used as a method and of what
-- shape, and a @let@ walks its body before its value so that the answer is in
-- hand by the time the value is reached. A method bound through an alias
-- propagates the shape one more step, which is exactly what elaboration's
-- @okNodeCase@/@okNodeMethod@ pair needs.
--
-- __A method the specialiser rewrote yields nothing, AND THAT IS NO LONGER
-- CORRECT — measured 2026-10-20.__ Where an index is pinned the method comes
-- back as a coercion around a subgoal, so the arm's binders belong to the
-- subgoal rather than to the method and a call in it matches nothing this
-- collected. It is refused by name. The claim that stood here was that nothing
-- was lost, because a pinned index guards every hypothesis of such a method
-- with an equation — @vtail@'s is @Eq Nat n (succ n)@. **Generalisation
-- invalidated it.** The motive quantifies a copy of every ambient entry a rule
-- demands, the induction hypothesis of the enclosing arm is such an entry
-- whenever its type mentions one, and its copy arrives UNGUARDED and refined to
-- the arm's own subject:
--
-- @
-- usMethod : ∀ (a1 : N) (b : N) -> Up a1 b -> (…)
--   -> ∀ (a2 : N) -> Up a2 a' -> (∀ (q : N) -> Up a2 q -> Eq {0} N a' q)
--   -> Eq {0} N (s a1) (s a2) -> Eq {0} N (s a') (s b)
-- @
--
-- The second-to-last binder is the hypothesis a recursion in that arm wants,
-- and after the equation solves @a2 := a1@ it is about the arm's own variable.
-- **So there IS a usable recursion in such an arm, and it is lost.** That is
-- @~bq3rn@, and what it waits on is the specialiser saying which binder of the
-- subgoal is which — see that item.
--
-- Where it sits in §2.5: beside "Thena.Tactics.Eliminate" and
-- "Thena.Tactics.Specialise" — above "Thena.Core.Term" and
-- "Thena.Global.Env", below "Thena.Engine".
module Thena.Tactics.Recurse
  ( resolveRecursion
  ) where

import Data.List (nub)

import Thena.Core.Context (Context, Entry (..), entryType)
import Thena.Core.Term
  ( Core (..)
  , Var
  , close
  , fresh
  , freeVars
  , open
  )
import Thena.Errors (RecursionError (..))
import Thena.Global.Env
  ( ConstructorDefinition (..)
  , GlobalEnv
  , InductiveDefinition (..)
  , lookupInductive
  , recursiveArgument
  )

-- | A method's telescope, as the declaration states it: how many constructor
-- arguments come first, and which of them each following hypothesis is about.
--
-- Both numbers are positions in the λ-chain, so nothing here is a guess about
-- the term — 'Thena.Global.Env.eliminatorType' built the type these positions
-- belong to from the same reading.
data Shape = Shape Int [Int]
  deriving (Eq, Show)

-- | What the walk carries down: the assumed name it is tying, the local
-- definitions an argument may have to be read through, and the hypotheses in
-- scope.
data Walking = Walking
  { subject    :: Var
  , aliases    :: [(Var, Core)]
  , hypotheses :: [(Var, Var)]
  , binders    :: Context
    -- ^ every binder descended under, so a refusal can name what the user
    -- wrote instead of a variable number. The same courtesy
    -- 'Thena.Errors.UnknownVariable' already does
  }

-- | Take @λ f -> body@, tie every call of @f@ to the hypothesis it is, and
-- answer the body.
--
-- The argument is what 'Thena.Development.Partial.extract' gives for a
-- development whose own subject was assumed: one λ binding the name being
-- defined, over everything the body elaborated to.
--
-- __It refuses rather than guesses.__ An application of @f@ naming no
-- hypothesis in scope is not recursion this translation can express, and an
-- occurrence of @f@ anywhere else would leave the body open.
resolveRecursion :: GlobalEnv -> Int -> Core -> (Either RecursionError Core, Int)
resolveRecursion env n0 tm = case tm of
  Lam i ty sc ->
    let (f, n1) = fresh n0
        -- The assumed name itself is a binder, so a refusal names the function
        -- rather than a variable number.
        start = Walking f [] [] [Hypothesis f i ty]
     in case go start (open f sc) n1 of
          (Left e, _, n2)   -> (Left e, n2)
          (Right b, _, n2)
            | f `elem` freeVars b -> (Left RecursiveNameNotApplied, n2)
            | otherwise           -> (Right b, n2)
  _ -> (Left RecursionNotAbstracted, n0)
  where
    -- The methods' telescopes for a datatype, in constructor order.
    shapesOf def =
      [ Shape (length args) (recursive args) | c <- inductiveConstructors def
      , let args = constructorArguments c ]
      where
        dn = inductiveName def
        np = length (inductiveParameters def)
        recursive args =
          [ k | (k, e) <- zip [0 ..] args
              , Just _ <- [recursiveArgument dn np (entryType e)] ]

    -- ------------------------------------------------------------------
    -- The walk
    -- ------------------------------------------------------------------

    -- Every case below answers three things, so they are threaded with this
    -- rather than nested by hand: the rewritten term or a refusal, the free
    -- variables seen used as a method, and the fresh counter.
    andThen r k = case r of
      (Left e,  u, n1) -> (Left e, u, n1)
      (Right x, u, n1) -> case k x n1 of
        (Left e,  u2, n2) -> (Left e, u ++ u2, n2)
        (Right y, u2, n2) -> (Right y, u ++ u2, n2)

    done x n = (Right x, [], n)

    -- What the walk carries.
    --
    -- @hypotheses@ pairs a recursive constructor argument with the hypothesis
    -- about it, both as variables of the term being walked. It grows only
    -- where a method is entered, which is the only place a hypothesis is
    -- bound.
    --
    -- __@aliases@ is why this is not a two-line function.__ Elaborating a name
    -- does not hand the variable over: it binds a copy, so an arm written
    -- @succ (double m)@ comes back applying @double@ to a @let@-bound @m1@
    -- that is defined as @m@. The call therefore has to be read through the
    -- local definitions, and they are collected on the way down.
    walkIn w asMethod t n = case asMethod of
      Just shape -> peel w shape t n
      Nothing    -> go w t n

    go w t n = case t of
      App {}            -> spine w t [] n
      Free v | v == subject w -> (Left RecursiveNameNotApplied, [], n)
      Lam i ty sc       -> under w i (Lam i) ty sc n
      Pi  i ty sc       -> under w i (Pi  i) ty sc n
      Canonical g ls as -> walkList w as n `andThen` \as' -> done (Canonical g ls as')
      Trusted a b c ->
        go w a n  `andThen` \a' n1 ->
        go w b n1 `andThen` \b' n2 ->
        go w c n2 `andThen` \c' -> done (Trusted a' b' c')

      -- Written out rather than threaded, because this is the one case that
      -- /reads/ what the walk reported: the shape a method was used at comes
      -- back from the body, and the value is walked with it in hand.
      --
      -- The body is walked with the definition in scope, which is what lets a
      -- call written over a copy be read.
      Let i v ty sc ->
        let (x, n1) = fresh n
            inner   = w { aliases = (x, v) : aliases w
                        , binders = binders w ++ [Definition x i v ty] }
         in case go inner (open x sc) n1 of
              (Left e, u, n2) -> (Left e, u, n2)
              (Right b, usedB, n2) ->
                let mine  = lookup x usedB
                    other = [ q | q@(y, _) <- usedB, y /= x ]
                 in case walkIn w mine v n2 of
                      (Left e, u, n3) -> (Left e, other ++ u, n3)
                      (Right v', usedV, n3) -> case go w ty n3 of
                        (Left e, u, n4) -> (Left e, other ++ usedV ++ u, n4)
                        (Right ty', usedT, n4) ->
                          -- An alias carries the shape one step further out,
                          -- which is what elaboration's method/case pair needs.
                          let viaName = case (mine, v) of
                                (Just sh, Free z) -> [(z, sh)]
                                _                 -> []
                           in ( Right (Let i v' ty' (close x b))
                              , other ++ usedV ++ usedT ++ viaName, n4 )

      Eliminate {} -> elimination w t n
      _            -> done t n

    under w i build ty sc n =
      go w ty n `andThen` \ty' n1 ->
        let (v, n2) = fresh n1
            inner   = w { binders = binders w ++ [Hypothesis v i ty] }
         in go inner (open v sc) n2 `andThen` \b -> done (build ty' (close v b))

    -- An application is taken apart whole, because a recursive call is a
    -- /prefix/ of its spine and the rest has to be put back.
    spine w t as n = case t of
      App g a -> spine w g (a : as) n
      Free v | v == subject w -> case tie w as n of
        (Left e, n1)  -> (Left e, [], n1)
        (Right r, n1) -> done r n1
      _ ->
        go w t n `andThen` \h n1 ->
        walkList w as n1 `andThen` \as' -> done (foldl App h as')

    -- The call, and the hypothesis it is. __The prefix ends at the argument
    -- that names a recursive argument__, so a call at a longer arity than the
    -- hypothesis has becomes an application of the hypothesis: @f m y@ with
    -- the hypothesis about @m@ is @ih y@.
    tie w as n =
      case nub [ (k, h) | (k, a) <- zip [(0 :: Int) ..] as
                        , Just y <- [through w a]
                        , (y', h) <- hypotheses w, y' == y ] of
        [(k, h)] -> (Right (foldl App (Free h) (drop (k + 1) as)), n)
        []       -> (Left (CallMatchesNoHypothesis (binders w) (call as)), n)
        several  -> (Left (CallMatchesSeveral (binders w) (call as)
                                              (length several)), n)
      where
        -- __Shown with the copies unfolded__, because elaborating a name binds
        -- one: without this, @loop zero@ is reported as @loop ‹Var 3727›@.
        call = foldl App (Free (subject w)) . map (expand w)

    -- An argument read through the local definitions, because elaborating a
    -- name binds a copy of it rather than handing the variable over.
    through w = look (0 :: Int)
      where
        look depth t = case t of
          Free v
            | depth > 64 -> Just v
            | otherwise  -> case lookup v (aliases w) of
                Just t' -> look (depth + 1) t'
                Nothing -> Just v
          _ -> Nothing

    -- The same walk, kept as a term: what a copy is defined as, for a message.
    expand w = look (0 :: Int)
      where
        look depth t = case t of
          Free v
            | depth <= 64, Just t' <- lookup v (aliases w) -> look (depth + 1) t'
          _ -> t

    walkList _ []         n = done [] n
    walkList w (a : rest) n =
      go w a n `andThen` \a' n1 ->
      walkList w rest n1 `andThen` \as' -> done (a' : as')

    elimination w t n = case t of
      Eliminate d ls ps mot ms is tgt ->
        let shapes = case lookupInductive d env of
              Just def -> map Just (shapesOf def) ++ repeat Nothing
              Nothing  -> repeat Nothing
            used = [ (v, sh) | (Free v, Just sh) <- zip ms shapes ]
         in methods w (zip ms shapes) n `andThen` \ms' n1 ->
            go w mot n1      `andThen` \mot' n2 ->
            walkList w ps n2 `andThen` \ps' n3 ->
            walkList w is n3 `andThen` \is' n4 ->
            go w tgt n4      `andThen` \tgt' n5 ->
              ( Right (Eliminate d ls ps' mot' ms' is' tgt'), used, n5 )
      _ -> done t n

    methods _ []                n = done [] n
    methods w ((mt, sh) : rest) n =
      walkIn w sh mt n `andThen` \m' n1 ->
      methods w rest n1 `andThen` \ms' -> done (m' : ms')

    -- Descend a method's λ-chain, collecting its hypotheses.
    --
    -- A term that is not the chain the declaration describes is walked as an
    -- ordinary term with the hypotheses already in scope. That is the
    -- specialised case, and refusing a call inside it is the point.
    peel w (Shape nargs recs) = chain []
      where
        chain args u j
          | length args >= nargs + length recs =
              go w { hypotheses = bound args ++ hypotheses w
                   , binders    = binders w ++ map snd args } u j
          | otherwise = case u of
              Lam i ty sc ->
                let (v, j1) = fresh j
                 in chain (args ++ [(v, Hypothesis v i ty)]) (open v sc) j1
                      `andThen` \b -> done (Lam i ty (close v b))
              _ -> go w u j

        -- The hypotheses, once the whole chain is bound: the λ at position
        -- @nargs + i@ is about the argument at position @recs !! i@.
        bound args =
          [ (y, h)
          | (i, a) <- zip [(0 :: Int) ..] recs
          , Just (y, _) <- [at a args]
          , Just (h, _) <- [at (nargs + i) args]
          ]

        at i xs = case drop i xs of
          x : _ -> Just x
          []    -> Nothing
