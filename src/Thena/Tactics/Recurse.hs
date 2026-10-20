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
-- __A method the specialiser rewrote hands its binders to a subgoal, and the
-- report follows them there__ (MS9 phase 193). Where an equation fires, the
-- method comes back as a coercion around a hole, so the arm's binders are the
-- /hole's/ and a call written against them matches nothing a walk over the
-- method itself collected. That is what refused a recursion inside an arm whose
-- split generalised: the motive quantifies a copy of every ambient entry a rule
-- demands, the enclosing arm's induction hypothesis is such an entry whenever
-- its type mentions one, and its copy arrives UNGUARDED and about the arm's own
-- subject —
--
-- @
-- usMethod : ∀ (a1 : N) (b : N) -> Up a1 b -> (…)
--   -> ∀ (a2 : N) -> Up a2 a' -> (∀ (q : N) -> Up a2 q -> Eq {0} N a' q)
--   -> Eq {0} N (s a1) (s a2) -> Eq {0} N (s a') (s b)
-- @
--
-- — so the recursion in such an arm is real and was simply unreachable.
--
-- __Two things make it reachable, and neither is a name or a type.__
--
-- * __The use site says which ambient entry each copy copies.__
--   "Thena.Tactics.Eliminate" applies the scheme to each generalised entry /as
--   itself/, in the order the motive quantified the copies, before the
--   reflexive proofs — so 'generalisedIn' reads them straight off the spine, and
--   a pair this walk already holds becomes a pair of copy /positions/.
-- * __And the method says which of its binders the hole kept.__ A specialised
--   method is a λ over its whole telescope whose body hands the hole the
--   binders that survived, in order, through one coercion per solved binder;
--   'handedTo' follows that and answers the list, which turns a position in the
--   telescope into a position in the arm.
--
-- __So nothing here matches by name or by type__, and the reason is the one
-- 'resolveRecursion' is a pass at all: where the motive does not depend on the
-- target, a pattern variable and the hypothesis about it have the same type, so
-- a search by type picks the wrong one and still typechecks (his ruling of
-- 2026-10-19, @.claude\/RULINGS.md@).
--
-- Where it sits in §2.5: beside "Thena.Tactics.Eliminate" and
-- "Thena.Tactics.Specialise" — above "Thena.Core.Term" and
-- "Thena.Global.Env", below "Thena.Engine".
module Thena.Tactics.Recurse
  ( resolveRecursion
  ) where

import Data.List (elemIndex, nub, stripPrefix)

import Thena.Core.Context (Context, Entry (..), entryType)
import Thena.Core.Term
  ( Core (..)
  , GlobalName (..)
  , Var
  , close
  , fresh
  , freeVars
  , instantiate
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

-- | Where an arm's hypotheses sit in the λ-chain that binds it: how many
-- binders to descend, and which pairs of them are a recursive argument and the
-- hypothesis about it.
--
-- __Pairs of positions rather than two counts__ (MS9 phase 193). The
-- declaration states a method's telescope as the constructor's arguments and
-- then one hypothesis per recursive argument, so the pairs for a method written
-- as its own λ-chain are @(recursive argument, arguments + i)@ — but a
-- generalised copy's pair is nowhere near that shape, and an arm the specialiser
-- rewrote keeps only the binders the equations left. Both are positions in one
-- list, so one list of pairs says all three.
data Shape = Shape Int [(Int, Int)]
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
    --
    -- __@withHyps@ is the one thing @induction@ and @case@ differ by__, and it
    -- is the same parameter 'Thena.Global.Env.Scheme' is: @caseD@'s methods are
    -- the eliminator's minus their hypotheses, so a method of one has pairs to
    -- state and a method of the other has none.
    shapesOf withHyps def =
      [ shape (length args) (recursive args) | c <- inductiveConstructors def
      , let args = constructorArguments c ]
      where
        dn = inductiveName def
        np = length (inductiveParameters def)
        recursive args =
          [ k | (k, e) <- zip [0 ..] args
              , Just _ <- [recursiveArgument dn np (entryType e)] ]
        shape nargs recs
          | withHyps  = Shape (nargs + length recs)
                              [ (r, nargs + i) | (i, r) <- zip [0 ..] recs ]
          | otherwise = Shape nargs []

    -- | Which ambient entries a split generalised, read off its use site.
    --
    -- The scheme is applied to each of them __as itself__, in the order the
    -- motive quantified the copies, and then to one reflexive proof per tied
    -- index — "Thena.Tactics.Eliminate", MS9 phase 191, whose note calls that
    -- application discharging the dependency. An entry is therefore always a
    -- bare variable and a proof never is, which is the whole of telling the two
    -- runs apart.
    generalisedIn as = [ v | Free v <- takeWhile isVar as ]
      where
        isVar (Free _) = True
        isVar _        = False

    -- The copies are further binders of every method, standing after the
    -- hypotheses, and __a copy inherits the pairing of the entry it copies__:
    -- if this walk already holds @(x, h)@ and the split generalised both, then
    -- the copy of @x@ is a recursive argument of this arm and the copy of @h@ is
    -- the hypothesis about it. That is the pair a recursion inside a
    -- generalising arm needs, and it is about the arm's own subject rather than
    -- the enclosing one.
    withCopies hyps gen (Shape count pairs) =
      Shape (count + length gen)
            (pairs ++ [ (count + i, count + j)
                      | (x, h) <- hyps
                      , Just i <- [elemIndex x gen]
                      , Just j <- [elemIndex h gen]
                      ])

    -- One shape per constructor, in declaration order, as an infinite list so a
    -- method of an undeclared datatype is simply not reported.
    methodShapes w withHyps d gen = case lookupInductive d env of
      Just def -> map (Just . withCopies (hypotheses w) gen)
                      (shapesOf withHyps def)
                    ++ repeat Nothing
      Nothing  -> repeat Nothing

    -- @caseD@ is the split tactic's other use site: @case … of@ elaborates to an
    -- application of the generated definition rather than to an 'Eliminate'
    -- node, so this is the same report read off the other spelling and not a
    -- second mechanism. The name is generated for every datatype, so it is not
    -- one a user can have bound to something else.
    analysedBy (GlobalName w) = do
      rest <- stripPrefix "case" w
      lookupInductive (GlobalName rest) env

    -- An item of a list, by position.
    at i xs = case drop i xs of
      x : _ -> Just x
      []    -> Nothing

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
                          -- which is what elaboration's method/case pair needs
                          -- — and a method the specialiser rewrote carries it
                          -- further in, to the hole its arm is written under
                          -- (MS9 phase 193).
                          let (viaName, n5) = case mine of
                                Nothing -> ([], n4)
                                Just sh -> case v of
                                  Free z -> ([(z, sh)], n4)
                                  _      -> subgoalShape w sh v n4
                           in ( Right (Let i v' ty' (close x b))
                              , other ++ usedV ++ usedT ++ viaName, n5 )

      Eliminate {} -> elimination w t [] n
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
      -- **The head is taken with the arguments it is applied to**, because a
      -- split's use site is the node applied to the entries it generalised and
      -- the walk has to read them (MS9 phase 193).
      Eliminate {} -> elimination w t as n
      Global gn ls | Just def <- analysedBy gn -> caseSplit w def gn ls as n
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

    elimination w t as n = case t of
      Eliminate d ls ps mot ms is tgt ->
        let shapes = methodShapes w True d (generalisedIn as)
            used = [ (v, sh) | (Free v, Just sh) <- zip ms shapes ]
         in methods w (zip ms shapes) n `andThen` \ms' n1 ->
            go w mot n1      `andThen` \mot' n2 ->
            walkList w ps n2 `andThen` \ps' n3 ->
            walkList w is n3 `andThen` \is' n4 ->
            go w tgt n4      `andThen` \tgt' n5 ->
            walkList w as n5 `andThen` \as' n6 ->
              ( Right (foldl App (Eliminate d ls ps' mot' ms' is' tgt') as')
              , used, n6 )
      _ -> done t n

    -- The same report off @caseD@'s spine, whose binder order is
    -- 'Thena.Global.Env.eliminatorParts'\' own: the parameters, the motive, one
    -- method per constructor, the indices, the target, and then what the motive
    -- generalised.
    caseSplit w def gn ls as n =
      let np = length (inductiveParameters def)
          ni = length (inductiveIndices def)
          nc = length (inductiveConstructors def)
          ms = take nc (drop (np + 1) as)
          shapes = methodShapes w False (inductiveName def)
                     (generalisedIn (drop (np + 1 + nc + ni + 1) as))
          used = [ (v, sh) | (Free v, Just sh) <- zip ms shapes ]
          shapeAt k
            | k >= np + 1, k < np + 1 + nc = shapes !! (k - (np + 1))
            | otherwise                    = Nothing
          tagged = [ (a, shapeAt k) | (k, a) <- zip [(0 :: Int) ..] as ]
       in methods w tagged n `andThen` \as' n1 ->
            ( Right (foldl App (Global gn ls) as'), used, n1 )

    methods _ []                n = done [] n
    methods w ((mt, sh) : rest) n =
      walkIn w sh mt n `andThen` \m' n1 ->
      methods w rest n1 `andThen` \ms' -> done (m' : ms')

    -- Descend a method's λ-chain, collecting its hypotheses.
    --
    -- A term that is not the chain the declaration describes is walked as an
    -- ordinary term with the hypotheses already in scope. That is the
    -- specialised case, and refusing a call inside it is the point.
    peel w (Shape count pairs) = chain []
      where
        chain args u j
          | length args >= count =
              go w { hypotheses = bound args ++ hypotheses w
                   , binders    = binders w ++ map snd args } u j
          | otherwise = case u of
              Lam i ty sc ->
                let (v, j1) = fresh j
                 in chain (args ++ [(v, Hypothesis v i ty)]) (open v sc) j1
                      `andThen` \b -> done (Lam i ty (close v b))
              _ -> go w u j

        -- The hypotheses, once the whole chain is bound, as the shape names
        -- them: a pair of positions in it.
        bound args =
          [ (y, h)
          | (i, j) <- pairs
          , Just (y, _) <- [at i args]
          , Just (h, _) <- [at j args]
          ]

    -- __Where a specialised method's arm actually is, and the shape it has
    -- there__ (MS9 phase 193).
    --
    -- A method the specialiser rewrote is a λ over its whole telescope whose
    -- body hands a /hole/ the binders the equations left, so the arm is written
    -- under the hole's λ-chain and this shape belongs to the hole's @let@ and
    -- not to the method's. The hole is one of the @let@s already descended
    -- under — 'Thena.Engine' claims the subgoal above the method it came from —
    -- so it is found by asking which of them this term hands anything to, and
    -- there is exactly one.
    --
    -- __The positions are translated, not assumed.__ A solved binder is gone
    -- from the hole's chain, so the telescope's position @i@ is at whatever
    -- place the term passes that binder, and a pair whose either half was solved
    -- is dropped rather than guessed at.
    subgoalShape w (Shape count pairs) v n =
      let (vs, body, n1) = openAll v n
          found =
            [ (z, args)
            | (z, _) <- aliases w
            , z `elem` freeVars body
            , Just args <- [handedTo z body []]
            ]
       in if length vs < count then ([], n1) else case found of
            [(z, args)] ->
              ( [ (z, Shape (length args)
                      [ (i', j')
                      | (i, j) <- pairs
                      , Just i' <- [place vs args i]
                      , Just j' <- [place vs args j]
                      ]) ]
              , n1 )
            _ -> ([], n1)
      where
        place vs args i = at i vs >>= \y -> elemIndex (Free y) args

    -- Every leading λ, opened at a throwaway variable, and the body under them.
    openAll t n = case t of
      Lam _ _ sc ->
        let (v, n1)      = fresh n
            (vs, b, n2)  = openAll (open v sc) n1
         in (v : vs, b, n2)
      _ -> ([], t, n)

    -- __The arguments a specialised method hands @z@, in order.__
    --
    -- "Thena.Tactics.Specialise" builds the term by composition: each
    -- transition λ-binds the problem as it stands and applies the sub-problem's
    -- term to the binders that survive it, so the hole is reached through a nest
    -- of such applications. A /solution/ puts a @J@-elimination between two of
    -- them — it coerces the sub-problem from the term the equation solved the
    -- binder to, back to the binder — and the arguments after that point are
    -- applied to the coercion rather than to the sub-problem. A coercion of a
    -- function is transparent to application, so they are carried through it.
    --
    -- @extra@ is what the result of @t@ is applied to, which is why this is not
    -- a spine walk: an argument may be written outside the coercion that wraps
    -- the binder it fills.
    handedTo z t extra = case t of
      Free y | y == z -> Just extra
      Lam _ _ sc -> case extra of
        a : rest -> handedTo z (instantiate a sc) rest
        []       -> Nothing
      App f a
        | z `elem` freeVars f -> handedTo z f (a : extra)
        | z `elem` freeVars a -> handedTo z a extra
      _ -> Nothing
