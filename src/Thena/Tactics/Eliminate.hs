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
-- whole tactic behind one 'Thena.Ops.Op', and this is the case it was granted
-- for: everything here is term construction over an 'InductiveDefinition', the
-- same kind of thing as 'Thena.Global.Env.eliminatorType' and
-- "Thena.Global.NoConfusion". A granular rule body would need a term-building
-- sub-vocabulary — motive assembly, telescope walking, @Eq@ application —
-- designed up front with nothing else asking for it, and §12 invariant 5
-- forbids exactly that.
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
  , eliminate
  ) where

import Thena.Core.Context (Context, Entry (..), entryIdent, entryType, entryVar, lamOver)
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
import Thena.Core.Typing (check, infer, sortOf)
import Thena.Errors (ElimError (..))
import Thena.Global.Env
  ( GlobalEnv
  , ConstructorDefinition (..)
  , InductiveDefinition (..)
  , eliminatorType
  , isDeclared
  , lookupInductive
  )

-- | What the tactic worked out: the subgoals, and the refinement.
--
-- 'elimMethods' is one entry per constructor, **in declaration order**, which
-- is the order 'Thena.Core.Term.Eliminate' expects its methods in. Each is a
-- hole the caller must put into the development /above/ the goal, so that the
-- goal can see it — the same placement 'Thena.Ops.Claim' already uses.
--
-- 'elimTerm' mentions those holes as @'Free' v@, so it is well typed only in a
-- context extended by them. 'eliminate' has already checked it there.
data Elimination = Elimination
  { elimMethods :: [(Var, Ident, Core)]
  , elimTerm    :: Core
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
-- **The target is abstracted before the indices**, which is a real choice and
-- not an accident of order. If an occurrence of the target contains an index
-- expression, abstracting indices first rewrites inside it, and the occurrence
-- then no longer matches the target. Both orders are sound — the use site
-- substitutes everything back — but this one generalises more.
eliminate
  :: GlobalEnv -> Context -> Int -> Core -> Core
  -> (Either ElimError Elimination, Int)
eliminate env ctx n0 goal tgt =
  case infer env ctx n0 tgt of
    (Left e, n1)    -> (Left (TargetNotTypeable e), n1)
    (Right tty, n1) -> case saturated (whnf env ctx tty) of
      Just (d, ps, as) -> build d ps as n1
      Nothing          -> (Left (TargetNotInductive ctx tgt (whnf env ctx tty)), n1)
  where
    -- @D p⃗ a⃗@ for a declared @D@, with every parameter and index supplied.
    -- Under-application is not an elimination target: the eliminator is
    -- saturated (§3.6) and so is the family it eliminates.
    saturated ty = case spineOf ty of
      Just (dn, args) -> do
        d <- lookupInductive dn env
        let np = length (inductiveParameters d)
            ni = length (inductiveIndices d)
        if length args == np + ni
          then let (ps, as) = splitAt np args in Just (d, ps, as)
          else Nothing
      Nothing -> Nothing

    build d ps as n1
      | not (null as), Just missing <- undeclared = (Left (NoEquality missing), n1)
      | otherwise = case indexTypes of
          Left e   -> (Left e, n1)
          Right is -> scheme d ps as is n1
      where
        -- §3.7, decided 2026-08-11: @Eq@ and @refl@ are referred to **by
        -- name**. No designation table, no pragma, no shape check — they are
        -- expected to be there, and elimination fails if they are not. A name
        -- check gives a message worth reading; leaving it to the typechecker
        -- would report a missing global from inside a generated term.
        undeclared
          | not (isDeclared equality env) = Just equality
          | not (isDeclared reflexivity env) = Just reflexivity
          | otherwise = Nothing

        -- The type each index is constrained at, with the family's parameters
        -- replaced by the target's. §3.7's limit lands here: @Eq Iₖ iₖ aₖ@ is
        -- homogeneous, so @Iₖ@ may not mention an earlier index.
        indexTypes = walk (zip [1 ..] (inductiveIndices d))
          where
            earlier = map entryVar (inductiveIndices d)
            subst   = zip (map entryVar (inductiveParameters d)) ps
            walk [] = Right []
            walk ((k, e) : rest) =
              let ty = substVars subst (entryType e)
                  taken = take (k - 1) earlier
               in if any (`elem` freeVars ty) taken
                    then Left (IndexTypeDepends k (entryIdent e))
                    else (ty :) <$> walk rest

    scheme d ps as indexTys n1 =
      let ni = length as

          -- One fresh variable per index, plus the motive's own target binder.
          (ivs, n2) = freshen ni n1
          (xv,  n3) = fresh n2

          familyAt is = foldl App (Global (inductiveName d)) (ps ++ is)

          -- The generalised goal. Target first; see the note above.
          (goalX,  n4) = replaceTerm tgt xv n3 goal
          (goalIx, n5) = foldl abstractIndex (goalX, n4) (zip ivs as)
          abstractIndex (g, n) (iv, a) = replaceTerm a iv n g

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
              || Just (entryVar e) == targetVar
              || v `notElem` entryUses e

          -- Which indices keep an equation, and which are simply abstracted.
          tied = [ (ity, iv, a)
                 | (k, (ity, iv, a)) <- zip [(0 :: Int) ..] (zip3 indexTys ivs as)
                 , not (friendlyAt k a)
                 ]

          -- @Eq Iₖ iₖ aₖ → …@, one non-dependent Π per *tied* index. A Π still
          -- needs a variable to close over even when nothing refers to it,
          -- exactly as 'Thena.Global.Env.eliminatorType' mints one per
          -- induction hypothesis.
          (equations, n6) = constrain tied n5 goalIx
          constrain []                  n b = (b, n)
          constrain ((ity, iv, a) : cs) n b =
            let (body, na) = constrain cs n b
                (qv,   nb) = fresh na
             in (Pi (Ident "q") (equationOf ity (Free iv) a) (close qv body), nb)

          -- The context the motive's body lives in, which is also where its
          -- universe is read.
          indexEntries =
            [ Hypothesis iv (entryIdent e) ity
            | (iv, e, ity) <- zip3 ivs (inductiveIndices d) indexTys
            ]
          bodyCtx =
            ctx ++ indexEntries ++ [Hypothesis xv (Ident "target") (familyAt (map Free ivs))]

          motiveTerm =
            lamOver indexEntries
              (Lam (Ident "target") (familyAt (map Free ivs)) (close xv equations))
       in
          -- Reading the universe **is** the check that the abstraction was
          -- type-preserving; the level is needed anyway, so it costs nothing
          -- extra (thesis §3.5.3, and see this module's header).
          case sortOf env bodyCtx n6 equations of
            (Left e, n7)  -> (Left (MotiveIllTyped e), n7)
            (Right l, n7) -> assemble d ps as tied motiveTerm l n7

    assemble d ps as tied motiveTerm l n7 =
      let (ety, n8) = eliminatorType d l n7
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

          node = Eliminate
            { eliminated = inductiveName d
            , parameters = ps
            , motive     = motiveTerm
            , methods    = map Free mvs
            , indices    = as
            , target     = tgt
            }
          -- The equations are reflexive at the use site, which is the whole
          -- point of the scheme (§3.7, thesis §3.5). Only the tied indices have
          -- one; a friendly index was abstracted outright and carries none.
          proof = foldl App node
            [ Canonical reflexivity [ity, a] | (ity, _, a) <- tied ]
       in case check env (ctx ++ methodEntries) n10 proof goal of
            (Left e, n11)  -> (Left (SchemeIllTyped e), n11)
            (Right (), n11) -> (Right (Elimination holes proof), n11)

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

    equationOf ity l r = foldl App (Global equality) [ity, l, r]

    -- The entry the target /is/, when it is a variable. It is the one entry
    -- allowed to mention a friendly index — the whole point is that the target
    -- follows the index into the motive.
    targetVar = case tgt of
      Free w -> Just w
      _      -> Nothing

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
spineOf :: Core -> Maybe (GlobalName, [Core])
spineOf = go []
  where
    go acc t = case t of
      App f a         -> go (a : acc) f
      Global g        -> Just (g, acc)
      Canonical g as  -> Just (g, as ++ acc)
      _               -> Nothing

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
          Canonical g as ->
            let (as', n1) = list n as in (Canonical g as', n1)
          Eliminate d ps m ms is tg ->
            let (ps', n1) = list n ps
                (m',  n2) = go n1 m
                (ms', n3) = list n2 ms
                (is', n4) = list n3 is
                (tg', n5) = go n4 tg
             in (Eliminate d ps' m' ms' is' tg', n5)
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
