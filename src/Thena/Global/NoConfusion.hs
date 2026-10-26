-- | Generating the @NoConfusion@ family and the @noConfusion@ lemma (§3.7
-- items 3 and 4).
--
-- These are what an elimination at specific indices uses to discharge the
-- equational hypotheses its motive carries: /injectivity/ of a former in each
-- argument, and /discrimination/ between distinct formers. MS1's target theorem
-- needs both — the matching branches the first, the impossible branches the
-- second.
--
-- **Its own module, not more of "Thena.Global.Declare".** Nothing forces the
-- split the way phase 12's did — @Declare@ already sits above @Typing@ — but
-- what is here is a different kind of code from what is there. @Declare@ asks
-- whether a declaration may be admitted; this /emits a proof term/, which is
-- the larger and riskier half of §3.7 and the one whose cost decides whether
-- the fallback (generating on demand inside the elimination tactic) is ever
-- reached.
--
-- **Everything emitted is checked before it is admitted** (§3.7): the two
-- definitions go through 'Thena.Core.Typing.check' in the environment they will
-- live in, and a failure is a 'Rejected', which "Thena.Global.Declare" turns
-- into a refusal. So unlike the eliminator, which is trusted derivation
-- (§5.3), this generator is verified.
--
-- == The shape, and why every case is CPS
--
-- §3.7 displays the family with @Unit@, @Empty@ and @Eq@ as its cases and
-- @Type₀@ as its result. That cannot be typed. The multi-argument case is
-- written CPS because MS1 has no product type, and @(C : Type₀) -> … -> C@
-- lives in @Type₁@ — 'Thena.Core.Typing.infer' gives a Π the @max@ of its two
-- levels, and the domain @Type₀@ is at level 1. **At the time there was no
-- cumulativity** — it arrived at MS3 phase 32 — so a @Type₀@ case could not sit
-- beside a @Type₁@ one in a single family.
--
-- So **every case is CPS and the family lands in @Type₁@** — decided by the
-- user 2026-08-22. Only the level in §3.7 was wrong; the decision to encode the
-- conjunction in continuation-passing style, and @AGENDA.md@ item 13 as the one
-- place products change it, both stand. For @Nat@:
--
-- @
-- NoConfusionNat : Nat -> Nat -> Type₁
--   NoConfusionNat zero     zero     =  Unit
--   NoConfusionNat zero     (succ b) =  Empty
--   NoConfusionNat (succ a) zero     =  Empty
--   NoConfusionNat (succ a) (succ b) =  Eq Nat a b
--
-- noConfusionNat : ∀ (x y : Nat) -> Eq Nat x y -> NoConfusionNat x y
-- @
--
-- A constructor with several arguments pairs one equation per argument,
-- right-nested: @dpair@'s @DPair (Eq A a a') (λ _ . Eq B b b')@, and where an
-- argument's type mentions an earlier argument the later equation is stated
-- after transporting along the earlier one — see 'telescopic'. **Phase 20 replaced a
-- continuation-passing encoding of that conjunction**, which phase 14 had been
-- forced into because @(C : Type₀) -> …@ is at @Type₁@ and there was then no
-- cumulativity to let a @Type₀@ case sit beside it. With the products in the
-- prelude the table above is the one §3.7 always displayed, at @Type₀@.
--
-- The prelude names this module needs are therefore @Eq@ and @refl@, and
-- @DPair@, @dpair@, @Unit@, @unit@ and @Empty@.
--
-- The family is two nested eliminations of the datatype — one to fix @x@'s
-- former, one to fix @y@'s. The lemma eliminates the equality first (its
-- eliminator is J), which fixes @y@ to be @x@, and then the datatype once, which
-- is why only the diagonal cases are ever proved: @λ C k . k refl … refl@.
module Thena.Global.NoConfusion
  ( Generated (..)
  , noConfusionNames
  , generateNoConfusion
  , dependentTelescope
  ) where

import Thena.Core.Level (Level (..))
import Thena.Errors (Skipped (..))
import Thena.Core.Context (Context, Entry (..), entryType, entryVar, lamOver, piOver)
import Thena.Core.Term
  ( Core (..)
  , GlobalName (..)
  , Ident (..)
  , Var
  , close
  , fresh
  , freeVars
  , instantiate
  )
import Thena.Core.Typing (check)
import Thena.Errors (TypeError)
import Thena.Global.Env
  ( ConstructorDefinition (..)
  , Definition (..)
  , GlobalEnv
  , InductiveDefinition (..)
  , addDefinition
  , isDeclared
  , lookupInductive
  , recursiveArgument
  )

-- | One equation 'telescopic' has already stated, as 'moveIn' looks back at it.
--
-- **@statedMoved@ is what decides the package.** An argument whose own left
-- side had to be transported into place cannot be substituted for in a later
-- argument's type, so a later argument that mentions it has to carry it along;
-- one that was already in place can simply be substituted.
data Stated = Stated
  { statedEntry :: Entry
    -- ^ the constructor argument the equation is about
  , statedMoved :: Bool
    -- ^ was its left side transported, rather than the binder itself?
  , statedType  :: Core
    -- ^ the type the equation is stated at
  , statedLeft  :: Core
    -- ^ its left side — the argument, moved if it had to be
  , statedRight :: Core
    -- ^ its right side, which is whatever the caller is comparing against
  , statedProof :: Var
    -- ^ the binder standing for a proof of it, bound by the pair it heads
  }

-- | What generation did.
--
-- 'Rejected' is a **generator bug**, not a user error: it means the checker
-- refused a term this module built. It is a case rather than an @error@ call
-- because §12 invariant 2 wants the 'TypeError' carried out to where it can be
-- printed.
data Generated
  = Generated GlobalEnv Int
  | Declined Skipped
  | Clash GlobalName
    -- ^ a generated name is already taken (§3.6: one namespace, shared with
    -- generated names — the declaration is rejected rather than either name
    -- being hidden)
  | Rejected GlobalName TypeError

-- | The two names a datatype generates: @NoConfusionNat@ and @noConfusionNat@.
--
-- Concatenation, per §3.6's own example of the rule — @noConfusionTerm@ is a
-- name the user could have written, and if they do, the declaration that would
-- generate it is refused.
noConfusionNames :: GlobalName -> (GlobalName, GlobalName)
noConfusionNames (GlobalName d) =
  (GlobalName ("NoConfusion" ++ d), GlobalName ("noConfusion" ++ d))

-- | Generate, check and admit both definitions — or say why not.
--
-- Called from "Thena.Global.Declare" /after/ the wrappers are installed, so the
-- datatype's own former and constructors are already resolvable: @Eq Term a b@
-- and @succ a@ inside the generated terms are ordinary globals.
--
-- The preconditions are tested in this order deliberately. A prelude-free
-- script (the golden transcripts, phase 11's accepted divergence) fails the
-- first one and gets no message at all; a script with the prelude that declares
-- @Vec@ reaches the third and is told.
generateNoConfusion :: GlobalEnv -> Int -> InductiveDefinition -> Generated
generateNoConfusion env n0 d
  | not (equalityInScope env)          = Declined NoEqInScope
  | not (productsInScope env d)        = Declined NoProducts
  | isDeclared famName env             = Clash famName
  | isDeclared lemName env             = Clash lemName
  | otherwise =
      let (famTy,   n1) = familyType n0
          (famBody, n2) = family n1
       in case verdict (check env [] n2 famBody famTy) of
            Left e   -> Rejected famName e
            Right () ->
              let env1          = addDefinition famName (MkDefinition (inductiveLevels d) [] famTy famBody) env
                  (lemTy,   n3) = lemmaType n2
                  (lemBody, n4) = lemma n3
               in case verdict (check env1 [] n4 lemBody lemTy) of
                    Left e   -> Rejected lemName e
                    Right () ->
                      Generated (addDefinition lemName (MkDefinition (inductiveLevels d) [] lemTy lemBody) env1) n4
  where
    -- Everything checked here is /generated/, so it holds no level meta and
    -- can owe no obligation. The counter is not wanted either — these checks
    -- run in an empty context on closed terms.
    verdict (r, _, _) = r

    (famName, lemName) = noConfusionNames (inductiveName d)

    dn        = inductiveName d
    ps        = inductiveParameters d
    idx       = inductiveIndices d
    np        = length ps
    cs        = inductiveConstructors d
    paramVars = varsOf ps

    -- @D params indices@, as an application of the generated wrapper — the same
    -- spelling 'Thena.Global.Env.constructorTarget' builds, so nothing has to
    -- reduce to see the two agree.
    -- **At the datatype's own level parameters**, like every other generated
    -- reference (phase 31g; the same fix `Thena.Global.Env` took in 31c).
    familyAt is = foldl App (Global dn (map LVar (inductiveLevels d))) (paramVars ++ is)

    -- **Everything this module writes is stated at the datatype's own level**
    -- (MS3 phase 31g), and that is exactly what cumulativity buys.
    --
    -- A constructor argument's type lives at some @ℓ_arg ≤ dl@ (the size
    -- restriction), so @Eq {dl}@ applied to it is well typed: subsumption
    -- lifts a @Type ℓ_arg@ into @Type dl@. Before phase 32 the equations would
    -- have had to be stated each at its own argument's level, and then could
    -- not have been conjoined — @And@ takes two types at **one** level.
    dl = inductiveLevel d

    eqAt a x y = foldl App (Global (GlobalName "Eq") [dl]) [a, x, y]
    reflAt a x = foldl App (Global (GlobalName "refl") [dl]) [a, x]

    -- **The conjunction is a dependent pair, one level per component.** Both
    -- are @dl@ here because every equation is stated at @dl@ — see the note
    -- above — so the join @Type (dl ⊔ dl)@ is @Type dl@ and the family's own
    -- level is unchanged.
    --
    -- **It is @DPair@ and not @And@ because of 'telescopic'**: where a
    -- constructor argument's type mentions an earlier argument, the equation
    -- about it is stated after transporting along the equations before it, so
    -- its type mentions the earlier equation's /proof/ and a conjunction of two
    -- types cannot hold it. The second component is a λ over that proof even
    -- where nothing uses it, which is @And@ with one more binder.
    --
    -- `[an opportunity this opens, and it is not taken here]` The pair carries
    -- a level per component, so the equations need not all be stated at @dl@:
    -- each could be stated at its own argument's level and paired at the join,
    -- which is what phase 32 §1 wanted and could not spell. That would make the
    -- lifting above unnecessary. It is a change to what is generated, not to
    -- what this phase is about.
    andAt p q        = foldl App (Global (GlobalName "And") [dl, dl]) [p, q]
    bothAt p q x y   = foldl App (Global (GlobalName "both") [dl, dl]) [p, q, x, y]
    dpairAt a b      = foldl App (Global (GlobalName "DPair") [dl, dl]) [a, b]
    dpairMk a b x y  = foldl App (Global (GlobalName "dpair") [dl, dl]) [a, b, x, y]

    -- ----------------------------------------------------------------------
    -- The family
    -- ----------------------------------------------------------------------

    -- @∀ params indices (x y : D params indices) -> Type dl@
    --
    -- **At the datatype's own level, not one above it.** Phase 14 had every
    -- case CPS-encoded, and @(C : Type l) -> C@ is itself at @Type (suc l)@;
    -- with @Empty@, @Unit@ and @And@ in the prelude every case is an ordinary
    -- proposition at @dl@ and the family follows it down. Phase 31g is what
    -- made @dl@ the datatype's own rather than @Type₀@; nothing else about the
    -- shape changed.
    familyType n =
      let (vx, n1) = fresh n
          (vy, n2) = fresh n1
          fam      = familyAt (varsOf idx)
       in ( piOver ps (piOver idx
              (Pi (Ident "x") fam (close vx
                (Pi (Ident "y") fam (close vy (Universe dl))))))
          , n2
          )

    -- @λ params indices x y . elim D params ‹motive› (‹methods›) indices x@
    --
    -- **@y@ is bound outside both eliminations, not consumed by the first.**
    -- The obvious reading of "eliminate @x@, then eliminate @y@" makes the
    -- first elimination compute a /function/ of @y@, and then its motive is
    -- Π-valued. That is well typed, but each method's body is a λ and the whole
    -- term is harder to read for no gain: with @y@ already in scope, the second
    -- elimination is simply what each method of the first returns, and both
    -- motives are the same constant.
    family n =
      let (vx, n1) = fresh n
          (vy, n2) = fresh n1
          (mt, n3) = typeMotive n2
          (ms, n4) = each (outerMethod mt (Free vy)) n3 cs
          fam      = familyAt (varsOf idx)
          body     = Eliminate dn (map LVar (inductiveLevels d)) paramVars mt ms (varsOf idx) (Free vx)
       in ( lamOver ps (lamOver idx
              (Lam (Ident "x") fam (close vx
                (Lam (Ident "y") fam (close vy body)))))
          , n4
          )

    -- @λ indices (t : D params indices) . Type dl@ — the motive of both
    -- eliminations, since both compute a type and neither result depends on
    -- what was eliminated. Valued in @Type (suc dl)@, which is the level
    -- 'Thena.Core.Typing.infer' reads off it.
    typeMotive n =
      let (is, n1) = freshen n idx
          (vt, n2) = fresh n1
       in ( lamOver is (Lam (Ident "t") (familyAt (varsOf is)) (close vt (Universe dl)))
          , n2
          )

    -- One per constructor of @x@: @λ Δ . λ IHs . elim D … y@, the second
    -- elimination, at the indices @y@ was given.
    outerMethod mt y c n =
      let args       = constructorArguments c
          (ms, n1)   = each (innerMethod mt args c) n cs
          inner      = Eliminate dn (map LVar (inductiveLevels d)) paramVars mt ms (varsOf idx) y
          (body, n2) = withHypotheses mt args inner n1
       in (lamOver args body, n2)

    -- One per constructor of @y@, given the constructor @x@ turned out to be.
    -- The arguments are **freshened**: on the diagonal the two telescopes are
    -- the same 'Context', so reusing its variables would have the inner binder
    -- capture the outer one and every equation read @Eq A a a@.
    innerMethod mt args c c' n =
      let (args', n1) = freshen n (constructorArguments c')
          (payload, n2)
            | constructorName c' == constructorName c = diagonal args args' n1
            | otherwise                               = (discriminate, n1)
          (body, n3) = withHypotheses mt args' payload n2
       in (lamOver args' body, n3)

    -- @Empty@ — the prelude's empty type, named rather than Church-encoded.
    -- Discharging an impossible branch is @elim Empty@ at whatever goal is
    -- wanted, which is a goal at /any/ level; the CPS form it replaces could
    -- only ever reach a @Type₀@ one.
    discriminate = Global (GlobalName "Empty") [dl]

    -- The telescopic equality of @x@'s arguments with @y@'s, which is what
    -- injectivity says, and @Unit@ for a constructor with no arguments.
    diagonal args args' n =
      let (ty, _, n1) = telescopic args (map (Free . entryVar) args') n
       in (ty, n1)

    -- ----------------------------------------------------------------------
    -- The lemma
    -- ----------------------------------------------------------------------

    -- @∀ params indices (x y : D params indices) -> Eq (D params indices) x y
    --   -> NoConfusionD params indices x y@
    lemmaType n =
      let (vx, n1) = fresh n
          (vy, n2) = fresh n1
          (ve, n3) = fresh n2
          fam      = familyAt (varsOf idx)
          result   = foldl App (Global famName (map LVar (inductiveLevels d)))
                       (paramVars ++ varsOf idx ++ [Free vx, Free vy])
       in ( piOver ps (piOver idx
              (Pi (Ident "x") fam (close vx
                (Pi (Ident "y") fam (close vy
                  (Pi (Ident "e") (eqAt fam (Free vx) (Free vy)) (close ve result)))))))
          , n3
          )

    -- @λ params indices x y e . elim Eq (D params indices) ‹motive› (‹refl›)
    --   (x, y) e@ — J, and the whole reason only diagonal cases are proved.
    lemma n =
      let (vx, n1) = fresh n
          (vy, n2) = fresh n1
          (ve, n3) = fresh n2
          fam      = familyAt (varsOf idx)
          (meq, n4)  = equalityMotive n3
          (mrfl, n5) = reflMethod n4
          body = Eliminate (GlobalName "Eq") [dl] [fam] meq [mrfl]
                   [Free vx, Free vy] (Free ve)
       in ( lamOver ps (lamOver idx
              (Lam (Ident "x") fam (close vx
                (Lam (Ident "y") fam (close vy
                  (Lam (Ident "e") (eqAt fam (Free vx) (Free vy)) (close ve body)))))))
          , n5
          )

    -- @λ u v (w : Eq (D …) u v) . NoConfusionD params indices u v@ — valued in
    -- @Type₀@, so J is used at level 0 here and the family's own eliminations
    -- at level 1.
    equalityMotive n =
      let (vu, n1) = fresh n
          (vv, n2) = fresh n1
          (vw, n3) = fresh n2
          fam      = familyAt (varsOf idx)
          result   = foldl App (Global famName (map LVar (inductiveLevels d)))
                       (paramVars ++ varsOf idx ++ [Free vu, Free vv])
       in ( Lam (Ident "u") fam (close vu
              (Lam (Ident "v") fam (close vv
                (Lam (Ident "w") (eqAt fam (Free vu) (Free vv)) (close vw result)))))
          , n3
          )

    -- @λ a . elim D params ‹motive› (‹methods›) indices a@ — the one method J
    -- leaves, which is @NoConfusionD … a a@ for an arbitrary @a@.
    reflMethod n =
      let (va, n1)   = fresh n
          (mdg, n2)  = diagonalMotive n1
          (ms,  n3)  = each (diagonalMethod mdg) n2 cs
          body       = Eliminate dn (map LVar (inductiveLevels d)) paramVars mdg ms (varsOf idx) (Free va)
       in (Lam (Ident "a") (familyAt (varsOf idx)) (close va body), n3)

    -- @λ indices (z : D params indices) . NoConfusionD params indices z z@.
    diagonalMotive n =
      let (is, n1) = freshen n idx
          (vz, n2) = fresh n1
          result   = foldl App (Global famName (map LVar (inductiveLevels d)))
                       (paramVars ++ varsOf is ++ [Free vz, Free vz])
       in ( lamOver is (Lam (Ident "z") (familyAt (varsOf is)) (close vz result))
          , n2
          )

    -- @λ Δ . λ IHs . dpair … (refl A₁ a₁) (dpair … (refl A₂ a₂) …)@ — the only
    -- proof this generator ever writes, built by the same function that builds
    -- the type it inhabits so that the two nestings cannot drift apart, and
    -- @unit@ where that type is @Unit@.
    --
    -- **Each equation is proved by @refl@ even where its type carries a
    -- transport**, because the proof supplies @refl@ for every earlier equation
    -- and a transport along @refl@ reduces away. That is the whole reason this
    -- generator is still as simple as it was before the telescopic case: the
    -- diagonal is where the paper's §3.3 construction costs nothing.
    diagonalMethod mdg c n =
      let args           = constructorArguments c
          (_, payload, n1) = telescopic args (map (Free . entryVar) args) n
          (body, n2)     = withHypotheses mdg args payload n1
       in (lamOver args body, n2)

    -- ----------------------------------------------------------------------
    -- Shared shapes
    -- ----------------------------------------------------------------------

    -- One inductive hypothesis binder per recursive argument, in argument
    -- order — the same reading of the record 'Thena.Global.Env.eliminatorType'
    -- makes, through the same function, so a method cannot bind a telescope its
    -- own type does not have. Nothing generated here ever /uses/ one.
    withHypotheses mot tel body = go tel
      where
        go []       n = (body, n)
        go (e : es) n = case recursiveArgument dn np (entryType e) of
          Nothing -> go es n
          Just is ->
            let (hv, n1)    = fresh n
                (below, n2) = go es n1
             in (Lam (Ident "ih") (foldl App mot (is ++ [Free (entryVar e)])) (close hv below), n2)

    -- ----------------------------------------------------------------------
    -- Telescopic equality, unpacked (Cockx, Devriese and Piessens, §3.3)
    -- ----------------------------------------------------------------------

    -- The equality of the constructor's own arguments with the terms @rs@, as
    -- one equation per argument, together with its proof for the case where
    -- @rs@ /are/ those arguments. Both at once, so the two nestings cannot
    -- drift apart.
    --
    -- The paper's equation 18 defines the equality of two sequences in one
    -- telescope inductively:
    --
    -- @
    -- ()      ≡ ()      :=  ⊤
    -- s; s̄    ≡ t; t̄    :=  (e : s ≡ t) (ē : e* s̄ ≡ t̄)
    -- @
    --
    -- so **the later equation is stated after transporting the earlier
    -- argument along the earlier equation**, which keeps every equation
    -- homogeneous and is why none of this needs a heterogeneous equality.
    -- @(e : …)(ē : …)@ is a telescope and not a conjunction — @ē@'s type
    -- mentions @e@ — which is what 'dpairAt' is for.
    --
    -- @Unit@ for a constructor with no arguments, and the bare equation for
    -- one. 'headOf' is where @e*@ happens.
    --
    -- **The pair is dependent exactly where the dependency is.** A later
    -- equation mentions this one's proof only where its own side had to be
    -- transported, and where it does not, @And@ says the same thing with one
    -- binder fewer — which is §3.7's own table, and what every datatype in the
    -- suite still generates. The same reason 'conjoin' used to drop the pair
    -- altogether for a single argument.
    telescopic args rs n0' = go [] Nothing args rs n0'
      where
        go _ _ []       _         n = (unitType, unitProof, n)
        go _ _ (_ : _)  []        n = (unitType, unitProof, n)
        go hist carry (e : es) (r : rs') n =
          let (ty, lhs, nextCarry, n1) = headOf hist carry e es r n
              eq  = eqAt ty lhs r
              prf = reflAt ty lhs
           in case es of
                [] -> (eq, prf, n1)
                _  ->
                  let (qv, n2)      = fresh n1
                      (carry', n3)  = nextCarry qv n2
                      h = Stated
                            { statedEntry = e
                            , statedMoved = lhs /= Free (entryVar e)
                            , statedType  = ty
                            , statedLeft  = lhs
                            , statedRight = r
                            , statedProof = qv
                            }
                      (restTy, restPrf, n4) = go (hist ++ [h]) carry' es rs' n3
                      binder = Lam (Ident "q") eq (close qv restTy)
                      prf'   = rewriting [(qv, prf)] restPrf
                   in ( if mentionedLater e es
                          then ( dpairAt eq binder
                               , dpairMk eq binder prf prf'
                               , n4 )
                          else ( andAt eq restTy
                               , bothAt eq restTy prf prf'
                               , n4 )
                      )

        unitType  = Global (GlobalName "Unit") [dl]
        unitProof = Global (GlobalName "unit") [dl]

        -- The type this argument's equation is stated at, its left side, and
        -- what the next argument inherits — @e*@ of equation 18, for one term.
        --
        -- **An argument whose type mentions nothing earlier is already where
        -- its equation wants it**, and that is the overwhelmingly common case:
        -- nothing is built, and the equation is @Eq Aₖ aₖ a'ₖ@ exactly as it was
        -- before any of this existed.
        --
        -- Otherwise it is transported along the equation for each argument its
        -- type mentions, one at a time, with the single-variable motive
        -- @λ z . Aₖ[aⱼ := z]@. **That motive is ill-formed exactly when a /later/
        -- argument mentions @aₖ@ as well** — once @aₖ@'s own left side is a
        -- transport, nothing can substitute it into a later type — so those
        -- arguments travel with it, packaged as nested pairs ('packType'). The
        -- package is transported once and then walked down, one component per
        -- argument, and each component's equation names the projection that the
        -- rest of the package is typed against.
        --
        -- **The package is the chain and not the telescope**, which is the whole
        -- of why this is affordable. @extend-there-extend@ has seven arguments
        -- and @i : extend-in(x : T ∈ Γ)@ mentions three of them, none of which
        -- any later argument mentions, so its package holds one thing and the
        -- construction is three transports. Packaging the suffix instead cost
        -- 6.3 MB of term for that one constructor and ten times the suite's
        -- running time, measured 2026-10-26.
        headOf hist carry e es r n = case carry of
          Just (p, inside@(e0 : _), done)
            | entryVar e0 == entryVar e -> walking p inside done n
          _ | null ownDeps              -> (entryType e, Free (entryVar e), keep, n)
            | otherwise                 ->
                let (p, done, n1) = foldl outward (packValue [] packed, [], n) mentioned
                 in walking p packed done n1
          where
            -- Nothing was built, so a package already in flight keeps flying.
            keep _ nn = (carry, nn)

            -- **Whether this argument moves at all is decided by its own type
            -- and nothing else.** Deciding it from the package instead was a
            -- defect: @Γ@ of @extend-there-extend@ mentions nothing earlier, so
            -- it does not move — but a later argument mentions @Γ@, so asking
            -- the package first dragged the whole telescope in and cost the
            -- 6.3 MB this construction exists to avoid.
            ownDeps = [ h | h <- hist, mentions h (entryType e) ]

            -- Every equation already stated about an argument that any member
            -- of the package mentions. Reaching here with a package in flight
            -- but not at its head means this argument is not in it, so none of
            -- these was moved.
            mentioned =
              [ h | h <- hist, any (mentions h) (map entryType packed) ]

            mentions h t = entryVar (statedEntry h) `elem` freeVars t

            -- This argument, and the arguments after it that have to travel
            -- with it: the ones whose types reach back into the chain, taken as
            -- a contiguous span so that one package is enough.
            packed = e : take carried es
            carried = case chain of
              [] -> 0
              _  -> maximum [ k | (k, x) <- zip [1 ..] es
                                , entryVar x `elem` map entryVar chain ]
            chain = settle []
            settle acc =
              let known = entryVar e : map entryVar acc
                  acc'  = [ x | x <- es
                              , any (`elem` freeVars (entryType x)) known ]
               in if length acc' == length acc then acc else settle acc'

            -- The package, moved along one equation about an argument outside
            -- it. Those arguments were in place where they were stated, so the
            -- equation's left side is the binder and the motive is a plain
            -- substitution.
            outward (t, done, nn) h =
              let v         = entryVar (statedEntry h)
                  (t', nn') = transportAt (statedType h)
                                (\z -> packType (done ++ [(v, z)]) packed)
                                (statedLeft h) (statedRight h)
                                (Free (statedProof h)) t nn
               in (t', done ++ [(v, statedRight h)], nn')

            -- At the head of a package: the component is its first projection,
            -- and what the next argument inherits is the tail transported along
            -- this argument's own equation.
            walking p inside done nn = case inside of
              [_] -> (rewriting done (entryType e), p, \_ m -> (Nothing, m), nn)
              _ : rest ->
                let a        = rewriting done (entryType e)
                    b        = Lam (Ident "z") a
                                 (close (entryVar e) (packType done rest))
                    (hd, n1) = firstOf a b p nn
                    onward q m =
                      let (tl, m1) = secondOf a b p m
                          (mv, m2) = transportAt a
                                       (\z -> packType (done ++ [(entryVar e, z)]) rest)
                                       hd r (Free q) tl m1
                       in (Just (mv, rest, done ++ [(entryVar e, r)]), m2)
                 in (a, hd, onward, n1)
              [] -> (rewriting done (entryType e), p, \_ m -> (Nothing, m), nn)

    -- @t@ with each listed variable rewritten to its term, left to right.
    -- 'close' then 'instantiate' is the only way to rewrite a variable (§3.4).
    rewriting ss t = foldl (\t' (v, r) -> instantiate r (close v t')) t ss

    -- A telescope as nested pairs: @DPair A₁ (λ a₁ . DPair A₂ (λ a₂ . A₃))@ for
    -- three entries, and the bare type for one.
    --
    -- **This is what makes a dependent telescope transportable.** A pair's
    -- second component is a λ, so each later type is written under a binder for
    -- the argument before it rather than against a free variable — and the
    -- whole thing is then one type, with one motive, that a single J can move.
    packType ss es = case es of
      []       -> Global (GlobalName "Unit") [dl]
      [e]      -> rewriting ss (entryType e)
      e : rest -> dpairAt (rewriting ss (entryType e))
                    (Lam (Ident "z") (rewriting ss (entryType e))
                       (close (entryVar e) (packType ss rest)))

    -- The arguments themselves, packaged to inhabit 'packType' of the same
    -- entries. Only ever called where @ss@ changes none of their types, which
    -- is why the components are the binders and not something carried.
    packValue ss es = case es of
      []       -> Global (GlobalName "unit") [dl]
      [e]      -> Free (entryVar e)
      e : rest -> dpairMk (rewriting ss (entryType e))
                    (Lam (Ident "z") (rewriting ss (entryType e))
                       (close (entryVar e) (packType ss rest)))
                    (Free (entryVar e))
                    (packValue ss rest)

    -- @elim DPair (A B) (λ p . A) ((λ x y . x)) () p@ — written only inside
    -- 'secondOf'\'s motive, which is where the prelude's @snd@ writes it too.
    -- **'moveIn' never projects a head**: the equation it is about already names
    -- the component, which is what 'statedLeft' is.
    firstOf a b p n =
      let (zv, n1) = fresh n
          (xv, n2) = fresh n1
          (yv, n3) = fresh n2
       in ( Eliminate (GlobalName "DPair") [dl, dl] [a, b]
              (Lam (Ident "p") (dpairAt a b) (close zv a))
              [ Lam (Ident "x") a (close xv
                  (Lam (Ident "y") (App b (Free xv)) (close yv (Free xv)))) ]
              [] p
          , n3 )

    -- @elim DPair (A B) (λ p . B (fst p)) ((λ x y . y)) () p@ — the second
    -- projection, and the only one 'moveIn' needs.
    --
    -- Built rather than named, for the reason "Thena.Tactics.Specialise" gives
    -- where it builds the same thing: the prelude's projections are
    -- /definitions/ and this module depends on the prelude's constructors alone.
    secondOf a b p n =
      let (zv, n1)  = fresh n
          (fp, n2)  = firstOf a b (Free zv) n1
          (xv, n3)  = fresh n2
          (yv, n4)  = fresh n3
       in ( Eliminate (GlobalName "DPair") [dl, dl] [a, b]
              (Lam (Ident "p") (dpairAt a b) (close zv (App b fp)))
              [ Lam (Ident "x") a (close xv
                  (Lam (Ident "y") (App b (Free xv)) (close yv (Free yv)))) ]
              [] p
          , n4 )

    -- @elim Eq (A) (λ u v w . M u -> M v) ((λ a z . z)) (x, y) e@ applied to
    -- @p@ — the prelude's @transport@, built inline for 'firstOf'\'s reason.
    --
    -- **J's motive here is a function type and not @M v@**, because the method
    -- has to be proved at @refl@ for an arbitrary @a@, where @M a -> M a@ is
    -- the identity and @M a@ is nothing in particular.
    transportAt a m x y e p n =
      let (uv, n1) = fresh n
          (vv, n2) = fresh n1
          (wv, n3) = fresh n2
          (dv, n4) = fresh n3
          (av, n5) = fresh n4
          (zv, n6) = fresh n5
          mot = Lam (Ident "u") a (close uv
                  (Lam (Ident "v") a (close vv
                    (Lam (Ident "w") (eqAt a (Free uv) (Free vv)) (close wv
                      (Pi (Ident "p") (m (Free uv)) (close dv (m (Free vv)))))))))
          meth = Lam (Ident "a") a (close av
                   (Lam (Ident "z") (m (Free av)) (close zv (Free zv))))
       in (App (Eliminate (GlobalName "Eq") [dl] [a] mot [meth] [x, y] e) p, n6)

-- --------------------------------------------------------------------------
-- Preconditions
-- --------------------------------------------------------------------------

-- | Is there an @Eq@ of the prelude's shape?
--
-- Matched structurally rather than by name alone. A user is free to declare
-- something else called @Eq@ — one namespace (§3.6) — and the cost of not
-- looking would be that every subsequent @data@ is refused with a type error
-- from a term the user never wrote.
equalityInScope :: GlobalEnv -> Bool
equalityInScope env = case lookupInductive (GlobalName "Eq") env of
  Nothing -> False
  Just e -> case (inductiveParameters e, inductiveIndices e, inductiveConstructors e) of
    -- **@Eq@ is level-polymorphic in exactly one parameter** (MS3 phase 31d),
    -- and the shape check follows it: the carrier lives at that parameter, and
    -- so does the family. Everything this module generates is still stated at
    -- @Eq {0}@ — no-confusion is only produced for a @Type₀@ datatype (the
    -- guard below), whose constructor arguments live at @Type₀@ too by the size
    -- restriction.
    ([a], [i, j], [c]) | [lv] <- inductiveLevels e ->
      inductiveLevel e == LVar lv
        && entryType a == Universe (LVar lv)
        && entryType i == Free (entryVar a)
        && entryType j == Free (entryVar a)
        && constructorName c == GlobalName "refl"
        && case constructorArguments c of
             [x] -> entryType x == Free (entryVar a)
                      && constructorIndices c == [Free (entryVar x), Free (entryVar x)]
             _   -> False
    _ -> False

-- | Are the prelude types /this/ datatype's table is written out of in scope?
--
-- Matched structurally, for 'equalityInScope'\'s reason and by the same
-- technique, and reported the same way — silently.
--
-- **Only what the generator will actually write is required.** The three names
-- are each demanded by one shape of case and by nothing else:
--
-- * @Empty@ by an off-diagonal case, so only where there are two or more
--   constructors to be off the diagonal of;
-- * @Unit@ and @unit@ by a diagonal case for a constructor with no arguments;
-- * @And@ and @both@ by a diagonal case for a constructor with two or more,
--   since one argument needs no conjunction and 'telescopic' emits the bare
--   equation;
-- * @DPair@ and @dpair@ by a diagonal case for a /dependent/ telescope, and
--   only there — see 'telescopic'.
--
-- Asking for all three unconditionally would be simpler and wrong. The prelude
-- must declare @Eq@ before @DPair@ — @DPair@\'s own no-confusion needs the
-- equality — and @Eq@\'s single constructor @refl@ takes a single argument, so
-- its table mentions none of the three. Under a blanket check @NoConfusionEq@
-- would be silently lost at the very line that makes everything else possible.
--
-- **And it is why @DPair@ stands third in the prelude, before @And@ and
-- @Unit@** (MS9 phase 212). @both@ takes two arguments, so @And@\'s own table
-- wants a pair; declared after it, @NoConfusionAnd@ would be lost the same
-- silent way.
productsInScope :: GlobalEnv -> InductiveDefinition -> Bool
productsInScope env d =
     (not needsEmpty || falsityInScope env)
  && (not needsUnit  || truthInScope env)
  && (not needsAnd   || conjunctionInScope env)
  && (not needsPair  || dependentPairInScope env)
  where
    cs         = inductiveConstructors d
    arity      = length . constructorArguments
    needsEmpty = length cs >= 2
    needsUnit  = any ((== 0) . arity) cs
    -- **Per position and not per arity**, because the two answers are what
    -- break the prelude's ordering if they are approximated. @dpair@ has two
    -- arguments and needs no @And@ at all — its one pair is dependent — and
    -- asking for @And@ anyway declined @NoConfusionDPair@ silently, @And@ being
    -- declared after it. The converse approximation is worse: a pair demanded
    -- and absent is a generated term that does not typecheck.
    needsAnd   = any (elem False . pairKinds) cs
    needsPair  = any (elem True  . pairKinds) cs

-- | @And {ℓ₀ ℓ₁} (A : Type ℓ₀) (B : Type ℓ₁) : Type (ℓ₀ ⊔ ℓ₁)
--   { both : ∀ (a : A) (b : B) -> And A B }@
--
-- **One level per conjunct** (MS3 phase 33c), inferred rather than written:
-- each @Type@ in the declaration is its own unknown, so writing @Type@ twice is
-- what gives the general form, and the join is computed.
--
-- The result level is compared **up to the algebra**, since that is what
-- @Eq Level@ is: @Type (ℓ₀ ⊔ ℓ₁)@ is what generalisation produces and
-- @normalise@ is what makes the comparison mean it.
conjunctionInScope :: GlobalEnv -> Bool
conjunctionInScope env = case lookupInductive (GlobalName "And") env of
  Nothing -> False
  Just e -> case (inductiveParameters e, inductiveIndices e, inductiveConstructors e) of
    ([a, b], [], [c]) | [l0, l1] <- inductiveLevels e ->
      inductiveLevel e == LMax (LVar l0) (LVar l1)
        && entryType a == Universe (LVar l0)
        && entryType b == Universe (LVar l1)
        && constructorName c == GlobalName "both"
        && case constructorArguments c of
             [x, y] -> entryType x == Free (entryVar a)
                         && entryType y == Free (entryVar b)
                         && null (constructorIndices c)
             _      -> False
    _ -> False

-- | @DPair {ℓ₀ ℓ₁} (A : Type ℓ₀) (B : A -> Type ℓ₁) : Type (ℓ₀ ⊔ ℓ₁)
--   { dpair : ∀ (a : A) (b : B a) -> DPair A B }@
--
-- **One level per component**, inferred rather than written: each @Type@ in the
-- declaration is its own unknown, so writing @Type@ twice is what gives the
-- general form, and the join is computed (MS3 phase 33c, where @And@ got the
-- same treatment). @Sigma@ beside it in the prelude is this construction pinned
-- at @Type₀@, which no-confusion cannot use — every equation it states is at the
-- datatype's own level.
--
-- The result level is compared **up to the algebra**, since that is what
-- @Eq Level@ is: @Type (ℓ₀ ⊔ ℓ₁)@ is what generalisation produces and
-- @normalise@ is what makes the comparison mean it.
dependentPairInScope :: GlobalEnv -> Bool
dependentPairInScope env = case lookupInductive (GlobalName "DPair") env of
  Nothing -> False
  Just e -> case (inductiveParameters e, inductiveIndices e, inductiveConstructors e) of
    ([a, b], [], [c]) | [l0, l1] <- inductiveLevels e ->
      inductiveLevel e == LMax (LVar l0) (LVar l1)
        && entryType a == Universe (LVar l0)
        && secondIsAFamilyOver a l1 (entryType b)
        && constructorName c == GlobalName "dpair"
        && case constructorArguments c of
             [x, y] -> entryType x == Free (entryVar a)
                         && entryType y == App (Free (entryVar b)) (Free (entryVar x))
                         && null (constructorIndices c)
             _      -> False
    _ -> False
  where
    -- @B : A -> Type l1@, matched rather than compared: the domain binder's
    -- 'Ident' is whatever the prelude's author wrote and says nothing.
    secondIsAFamilyOver a l1 t = case t of
      Pi _ dom sc -> dom == Free (entryVar a)
                       && instantiate (Free (entryVar a)) sc == Universe (LVar l1)
      _           -> False

-- | @Unit : Type₀ { unit : Unit }@ — @unit@ is checked because 'telescopic'
-- writes it, not only the type.
truthInScope :: GlobalEnv -> Bool
truthInScope env = case lookupInductive (GlobalName "Unit") env of
  Nothing -> False
  Just e -> case (inductiveParameters e, inductiveIndices e, inductiveConstructors e) of
    ([], [], [c]) | [lv] <- inductiveLevels e ->
      inductiveLevel e == LVar lv
        && constructorName c == GlobalName "unit"
        && null (constructorArguments c)
        && null (constructorIndices c)
    _ -> False

-- | @Empty : Type₀ { }@ — no constructor to check, which is the point of it.
falsityInScope :: GlobalEnv -> Bool
falsityInScope env = case lookupInductive (GlobalName "Empty") env of
  Nothing -> False
  Just e -> case inductiveLevels e of
    [lv] -> null (inductiveParameters e)
              && null (inductiveIndices e)
              && null (inductiveConstructors e)
              && inductiveLevel e == LVar lv
    _ -> False

-- | Does some argument of this constructor have a type that mentions an
-- argument before it?
--
-- **This no longer decides whether no-confusion is generated** — 'telescopic'
-- states a transported chain of equations for exactly this case, and before
-- MS9 phase 212 the whole datatype was declined when the answer was yes.
-- What is left of it is a question the transitions ask: a dependent telescope's
-- equations carry transports, and "Thena.Tactics.Specialise" rebuilds the chain
-- rather than reading it back, so it declines a chain it cannot yet rebuild.
-- | Is this argument mentioned by the type of any argument after it?
--
-- **This one question decides which pair each equation is held in**, and it is
-- asked in two places that must agree: 'telescopic' builds the pair, and
-- 'productsInScope' says which prelude types the constructor will therefore
-- need. @True@ means the equations after this one are stated about a transport
-- along /this/ one's proof, so the pair has to be @DPair@; @False@ means @And@
-- says the same thing with one binder fewer.
mentionedLater :: Entry -> [Entry] -> Bool
mentionedLater e after =
  any ((entryVar e `elem`) . freeVars . entryType) after

-- | Which pair each of a constructor's equations is held in, in argument order,
-- one entry shorter than the telescope — the last equation heads no pair.
pairKinds :: ConstructorDefinition -> [Bool]
pairKinds c = case constructorArguments c of
  []     -> []
  args   -> [ mentionedLater e after
            | (e, after) <- zip args (drop 1 (suffixes args))
            , not (null after) ]
  where
    suffixes xs = case xs of
      []      -> [[]]
      _ : rest -> xs : suffixes rest

dependentTelescope :: ConstructorDefinition -> Bool
dependentTelescope c = go [] (constructorArguments c)
  where
    go _    []       = False
    go seen (e : es) =
         any (`elem` seen) (freeVars (entryType e))
      || go (entryVar e : seen) es

-- --------------------------------------------------------------------------
-- Small helpers
-- --------------------------------------------------------------------------

varsOf :: Context -> [Core]
varsOf = map (Free . entryVar)

-- | A second copy of a telescope, with new variables — primed, so a printed
-- term does not show two binders with one name.
--
-- **Every later entry is repointed at the new variable** — a telescope is
-- dependent in general, and an entry whose type still named the /old/ variable
-- would be a copy that silently refers back into the original. Phase 17 found
-- this the hard way: it is invisible for every telescope in the suite, because
-- none of them is dependent where this is used, and it made
-- @data Below : ∀ (n : Nat) (i : Fin n) -> Type₀@ generate a
-- @NoConfusionBelow@ that did not typecheck — reported as "the variables
-- Var 125 and Var 121 are different", which is exactly what it was.
--
-- 'close' then 'instantiate' is the only way to rewrite a variable (§3.4), and
-- it is safe here because both are free variables of the ambient context.
freshen :: Int -> Context -> (Context, Int)
freshen n0 = go n0
  where
    go n []       = ([], n)
    go n (e : es) =
      let (v, n1)    = fresh n
          (rest, n2) = go n1 (map (repoint (entryVar e) v) es)
       in (copy v e : rest, n2)

    copy v e = case e of
      Hypothesis _ (Ident i) t   -> Hypothesis v (Ident (i ++ "'")) t
      Definition _ (Ident i) s t -> Definition v (Ident (i ++ "'")) s t

    repoint old new e = case e of
      Hypothesis w i t   -> Hypothesis w i (swap t)
      Definition w i s t -> Definition w i (swap s) (swap t)
      where
        swap t = instantiate (Free new) (close old t)

-- | Map with the counter threaded, left to right.
each :: (a -> Int -> (b, Int)) -> Int -> [a] -> ([b], Int)
each f = go
  where
    go n []       = ([], n)
    go n (x : xs) =
      let (y,  n1) = f x n
          (ys, n2) = go n1 xs
       in (y : ys, n2)
