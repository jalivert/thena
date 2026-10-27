-- | The equipment every generator writes its terms out of.
--
-- **Two generators now, where there was one.** "Thena.Global.NoConfusion"
-- emits the no-confusion family and its two lemmas; "Thena.Global.NoCycle"
-- emits the acyclicity equipment the cycle transition needs. They share the
-- telescopic equality of §3.3, the prelude spellings, and the question of
-- whether a prelude type is in scope and well shaped — so those live here and
-- are stated once.
--
-- **The §3.3 walk is the reason this module exists** (MS9 phase 219). A second
-- reading of the paper's equation 18 would be a second thing to keep in step
-- with the first, and the chain is exactly where that would go wrong silently:
-- a transport left out of one copy is a term that still typechecks and says
-- less than its name. 'stations' walks a telescope once and the two shapes the
-- generators want — 'package', which nests the equations into pairs, and
-- 'chained', which curries them into a Π-telescope — are folds of that one
-- walk.
--
-- **Each generator composes its own precondition out of the primitives here**,
-- and does not share one. What is checked is whether @Eq@, @Unit@, @Empty@,
-- @And@ and @DPair@ are in scope /and of the prelude's shape/; which of them a
-- given generator will actually write is its own question, asked in its own
-- module. Sharing the composite is what @.claude\/HAZARDS.md@ records as
-- /an additive artifact is not additive if it shares the bundle's up-front
-- guard/.
module Thena.Global.Generate
  ( -- * What generation did
    Generated (..)

    -- * Telescopic equality, unpacked (Cockx, Devriese and Piessens, §3.3)
  , Stated (..)
  , stations
  , telescopic
  , package
  , chained
  , lamsOver
  , telescopicChain

    -- * The prelude spellings, at a datatype's own level
  , eqAt
  , reflAt
  , andAt
  , bothAt
  , dpairAt
  , dpairMk
  , unitType
  , unitProof
  , emptyType
  , andFirst
  , andSecond
  , transportAt
  , packType
  , packValue
  , firstOf
  , secondOf
  , rewriting

    -- * Is a prelude type in scope, and of the prelude's shape?
  , equalityInScope
  , conjunctionInScope
  , dependentPairInScope
  , truthInScope
  , falsityInScope

    -- * Eliminating a chain down to its diagonal
  , Chain (..)
  , chainGoalType
  , chainProof
  , retypeIn
  , rewriteStated
  , curriedRefls
  , unpackChain
  , chainIsFlat

    -- * Small helpers
  , mentionsAnEarlierEntry
  , varsOf
  , freshen
  , freshenAs
  , each
  ) where

import Thena.Core.Level (Level (..))
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
import Thena.Errors (Skipped (..), TypeError)
import Thena.Global.Env
  ( ConstructorDefinition (..)
  , GlobalEnv
  , InductiveDefinition (..)
  , lookupInductive
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

-- --------------------------------------------------------------------------
-- Telescopic equality, unpacked (Cockx, Devriese and Piessens, §3.3)
-- --------------------------------------------------------------------------

-- | The prelude spellings everything generated here is written out of, each at
-- the datatype's own level (MS3 phase 31g) — see 'generateNoConfusion'\'s @dl@
-- for why that is what cumulativity buys.
--
-- **Top level and level-indexed since MS9 phase 219**, where "Thena.Global.NoCycle"
-- became the second generator to state the same chain. It is stated once, here,
-- and that is the property the module was already written for: a second copy of
-- 'stations' would be a second reading of §3.3 to keep in step.

eqAt :: Level -> Core -> Core -> Core -> Core
eqAt dl a x y = foldl App (Global (GlobalName "Eq") [dl]) [a, x, y]
reflAt :: Level -> Core -> Core -> Core
reflAt dl a x = foldl App (Global (GlobalName "refl") [dl]) [a, x]

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
andAt :: Level -> Core -> Core -> Core
andAt dl p q        = foldl App (Global (GlobalName "And") [dl, dl]) [p, q]
bothAt :: Level -> Core -> Core -> Core -> Core -> Core
bothAt dl p q x y   = foldl App (Global (GlobalName "both") [dl, dl]) [p, q, x, y]
dpairAt :: Level -> Core -> Core -> Core
dpairAt dl a b      = foldl App (Global (GlobalName "DPair") [dl, dl]) [a, b]
dpairMk :: Level -> Core -> Core -> Core -> Core -> Core
dpairMk dl a b x y  = foldl App (Global (GlobalName "dpair") [dl, dl]) [a, b, x, y]
unitType :: Level -> Core
unitType dl         = Global (GlobalName "Unit") [dl]
unitProof :: Level -> Core
unitProof dl        = Global (GlobalName "unit") [dl]


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
-- **The pair is dependent exactly where the dependency is, and the question
-- is asked of the type that was built rather than predicted from the
-- telescope.** A later equation mentions this one's proof only where its own
-- side had to be transported, and where it does not, @And@ says the same
-- thing with one binder fewer — which is §3.7's own table, and what every
-- datatype in the suite still generates. The same reason 'conjoin' used to
-- drop the pair altogether for a single argument.
--
-- **Predicting it from \"is this argument mentioned later\" was wrong, and
-- phase 216 found the shape it was wrong on.** An argument that is carried
-- inside a package but that no later argument mentions still has the rest
-- of the package transported along /its/ proof, because 'walking' moves the
-- tail one component at a time — so the rest mentions the proof while
-- nothing mentions the argument. @Use@ below generated an @And@ whose
-- second conjunct had that proof free, and the checker refused the family
-- it had built:
--
-- @
-- data Holder (A : Type₀) : ∀ (n : N) -> Vec A n -> Type₀ where
--   hmk : ∀ (n : N) (as : Vec A n) -> Holder A n as
-- data Use (A : Type₀) : Type₀ where
--   umk : ∀ (n : N) (as : Vec A n) (pa : A) (h : Holder A n as) -> Use A
-- @
--
-- @pa@ sits between @as@ and the argument that reaches back past it, so the
-- package is @as; pa; h@ and @pa@ is interior to it. 'mentionedLater' still
-- says which prelude types the constructor needs — see 'pairKinds' — and
-- that is all it says now.
telescopic :: Level -> Context -> [Core] -> Int -> (Core, Core, Int)
telescopic dl args rs n0' =
  let (hs, n1)  = stations dl args rs n0'
      (ty, prf) = package dl hs
   in (ty, prf, n1)

-- | The package, folded from the stations right to left.
--
-- **The dependent pair is used exactly where the dependency is**, and the
-- question is asked of the type that was built rather than predicted from
-- the telescope — see 'stations' for the shape phase 216 found that wrong
-- on. Where a later equation does not mention this one's proof, @And@ says
-- the same thing with one binder fewer.
package :: Level -> [Stated] -> (Core, Core)
package dl []  = (unitType dl, unitProof dl)
package dl [h] = ( eqAt dl (statedType h) (statedLeft h) (statedRight h)
              , reflAt dl (statedType h) (statedLeft h)
              )
package dl (h : hs) =
  let eq                = eqAt dl (statedType h) (statedLeft h) (statedRight h)
      prf               = reflAt dl (statedType h) (statedLeft h)
      (restTy, restPrf) = package dl hs
      qv                = statedProof h
      binder            = Lam (Ident "q") eq (close qv restTy)
      prf'              = rewriting [(qv, prf)] restPrf
   in if qv `elem` freeVars restTy
        then (dpairAt dl eq binder, dpairMk dl eq binder prf prf')
        else (andAt dl eq restTy,   bothAt dl eq restTy prf prf')

-- | One 'Stated' per argument: the equation it contributes, the type that
-- equation is stated at, and the binder standing for its proof.
--
-- **Separated from the packaging at MS9 phase 218**, which wants the same
-- walk curried into a Π-telescope rather than nested into pairs — a
-- specialiser holds its equations as separate binders, so a lemma it calls
-- must take them that way. One walk, two shapes, and they cannot drift.
stations :: Level -> Context -> [Core] -> Int -> ([Stated], Int)
stations dl args rs n0' = go [] Nothing args rs n0'
  where
    go _ _ []       _         n = ([], n)
    go _ _ (_ : _)  []        n = ([], n)
    go hist carry (e : es) (r : rs') n =
      let (ty, lhs, nextCarry, n1) = headOf hist carry e es r n
          (qv, n2) = fresh n1
          h = Stated
                { statedEntry = e
                , statedMoved = lhs /= Free (entryVar e)
                , statedType  = ty
                , statedLeft  = lhs
                , statedRight = r
                , statedProof = qv
                }
       in case es of
            [] -> ([h], n2)
            _  ->
              let (carry', n3) = nextCarry qv n2
                  (rest,   n4) = go (hist ++ [h]) carry' es rs' n3
               in (h : rest, n4)

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
            let (p, done, n1) = foldl outward (packValue dl [] packed, [], n) mentioned
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
              (t', nn') = transportAt dl (statedType h)
                            (\z -> packType dl (done ++ [(v, z)]) packed)
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
                             (close (entryVar e) (packType dl done rest))
                (hd, n1) = firstOf dl a b p nn
                onward q m =
                  let (tl, m1) = secondOf dl a b p m
                      (mv, m2) = transportAt dl a
                                   (\z -> packType dl (done ++ [(entryVar e, z)]) rest)
                                   hd r (Free q) tl m1
                   in (Just (mv, rest, done ++ [(entryVar e, r)]), m2)
             in (a, hd, onward, n1)
          [] -> (rewriting done (entryType e), p, \_ m -> (Nothing, m), nn)

-- @t@ with each listed variable rewritten to its term, left to right.
-- 'close' then 'instantiate' is the only way to rewrite a variable (§3.4).
rewriting :: [(Var, Core)] -> Core -> Core
rewriting ss t = foldl (\t' (v, r) -> instantiate r (close v t')) t ss

-- A telescope as nested pairs: @DPair A₁ (λ a₁ . DPair A₂ (λ a₂ . A₃))@ for
-- three entries, and the bare type for one.
--
-- **This is what makes a dependent telescope transportable.** A pair's
-- second component is a λ, so each later type is written under a binder for
-- the argument before it rather than against a free variable — and the
-- whole thing is then one type, with one motive, that a single J can move.
packType :: Level -> [(Var, Core)] -> Context -> Core
packType dl ss es = case es of
  []       -> Global (GlobalName "Unit") [dl]
  [e]      -> rewriting ss (entryType e)
  e : rest -> dpairAt dl (rewriting ss (entryType e))
                (Lam (Ident "z") (rewriting ss (entryType e))
                   (close (entryVar e) (packType dl ss rest)))

-- The arguments themselves, packaged to inhabit 'packType' of the same
-- entries. Only ever called where @ss@ changes none of their types, which
-- is why the components are the binders and not something carried.
packValue :: Level -> [(Var, Core)] -> Context -> Core
packValue dl ss es = case es of
  []       -> Global (GlobalName "unit") [dl]
  [e]      -> Free (entryVar e)
  e : rest -> dpairMk dl (rewriting ss (entryType e))
                (Lam (Ident "z") (rewriting ss (entryType e))
                   (close (entryVar e) (packType dl ss rest)))
                (Free (entryVar e))
                (packValue dl ss rest)

-- @elim DPair (A B) (λ p . A) ((λ x y . x)) () p@ — written only inside
-- 'secondOf'\'s motive, which is where the prelude's @snd@ writes it too.
-- **'moveIn' never projects a head**: the equation it is about already names
-- the component, which is what 'statedLeft' is.
firstOf :: Level -> Core -> Core -> Core -> Int -> (Core, Int)
firstOf dl a b p n =
  let (zv, n1) = fresh n
      (xv, n2) = fresh n1
      (yv, n3) = fresh n2
   in ( Eliminate (GlobalName "DPair") [dl, dl] [a, b]
          (Lam (Ident "p") (dpairAt dl a b) (close zv a))
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
secondOf :: Level -> Core -> Core -> Core -> Int -> (Core, Int)
secondOf dl a b p n =
  let (zv, n1)  = fresh n
      (fp, n2)  = firstOf dl a b (Free zv) n1
      (xv, n3)  = fresh n2
      (yv, n4)  = fresh n3
   in ( Eliminate (GlobalName "DPair") [dl, dl] [a, b]
          (Lam (Ident "p") (dpairAt dl a b) (close zv (App b fp)))
          [ Lam (Ident "x") a (close xv
              (Lam (Ident "y") (App b (Free xv)) (close yv (Free yv)))) ]
          [] p
      , n4 )

-- | @elim And (A B) (λ _ . A) ((λ a b . a)) () c@ — the first projection, built
-- rather than named for 'firstOf'\'s reason: the prelude\'s projections are
-- /definitions/ and what is generated here depends on its constructors alone.
andFirst :: Level -> Core -> Core -> Core -> Int -> (Core, Int)
andFirst dl a b p n =
  let (zv, n1) = fresh n
      (xv, n2) = fresh n1
      (yv, n3) = fresh n2
   in ( Eliminate (GlobalName "And") [dl, dl] [a, b]
          (Lam (Ident "c") (andAt dl a b) (close zv a))
          [ Lam (Ident "x") a (close xv
              (Lam (Ident "y") b (close yv (Free xv)))) ]
          [] p
      , n3 )

-- | @elim And (A B) (λ _ . B) ((λ a b . b)) () c@ — the second.
andSecond :: Level -> Core -> Core -> Core -> Int -> (Core, Int)
andSecond dl a b p n =
  let (zv, n1) = fresh n
      (xv, n2) = fresh n1
      (yv, n3) = fresh n2
   in ( Eliminate (GlobalName "And") [dl, dl] [a, b]
          (Lam (Ident "c") (andAt dl a b) (close zv b))
          [ Lam (Ident "x") a (close xv
              (Lam (Ident "y") b (close yv (Free yv)))) ]
          [] p
      , n3 )


-- @elim Eq (A) (λ u v w . M u -> M v) ((λ a z . z)) (x, y) e@ applied to
-- @p@ — the prelude's @transport@, built inline for 'firstOf'\'s reason.
--
-- **J's motive here is a function type and not @M v@**, because the method
-- has to be proved at @refl@ for an arbitrary @a@, where @M a -> M a@ is
-- the identity and @M a@ is nothing in particular.
transportAt :: Level -> Core -> (Core -> Core) -> Core -> Core -> Core -> Core -> Int -> (Core, Int)
transportAt dl a m x y e p n =
  let (uv, n1) = fresh n
      (vv, n2) = fresh n1
      (wv, n3) = fresh n2
      (dv, n4) = fresh n3
      (av, n5) = fresh n4
      (zv, n6) = fresh n5
      mot = Lam (Ident "u") a (close uv
              (Lam (Ident "v") a (close vv
                (Lam (Ident "w") (eqAt dl a (Free uv) (Free vv)) (close wv
                  (Pi (Ident "p") (m (Free uv)) (close dv (m (Free vv)))))))))
      meth = Lam (Ident "a") a (close av
               (Lam (Ident "z") (m (Free av)) (close zv (Free zv))))
   in (App (Eliminate (GlobalName "Eq") [dl] [a] mot [meth] [x, y] e) p, n6)

-- | The curried chain: one Π per equation, in order, each closing over the
-- binder that stands for its proof so the next equation's transports can
-- name it.
chained :: Level -> [Stated] -> Core -> Core
chained dl hs result =
  foldr
    (\h acc ->
       Pi (Ident "q")
          (eqAt dl (statedType h) (statedLeft h) (statedRight h))
          (close (statedProof h) acc))
    result hs


-- | One λ per equation of a chain, matching 'chained' binder for binder.
lamsOver :: Level -> [Stated] -> Core -> Core
lamsOver dl hs body =
  foldr
    (\h acc ->
       Lam (Ident "q")
           (eqAt dl (statedType h) (statedLeft h) (statedRight h))
           (close (statedProof h) acc))
    body hs

-- | @Empty@ at the datatype's own level — the off-diagonal case, and what the
-- acyclicity relations are negations into.
emptyType :: Level -> Core
emptyType dl = Global (GlobalName "Empty") [dl]

-- | The curried telescopic equality between the telescope @tel@ and the terms
-- @rs@, ending in @result@: one Π per entry, each closing over the binder that
-- stands for its proof so the next entry's transports can name it.
--
-- **This is the chain as a /type/ and nothing else**, which is what a generator
-- that only states a proposition about two telescopes needs — @NotEq@\'s
-- @‹chain› -> Empty@ is the whole of its body. A generator that also has to
-- /prove/ something equation by equation wants 'stations' itself, so that it
-- can name each proof binder.
telescopicChain :: Level -> Context -> [Core] -> Core -> Int -> (Core, Int)
telescopicChain dl tel rs result n =
  let (hs, n1) = stations dl tel rs n
   in (chained dl hs result, n1)

-- --------------------------------------------------------------------------
-- Eliminating a chain down to its diagonal (MS9 phase 220)
-- --------------------------------------------------------------------------

-- | A chain to be eliminated: one telescope, two instantiations of it, and what
-- is to be proved about the two.
--
-- **Three generated lemmas state a chain and then eliminate it, and this is the
-- one walk all three go through.** The telescopic no-confusion lemma eliminates
-- the chain between @(ī; x)@ and @(j̄; y)@; @noCycleD@ eliminates the same chain
-- down to \"nothing is below itself\"; and the @Step@ lemma\'s diagonal case
-- eliminates the chain between a constructor\'s argument telescope and a second
-- copy of it. A second copy of the walk would be a second thing to keep in step,
-- and the failure mode is silent — a transport left out of one copy still
-- typechecks.
--
-- **Both sides are generalised at every step, not just the one being
-- eliminated**: a later entry\'s type mentions the entry the step is about, so it
-- cannot stay in scope across the elimination. The motive re-quantifies the rest
-- of the telescope on both sides, along with the equations after this one, and
-- the J is then applied to exactly those.
data Chain = Chain
  { chainLevel     :: Level
    -- ^ the level every equation is stated at
  , chainTelescope :: Context
    -- ^ the telescope both sides instantiate
  , chainGoal      :: [Core] -> [Core] -> Core
    -- ^ what is to be proved, at the left and right instantiations
  , chainDiagonal  :: [Core] -> Int -> (Core, Int)
    -- ^ its inhabitant where the two sides have become one
  }

-- | @∀ ⟨Θ⟩ ⟨Θ\'⟩ ⟨the chain between them⟩ -> goal@, which 'chainProof' inhabits.
chainGoalType :: Chain -> Int -> (Core, Int)
chainGoalType ch = goalFrom ch [] [] (chainTelescope ch)

-- | The nested J, one step per entry of the telescope, ending in the diagonal.
chainProof :: Chain -> Int -> (Core, Int)
chainProof ch = proofFrom ch [] (chainTelescope ch)

-- | The goal, with some positions already unified and one supplied.
--
-- @shared@ are positions J has already unified, so both sides carry the same
-- term and neither needs an equation. @supplied@ are positions whose two sides
-- /and whose equation/ are given rather than bound — that is what a step\'s
-- motive does with @u@, @v@ and @w@, and it is why the transports in the
-- equations after it come out along @w@ rather than along a binder of this type.
-- @remaining@ is quantified fresh on both sides.
--
-- **The chain is generated over the whole telescope and the supplied positions
-- are then substituted out**, not generated over the tail: a later equation is
-- stated after transporting along the earlier ones, and an earlier position left
-- out of the walk is an earlier transport left out of the type.
goalFrom :: Chain -> [Core] -> [(Core, Core, Core)] -> Context -> Int -> (Core, Int)
goalFrom ch shared supplied remaining n =
  let dl           = chainLevel ch
      givenEntries = [ Hypothesis v i t | (v, i, t) <- suppliedEntries ]
      -- **The left side keeps the telescope's own names and the right side is
      -- primed**, so a generated lemma reads @∀ (n : N) (x : Ev n) (n' : N)
      -- (x' : Ev n') -> …@. Freshening both would name them @n'@ and @n'1@.
      (lsCtx, n1)  = freshenAs id n remaining
      (rsCtx, n2)  = freshen n1 remaining
      lsCtx'       = retypeIn theta (shared ++ suppliedLefts)  lsCtx
      rsCtx'       = retypeIn theta (shared ++ suppliedRights) rsCtx
      lefts        = shared ++ suppliedLefts  ++ varsOf lsCtx'
      rights       = shared ++ suppliedRights ++ varsOf rsCtx'
      (hs, n3)     = stations dl (givenEntries ++ lsCtx')
                       (suppliedRights ++ varsOf rsCtx') n2
      given        = [ (statedProof h, pr) | (h, (_, _, pr)) <- zip hs supplied ]
      bound        = drop (length supplied) hs
   in ( piOver lsCtx' (piOver rsCtx'
          (rewriting given (chained dl bound (chainGoal ch lefts rights))))
      , n3
      )
  where
    theta          = chainTelescope ch
    suppliedLefts  = [ l | (l, _, _) <- supplied ]
    suppliedRights = [ r | (_, r, _) <- supplied ]
    -- A supplied position's left side is a variable the caller bound, so it can
    -- stand as the telescope entry 'stations' states its equation from.
    suppliedEntries =
      [ (v, i, t)
      | ((Free v, _, _), Hypothesis _ i t) <- zip supplied entries ]
    entries = retypeIn theta shared (take (length supplied) (drop (length shared) theta))

-- | The nested J itself. Each step binds the two sides of one position, the
-- rest of the telescope on both sides, and every equation of the chain; it
-- eliminates this position's equation and applies what comes back to the rest.
proofFrom :: Chain -> [Core] -> Context -> Int -> (Core, Int)
proofFrom ch shared remaining n = case remaining of
  []     -> chainDiagonal ch shared n
  e : es ->
    let dl          = chainLevel ch
        theta       = chainTelescope ch
        a0          = case retypeIn theta shared [e] of
                        (e' : _) -> entryType e'
                        []       -> entryType e
        (lsCtx, n1) = freshen n es
        (rsCtx, n2) = freshen n1 es
        (vl, n3)    = fresh n2
        (vr, n4)    = fresh n3
        lsCtx'      = retypeIn theta (shared ++ [Free vl]) lsCtx
        rsCtx'      = retypeIn theta (shared ++ [Free vr]) rsCtx
        (hs, n5)    = stations dl (Hypothesis vl (Ident "u") a0 : lsCtx')
                        (Free vr : varsOf rsCtx') n4
        (q0, rest)  = case hs of
                        (h : more) -> (statedProof h, more)
                        []         -> (vl, [])
        (mt, n6)    = stepMotive ch shared es a0 n5
        (mh, n7)    = stepMethod ch shared es a0 n6
        applied     = foldl App
                        (Eliminate (GlobalName "Eq") [dl] [a0] mt [mh]
                           [Free vl, Free vr] (Free q0))
                        (varsOf lsCtx' ++ varsOf rsCtx'
                           ++ map (Free . statedProof) rest)
     in ( Lam (Ident "u") a0 (close vl
            (lamOver lsCtx'
              (Lam (Ident "v") a0 (close vr
                (lamOver rsCtx' (lamsOver dl hs applied))))))
        , n7
        )

-- | @λ u v w . ‹the rest, with this position's equation supplied as w›@.
stepMotive :: Chain -> [Core] -> Context -> Core -> Int -> (Core, Int)
stepMotive ch shared es a0 n =
  let dl       = chainLevel ch
      (uv, n1) = fresh n
      (vv, n2) = fresh n1
      (wv, n3) = fresh n2
      (t,  n4) = goalFrom ch shared [(Free uv, Free vv, Free wv)] es n3
   in ( Lam (Ident "u") a0 (close uv
          (Lam (Ident "v") a0 (close vv
            (Lam (Ident "w") (eqAt dl a0 (Free uv) (Free vv)) (close wv t)))))
      , n4
      )

-- | @λ c . ‹the rest at one shared position more›@ — the only method J leaves,
-- and the step that makes the recursion finite.
stepMethod :: Chain -> [Core] -> Context -> Core -> Int -> (Core, Int)
stepMethod ch shared es a0 n =
  let (cv, n1) = fresh n
      (t,  n2) = proofFrom ch (shared ++ [Free cv]) es n1
   in (Lam (Ident "c") a0 (close cv t), n2)

-- | The entries' types, with the positions already decided replaced by the
-- terms that decided them.
--
-- **The positions are counted from the front of the telescope and nowhere
-- else.** An entry's type can only mention entries before it, so the terms that
-- have decided the first @length ts@ positions are the whole of what any later
-- entry needs substituting — and every caller here holds exactly that prefix.
retypeIn :: Context -> [Core] -> Context -> Context
retypeIn theta ts ctx = map rewriteEntry ctx
  where
    ss = zip (map entryVar (take (length ts) theta)) ts
    rewriteEntry e = case e of
      Hypothesis v i t   -> Hypothesis v i (rewriting ss t)
      Definition v i s t -> Definition v i (rewriting ss s) (rewriting ss t)

-- | One station with its three terms rewritten.
--
-- **This is how a chain stated over a telescope is read at terms that are not
-- its variables.** 'stations' takes its left sides from the telescope's own
-- binders, so a caller that needs the chain between two /applications/ builds it
-- generically and substitutes afterwards. The result is what the generated
-- relation reduces to when applied to those terms, because the relation's own
-- body is the generic chain under the same binders.
rewriteStated :: [(Var, Core)] -> Stated -> Stated
rewriteStated ss h = h
  { statedType  = rewriting ss (statedType h)
  , statedLeft  = rewriting ss (statedLeft h)
  , statedRight = rewriting ss (statedRight h)
  }

-- | The chain's own proof where the two sides coincide, one @refl@ per station,
-- curried.
--
-- **Each @refl@ is substituted into the stations after it as it is produced**,
-- which is what makes the later ones typecheck: the transport an equation was
-- stated after contracts once the proof it travels along is reflexivity. It is
-- the same move 'package' makes, in the curried shape.
curriedRefls :: Level -> [Stated] -> [Core]
curriedRefls dl = go []
  where
    go _  []       = []
    go ss (h : hs) =
      let p = rewriting ss (reflAt dl (statedType h) (statedLeft h))
       in p : go (ss ++ [(statedProof h, p)]) hs

-- | Bind each station's proof out of a package of them, with one constant-motive
-- elimination per station, and run @body@ underneath.
--
-- **The pair each station is held in is decided the way 'package' decides it**,
-- by asking whether the rest of the package mentions this station's proof, and
-- from the same @package@ call — so an unpacking cannot disagree with the
-- packing it is reading.
unpackChain :: Level -> [Stated] -> Core -> Core -> Core -> Int -> (Core, Int)
unpackChain dl hs goal pkg body n = case hs of
  []      -> (body, n)
  [h]     -> (rewriting [(statedProof h, pkg)] body, n)
  h : rest ->
    let eq          = eqAt dl (statedType h) (statedLeft h) (statedRight h)
        qv          = statedProof h
        restTy      = fst (package dl rest)
        dependent   = qv `elem` freeVars restTy
        binder      = Lam (Ident "q") eq (close qv restTy)
        pairTy      = if dependent then dpairAt dl eq binder else andAt dl eq restTy
        sndTy       = if dependent then App binder (Free qv) else restTy
        (rv, n1)    = fresh n
        (pv, n2)    = fresh n1
        (inner, n3) = unpackChain dl rest goal (Free rv) body n2
        mot         = Lam (Ident "p") pairTy (close pv goal)
        meth        = Lam (Ident "q") eq (close qv
                        (Lam (Ident "r") sndTy (close rv inner)))
        former      = if dependent then "DPair" else "And"
        args        = if dependent then [eq, binder] else [eq, restTy]
     in (Eliminate (GlobalName former) [dl, dl] args mot [meth] [] pkg, n3)

-- | Is the chain over this telescope flat — no station's left side mentioning
-- an entry that comes after its own?
--
-- **That is what a package of two entries or more looks like from outside.**
-- Where an entry reaches back into the chain /and/ a later entry reaches back to
-- it, 'stations' packages the two together, transports the package, and reads
-- each component back out by projection — so the earlier station's left side is
-- a projection out of a pair that holds the later entries.
--
-- **It is read off the real walk and not predicted from the telescope**, which
-- is the lesson of @.claude\/HAZARDS.md@, /a predicate over the input stands in
-- for a fact about the output/: @vcons@'s @as@ reaches back to @n@ and nothing
-- reaches back to @as@, so its package holds one entry and the chain is flat,
-- which no question about the telescope alone answers.
--
-- **What it gates is the nested J and nothing else** — see 'Chain'. A
-- projection's own type mentions the /bound/ proof variable of the equation the
-- package was transported along, so a step's motive and the type the step's
-- method actually has are not convertible: the motive carries that variable and
-- the method has eliminated it.
chainIsFlat :: Level -> Context -> Int -> Bool
chainIsFlat dl tel n0 =
  let (hs, _) = stations dl tel (varsOf tel) n0
   in all ok (zip [0 ..] hs)
  where
    ok (k, h) =
      not (any (`elem` freeVars (statedLeft h)) (map entryVar (drop (k + 1) tel)))

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

-- --------------------------------------------------------------------------
-- Small helpers
-- --------------------------------------------------------------------------

varsOf :: Context -> [Core]
varsOf = map (Free . entryVar)

-- | Does any entry of this telescope mention an earlier one?
--
-- **It is the question "will the chain over this telescope want a pair"**, and
-- both generators ask it. 'stations' packages an entry that a later entry
-- reaches back to together with everything after it, and 'packType' of two
-- entries or more is a @DPair@ — so a telescope with no dependency asks for
-- nothing beyond @Eq@, which is what lets @Eq@\'s own equipment be generated
-- before @DPair@ is declared.
mentionsAnEarlierEntry :: Context -> Bool
mentionsAnEarlierEntry es' = case es' of
  []       -> False
  (e : es) ->
    entryVar e `elem` concatMap (freeVars . entryType) es
      || mentionsAnEarlierEntry es

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
freshen = freshenAs (++ "'")

-- | 'freshen', with a say in what the copy's binders are called.
--
-- **The names are what a user reads off a generated lemma**, so the two
-- instantiations a chain quantifies want @x@ and @x'@ and not @x'@ and @x'1@ —
-- the second being what two 'freshen's of one telescope print as, the printer
-- disambiguating a repeated name by number. 'goalFrom' keeps the telescope's own
-- names on the left and primes the right.
freshenAs :: (String -> String) -> Int -> Context -> (Context, Int)
freshenAs rename n0 = go n0
  where
    go n []       = ([], n)
    go n (e : es) =
      let (v, n1)    = fresh n
          (rest, n2) = go n1 (map (repoint (entryVar e) v) es)
       in (copy v e : rest, n2)

    copy v e = case e of
      Hypothesis _ (Ident i) t   -> Hypothesis v (Ident (rename i)) t
      Definition _ (Ident i) s t -> Definition v (Ident (rename i)) s t

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
