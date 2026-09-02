-- | Elaboration — turning a surface term into a development (MS4 phase 41).
--
-- **Step 1 of a two-step, and his design** (2026-09-02): the elaborator is
-- written in Haskell behind one large instruction first, and then broken into
-- the clauses of a rule named @elaborate@. `PLAN-machine.md` §7.2's /large and
-- small instructions coexist/ is the licence, and "Thena.Tactics.Eliminate" is
-- the precedent. §12 invariant 5 is the argument: **writing it here is how step
-- 2 finds out which ops it wants**, rather than having them guessed into a
-- phase up front.
--
-- == It emits instructions; it does not do the work
--
-- Every case compiles to a short program of ops that **already exist**, and to
-- an @Elaborate@ of each sub-term — so the op recurses through itself and each
-- case stays a line or two. Three things follow, and the first is why the shape
-- was chosen:
--
--   * **step 2 is a decomposition, not a rewrite.** The rule clauses that
--     replace this will emit the same instructions from a body instead of from
--     Haskell. Nothing about /what runs/ changes.
--   * **it is observable**: @:step@ shows an elaboration as ordinary
--     instructions, which is the whole of what the machine is for.
--   * **it cannot cheat.** A case that wanted something the op vocabulary does
--     not have cannot quietly reach past it — it has to fail, and that failure
--     is the list step 2 works from.
--
-- == What is here, and what is not
--
-- Phase 41 compiles the **leaves**: a name, a universe, and the two
-- placeholders. Lambdas, Π, application, @let@, ascription and @elim@ are
-- phase 41b, and each of them needs something the vocabulary does not yet have
-- — see 'NoElaborationRule'.
module Thena.Elaborate
  ( compile
  ) where

import Thena.Core.Context (Context, entryIdent, entryVar)

import Thena.Core.Level (Level (..), freshLevelMeta, levelOfNat)
import Thena.Core.Term (Core (..), GlobalName (..), Ident (..), Var)
import qualified Data.List.NonEmpty as NE

import Thena.Development.Partial (Partial (..))
import Thena.Errors (FailReason (..), ResolveError (..), SyntaxError (..))
import Thena.Global.Env
  ( GlobalEnv
  , definitionLevels
  , lookupDefinition
  , inductiveConstructors
  , inductiveIndices
  , inductiveParameters
  , isDeclared
  , lookupInductive
  )
import Thena.Ops (Instr (..), Op (..), Operand (..), Value (..))
import Thena.Surface.Concrete
  (Plicity (..), Surface (..), SurfaceArg (..), SurfaceBinder (..))

-- | The program that elaborates one surface node into the focused hole.
--
-- Takes Γ at the focus and the name counter, exactly as the ops it emits do,
-- and hands back the counter it advanced — a universe whose level is left open
-- mints a meta.
--
-- **A node it cannot yet elaborate is a failure and not a silence.** That list
-- is phase 41b's specification.
-- | The names one compiled node binds, all carrying its own number.
--
-- **A fixed name is a bug and this is the fix** (MS4 phase 41e). A nested
-- @Elaborate@ runs in the /same/ body environment, so an inner node that binds
-- @here@ shadows the outer node's — and the outer @goto here@ then lands on the
-- inner component. @elaborate (\ A -> \ y -> y)@ failed exactly that way with
-- /"that names no hole or guess"/, from the moment @here@ was introduced.
--
-- The number comes from the machine's own counter, which only ever grows, so
-- two nodes can never share one. Each 'compile' consumes a tick for it — the
-- same thing 'Thena.Core.Term.fresh' does with the same counter.
data Names = Names
  { hereName, domName, codName, arrName, funName, argName
  , appName, refName, tyName, goalName, valName, elimName :: String }

namesFor :: Int -> Names
namesFor n =
  Names (w "here") (w "dom") (w "cod") (w "arr") (w "fun") (w "arg")
        (w "app") (w "ref") (w "ty") (w "goal") (w "val") (w "elim")
  where w x = x ++ show n

compile :: GlobalEnv -> Context -> Int -> Surface -> Either FailReason ([Instr], Int)
compile env ctx n0 s = case s of
  -- @E⟦x⟧ = FILL x; SOLVE@ — Brady's variable case, and the one clause of his
  -- elaborator that has run in this system since phase 17b. What was
  -- @elab-var@'s body is now these two instructions.
  --
  -- Local names first, then the globals: a binder shadows a global of the same
  -- name, which is what one namespace (§3.6) requires. The same order
  -- "Thena.Syntax.Resolve" uses, for the same reason.
  -- **A global's level arguments are inserted here** (MS4 phase 44). His
  -- ruling: /"obviously we have them implicitly inserted. That's the whole
  -- idea."/
  --
  -- One meta per prenex parameter, and unification decides them — which is
  -- typical ambiguity applied to a use site rather than to a written @Type@.
  -- Before this every global was written @g []@ and the whole prelude was out
  -- of elaboration's reach: @elaborate (Eq Nat zero zero)@ said /"Eq has 1
  -- level parameter, and was given 0 level arguments"/.
  --
  -- **A former and a constructor are definitions too** (§3.7 generates a
  -- wrapper for each), so one lookup answers for all three.
  SurfaceName x -> case resolveName x of
    Nothing        -> Left (CannotRead (ResolveFailed (NotInScope x)))
    Just (t, n')   -> fmap (bump n') (attach t)

  SurfaceUniverse k  -> attach (Universe (levelOfNat k))

  -- Typical ambiguity: the level is a meta and conversion decides it (phase
  -- 33). Writing @Typeₙ@ is always available and is the recovery.
  SurfaceUniverseOpen ->
    let (v, n1) = freshLevelMeta n
     in Right ([Do (Try (lit (Universe (LVar v)))), Do Solve], n1)

  -- @E⟦_⟧@ — **elaborate by not elaborating.** His words, 2026-09-01. Brady's
  -- @UNFOCUS@ exists because his focus /is/ the head of a hole queue and he has
  -- to move something off it; ours is a cursor, so leaving the hole alone is
  -- the whole of it. Unification is expected to find it, and if it does not,
  -- the hole is simply still there.
  SurfacePlaceholder -> Right ([], n)

  -- A **named** placeholder becomes a real hole, which is what the focused hole
  -- already is. Giving it the written name, and the clauses that ask the user
  -- or hand control over, are phase 44's.
  SurfaceHole _ -> Right ([], n)

  -- @E⟦e a⟧@ — Brady's application case with his own correction to the printed
  -- rule (the missing @FILL@ and @SOLVE@, @IDRIS.md@):
  --
  -- > CLAIM (A : Type); CLAIM (B : Type); CLAIM (f : A → B); CLAIM (s : A)
  -- > FILL (f s); FOCUS f; E⟦e⟧; FOCUS s; E⟦a⟧; SOLVE
  --
  -- **A spine is folded right to left**: @h a₁ … aₙ@ is @(h a₁ … aₙ₋₁) aₙ@, so
  -- one clause covers every arity and the head of the recursion is an ordinary
  -- 'Surface'. Brady's other rule, @E⟦x ⃗a⟧@, is the one that expands implicits
  -- and needs the whole list at once — phase 44's.
  --
  -- **@prim-apply@ is not involved.** It claims holes and yields only the
  -- spine, so a body cannot reach them; here each claim is emitted and named,
  -- and @goto@ reaches it. Brady's arrangement rather than ours.
  --
  -- **@FILL@ is written out rather than reached through @unify-refine-core@**,
  -- which is @elaboration-in-rules.md@'s **gap 4** — /"Brady needs @FILL@ and
  -- @SOLVE@ separated, with the two @FOCUS@es between them"/. Splitting the
  -- rule turns out not to be needed to get it: the pieces are all ops, so the
  -- filling half is emitted here and the @prim-solve@ after the arguments.
  SurfaceApp h as
    | SurfaceArg Implicit _ <- NE.last as ->
        Left (NoElaborationRule "an implicit argument")

    -- **Brady's OTHER application rule, @E⟦x ⃗a⟧@** (MS4 phase 44), taken
    -- whenever the head is a name — which is the case his has and the binary
    -- one cannot do.
    --
    -- The binary rule claims @f : A -> B@, an **arrow**, so @B@ cannot mention
    -- the argument; a dependent head like @Eq {ℓ} (A : Type ℓ) : A -> A -> …@
    -- then makes unification try to solve a hole with a term mentioning a
    -- binder out of its scope. @make-apply@ walks the head's real telescope
    -- instead, claiming each domain in the scope of the holes already claimed.
    --
    -- **The whole spine at once**, which is why phase 39's AST is a spine: the
    -- arguments are not folded here, they are handed over together.
    | SurfaceName x <- h, Just (hd, nh) <- resolveName x ->
        let args   = [ a | SurfaceArg _ a <- NE.toList as ]
            slot k = argName names ++ show (k :: Int)
         in fmap (bump nh) $ Right
              ( concat
                  [ [Bind (hereName names) Here]
                  , [ Bind (slot k) (FreshName (lit' ("a" ++ show k)))
                    | k <- [0 .. length args - 1]
                    ]
                  , [ Bind (appName names)
                        (MakeApply (lit hd)
                           [ Ref (slot k) | k <- [0 .. length args - 1] ])
                    ]
                    -- **The arguments are elaborated BEFORE the @FILL@**,
                    -- where the binary rule fills first. Brady's printed order
                    -- is @FILL x ⃗n@ then @⃗ELAB ARG@, and it cannot be kept:
                    -- unifying the spine's type with the goal /solves/ the
                    -- argument holes — @refl Nat zero@ at a concrete @Eq@ goal
                    -- determines both — and a solved hole is a definition, so
                    -- the @goto@ that followed found no hole. Same reason
                    -- @elim@ fills last (phase 41i).
                  , concat
                      [ [ Do (Goto (Ref (slot k)))
                        , Do (Elaborate (Lit (VSurface a)))
                        ]
                      | (k, a) <- zip [0 ..] args
                      ]
                  , [Do (Goto (Ref (hereName names)))]
                  , fill (Ref (appName names))
                  , [Do Solve]
                  ]
              , n
              )

    | otherwise ->
        let front = NE.init as
            fun   = case front of
                      [] -> h
                      _  -> SurfaceApp h (NE.fromList front)
            SurfaceArg _ arg = NE.last as
            (l1, n1) = freshLevelMeta n
            (l2, n2) = freshLevelMeta n1
            nm k w   = Bind k (FreshName (lit' w))
         in Right
              ( concat
                  [ [ Bind (hereName names) Here
                    , nm (domName names ++ "n") "A"
                    , Bind (domName names)
                        (Claim (Ref (domName names ++ "n")) (lit (Universe (LVar l1))))
                    , nm (codName names ++ "n") "B"
                    , Bind (codName names)
                        (Claim (Ref (codName names ++ "n")) (lit (Universe (LVar l2))))
                    , Bind (arrName names) (Arrow (Ref (domName names)) (Ref (codName names)))
                    , nm (funName names ++ "n") "f"
                    , Bind (funName names)
                        (Claim (Ref (funName names ++ "n")) (Ref (arrName names)))
                    , nm (argName names ++ "n") "s"
                    , Bind (argName names)
                        (Claim (Ref (argName names ++ "n")) (Ref (domName names)))
                    , Bind (appName names)
                        (ApplyTo (Ref (funName names)) (Ref (argName names)))
                    ]
                    -- @FILL@: park it in a definition, unify its type with the
                    -- goal's, attach it. Thesis §2.7's @=@-binding, and the
                    -- reason it is a definition rather than a direct @try@ is
                    -- that @f s@'s type is @B@, a hole, and not yet the goal's.
                  , fill (Ref (appName names))
                    -- The two @FOCUS@es, and only then the @SOLVE@.
                  , [ Do (Goto (Ref (funName names)))
                    , Do (Elaborate (Lit (VSurface fun)))
                    , Do (Goto (Ref (argName names)))
                    , Do (Elaborate (Lit (VSurface arg)))
                    , Do (Goto (Ref (hereName names)))
                    , Do Solve
                    ]
                  ]
              , n2
              )

  -- @E⟦\ x => e⟧ = ATTACK; LAMBDA x; E⟦e⟧; SOLVE@ — Brady's λ case, and the
  -- first structural one this elaborator can do (MS4 phase 41b).
  --
  -- **One @prim-intro@ per binder, and each is given the SURFACE name.** That
  -- is what @prim-intro@'s optional operand is for: without it the binder keeps
  -- the identifier written in the /type/, so @\ y -> y@ at a goal
  -- @∀ (x : A) -> A@ would bind @x@ and the body's @y@ would resolve to
  -- nothing.
  --
  -- **Then @into@, then one @along@ per binder** — the navigation the phase-26
  -- mockup established and tested. It is counting structure rather than holding
  -- a handle, which is @elaboration-in-rules.md@'s gap 1; it is exact here
  -- because this clause knows how many binders it introduced.
  --
  -- **And the moves are undone before @prim-solve@**, which is the invariant
  -- every later case will lean on: **an @Elaborate@ leaves the focus where it
  -- found it.** The leaves do it by not moving at all — @prim-try@ and
  -- @prim-solve@ rewrite the focused component in place — and this clause does
  -- it by balancing its own moves.
  SurfaceLam bs body ->
    let names' = [ x | SurfaceBinder _ x _ <- NE.toList bs ]
     in case [ () | SurfaceBinder p _ ty <- NE.toList bs
             , p == Implicit || ty /= Nothing ] of
          _ : _ -> Left (NoElaborationRule "a lambda binder with a type or braces")
          []    -> Right
            ( concat
                [ [Bind (hereName names) Here, Do Attack]
                , [ Do (Intro (Just (lit' x))) | x <- names' ]
                , [Do Into]
                , replicate (length names') (Do Along)
                , [Do (Elaborate (Lit (VSurface body)))]
                , [Do (Goto (Ref (hereName names))), Do Solve]
                ]
            , n
            )
  -- @E⟦(x : t) -> e⟧ = ATTACK; CLAIM (X : Type); PI (x : X); FOCUS X; E⟦t⟧;
  -- E⟦e⟧; SOLVE@ — Brady's Π case, on the fifth component (MS4 phase 41f).
  --
  -- **@quantify@ is @PI@, and it is the reason the component exists.** The
  -- codomain must be elaborated with @x@ in Γ, and writing a component is the
  -- only way anything gets into Γ; every component there was extracted as a
  -- /term/, so the chain could say @λ x : A . B@ and never @Π x : A . B@. The
  -- user's ruling, 2026-09-02, and his reason is that a declaration hits the
  -- same wall — Brady elaborates a signature as a development of its own
  -- (@IDRIS.md@ §4.6) before elaborating the body against it.
  --
  -- **A binder group binds one name** ("Thena.Surface.Concrete"), so a run of
  -- them is a run of @quantify@s under one @attack@, exactly as the λ case
  -- emits a run of @prim-intro@s.
  --
  -- The domain hole is claimed **outside** the @attack@ and elaborated
  -- **after** the binders are in place, which is Brady's order: the binder's
  -- type is the hole's /variable/, so it is in scope before it is solved.
  -- @E⟦(x : t) -> e⟧ = ATTACK; CLAIM (X : Type); PI (x : X);
  -- FOCUS X; E⟦t⟧; E⟦e⟧; SOLVE@ — Brady's Π case, on the fifth component
  -- (MS4 phase 41f).
  --
  -- **@quantify@ is @PI@, and it is the reason the component exists.** The
  -- codomain must be elaborated with @x@ in Γ, and writing a component is the
  -- only way anything gets into Γ; every component there was extracted as a
  -- /term/, so the chain could say @λ x : A . B@ and never @Π x : A . B@. The
  -- user's ruling, 2026-09-02, and his reason is that a declaration hits the
  -- same wall — Brady elaborates a signature as a development of its own
  -- (@IDRIS.md@ §4.6) before elaborating the body against it.
  --
  -- **One binder per clause; a group nests.** @∀ (A : Type₀) (a : A) -> B@ is
  -- @∀ (A : Type₀) -> ∀ (a : A) -> B@, and it has to be: the domain hole is
  -- claimed /outside/ the @attack@, where an earlier binder of the same group
  -- is not in scope. The λ case can emit a run of @prim-intro@s because each
  -- reads its type from the goal; this one is given the type and must place it.
  --
  -- **The domain is elaborated before the body**, which is Brady's order and
  -- not a preference. With the body first, its @FILL@ unifies the binder's
  -- type — the domain hole's variable — against the goal and /solves the
  -- domain hole/, so @∀ (A : Type₀) -> A@ at @Type₁@ silently made @A@'s type
  -- @Type₁@ and then could not find the hole its annotation was owed.
  SurfacePi bs body -> case NE.uncons bs of
    (b, Just rest) -> compile env ctx n0 (SurfacePi (b NE.:| []) (SurfacePi rest body))
    (SurfaceBinder Implicit _ _, Nothing) ->
      Left (NoElaborationRule "a ∀ binder in braces")
    (SurfaceBinder _ _ Nothing, Nothing) ->
      Left (NoElaborationRule "a ∀ binder with no type")
    (SurfaceBinder _ x (Just ty), Nothing) ->
      let (l, n1) = freshLevelMeta n
       in Right
            ( [ Bind (hereName names) Here
              , Bind (domName names ++ "n") (FreshName (lit' "A"))
              , Bind (domName names)
                  (Claim (Ref (domName names ++ "n")) (lit (Universe (LVar l))))
              , Do Attack
                -- @quantify@ acts at the guess, as @prim-intro@ does, so the
                -- descent comes after it — the λ case's @into@, @along@
                -- exactly.
              , Do (Quantify (lit' x) (Ref (domName names)))
              , Do Into
              , Do Along
                -- The codomain hole, held rather than counted — phase 41c's
                -- @here@ doing for a nested focus what it does for the outer.
              , Bind (codName names) Here
              , Do (Goto (Ref (domName names)))
              , Do (Elaborate (Lit (VSurface ty)))
              , Do (Goto (Ref (codName names)))
              , Do (Elaborate (Lit (VSurface body)))
              , Do (Goto (Ref (hereName names)))
              , Do Solve
              ]
            , n1
            )

  -- @E⟦A -> B⟧@ — the application case's shape with @arrow@ where it has
  -- @apply-to@, and **no new op at all**.
  --
  -- It is not the Π case with an anonymous binder: an arrow's codomain cannot
  -- mention the domain, so there is nothing to put in Γ and nothing to attack.
  -- Two claims, the term, and the same @FILL@ every other case ends with.
  SurfaceArrow a b ->
    let (l1, n1) = freshLevelMeta n
        (l2, n2) = freshLevelMeta n1
     in Right
          ( concat
              [ [ Bind (hereName names) Here
                , Bind (domName names ++ "n") (FreshName (lit' "A"))
                , Bind (domName names)
                    (Claim (Ref (domName names ++ "n")) (lit (Universe (LVar l1))))
                , Bind (codName names ++ "n") (FreshName (lit' "B"))
                , Bind (codName names)
                    (Claim (Ref (codName names ++ "n")) (lit (Universe (LVar l2))))
                , Bind (arrName names) (Arrow (Ref (domName names)) (Ref (codName names)))
                ]
              , fill (Ref (arrName names))
              , [ Do (Goto (Ref (domName names)))
                , Do (Elaborate (Lit (VSurface a)))
                , Do (Goto (Ref (codName names)))
                , Do (Elaborate (Lit (VSurface b)))
                , Do (Goto (Ref (hereName names)))
                , Do Solve
                ]
              ]
          , n2
          )

  -- @E⟦let x = v in e⟧ = ATTACK; CLAIM (X : Type); CLAIM (V : X);
  -- LET (x : X ↦→ V); FOCUS V; E⟦v⟧; E⟦e⟧; SOLVE@ — Brady's @let@ case, and
  -- **@define@ is his @LET@**.
  --
  -- @IDRIS.md@ records @define@ as /"close but infers the type"/, and that
  -- turns out to be the reason it fits rather than the reason it does not: the
  -- value handed to it is @V@'s /variable/, whose type is the claimed @X@, so
  -- inferring gives back exactly the type Brady writes down.
  --
  -- **No @attack@ and no @solve@**, where Brady has both. His @LET@ acts on the
  -- goal; ours writes a component /above/ the focus, so the body elaborates
  -- into the hole this clause was called at and the clause is three
  -- instructions shorter. The definition is in Γ by then, so the body's @x@
  -- resolves to it.
  --
  -- **The definition carries the name the user wrote**, which is what made
  -- phase 24c's taken-name check untenable — see "Thena.Engine"'s @claim@.
  SurfaceLet x ann v body ->
    let (l, n1) = freshLevelMeta n
     in Right
          ( concat
              [ [ Bind (hereName names) Here
                , Bind (tyName names ++ "n") (FreshName (lit' "X"))
                , Bind (tyName names)
                    (Claim (Ref (tyName names ++ "n")) (lit (Universe (LVar l))))
                , Bind (valName names ++ "n") (FreshName (lit' "V"))
                , Bind (valName names)
                    (Claim (Ref (valName names ++ "n")) (Ref (tyName names)))
                ]
                -- An annotation elaborates into @X@; without one @X@ is left
                -- for the value's own @FILL@ to unify against.
              , [ i | Just ty <- [ann]
                    , i <- [ Do (Goto (Ref (tyName names)))
                           , Do (Elaborate (Lit (VSurface ty)))
                           ]
                ]
              , [ Do (Goto (Ref (valName names)))
                , Do (Elaborate (Lit (VSurface v)))
                , Do (Goto (Ref (hereName names)))
                , Do (Define (lit' x) (Ref (valName names)))
                , Do (Elaborate (Lit (VSurface body)))
                ]
              ]
          , n1
          )

  -- @E⟦e : T⟧@ — Brady gives no rule for ascription, and it needs no new op.
  --
  -- Claim @X : Type@, elaborate @T@ into it, and **unify @X@ with the goal**:
  -- that is the whole of what an ascription says, since @X@ is a solved hole
  -- by then and δ unfolds it ("Thena.Core.Reduce"). Then elaborate @e@ at the
  -- same hole, whose type the unification has just constrained.
  --
  -- No second hole for @e@ and no @FILL@ of its own — the ascription does not
  -- build a term, it narrows the one the goal was already asking for.
  SurfaceAnnot e ty ->
    let (l, n1) = freshLevelMeta n
     in Right
          ( [ Bind (hereName names) Here
            , Bind (tyName names ++ "n") (FreshName (lit' "X"))
            , Bind (tyName names)
                (Claim (Ref (tyName names ++ "n")) (lit (Universe (LVar l))))
            , Do (Goto (Ref (tyName names)))
            , Do (Elaborate (Lit (VSurface ty)))
            , Do (Goto (Ref (hereName names)))
            , Bind (goalName names) Goal
              -- **@unify-into@ and not @unify@** (MS4 phase 41g). Brady's @FILL@
        -- /"UNIFYs its type with the goal's"/, and in a cumulative system that
        -- is too strong: the term's type need only be /usable/ where the goal
        -- is wanted. @prim-try@ on the next line does the real check and
        -- subsumes, so what is asked here is solving, not deciding.
      , Do (UnifyInto (Ref (tyName names)) (Ref (goalName names)))
            , Do (Elaborate (Lit (VSurface e)))
            ]
          , n1
          )

  -- @E⟦elim d ⃗p P ⃗m ⃗i t⟧@ — the last case, and Brady has no rule for it
  -- because IDRIS− has pattern matching where the surface language has
  -- eliminators (his: /"yes, for now we use eliminators in the surface too"/).
  --
  -- **It is the application case with @make-elim@ where that has @apply-to@.**
  -- The eliminator has no global name to apply — §3.7 generates nothing for it
  -- — but 'Thena.Global.Env.eliminatorType' builds its Π telescope on demand,
  -- in @Eliminate@'s own field order, so claiming a hole per domain is the
  -- same walk @prim-apply@ does and the op does it.
  --
  -- **The names are minted here and handed down.** That is what makes the
  -- holes reachable afterwards — his decision, 2026-09-02, closing
  -- @elaboration-in-rules.md@'s complaint that @prim-apply@ /"claims holes and
  -- yields only the spine, so a body cannot reach them"/. Phase 41f is what
  -- made it sound: @claim@ takes a name as given.
  --
  -- **The arity is checked here, against the declaration**, so the message
  -- names the field group the user got wrong rather than a total. The op
  -- checks the total as well, because a rule body can call it directly.
  SurfaceElim d ps mot ms is tgt -> case lookupInductive (GlobalName d) env of
    Nothing  -> Left (CannotRead (ResolveFailed (NotADatatype d)))
    Just def
      | length ps /= wantP -> arity (WrongNumberOfEliminationParameters d wantP (length ps))
      | length ms /= wantM -> arity (WrongNumberOfMethods d wantM (length ms))
      | length is /= wantI -> arity (WrongNumberOfEliminationIndices d wantI (length is))
      | otherwise ->
          let fields  = ps ++ [mot] ++ ms ++ is ++ [tgt]
              slot k  = elimName names ++ show (k :: Int)
              hint k  = lit' ("e" ++ show k)
           in Right
                ( concat
                    [ [Bind (hereName names) Here]
                    , [ Bind (slot k) (FreshName (hint k))
                      | k <- [0 .. length fields - 1]
                      ]
                    , [ Bind (elimName names)
                          (MakeElim (GlobalName d)
                             [ Ref (slot k) | k <- [0 .. length fields - 1] ])
                      ]
                      -- **The fields are elaborated BEFORE the @FILL@**, where
                      -- the application case fills first. The difference is
                      -- what the node's type is: @f s@ has type @B@, a bare
                      -- hole that unification solves, but an elimination has
                      -- type @P ⃗i t@ — the motive applied — which is a spine
                      -- with a flexible head and no pattern, so it parks and
                      -- @prim-try@ then has nothing to check against. With the
                      -- motive and the target elaborated first it is a type.
                    , concat
                        [ [ Do (Goto (Ref (slot k)))
                          , Do (Elaborate (Lit (VSurface f)))
                          ]
                        | (k, f) <- zip [0 ..] fields
                        ]
                    , [Do (Goto (Ref (hereName names)))]
                    , fill (Ref (elimName names))
                    , [Do Solve]
                    ]
                , n
                )
      where
        wantP = length (inductiveParameters def)
        wantM = length (inductiveConstructors def)
        wantI = length (inductiveIndices def)
        arity = Left . CannotRead . ResolveFailed

  where
    -- Each node takes one tick of the counter for the names it binds.
    n     = n0 + 1
    names = namesFor n0

    -- @E⟦x⟧ = FILL x; SOLVE@ — and **@FILL@ is not @try@**.
    --
    -- @try@ /checks/ the term against the goal, so it needs the two types to
    -- match already; Brady's @FILL@ *"UNIFYs its type with the goal's"*. That
    -- is the difference between a leaf at a concrete goal — which is all
    -- @elab-var@ ever met — and one at a goal that is still a hole, which is
    -- exactly what the application case claims for its function and argument.
    -- So every leaf goes through the same filling sequence the application
    -- case does.
    attach t = Right (fill (lit t) ++ [Do Solve], n)

    -- Thesis §2.7's @=@-binding: park the term in a definition, unify the type
    -- it has with the type the hole wants, and only then attach it. What
    -- @unify-refine-core@'s body does, emitted rather than called, so that the
    -- application case can put its two @FOCUS@es before the @prim-solve@
    -- (@elaboration-in-rules.md@'s gap 4).
    fill t =
      [ Bind (refName names ++ "n") (FreshName (lit' "refined"))
      , Bind (refName names) (Define (Ref (refName names ++ "n")) t)
      , Bind (tyName names) (Typing (Ref (refName names)))
      , Bind (goalName names) Goal
        -- **@unify-into@ and not @unify@** (MS4 phase 41g). Brady's @FILL@
        -- /"UNIFYs its type with the goal's"/, and in a cumulative system that
        -- is too strong: the term's type need only be /usable/ where the goal
        -- is wanted. @prim-try@ on the next line does the real check and
        -- subsumes, so what is asked here is solving, not deciding.
      , Do (UnifyInto (Ref (tyName names)) (Ref (goalName names)))
      , Do (Try (Ref (refName names)))
      ]
    lit' x   = Lit (VText x)

    -- **What a name denotes, with its level arguments inserted** (MS4 phase
    -- 44). Shared by the leaf case and the global-head application case, so
    -- the two cannot come to disagree about what a name means.
    --
    -- Locals first, then the globals: a binder shadows a global of the same
    -- name, which is what one namespace (§3.6) requires — the same order
    -- "Thena.Syntax.Resolve" uses.
    resolveName x = case inContext x of
      Just v  -> Just (Free v, n)
      Nothing -> case lookupDefinition (GlobalName x) env of
        Just d ->
          let (ls, n') = levelArgs (length (definitionLevels d)) n
           in Just (Global (GlobalName x) ls, n')
        Nothing
          | isDeclared (GlobalName x) env -> Just (Global (GlobalName x) [], n)
          | otherwise                     -> Nothing

    -- One fresh level meta per prenex parameter of the global being used.
    levelArgs k n' = case k of
      0 -> ([], n')
      _ -> let (l, n1)  = freshLevelMeta n'
               (ls, n2) = levelArgs (k - 1) n1
            in (LVar l : ls, n2)

    -- 'attach' hands back the counter this clause started from; a name that
    -- minted level metas has moved it on.
    bump n' (is, _) = (is, n')


    -- The innermost binding of that name, if the context has one. The same
    -- reading "Thena.Syntax.Resolve" gives it, kept here rather than shared:
    -- that module is about @Raw@, and the two languages must not acquire a
    -- function in common.
    inContext :: String -> Maybe Var
    inContext x = foldl pick Nothing ctx
      where
        pick acc e
          | entryIdent e == Ident x = Just (entryVar e)
          | otherwise               = acc
    lit t    = Lit (VTerm (Trailing t))
