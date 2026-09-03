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

import Thena.Core.Level (Level (..), freshLevelMeta)
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
  (Plicity (..), Surface (..), SurfaceArg (..))
import Thena.Surface.Zipper
  ( SurfaceZipper, focus
  , intoArg
  , intoElimField
  )

-- | The program that elaborates one surface node into the focused hole.
--
-- Takes Γ at the focus and the name counter, exactly as the ops it emits do,
-- and hands back the counter it advanced — a universe whose level is left open
-- mints a meta.
--
-- **A node it cannot yet elaborate is a failure and not a silence.** That list
-- is phase 41b's specification.
-- | What a case that has moved gets if it reaches @prim-elaborate@ anyway.
--
-- Nothing routes one here: every clause of @elaborate@ names the node it is
-- for, so a node's own clause is the only head that matches it. Reaching this
-- op means the rule base has lost that clause, or a body wrote
-- @prim-elaborate@ by hand.
-- | What the name-headed application case answers when the plicities do not
-- fit: the binary clause is next in the rule base and takes it.
binaryIsAClause :: FailReason
binaryIsAClause =
  NoElaborationRule "an application whose head's plicities do not fit"

movedToTheRuleBase :: FailReason
movedToTheRuleBase =
  NoElaborationRule "a surface node whose clause is in the rule base, not in \
                    \this op"

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
  { hereName, argName, appName, refName, tyName, goalName, elimName :: String }

namesFor :: Int -> Names
namesFor n =
  Names (w "here") (w "arg") (w "app") (w "ref") (w "ty") (w "goal") (w "elim")
  where w x = x ++ show n

compile
  :: GlobalEnv -> [(GlobalName, [Plicity])] -> Context -> Int -> SurfaceZipper
  -> Either FailReason ([Instr], Int)
compile env sigs ctx n0 z = case focus z of
  -- **@E⟦do { … }⟧ = play the block@** (MS4 phase 45). The whole of it: a block
  -- is written down, so there is nothing to elaborate — it is already the
  -- machine's own language, and the instruction that plays it is the
  -- elaboration.
  --
  -- **Resolved here, not in the grammar.** Which word names an op and which
  -- names a rule is "Thena.Rules"' question (phase 25e), and answering it in a
  -- parser would write the op vocabulary in a second place.
  --
  -- **It leaves the focus wherever the block left it**, which is the one way it
  -- differs from every other case: those restore the focus by construction
  -- (phase 41b's invariant), and a block does what the user wrote. That is the
  -- second principle — the block may do something strange, and repairing it is
  -- the user's.
  SurfaceName _       -> Left movedToTheRuleBase
  SurfaceUniverse _   -> Left movedToTheRuleBase
  SurfaceUniverseOpen -> Left movedToTheRuleBase
  SurfacePlaceholder  -> Left movedToTheRuleBase
  SurfaceHole _       -> Left movedToTheRuleBase
  SurfaceArrow _ _    -> Left movedToTheRuleBase
  SurfaceAnnot _ _    -> Left movedToTheRuleBase
  SurfaceLet {}       -> Left movedToTheRuleBase
  SurfacePi _ _       -> Left movedToTheRuleBase
  SurfaceDo _         -> Left movedToTheRuleBase
  SurfaceLam _ _      -> Left movedToTheRuleBase

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
    -- **@EXPAND@ is here** (MS4 phase 44b): the written arguments are matched
    -- against the head's plicities and a slot is opened for every implicit
    -- position the user did not write. An inserted slot is claimed like any
    -- other and simply not elaborated into — unification is what finds its
    -- value, which is Brady's /"it is unification which finds values of
    -- implicit arguments"/.
    --
    -- **A written @{a}@ fills an implicit slot** rather than being refused, so
    -- an argument the elaborator would have supplied can always be given by
    -- hand — his requirement: /"They are allowed to be written explicitly
    -- too."/
    | SurfaceName x <- h, Just (hd, nh) <- resolveName x
    , Just slots <- expand (plicitiesOf x) (zip [0 ..] (NE.toList as)) ->
        let slot k = argName names ++ show (k :: Int)
         in fmap (bump nh) $ Right
              ( concat
                  [ [Bind (hereName names) Here]
                  , [ Bind (slot k) (FreshName (lit' ("a" ++ show k)))
                    | k <- [0 .. length slots - 1]
                    ]
                  , [ Bind (appName names)
                        (MakeApply (lit hd)
                           [ Ref (slot k) | k <- [0 .. length slots - 1] ])
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
                        , Do (elaborating (Lit (VSurface (intoArg h as j a z))))
                        ]
                      | (k, Just (j, a)) <- zip [0 ..] slots
                      ]
                  , [Do (Goto (Ref (hereName names)))]
                  , fill (Ref (appName names))
                  , [Do Solve]
                  ]
              , n
              )
    -- **A brace that could not be placed is refused, not ignored.** The binary
    -- clause has no notion of plicity at all, so falling through to it would
    -- report a type mismatch about a term the user never meant to write
    -- explicitly.
    | any implicitArg (NE.toList as) ->
        Left (NoElaborationRule "an implicit argument this head has no position for")

    -- **Anything else belongs to the binary clause**, which is a rule as of MS4
    -- phase 49d. What is left in this op is only the half that needs @expand@ —
    -- matching written arguments against the head\'s plicities, which is a
    -- computation over two lists that a rule cannot do (@ms4/CLOSEOUT.md@ 28).
    -- Failing here is what sends a head whose arguments do not line up on to
    -- the clause below it, exactly as the @case@ fell through before.
    | otherwise -> Left binaryIsAClause

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
                          , Do (elaborating
                                 (Lit (VSurface
                                        (intoElimField d ps mot ms is tgt k f z))))
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

    -- **A sub-term goes through the RULE, not through this op** (MS4 phase 49).
    -- While elaboration lived entirely in Haskell the recursion was
    -- @prim-elaborate@ calling itself; now each surface node is a clause of
    -- @elaborate@ and a sub-term has to be dispatched over them.
    --
    -- **That is what makes the decomposition incremental**: a case moved into
    -- the rule base is reached from here without this module changing again,
    -- and when the last one moves this module goes.
    elaborating o = Call (GlobalName "elaborate") [o]

    -- What the machine recorded about this name's argument positions, if it
    -- recorded anything. A name with no entry — every DC-declared global, and
    -- every local — takes what was written and nothing more.
    plicitiesOf x = case lookup (GlobalName x) sigs of
      Just ps -> ps
      Nothing -> []

    -- | Brady's @EXPAND@: line the written arguments up against the plicities.
    --
    -- @Just a@ is a slot to elaborate into, @Nothing@ one the elaborator
    -- opened and left for unification. It fails — @Nothing@ overall — when the
    -- written arguments cannot be lined up at all, and the binary rule below
    -- then has its turn.
    -- **A slot that the user wrote carries the argument and its position in
    -- the spine** (MS4 phase 46), where it used to carry the argument alone.
    -- The position is what the zipper needs — @intoArg@ descends to a place in
    -- the spine rather than to a detached subterm — and carrying the argument
    -- beside it keeps the descent total, with no indexing at the call site.
    expand ps as' = case (ps, as') of
      ([], [])                            -> Just []
      -- Nothing recorded, or more arguments than positions: take them as
      -- written. A partially applied head is ordinary, and so is a head whose
      -- result is itself a function.
      ([], rest)
        | all (written . snd) rest        -> Just [ Just (i, a) | (i, SurfaceArg _ a) <- rest ]
        | otherwise                       -> Nothing
      -- An implicit position the user did write, in braces.
      (Implicit : more, (i, SurfaceArg Implicit a) : rest) ->
        (Just (i, a) :) <$> expand more rest
      -- An implicit position the user did not: insert it.
      (Implicit : more, rest)             -> (Nothing :) <$> expand more rest
      (Explicit : more, (i, SurfaceArg Explicit a) : rest) ->
        (Just (i :: Int, a :: Surface) :) <$> expand more rest
      -- An explicit position written in braces, or one not written at all.
      (Explicit : _, _)                   -> Nothing

    written (SurfaceArg Explicit _) = True
    written _                       = False

    implicitArg (SurfaceArg Implicit _) = True
    implicitArg _                       = False

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
