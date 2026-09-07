-- | The global environment: what a session has declared (§3.3.1, §3.7).
--
-- **Data only, and deliberately so.** This module sits below
-- "Thena.Core.Reduce" because δ unfolds a 'Global' and ι reads an
-- 'InductiveDefinition', while /checking/ a declaration needs level inference,
-- which needs @Typing@, which needs @Reduce@. Putting one check in here
-- reintroduces that cycle and it will not be obvious why (§2.5). The checks and
-- the generation live in "Thena.Global.Declare", above @Typing@.
--
-- The global environment does not backtrack (§7.4): it is a field of
-- 'Thena.Engine.Machine' beside 'Thena.Engine.Development' rather than inside
-- it, so a datatype declared in a branch that later fails survives.
module Thena.Global.Env
  ( -- * Kinds of global binding (§3.3.1)
    Definition (..)

    -- * Inductive definitions (§3.7)
  , InductiveDefinition (..)
  , ConstructorDefinition (..)

    -- * The environment
  , GlobalEnv (..)
  , emptyGlobals
  , Constant (..)
  , lookupConstant
  , lookupDefinition
  , lookupInductive
  , isDeclared
  , declaredNames
  , addConstant
  , generalised
  , substLevelsInInductive
  , levelMetasInInductive
  , addDefinition
  , addInductive

    -- * The types a declaration stands for
  , formerType
  , constructorType
  , constructorTarget
  , formerArity
  , recursiveArgument
  , eliminatorType
  , eliminatorWrapper
  , eliminatorName
  , varsInEnv
  ) where

import Data.List (nub)

import Thena.Core.Level
  ( Level (..)
  , LevelVar
  , Unmet
  , minimise
  , Obligation
  , freshLevelRigid
  , metasIn
  , substLevel
  , substObligation
  )
import Thena.Core.Context
  (Context, Entry (..), entryType, entryVar, lamOver, piOver, substLevelsInEntry)
import Thena.Core.Term
  ( Core (..)
  , Var
  , GlobalName (..)
  , Ident (..)
  , close
  , fresh
  , levelMetasIn
  , substLevelsIn
  )

-- | A global with a body — the @definition@ kind of §3.3.1's table: proved
-- theorems, the generated former wrappers, the prelude. δ-reducible.
--
-- The constructor is @MkDefinition@ because 'Thena.Core.Context.Entry' already
-- has a data constructor called @Definition@ and the two would be ambiguous
-- wherever both modules are in scope. Same technique as @MkScope@.
-- | A type and no body — a datatype's former, and each of its constructors.
--
-- **It carries level parameters for the same reason 'Definition' does** (MS3
-- phase 31b): a polymorphic datatype's former is polymorphic, and so is every
-- constructor of it. They are always exactly the datatype's own parameters,
-- and they are stored rather than looked up through 'inductives' because
-- 'addConstant' has them in hand and the tables are denormalised already — a
-- former appears in @constants@ and @definitions@ both.
data Constant = MkConstant
  { constantLevels :: [LevelVar]
  , constantType   :: Core
  }
  deriving (Eq, Show)

data Definition = MkDefinition
  { definitionLevels :: [LevelVar]
    -- ^ the prenex level parameters, in the order a use site supplies them
    -- (MS3 phase 30). **Empty for everything a monomorphic declaration
    -- generates**, and non-empty only for a theorem stated with @{ℓ}@.
    --
    -- The binder lives here and nowhere else: prenex means all the
    -- quantifiers are at the definition's head, so a flat list is the whole of
    -- the binding structure and 'Thena.Core.Level.Level' needs no binder of
    -- its own. Instantiating is 'Thena.Core.Level.instantiateLevels' followed
    -- by a substitution.
    --
    -- **Filled by generalisation from phase 33b**, not written: a theorem's
    -- levels are inferred, and 'generalised' is what turns the metas its proof
    -- was left holding into these.
  , definitionConstraints :: [Obligation]
    -- ^ the @≤@ relations between its own level parameters that must hold at
    -- every use (MS3 phase 33b).
    --
    -- **Storing these is required for soundness, not merely for earliness** —
    -- @discussion\/level-binders-and-constraints.md@ §4. Re-collection walks the
    -- /finished term/, and a caller's term holds @Global foo [5, 0]@ opaquely,
    -- so the body's obligations are never regenerated unless every definition
    -- is δ-unfolded. Without this list a call site has nothing to read, and a
    -- constraint arising inside a body is invisible in that body's /type/.
    --
    -- **It does not reopen §4's "re-collect, do not store".** Nothing is pooled
    -- during a proof: this field never changes after generalisation, and what
    -- a use site owes is reconstituted from it plus the level arguments in the
    -- term. And it does not recurse — this list is already the full residue of
    -- this definition's own generalisation.
    --
    -- **It is usually empty**, because a rigid gets the /validity/ reading:
    -- @ℓ ≤ suc ℓ@ discharges and @suc ℓ ≤ ℓ@ is refused outright, so only a
    -- genuine relation between independent parameters survives.
  , definitionType :: Core
  , definitionBody :: Core
  }
  deriving (Eq, Show)

-- | Build a definition by generalising the level metas its type and body are
-- still carrying (MS3 phase 33b).
--
-- **This is R2 of @discussion\/level-binders-and-constraints.md@ §2 done: a
-- rewrite.** Each surviving 'Thena.Core.Level.LMeta' becomes a fresh
-- 'Thena.Core.Level.LRigid' — /fresh/, and not the same @Int@ under a new
-- constructor, because MS2 closeout 4f is that one counter serves every sort
-- precisely so a number the user has seen as @?ℓ7@ is never reissued as
-- something else.
--
-- **The order is first appearance in the type, then in the body**, because a
-- use site supplies level arguments positionally and the type is what a use
-- site reads.
--
-- The residue is generalised along with them, and becomes the scheme's
-- constraints. It is not filtered: a relation between two of the new parameters
-- is exactly what a scheme constraint is /for/, and asking 'levelLeq' to decide
-- it here would refuse the useful case — a rigid is not bounded by another
-- rigid, which is the whole reason the constraint has to travel to the use.
generalised
  :: Int -> [Obligation] -> Core -> Core -> Either Unmet (Definition, Int)
generalised n residue ty body = do
    -- **Default the ambiguous ones first, then generalise what is left**
    -- (phase 51). The order is the whole of it: a meta the type does not
    -- mention cannot be determined by a use — unification only ever sees the
    -- type — so making it a parameter asks every caller to write something that
    -- says nothing. 'Thena.Core.Level.minimise' gives it its least value
    -- instead, and refuses when there is no least one.
    (defaults, kept) <- minimise ambiguous residue
    let ty1   = substLevelsIn defaults ty
        body1 = substLevelsIn defaults body
        -- Recomputed after the defaulting rather than reused: solving may have
        -- discharged a meta the type mentioned too.
        metas = levelMetasIn ty1
                  ++ [ v | v <- levelMetasIn body1, v `notElem` levelMetasIn ty1 ]
        (binding, n') = mint n metas
        sub   = [ (v, LVar w) | (v, w) <- binding ]
    Right
      ( MkDefinition (map snd binding) (map (substObligation sub) kept)
          (substLevelsIn sub ty1) (substLevelsIn sub body1)
      , n'
      )
  where
    ambiguous =
      [ v | v <- levelMetasIn body, v `notElem` levelMetasIn ty ]

    mint k []       = ([], k)
    mint k (v : vs) = let (w, k1)  = freshLevelRigid k
                          (ws, k2) = mint k1 vs
                       in ((v, w) : ws, k2)

-- | One inductive definition — a single record, as §3.7 requires.
--
-- **Parameters and indices are disambiguated here**, not recovered from the
-- shape of a term: parameters are fixed for the whole definition and are not
-- abstracted in the eliminator's scheme, while indices are (thesis §4.1.2).
--
-- Both telescopes are 'Context'es, which is what they are: a list of named,
-- typed bindings where a later type may mention an earlier binding as a
-- 'Thena.Core.Term.Free'. That reuse is not a shortcut — @whnf@, @infer@,
-- @check@ and @certify@ all take a 'Context' (§7.4), so a telescope needs no
-- conversion to be used, and no second binding discipline has to be kept in
-- step with the one §3.6 already has.
--
-- Field names are prefixed because 'Thena.Core.Term.Core' already has
-- @parameters@ and @indices@ as selectors of 'Thena.Core.Term.Eliminate'.
data InductiveDefinition = InductiveDefinition
  { inductiveName         :: GlobalName
  , inductiveLevels       :: [LevelVar]
    -- ^ prenex level parameters (MS3 phase 31b). Every constructor and the
    -- former share them; a use site supplies one level per parameter
  , inductiveParameters   :: Context   -- ^ in scope in the indices and in every constructor
  , inductiveIndices      :: Context   -- ^ in scope in neither; each constructor supplies its own
  , inductiveLevel        :: Level
    -- ^ the declared result universe. **No longer concrete** (§3.7 said it
    -- was): it may mention 'inductiveLevels'
  , inductiveConstructors :: [ConstructorDefinition]
  }
  deriving (Eq, Show)

-- | One value constructor.
--
-- 'constructorArguments' is a telescope over the datatype's parameters;
-- 'constructorIndices' are the index expressions of its target, one per entry
-- of 'inductiveIndices', over the parameters and the arguments both. So
-- @cons@'s target @Vec A (succ n)@ is stored as @[succ n]@ and the @A@ is not
-- stored at all — a constructor must pass the parameters through unchanged, and
-- "Thena.Global.Declare" checks that it does.
--
-- **Which arguments are recursive is not stored.** It is read off the argument
-- types, whose head is the datatype exactly when the argument is recursive.
-- Storing it as well would be a second encoding of what the record already
-- holds, and two encodings can disagree (§3.7, decided 2026-08-11 for the same
-- reason ι-rules are not emitted).
data ConstructorDefinition = ConstructorDefinition
  { constructorName      :: GlobalName
  , constructorArguments :: Context
  , constructorIndices   :: [Core]
  }
  deriving (Eq, Show)

-- | Apply a level substitution to a whole declaration (MS3 phase 33c).
--
-- Levels live in five places here — the declared universe, the parameters' and
-- indices' types, each constructor's argument types, and each constructor's
-- index expressions — and this is the list. Everything else in the record is a
-- name or a count.
--
-- What computing a bare @Type@'s level and generalising a declaration both need.
substLevelsInInductive
  :: [(LevelVar, Level)] -> InductiveDefinition -> InductiveDefinition
substLevelsInInductive sub d = d
  { inductiveParameters   = map at (inductiveParameters d)
  , inductiveIndices      = map at (inductiveIndices d)
  , inductiveLevel        = substLevel sub (inductiveLevel d)
  , inductiveConstructors = map constructor (inductiveConstructors d)
  }
  where
    at = substLevelsInEntry sub

    constructor c = c
      { constructorArguments = map at (constructorArguments c)
      , constructorIndices   = map (substLevelsIn sub) (constructorIndices c)
      }

-- | Every level meta a declaration mentions, without duplicates, in the order a
-- reader meets them: the parameters, the indices, the declared universe, then
-- the constructors.
levelMetasInInductive :: InductiveDefinition -> [LevelVar]
levelMetasInInductive d =
  nub (concatMap (levelMetasIn . entryType) (inductiveParameters d)
        ++ concatMap (levelMetasIn . entryType) (inductiveIndices d)
        ++ metasIn (inductiveLevel d)
        ++ concatMap constructor (inductiveConstructors d))
  where
    constructor c =
      concatMap (levelMetasIn . entryType) (constructorArguments c)
        ++ concatMap levelMetasIn (constructorIndices c)

-- | Three tables, because §3.3.1 gives two kinds of term-level binding and the
-- inductive records are not term-level bindings at all.
--
-- **A former appears in two of them under one name**: @succ@ is a constant
-- (the type of the saturated 'Thena.Core.Term.Canonical') and a definition (the
-- generated wrapper whose body is that 'Thena.Core.Term.Canonical'). They are
-- reached from different 'Thena.Core.Term.Core' nodes, which is exactly why
-- 'Thena.Core.Term.GlobalName' needs no tag (§3.6).
--
-- Association lists, newest first. There is no @Map@ here for the same reason
-- 'Thena.Ops.Env' and 'Context' are lists: speed is a stated non-goal (§1), and
-- a dependency is not worth adding for a table that holds a prelude.
data GlobalEnv = GlobalEnv
  { constants   :: [(GlobalName, Constant)]             -- ^ a type and no body
  , definitions :: [(GlobalName, Definition)]           -- ^ a type and a body
  , inductives  :: [(GlobalName, InductiveDefinition)]  -- ^ what the checker and ι consult
  }
  deriving (Eq, Show)

emptyGlobals :: GlobalEnv
emptyGlobals = GlobalEnv [] [] []

-- | The type of a saturated former or, from phase 10, of an eliminator.
lookupConstant :: GlobalName -> GlobalEnv -> Maybe Constant
lookupConstant g = lookup g . constants

-- | What a 'Thena.Core.Term.Global' names: the third form of δ (§3.6).
lookupDefinition :: GlobalName -> GlobalEnv -> Maybe Definition
lookupDefinition g = lookup g . definitions

-- | What ι and the eliminator generator read.
lookupInductive :: GlobalName -> GlobalEnv -> Maybe InductiveDefinition
lookupInductive g = lookup g . inductives

-- | Is the name taken, in any table?
--
-- One namespace, shared with generated names (§3.6): @noConfusionTerm@ is a
-- name the user could have written, and if they do, declaring the datatype that
-- would generate it is rejected rather than one of the two being hidden.
isDeclared :: GlobalName -> GlobalEnv -> Bool
isDeclared g e =
  g `elem` map fst (constants e)
    || g `elem` map fst (definitions e)
    || g `elem` map fst (inductives e)

-- | Every name the global environment binds (phase 24c).
--
-- @fresh-name@ avoids these as well as the development's own, so a generated
-- hole never shadows a datatype, a constructor or a proved theorem — something
-- a rule author cannot anticipate and a reader would find baffling.
declaredNames :: GlobalEnv -> [GlobalName]
declaredNames e =
  map fst (constants e) ++ map fst (definitions e) ++ map fst (inductives e)

addConstant :: GlobalName -> [LevelVar] -> Core -> GlobalEnv -> GlobalEnv
addConstant g ls t e = e { constants = (g, MkConstant ls t) : constants e }

addDefinition :: GlobalName -> Definition -> GlobalEnv -> GlobalEnv
addDefinition g d e = e { definitions = (g, d) : definitions e }

addInductive :: GlobalName -> InductiveDefinition -> GlobalEnv -> GlobalEnv
addInductive g d e = e { inductives = (g, d) : inductives e }

-- --------------------------------------------------------------------------
-- The types a declaration stands for
-- --------------------------------------------------------------------------
--
-- Derivation, not storage. These are what "Thena.Global.Declare" writes into
-- the tables and what "Thena.Repl" prints back, and they are here so that the
-- two cannot disagree about what the record means — the same argument that
-- keeps the ι-rules out of the record (§3.7).

-- | @∀ params indices -> Type_l@ — the type of the type former.
formerType :: InductiveDefinition -> Core
formerType d =
  piOver (inductiveParameters d ++ inductiveIndices d) (Universe (inductiveLevel d))

-- | @∀ params args -> D params indices@ — the type of a value constructor.
--
-- The parameters come first and are shared: a constructor abstracts them just
-- as the type former does, which is what makes @cons@ usable as an ordinary
-- function of four arguments.
constructorType :: InductiveDefinition -> ConstructorDefinition -> Core
constructorType d c =
  piOver
    (inductiveParameters d ++ constructorArguments c)
    (constructorTarget d c)

-- | @D params indices@ — a constructor's result type, rebuilt.
--
-- The parameters are passed through unchanged, which is why the record does not
-- store them a second time (§3.7).
constructorTarget :: InductiveDefinition -> ConstructorDefinition -> Core
constructorTarget d c =
  -- **At the datatype's own level parameters** (MS3 phase 31c). A constructor's
  -- target is the family it builds, and inside the declaration that family is
  -- the one being declared — so the reference carries exactly the parameters,
  -- and instantiating the constructor instantiates its target with it.
  foldl App (Global (inductiveName d) (map LVar (inductiveLevels d)))
    (map (Free . entryVar) (inductiveParameters d) ++ constructorIndices c)

-- | How many arguments a generated former wrapper takes before its body's
-- 'Thena.Core.Term.Canonical' is saturated — or 'Nothing' if this name is not
-- a former at all (an ordinary definition: a proved theorem, the prelude).
--
-- Derived from the record for the same reason 'formerType' and
-- 'constructorType' are: "Thena.Global.Declare" builds each wrapper by
-- abstracting exactly this telescope, so reading the count back off the same
-- fields is what stops generation and reduction disagreeing about a former's
-- arity (§3.7). Counting the @λ@s in the stored body would be a second
-- encoding of the same fact.
--
-- **What wants it: δ (§5.1).** Unfolding a wrapper that has not been given
-- enough arguments turns a compact neutral term into a lambda around a
-- 'Thena.Core.Term.Canonical' and exposes nothing a consumer can use — no ι
-- can fire on it, nothing can project from it. Decided by the user
-- 2026-08-22; "Thena.Core.Reduce" has the argument and the one obligation it
-- puts on phase 8's conversion.
--
-- A type former counts its parameters and its indices; a value constructor
-- counts the parameters (shared, and abstracted by every constructor) and its
-- own arguments. Nullary formers give @Just 0@, which is saturated
-- immediately — @Nat@ still unfolds to @Canonical "Nat" []@ on its own.
formerArity :: GlobalName -> GlobalEnv -> Maybe Int
formerArity g e = case lookup g (inductives e) of
  Just d  -> Just (length (inductiveParameters d) + length (inductiveIndices d))
  Nothing -> lookupConstructor
  where
    lookupConstructor =
      case [ (d, c)
           | (_, d) <- inductives e
           , c      <- inductiveConstructors d
           , constructorName c == g
           ] of
        (d, c) : _ ->
          Just (length (inductiveParameters d) + length (constructorArguments c))
        [] -> Nothing

-- | Is this constructor argument recursive, and if so at which indices?
--
-- @Just is@ when the argument\'s type is an application of the datatype itself,
-- with @is@ the indices it is at; 'Nothing' otherwise. The type must already
-- have the enclosing telescope\'s actual values substituted in where that
-- matters — 'Thena.Core.Reduce' does that before asking, 'eliminatorType' does
-- not need to because it works with the declaration\'s own formal variables.
--
-- **Here rather than in either caller, because there are two.** ι builds one
-- recursive /call/ per recursive argument and the eliminator\'s type builds one
-- inductive /hypothesis/ per recursive argument, and if the two ever disagreed
-- about which arguments those are, a datatype would reduce by a rule its own
-- eliminator is not typed for. Same argument as 'formerType' and 'formerArity':
-- one reading of the record, consulted twice.
--
-- **Complete only because "Thena.Global.Declare" rejects higher-order
-- recursion.** A @sup : (Nat -> Ord) -> Ord@ argument (thesis §4.1.3) has spine
-- head 'Pi', so it answers 'Nothing' — no recursive call and no inductive
-- hypothesis. Today that declaration never gets admitted; if MS1\'s limit is
-- lifted, this function and both its callers change in the same commit.
recursiveArgument :: GlobalName -> Int -> Core -> Maybe [Core]
recursiveArgument dn np ty = case spine ty of
  (Global g _, args) | g == dn -> Just (drop np args)
  _                          -> Nothing
  where
    spine = go []
      where
        go as (App f a) = go (a : as) f
        go as t         = (t, as)

-- | The type of the datatype\'s eliminator, at the universe the motive lives in
-- (§3.7, thesis §4.1.4).
--
-- @
-- ∀ params
--   (P : ∀ indices (t : D params indices) -> Type l)
--   (m₁ : ∀ Δ₁ -> IHs -> P ī₁ ‹c₁ params Δ₁›)
--   …
--   indices (t : D params indices)
--   -> P indices t
-- @
--
-- **Derived, and stored nowhere at all** — §3.7's "the eliminator's type is
-- generated and stored as a constant" was reversed by the user 2026-08-22,
-- planning phase 10. Every caller — @infer@, @:elim@, the elimination tactic —
-- calls this function, so there is no stored copy to drift from it. A
-- @NatElim@ in 'constants' would also be a trap: it would resolve in term
-- position as a bodyless 'Thena.Core.Term.Global', a term that typechecks and
-- never reduces. Same argument as 'formerType' and 'formerArity', and the same
-- one §3.7 makes against emitting ι-rules.
--
-- **The level is an argument, not a field**, which is §3.7\'s "universe
-- polymorphism of the eliminator, without universe polymorphism": there is no
-- one type for @NatElim@, there is one per universe the motive is valued in,
-- and the caller reads that off the motive at the use site.
--
-- **Parameters are abstracted at the front.** §3.7\'s "parameters not abstracted
-- in the scheme" is about the motive and the methods, which range over the
-- indices and not the parameters — and they do not here either. Putting the
-- parameters outermost is what makes the binder order match
-- 'Thena.Core.Term.Eliminate'\'s own field order exactly, so typing the node is
-- the ordinary application rule walked down this telescope and nothing else.
--
-- Takes and returns the name counter: the motive, the methods and the target
-- are binders the declaration has no variables for, and only
-- 'Thena.Core.Term.fresh' mints one (§3.5). Unlike 'formerType' it therefore
-- cannot be a plain function of the record; that is the cost of \'Var\''s hidden
-- constructor, paid here rather than by a second way to make a variable.
eliminatorType :: InductiveDefinition -> Level -> Int -> (Core, Int)
eliminatorType d l n0 = (piOver tel goal, n1)
  where (tel, goal, _, n1) = eliminatorParts d l n0

-- | The name the generated eliminator wrapper is bound to: @elimNat@,
-- @elimVec@ (MS4 phase 49e).
--
-- The same shape as
-- 'Thena.Global.NoConfusion.noConfusionNames' — a fixed word and the
-- datatype\'s own name — and it is an ordinary identifier a user may write.
-- @elim@ is a keyword, but keywords are whole tokens, so @elimNat@ lexes as one
-- name and there is nothing to reserve.
eliminatorName :: GlobalName -> GlobalName
eliminatorName (GlobalName d) = GlobalName ("elim" ++ d)

-- | The eliminator as an ordinary global definition — its type and its body
-- (MS4 phase 49e).
--
-- **§3.7 item 2 for the eliminator.** A former and a value constructor each get
-- a wrapper whose body is the 'Thena.Core.Term.Canonical' they name
-- ('generate'); this is the same thing for the 'Thena.Core.Term.Eliminate'
-- node, and it exists for the same reason: a node that is only ever saturated
-- is unusable as a function until something abstracts it.
--
-- **What it buys is a name to apply.** Elaborating @elim D …@ used to need an
-- op of its own — @make-elim@, which claimed a hole per field and handed back
-- the node — precisely because §3.7 generated nothing for the eliminator and
-- there was nothing to apply. With this definition in the environment @elim D
-- …@ is an ordinary name-headed application and the elaborator needs no
-- eliminator case at all (his proposal, 2026-09-03).
--
-- **The motive's level is a prenex parameter**, given here as an argument the
-- way 'eliminatorType' takes it. Inside @make-elim@ it was a fresh /meta/,
-- minted per use and invisible; as a parameter of the wrapper it is minted once
-- at declaration and instantiated at each use by the same machinery every other
-- polymorphic global goes through (phase 44). That is a special case becoming
-- the general mechanism, not a change of behaviour.
--
-- **The body instantiates the datatype at the wrapper\'s own level
-- parameters**, exactly as 'generate' does for a former — so @elimD {ℓ…}@
-- unfolds to an 'Thena.Core.Term.Eliminate' at those levels and the two agree
-- by construction. @make-elim@ wrote @[]@ there, which is why a polymorphic
-- datatype could not be eliminated through it.
eliminatorWrapper :: InductiveDefinition -> Level -> Int -> (Core, Core, Int)
eliminatorWrapper d l n0 = (piOver tel goal, lamOver tel node, n1)
  where (tel, goal, node, n1) = eliminatorParts d l n0

-- | The telescope, the conclusion under it, and the saturated node its own
-- binders form.
--
-- **One walk, read by two callers** — 'eliminatorType' wants the Π, and
-- 'eliminatorWrapper' wants the Π /and/ the λ over the same variables. Building
-- the telescope as a 'Context' rather than as nested 'Pi's is what lets the
-- second exist: the binders are named here, so the node can be assembled where
-- its pieces are in scope instead of being recovered by splitting a list of
-- variables peeled back off the type.
eliminatorParts
  :: InductiveDefinition -> Level -> Int -> (Context, Core, Core, Int)
eliminatorParts d l n0 = (telescope, motiveAt indexVars (Free ctv), node, nEnd)
  where
    dn      = inductiveName d
    params  = inductiveParameters d
    indices = inductiveIndices d
    np      = length params
    levels  = map LVar (inductiveLevels d)

    (pv,  n1) = fresh n0                 -- the motive
    (mtv, n2) = fresh n1                 -- the motive's own target binder
    (ctv, n3) = fresh n2                 -- the conclusion's target binder

    paramVars = map (Free . entryVar) params
    indexVars = map (Free . entryVar) indices

    -- The binder order is 'Thena.Core.Term.Eliminate'\'s own field order, which
    -- is what makes typing the node the ordinary application rule walked down
    -- this telescope and nothing else.
    telescope =
      params
        ++ [Hypothesis pv (Ident "P") motiveType]
        ++ methodEntries
        ++ indices
        ++ [Hypothesis ctv (Ident "target") (familyAt indexVars)]

    node =
      Eliminate dn levels paramVars (Free pv)
        (map (Free . entryVar) methodEntries) indexVars (Free ctv)

    -- @D params is@
    familyAt is = foldl App (Global dn levels) (paramVars ++ is)

    -- @P is v@
    motiveAt is v = foldl App (Free pv) (is ++ [v])

    -- @forall indices (t : D params indices) -> Type l@
    motiveType =
      piOver indices (Pi (Ident "target") (familyAt indexVars) (close mtv (Universe l)))

    (methodEntries, nEnd) = methods (inductiveConstructors d) n3

    methods []       n = ([], n)
    methods (c : cs) n =
      let (mty, na)    = methodType c n
          (mv,  nb)    = fresh na
          (below, nc)  = methods cs nb
       in (Hypothesis mv (Ident "method") mty : below, nc)

    -- @forall D -> IH1 -> ... -> IHn -> P is (c params D)@
    methodType c n =
      let args = constructorArguments c
          goal = motiveAt (constructorIndices c)
                          (Canonical (constructorName c) levels
                                     (paramVars ++ map (Free . entryVar) args))
          (body, na) = hypotheses args n goal
       in (piOver args body, na)

    -- One inductive hypothesis per recursive argument, in argument order. The
    -- binder is non-dependent -- nothing may refer to an induction hypothesis --
    -- but a 'Thena.Core.Term.Scope' still needs a variable to close over, so
    -- each takes one from the counter rather than reusing a sentinel.
    hypotheses []       n acc = (acc, n)
    hypotheses (e : es) n acc = case recursiveArgument dn np (entryType e) of
      Nothing -> hypotheses es n acc
      Just is ->
        let (hv, na)   = fresh n
            (below, nb) = hypotheses es na acc
         in (Pi (Ident "ih") (motiveAt is (Free (entryVar e))) (close hv below), nb)

-- | Every 'Var' the environment holds.
--
-- **The inductive records are where they are.** A global definition's type and
-- body are closed, but 'inductiveParameters', 'inductiveIndices' and each
-- constructor's arguments are 'Context'es — telescopes of *named, numbered*
-- bindings, minted when the datatype was declared and living in the environment
-- ever after.
--
-- 'Thena.Kernel.certify' needs them: it walks terms it did not build, and
-- 'eliminatorType' reuses a datatype's own parameter variables while minting
-- fresh ones beside them. Starting the counter below either is how a fresh
-- variable collides with a declared one.
varsInEnv :: GlobalEnv -> [Var]
varsInEnv e = concatMap (ofInductive . snd) (inductives e)
  where
    ofInductive d =
      map entryVar (inductiveParameters d)
        ++ map entryVar (inductiveIndices d)
        ++ concatMap (map entryVar . constructorArguments) (inductiveConstructors d)
