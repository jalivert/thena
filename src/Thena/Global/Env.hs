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
-- 'Thena.Engine.Machine' beside 'Thena.Engine.ProofState' rather than inside
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
  , lookupConstant
  , lookupDefinition
  , lookupInductive
  , isDeclared
  , addConstant
  , addDefinition
  , addInductive

    -- * The types a declaration stands for
  , formerType
  , constructorType
  , constructorTarget
  , formerArity
  ) where

import Thena.Core.Context (Context, entryVar, piOver)
import Thena.Core.Term (Core (..), GlobalName, Level)

-- | A global with a body — the @definition@ kind of §3.3.1's table: proved
-- theorems, the generated former wrappers, the prelude. δ-reducible.
--
-- The constructor is @MkDefinition@ because 'Thena.Core.Context.Entry' already
-- has a data constructor called @Definition@ and the two would be ambiguous
-- wherever both modules are in scope. Same technique as @MkScope@.
data Definition = MkDefinition
  { definitionType :: Core
  , definitionBody :: Core
  }
  deriving (Eq, Show)

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
  , inductiveParameters   :: Context   -- ^ in scope in the indices and in every constructor
  , inductiveIndices      :: Context   -- ^ in scope in neither; each constructor supplies its own
  , inductiveLevel        :: Level     -- ^ the declared result universe, concrete (§3.7)
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
  { constants   :: [(GlobalName, Core)]                 -- ^ a type and no body
  , definitions :: [(GlobalName, Definition)]           -- ^ a type and a body
  , inductives  :: [(GlobalName, InductiveDefinition)]  -- ^ what the checker and ι consult
  }
  deriving (Eq, Show)

emptyGlobals :: GlobalEnv
emptyGlobals = GlobalEnv [] [] []

-- | The type of a saturated former or, from phase 10, of an eliminator.
lookupConstant :: GlobalName -> GlobalEnv -> Maybe Core
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

addConstant :: GlobalName -> Core -> GlobalEnv -> GlobalEnv
addConstant g t e = e { constants = (g, t) : constants e }

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
  foldl App (Global (inductiveName d))
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
