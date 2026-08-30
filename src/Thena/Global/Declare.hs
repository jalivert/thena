-- | Admitting an inductive definition: what is checked, and what is generated
-- (§3.7).
--
-- Above "Thena.Core.Typing" in the layering, and "Thena.Global.Env" is below
-- "Thena.Core.Reduce" — that split is the whole reason @Global@ is two modules
-- (§2.5). Nothing here may move down into 'Thena.Global.Env'.
--
-- **The universe check landed at phase 8**, as §9 said it would: thesis
-- §4.1.1 restricts the universe of a constructor's arguments and checking it
-- needs level inference. 'universes' below is it.
--
-- **The eliminator is generated nowhere** — its type is a derived function of
-- the record, 'Thena.Global.Env.eliminatorType' (§3.7, reversed by the user
-- 2026-08-22). What phase 14 adds here is §3.7's items 3 and 4, the
-- @NoConfusion@ family and the @noConfusion@ lemma, and they live in
-- "Thena.Global.NoConfusion" because emitting a proof term is a different kind
-- of code from deciding whether a declaration may be admitted. Phase 6 has item
-- 2, the former wrappers, which are purely syntactic and need no typing.
module Thena.Global.Declare
  ( DeclareError (..)
  , declare
  ) where

import Control.Monad (foldM)

import Thena.Core.Context (Context, Entry (..), entryType, entryVar, lamOver)
import Thena.Core.Reduce (whnf)
import Thena.Core.Level
  ( Level (..)
  , Obligation (..)
  , freshLevelRigid
  , levelMax
  , loneMeta
  , metasIn
  , solveLevels
  )
import Thena.Core.Term ()
import Thena.Core.Typing (infer)
import Thena.Errors (TypeError (..))
import Thena.Core.Term
  ( Core (..)
  , GlobalName
  , Ident
  , fresh
  , globalsIn
  , open
  )
import Thena.Global.NoConfusion
  ( Generated (..)
  , Skipped (..)
  , generateNoConfusion
  )
import Thena.Global.Env
  ( ConstructorDefinition (..)
  , Definition (..)
  , GlobalEnv
  , InductiveDefinition (..)
  , addConstant
  , addDefinition
  , addInductive
  , constructorType
  , formerType
  , levelMetasInInductive
  , substLevelsInInductive
  , isDeclared
  )

-- | Structured, per §12 invariant 2. Every case names the constructor it is
-- about, and the positivity cases also name the argument, because a datatype
-- with seven constructors is otherwise a hunt.
--
-- 'HigherOrderRecursion' and 'NestedRecursion' are **MS1 limits, not
-- unsoundness**: §3.7 admits both as representable and rejected for now, so
-- they are deliberately separate from 'NotStrictlyPositive', which is the real
-- thing. Keeping them apart is what lets the message say "not yet" rather than
-- "never".
data DeclareError
  = AlreadyDeclared GlobalName
    -- ^ one namespace, shared with generated names (§3.6)
  | RepeatedName GlobalName
    -- ^ the declaration itself uses the name twice
  | WrongNumberOfIndices GlobalName Int Int
    -- ^ constructor, indices expected, indices given
  | NotStrictlyPositive GlobalName Ident
    -- ^ the datatype occurs to the left of an arrow in this argument
  | HigherOrderRecursion GlobalName Ident
    -- ^ @sup : (Nat -> Ord) -> Ord@ — thesis §4.1.3, out of MS1
  | NestedRecursion GlobalName Ident
    -- ^ the datatype occurs under another type former, as in @List D@
  | ArgumentNotAType GlobalName Ident TypeError
    -- ^ this argument's type does not itself have a type (phase 8)
  | ArgumentTooLarge GlobalName Ident Level Level
    -- ^ constructor, argument, the universe the argument lives in, and the
    -- datatype's own — thesis §4.1.1 (phase 8)
  | NoConfusionRejected GlobalName TypeError
    -- ^ **a generator bug, not a user mistake** (phase 14): the checker refused
    -- a definition "Thena.Global.NoConfusion" emitted. It is a refusal rather
    -- than a crash because §3.7 has these checked like anything else, and a
    -- checked thing that fails has to be able to say so.
  deriving (Eq, Show)

-- | Check a declaration and admit it, or say why not.
--
-- Takes and returns the session's name counter: peeling a constructor
-- argument's own binders opens 'Thena.Core.Term.Scope's, and only
-- 'Thena.Core.Term.fresh' mints the variables to open them with (§3.5). Phase
-- 10's generator will want the counter for more than that.
--
-- **The caller is the driver, not the machine** (decided by the user, planning
-- phase 6). @define-data@ yields the resolved declaration through the single
-- channel and the driver runs this, exactly as §7.5 has the driver run kernel
-- policy for @Certify@ at phase 12. No instruction writes globals.
-- **Also reports what no-confusion did not do.** The 'Skipped' is a fact about
-- the declaration the user just wrote — @Vec@ gets no @noConfusionVec@ — and
-- the driver says it. 'Thena.Global.NoConfusion.NoEquality' is the one case
-- that is about the environment instead, and it is silent.
declare
  :: GlobalEnv -> Int -> InductiveDefinition
  -> Either DeclareError (GlobalEnv, Int, Maybe Skipped)
declare env n d0 = do
  checkNames env d0
  n1 <- foldM
          (constructor (inductiveName d0) (length (inductiveIndices d0)))
          n
          (inductiveConstructors d0)
  -- **Compute, check, then generalise** (MS3 phase 33c). A bare @Type@ in the
  -- declared position becomes the least universe containing the constructors'
  -- arguments; the size restriction is then checked against whatever the
  -- declared level is, written or computed; and what is still a meta afterwards
  -- becomes a prenex level parameter. Everything below this line sees a
  -- finished declaration, which is why the wrappers and no-confusion need to
  -- know nothing about any of it.
  (d1, n2) <- computed env n1 d0
  n2' <- universes env n2 d1
  let (d, n4) = generaliseInductive n2' d1
  -- The wrappers first: the generated terms name the datatype's own former and
  -- constructors, so they must already resolve.
  let env1 = generate d env
  case generateNoConfusion env1 n4 d of
    Generated env2 n3 -> Right (env2, n3, Nothing)
    Declined NoEquality -> Right (env1, n2, Nothing)
    Declined NoProducts -> Right (env1, n2, Nothing)
    Declined why        -> Right (env1, n2, Just why)
    Clash g            -> Left (AlreadyDeclared g)
    Rejected g e       -> Left (NoConfusionRejected g e)

-- --------------------------------------------------------------------------
-- Checking
-- --------------------------------------------------------------------------

-- | Thesis §4.1.1: the declared universe must dominate the universes its
-- constructors\' arguments live in. Without it a larger universe can be
-- embedded in a smaller one and the system is inconsistent.
--
-- **Checked in an environment where the type former exists and nothing else
-- of the declaration does.** That is not a convenience: a recursive argument\'s
-- type mentions @D@, so it cannot be typed at all until @D@ has one, and the
-- eliminator and the wrappers must /not/ exist yet because they are generated
-- from the completed declaration (@AGENDA.md@ item 28 confirms this is the
-- intended reading, and Agda and Idris agree).
--
-- **Applied uniformly, to recursive and non-recursive arguments alike**, though
-- §4.1.1 restricts only the non-recursive ones. It comes to the same thing: a
-- recursive argument is an application of @D@, whose type is the declared
-- universe exactly, so @≤@ holds for it by construction. One rule beats two
-- with a classification between them.
--
-- The context is the parameters plus the arguments already walked, which is
-- what the stored types are written against — no opening, no substitution.
argumentLevels
  :: GlobalEnv -> Int -> InductiveDefinition
  -> Either DeclareError ([(GlobalName, Ident, Level)], Int)
argumentLevels env n0 d = foldM eachConstructor ([], n0) (inductiveConstructors d)
  where
    provisional = addConstant (inductiveName d) (inductiveLevels d) (formerType d) env

    eachConstructor acc c = go acc (inductiveParameters d) (constructorArguments c)
      where
        go seen _   []       = Right seen
        -- Level obligations are dropped, as everywhere outside the checking
        -- pass ("Thena.Core.Typing"'s header says why once). A declaration
        -- names no global whose scheme could owe one.
        go (seen, n') ctx (e : es) = case infer provisional ctx n' (entryType e) of
          (Left err, _, _) -> Left (ArgumentNotAType (constructorName c) (identOf e) err)
          (Right ty, _, n'') -> case whnf provisional ctx ty of
            Universe l -> go (seen ++ [(constructorName c, identOf e, l)], n'') (ctx ++ [e]) es
            ty' -> Left (ArgumentNotAType (constructorName c) (identOf e)
                          (notAType ctx (entryType e) ty'))

    identOf :: Entry -> Ident
    identOf e = case e of
      Hypothesis _ i _   -> i
      Definition _ i _ _ -> i

    notAType :: Context -> Core -> Core -> TypeError
    notAType = NotAType

-- | Thesis §4.1.1: the declared universe must dominate the universes its
-- constructors\' arguments live in. Without it a larger universe can be
-- embedded in a smaller one and the system is inconsistent.
--
-- **Checked in an environment where the type former exists and nothing else
-- of the declaration does** — 'argumentLevels' does that, and this reads its
-- answer. A recursive argument\'s type mentions @D@, so it cannot be typed at
-- all until @D@ has one, and the eliminator and the wrappers must /not/ exist
-- yet because they are generated from the completed declaration (@AGENDA.md@
-- item 28 confirms this is the intended reading, and Agda and Idris agree).
--
-- **Applied uniformly, to recursive and non-recursive arguments alike**, though
-- §4.1.1 restricts only the non-recursive ones. It comes to the same thing: a
-- recursive argument is an application of @D@, whose type is the declared
-- universe exactly, so @≤@ holds for it by construction. One rule beats two
-- with a classification between them.
--
-- **The three answers of @levelLeq@ are now read as three** (MS3 phase 33c).
-- An undecided relation is an obligation, exactly as it is in conversion, and
-- 'Thena.Core.Level.solveLevels' decides it — @suc ?ℓ ≤ 1@ pins @?ℓ@ at zero
-- rather than being refused for not being obviously true. What the solver
-- cannot settle **is still refused**: a datatype has nowhere to carry a
-- conditional constraint, because 'Thena.Global.Env.definitionConstraints' is a
-- definition\'s and a use of a former supplies levels without proving anything.
universes :: GlobalEnv -> Int -> InductiveDefinition -> Either DeclareError Int
universes env n0 d = do
  (ls, n1) <- argumentLevels env n0 d
  let owed = [ AtMost l (inductiveLevel d) | (_, _, l) <- ls ]
  case solveLevels owed of
    Right (_, []) -> Right n1
    -- Which argument to name: the first whose own relation does not hold on
    -- its own. There is always one, because the whole set failed.
    _ -> case [ (g, i, l) | (g, i, l) <- ls
              , solveLevels [AtMost l (inductiveLevel d)] /= Right ([], []) ] of
           (g, i, l) : _ -> Left (ArgumentTooLarge g i l (inductiveLevel d))
           []            -> Right n1

-- | The universe a bare @Type@ in the declared position stands for: the least
-- one that contains every constructor argument (MS3 phase 33c).
--
-- **This is §4.3\'s compute-versus-constrain, settled for declarations by
-- computing** — and it is what makes @data Eq (A : Type) : A -> A -> Type@ come
-- out as @Eq {ℓ}@ rather than @Eq {ℓ0 ℓ1}@ with @ℓ0 ≤ ℓ1@. Constraining would
-- have given the datatype a second parameter that every use has to supply, and
-- MS3\'s own done-when — @examples\/determinacy.thena@ byte-identical — forbids
-- that.
--
-- **Only a bare @Type@ is computed. A written @Typeₙ@ is still checked**, so
-- @data Big : Type₀ where { wrap : Type₀ -> Big }@ is refused exactly as it
-- always was: saying which universe a datatype lives in is a claim the system
-- keeps you to.
--
-- **A level mentioning the meta being computed contributes nothing** — that is
-- the recursive argument, whose type is the declared universe by construction,
-- and including it would make the substitution cyclic. §4.1.1 restricts only
-- the non-recursive arguments and this is where the distinction earns its keep.
computed
  :: GlobalEnv -> Int -> InductiveDefinition
  -> Either DeclareError (InductiveDefinition, Int)
computed env n0 d = case loneMeta (inductiveLevel d) of
  Nothing -> Right (d, n0)
  Just m  -> do
    (ls, n1) <- argumentLevels env n0 d
    case [ l | (_, _, l) <- ls, m `notElem` metasIn l ] of
      -- **Nothing contributes, so nothing is computed and the meta is left for
      -- generalisation.** @Empty@ and @Unit@ are this case, and it is the whole
      -- difference between them coming out polymorphic and coming out pinned at
      -- @Type₀@: there is no argument to take a max of, and @max of nothing@ is
      -- zero, which would be an answer invented rather than derived.
      []      -> Right (d, n1)
      l : ls' -> Right (substLevelsInInductive [(m, foldr levelMax l ls')] d, n1)

-- | Turn the level metas a declaration is left holding into its prenex
-- parameters (MS3 phase 33c) — 'Thena.Global.Env.generalised' for declarations.
--
-- A datatype carries **no constraints**, so unlike a definition there is
-- nothing to store beside the parameters: 'universes' has already refused
-- anything the solver could not settle outright.
--
-- **The parameters it already has are kept and the new ones appended.** While
-- @data D {ℓ}@ still exists a declaration can arrive with rigids the resolver
-- put there, and overwriting them makes @Empty {l}@ take no level argument at
-- all — which is how this was found. Phase 33c deletes that syntax, and then
-- the list coming in is always empty; the append is right either way.
generaliseInductive
  :: Int -> InductiveDefinition -> (InductiveDefinition, Int)
generaliseInductive n0 d =
  (rewritten { inductiveLevels = inductiveLevels d ++ map snd binding }, n1)
  where
    (binding, n1) = mint n0 (levelMetasInInductive d)
    rewritten     = substLevelsInInductive [ (v, LVar w) | (v, w) <- binding ] d

    mint k []       = ([], k)
    mint k (v : vs) = let (w, k1)  = freshLevelRigid k
                          (ws, k2) = mint k1 vs
                       in ((v, w) : ws, k2)

-- | Every name a declaration introduces must be free, and distinct from the
-- others it introduces.
checkNames :: GlobalEnv -> InductiveDefinition -> Either DeclareError ()
checkNames env d = go [] (inductiveName d : map constructorName (inductiveConstructors d))
  where
    go _ [] = Right ()
    go seen (g : gs)
      | g `elem` seen    = Left (RepeatedName g)
      | isDeclared g env = Left (AlreadyDeclared g)
      | otherwise        = go (g : seen) gs

-- | One constructor: it must target the family at the right number of indices,
-- and every argument must be strictly positive.
--
-- The index count is re-checked here even though "Thena.Syntax.Resolve" splits
-- the target and could not produce a mismatch, because phase 10 will build
-- 'InductiveDefinition's without going through the parser.
constructor
  :: GlobalName -> Int -> Int -> ConstructorDefinition
  -> Either DeclareError Int
constructor dn expected n c
  | given /= expected = Left (WrongNumberOfIndices (constructorName c) expected given)
  | otherwise         = foldM (argument dn (constructorName c)) n (constructorArguments c)
  where
    given = length (constructorIndices c)

-- | An argument of a constructor. A telescope entry with a body cannot come
-- out of the resolver; if one is built by hand, its value is held to the same
-- rule as its type.
argument :: GlobalName -> GlobalName -> Int -> Entry -> Either DeclareError Int
argument dn cn n e = case e of
  Hypothesis _ i t   -> positive dn cn i n t
  Definition _ i s t
    | dn `elem` globalsIn s -> Left (NestedRecursion cn i)
    | otherwise             -> positive dn cn i n t

-- | Strict positivity, and MS1's two further restrictions (§3.7).
--
-- Peel the argument's own binders. The datatype may not occur in any of their
-- domains — that is strict positivity, and it is the case that is unsound. What
-- is left is the argument's head:
--
--   * the datatype itself, with nothing peeled — a recursive argument, which is
--     what makes the definition inductive;
--   * the datatype itself, with something peeled — @(Nat -> Ord) -> Ord@, a
--     higher-order recursive argument (§4.1.3), representable and rejected;
--   * anything else mentioning the datatype — @List D@ — nested recursion,
--     which needs a positivity check on the /other/ former and is out of MS1;
--   * anything else — an ordinary non-recursive argument.
positive
  :: GlobalName -> GlobalName -> Ident -> Int -> Core
  -> Either DeclareError Int
positive dn cn i = peel False
  where
    peel peeled n t = case t of
      Pi _ dom body
        | dn `elem` globalsIn dom -> Left (NotStrictlyPositive cn i)
        | otherwise ->
            let (v, n1) = fresh n
             in peel True n1 (open v body)
      _ -> settle peeled n t

    settle peeled n t = case fst (spine t) of
      Global g _
        | g == dn ->
            if peeled
              then Left (HigherOrderRecursion cn i)
              else if any mentions (snd (spine t))
                then Left (NestedRecursion cn i)
                else Right n
      _ | mentions t -> Left (NestedRecursion cn i)
        | otherwise  -> Right n

    mentions t = dn `elem` globalsIn t

-- --------------------------------------------------------------------------
-- Generating
-- --------------------------------------------------------------------------

-- | §3.7 item 2: a global function for every former, value constructor and type
-- former alike, whose body is the 'Canonical'.
--
-- Each former contributes **two** entries under one name (§3.3.1): a constant,
-- which is the type of the saturated 'Canonical', and a definition, which is
-- the wrapper. The user only ever reaches the wrapper — the resolver never
-- builds a 'Canonical' (§3.6) — and a 'Canonical' enters a term only by
-- δ-unfolding the wrapper and β-reducing.
--
-- This is what makes a former usable as an ordinary function value: @succ@ on
-- its own is that global, so @map succ xs@ works, and it is why 'Core' needs no
-- under-applied 'Canonical' (§12 invariant 6).
generate :: InductiveDefinition -> GlobalEnv -> GlobalEnv
generate d env = addInductive dn d (foldl former env (typeFormer : map value cs))
  where
    dn = inductiveName d
    ps = inductiveParameters d
    cs = inductiveConstructors d

    typeFormer = (dn, ps ++ inductiveIndices d, formerType d)
    value c    = (constructorName c, ps ++ constructorArguments c, constructorType d c)

    -- **The wrapper inherits the datatype's level parameters** (phase 31b),
    -- and its body instantiates the 'Canonical' at exactly those parameters —
    -- so @succ {ℓ}@ unfolds to @Canonical succ [ℓ] …@ and the two agree by
    -- construction rather than by a rule someone has to remember.
    former e (g, tel, ty) =
      addDefinition g (MkDefinition lvs [] ty body) (addConstant g lvs ty e)
      where
        lvs  = inductiveLevels d
        body = lamOver tel (Canonical g (map LVar lvs) (map (Free . entryVar) tel))

-- | An application spine, head first.
spine :: Core -> (Core, [Core])
spine = go []
  where
    go as (App f a) = go (a : as) f
    go as t         = (t, as)
