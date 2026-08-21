-- | Admitting an inductive definition: what is checked, and what is generated
-- (§3.7).
--
-- Above "Thena.Core.Typing" in the layering, and "Thena.Global.Env" is below
-- "Thena.Core.Reduce" — that split is the whole reason @Global@ is two modules
-- (§2.5). Nothing here may move down into 'Thena.Global.Env'.
--
-- **The universe check is not in this phase.** Thesis §4.1.1 restricts the
-- universe of a constructor's non-recursive arguments, and checking it needs
-- level inference, so it is back-filled here at phase 8 when @infer@ exists
-- (§9). This is a marked omission, not an oversight.
--
-- **Eliminator generation is not in this phase either.** Phase 10 extends this
-- module with §3.7's items 1, 3 and 4 — the eliminator's type, the
-- @NoConfusion@ family and the @noConfusion@ lemma. Phase 6 has item 2, the
-- former wrappers, which are purely syntactic and need no typing.
module Thena.Global.Declare
  ( DeclareError (..)
  , declare
  ) where

import Control.Monad (foldM)

import Thena.Core.Context (Entry (..), entryVar, lamOver)
import Thena.Core.Term
  ( Core (..)
  , GlobalName
  , Ident
  , fresh
  , globalsIn
  , open
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
declare
  :: GlobalEnv -> Int -> InductiveDefinition
  -> Either DeclareError (GlobalEnv, Int)
declare env n d = do
  checkNames env d
  n1 <- foldM
          (constructor (inductiveName d) (length (inductiveIndices d)))
          n
          (inductiveConstructors d)
  Right (generate d env, n1)

-- --------------------------------------------------------------------------
-- Checking
-- --------------------------------------------------------------------------

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
      Global g
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

    former e (g, tel, ty) =
      addDefinition g (MkDefinition ty body) (addConstant g ty e)
      where
        body = lamOver tel (Canonical g (map (Free . entryVar) tel))

-- | An application spine, head first.
spine :: Core -> (Core, [Core])
spine = go []
  where
    go as (App f a) = go (a : as) f
    go as t         = (t, as)
