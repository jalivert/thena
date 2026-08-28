module Thena.Core.TermTests (tests) where

import Data.List (nub, sort)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import Test.Tasty.QuickCheck
  ( Gen
  , elements
  , forAll
  , listOf
  , oneof
  , resize
  , sized
  , testProperty
  , (===)
  )

import Thena.Core.Level (levelOfNat)
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

-- --------------------------------------------------------------------------
-- Variables the tests use
-- --------------------------------------------------------------------------

-- | Variables a generated term may mention free. Numbered from 100 so they can
-- never collide with a binder variable, which is numbered by nesting depth.
poolVars :: [Var]
poolVars = [poolVarA, poolVarB, poolVarC]

-- | The pool, named individually. Named rather than reached for with 'head',
-- which is partial and which @-Wall@ rejects (@-Wx-partial@, GHC 9.12).
poolVarA, poolVarB, poolVarC :: Var
poolVarA = fst (fresh 100)
poolVarB = fst (fresh 101)
poolVarC = fst (fresh 102)

-- | Variables no generated term can mention: the pool sits at 100..102 and
-- binder variables are numbered by nesting depth, so 900 and 901 are free.
unusedVarA, unusedVarB :: Var
unusedVarA = fst (fresh 900)
unusedVarB = fst (fresh 901)

-- | A binder's variable at nesting depth @d@.
--
-- Numbering by depth is what keeps the generator honest: no binder reuses the
-- variable of a binder it sits inside, which is the case where 'close' would
-- capture an occurrence belonging to the outer one. Two *sibling* binders may
-- share a variable, and that is harmless — the sibling's scope is already closed
-- by the time the enclosing 'close' runs.
binderVar :: Int -> Var
binderVar d = fst (fresh d)

mintFrom :: Int -> [Var]
mintFrom n = let (v, n') = fresh n in v : mintFrom n'

-- --------------------------------------------------------------------------
-- The generator
-- --------------------------------------------------------------------------

-- | @genCore depth@ generates a term under @depth@ enclosing binders, so
-- @binderVar 0 .. binderVar (depth - 1)@ are in scope and may appear free.
--
-- Every 'Scope' is built by 'close'. The generator has no more access to
-- 'Scope'\'s constructor than any other module does, so it cannot produce a
-- dangling index even by accident — which is the property under test, and the
-- reason not to give the tests a privileged way in.
genCore :: Int -> Gen Core
genCore depth = sized go
  where
    go :: Int -> Gen Core
    go n
      | n <= 1    = genLeaf
      | otherwise = oneof [genLeaf, genNode n]

    inScope :: [Var]
    inScope = poolVars ++ map binderVar [0 .. depth - 1]

    genLeaf :: Gen Core
    genLeaf =
      oneof
        [ Free <$> elements inScope
        , (\g -> Global g []) <$> genGlobalName
        , Universe . levelOfNat <$> elements [0, 1]
        ]

    genNode :: Int -> Gen Core
    genNode n =
      oneof
        [ Pi <$> genIdent <*> half <*> (close (binderVar depth) <$> deeper)
        , Lam <$> genIdent <*> half <*> (close (binderVar depth) <$> deeper)
        , Let <$> genIdent <*> half <*> half <*> (close (binderVar depth) <$> deeper)
        , App <$> half <*> half
        , (\g as -> Canonical g [] as) <$> genGlobalName <*> resize (n `div` 3) (listOf half)
        , (\d -> Eliminate d [])
            <$> genGlobalName
            <*> resize (n `div` 4) (listOf half)
            <*> half
            <*> resize (n `div` 4) (listOf half)
            <*> resize (n `div` 4) (listOf half)
            <*> half
        ]
      where
        half   = resize (n `div` 2) (genCore depth)
        deeper = resize (n `div` 2) (genCore (depth + 1))

genIdent :: Gen Ident
genIdent = Ident <$> elements ["x", "y", "z", "n"]

genGlobalName :: Gen GlobalName
genGlobalName = GlobalName <$> elements ["Nat", "Vec", "S", "plus"]

-- | A closed-at-top term: its free variables come only from 'poolVars'.
genTerm :: Gen Core
genTerm = genCore 0

-- --------------------------------------------------------------------------
-- Well-scopedness, checked through the public API only
-- --------------------------------------------------------------------------

-- | Opening every 'Scope' with a variable of its own leaves nothing 'Bound'.
--
-- Uses only exported functions, which is the point: if the tests could see
-- inside a 'Scope' they would not be testing the barrier. A 'Bound' reached here
-- is genuinely dangling, because every enclosing scope has already been opened
-- on the way down.
wellScoped :: Core -> Bool
wellScoped = go 1000
  where
    go :: Int -> Core -> Bool
    go c t = case t of
      Bound _        -> False
      Free _         -> True
      Global _ _     -> True
      Universe _     -> True
      Pi _ s b       -> go c s && under c b
      Lam _ s b      -> go c s && under c b
      App f a        -> go c f && go c a
      Let _ v s b    -> go c v && go c s && under c b
      Canonical _ _ as -> all (go c) as
      Eliminate _ _ ps m ms is tgt ->
        all (go c) ps && go c m && all (go c) ms && all (go c) is && go c tgt
      where
        under n sc = let (v, n') = fresh n in go n' (open v sc)

-- --------------------------------------------------------------------------
-- Hand-built terms, for the alpha-equivalence cases
-- --------------------------------------------------------------------------

tyA :: Core
tyA = Global (GlobalName "A") []

-- | @λ ‹name› : A . ‹name›@, built with a variable of its own.
identityLam :: String -> Int -> Core
identityLam name n =
  let (x, _) = fresh n
   in Lam (Ident name) tyA (close x (Free x))

-- | @λ ‹outer› : A . λ ‹inner› : A . ‹whichever the flag picks›@.
constLam :: String -> String -> Int -> Bool -> Core
constLam outer inner n takeOuter =
  let (x, n') = fresh n
      (y, _)  = fresh n'
      body    = Free (if takeOuter then x else y)
   in Lam (Ident outer) tyA (close x (Lam (Ident inner) tyA (close y body)))

-- --------------------------------------------------------------------------
-- The tree
-- --------------------------------------------------------------------------

tests :: TestTree
tests =
  testGroup
    "Thena.Core.Term"
    [ testGroup "close and open" closeOpenTests
    , testGroup "Eq is alpha-equivalence" alphaTests
    , testGroup "instantiate" instantiateTests
    , testGroup "freeVars" freeVarsTests
    ]

closeOpenTests :: [TestTree]
closeOpenTests =
  [ testProperty "generated terms are well scoped" $
      forAll genTerm wellScoped

  , testProperty "open x . close x is the identity" $
      forAll genTerm $ \t ->
        forAll (elements poolVars) $ \x ->
          open x (close x t) === t

  , testProperty "closing a variable that does not occur changes nothing" $
      forAll genTerm $ \t ->
        open unusedVarA (close unusedVarA t) === t

  , testProperty "close then open renames, and touches nothing else" $
      forAll genTerm $ \t ->
        forAll (elements poolVars) $ \x ->
          forAll (elements [unusedVarA, unusedVarB]) $ \y ->
            asSet (map (\v -> if v == x then y else v) (freeVars t))
              === asSet (freeVars (open y (close x t)))

  , testProperty "a closed and reopened term is still well scoped" $
      forAll genTerm $ \t ->
        forAll (elements poolVars) $ \x ->
          wellScoped (open x (close x t))
  ]

alphaTests :: [TestTree]
alphaTests =
  [ testCase "lambdas differing only in their identifier are equal" $
      identityLam "x" 0 @?= identityLam "y" 1

  , testCase "nested binders: the identifiers do not matter" $
      constLam "x" "y" 0 True @?= constLam "a" "b" 10 True

  , testCase "nested binders: which variable the body uses does matter" $
      (constLam "x" "y" 0 True == constLam "x" "y" 0 False) @?= False

  , testCase "a bound variable is not equal to a free one" $
      (identityLam "x" 0 == Lam (Ident "x") tyA (close unusedVarA tyA))
        @?= False

  , testProperty "the identifier never affects equality" $
      forAll genTerm $ \body ->
        forAll (elements poolVars) $ \x ->
          Lam (Ident "x") tyA (close x body)
            === Lam (Ident "zzz") tyA (close x body)

  , testProperty "a term equals itself" $
      forAll genTerm $ \t -> t === t
  ]

instantiateTests :: [TestTree]
instantiateTests =
  [ testProperty "instantiate at the variable just closed gives the term back" $
      forAll genTerm $ \v ->
        instantiate v (close poolVarA (Free poolVarA)) === v

  , testProperty "instantiating a variable that does not occur changes nothing" $
      forAll genTerm $ \t ->
        forAll genTerm $ \v ->
          instantiate v (close unusedVarA t) === t

  , testProperty "open is instantiate with a variable" $
      forAll genTerm $ \t ->
        forAll (elements poolVars) $ \x ->
          open x (close x t) === instantiate (Free x) (close x t)
  ]

freeVarsTests :: [TestTree]
freeVarsTests =
  [ testProperty "no repeats" $
      forAll genTerm $ \t -> freeVars t === nub (freeVars t)

  , testProperty "closing removes the variable" $
      forAll genTerm $ \t ->
        forAll (elements poolVars) $ \x ->
          notElem x (freeVars (open unusedVarB (close x t)))

  , testCase "an Eliminate node's every field is traversed" $
      let vs = take 6 (mintFrom 200)
          node =
            Eliminate
              { eliminated = GlobalName "Nat"
              , parameters = [Free (vs !! 0)]
              , motive     = Free (vs !! 1)
              , methods    = [Free (vs !! 2)]
              , indices    = [Free (vs !! 3)]
              , target     = Free (vs !! 4)
              }
       in asSet (freeVars node) @?= asSet (take 5 vs)

  , testCase "a Canonical node's arguments are traversed" $
      let vs = take 2 (mintFrom 300)
       in asSet (freeVars (Canonical (GlobalName "S") [] (map Free vs)))
            @?= asSet vs
  ]

asSet :: [Var] -> [Var]
asSet = sort . nub
