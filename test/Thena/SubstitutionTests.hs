-- | Generated substitution (MS6 phase 105; @ms6\/SPEC.md@ §4.7).
--
-- **The load-bearing test is the de Bruijn crossing**: a random term and a
-- random simultaneous map, substituted by the generated @L-subst-all@ and
-- then converted to de Bruijn form, must be what de Bruijn substitution — which
-- cannot capture, having no names to capture with — makes of the converted
-- term. Named substitution against nameless, each written without the other.
-- The names in the generators are a handful, primes included, so that capture
-- and the priming of a fresh name are exercised rather than hoped for.
--
-- That crossing says nothing about /which/ names come out, and his choice
-- (2026-09-21) was that a binder is renamed only when keeping it would
-- capture. So that is a property of its own, stated as the spec states it.
--
-- The oracle reads the roles off 'ConstructorDefinition', not off the
-- grammar the generator read, so it also checks that the two agree.
module Thena.SubstitutionTests (tests) where

import Data.List (elemIndex, nub, sort)
import Data.Maybe (fromMaybe, isNothing)

import Test.Tasty (TestTree, testGroup, withResource)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import Test.Tasty.QuickCheck
  (Gen, counterexample, elements, forAll, ioProperty, listOf, oneof, resize, sized, testProperty, withNumTests, (===))

import Thena.Core.Level (Level (..))
import Thena.Core.Reduce (whnf)
import Thena.Core.Term (Core (..), GlobalName (..), Literal (..))
import Thena.Driver (Response (..), Session (..), loadProofSource)
import Thena.Engine (Machine (globals))
import Thena.Global.Env
  ( ArgRole (..)
  , ConstructorDefinition (..)
  , GlobalEnv
  , InductiveDefinition (..)
  , definitionLevels
  , definitionType
  , lookupDefinition
  , lookupInductive
  )
import Thena.Repl (renderCore, renderResponse, startingSession)

tests :: TestTree
tests =
  withResource loaded (const (pure ())) $ \io ->
    testGroup
      "generated substitution"
      [ testGroup "what is declared (§4.7)" (declared io)
      , testGroup "worked cases" (worked io)
      , testGroup "against the nameless oracle" (crossing io)
      , testGroup "what can and cannot be generated" refused
      , testGroup "a proof can follow the decision (phase 109a)" followed
      ]

-- ---------------------------------------------------------------------------
-- The fixture

-- | STLC's LC, and a language with two binders in one production, bound in one
-- argument (@lam2@) and in two different ones (@half@). @y@ is a second class
-- of the same strings: two binders need two names, and that is not two sorts.
source :: String
source =
  unlines
    [ "module Subst where"
    , ""
    , "x : Token String"
    , "x = /[a-z][a-zA-Z0-9']*/"
    , ""
    , "y : Token String"
    , "y = /[a-z][a-zA-Z0-9']*/"
    , ""
    , "language Ty, T, S where"
    , "  base  -> \953"
    , "  arrow -> ( T -> S )"
    , ""
    , "language LC, M, N, E where"
    , "  var : x as occurrence -> x"
    , "  abs : x as binder     -> ( \955 x : T . E[x] )"
    , "  app                   -> ( M N )"
    , ""
    , "language LB, P, Q where"
    , "  bvar : x as occurrence     -> x"
    , "  lam2 : { x, y } as binders -> ( \955\955 x y . P[x, y] )"
    , "  half : { x, y } as binders -> ( \956 x y . P[x] Q[y] )"
    , "  bapp                       -> ( P Q )"
    ]

loaded :: IO GlobalEnv
loaded = do
  (s0, _) <- startingSession
  case loadProofSource s0 source of
    (s1, ProofLoaded {}) -> pure (globals (sessionMachine s1))
    (s1, other) -> assertFailure (unlines (renderResponse s1 other))

-- ---------------------------------------------------------------------------
-- Terms, on the Haskell side

-- | A term of a generated language: a constructor and its fields.
data Tm = Tm String [Field]
  deriving (Eq, Show)

data Field = Name String | Sub Tm | Other Core
  deriving (Show)

instance Eq Field where
  Name a == Name b = a == b
  Sub a == Sub b = a == b
  Other _ == Other _ = True     -- a Ty rides along untouched
  _ == _ = False

base :: Core
base = Canonical (GlobalName "base") [] []

toCore :: Tm -> Core
toCore (Tm c fs) = Canonical (GlobalName c) [] (map field fs)
  where
    field f = case f of
      Name s -> Primitive (LString s)
      Sub t -> toCore t
      Other t -> t

-- | A closed value of a language, read back: whnf, and again under each
-- constructor. There is no normaliser, and a data value needs none.
fromCore :: GlobalEnv -> Core -> Maybe Tm
fromCore env t = case whnf env [] t of
  Canonical (GlobalName c) _ as -> Tm c <$> traverse field as
  _ -> Nothing
  where
    field a = case whnf env [] a of
      Primitive (LString s) -> Just (Name s)
      Canonical (GlobalName "base") _ _ -> Just (Other base)
      a' -> Sub <$> fromCore env a'

listOfStrings :: GlobalEnv -> Core -> Maybe [String]
listOfStrings env t = case whnf env [] t of
  Canonical (GlobalName "nil") _ _ -> Just []
  Canonical (GlobalName "cons") _ as | [h, r] <- lastTwo as -> case whnf env [] h of
    Primitive (LString s) -> (s :) <$> listOfStrings env r
    _ -> Nothing
  _ -> Nothing
  where lastTwo as = drop (length as - 2) as

-- | A global applied, at level zero for every level it takes.
call :: GlobalEnv -> String -> [Core] -> Core
call env f = foldl App (Global (GlobalName f) (replicate levels LZero))
  where levels = maybe 0 (length . definitionLevels) (lookupDefinition (GlobalName f) env)

stringList :: GlobalEnv -> [String] -> Core
stringList env = foldr (\s r -> call env "cons" [str, Primitive (LString s), r]) (call env "nil" [str])
  where str = Global (GlobalName "String") []

-- | A simultaneous map, as @List (And String L)@.
substMap :: GlobalEnv -> String -> [(String, Tm)] -> Core
substMap env lang = foldr (\(k, t) r -> call env "cons" [pair, both k t, r]) (call env "nil" [pair])
  where
    pair = call env "And" [str, Global (GlobalName lang) []]
    both k t = call env "both" [str, Global (GlobalName lang) [], Primitive (LString k), toCore t]
    str = Global (GlobalName "String") []

-- | The roles of a language's constructors, as the environment records them.
rolesOf :: GlobalEnv -> String -> [(String, [ArgRole])]
rolesOf env lang = case lookupInductive (GlobalName lang) env of
  Just d -> [ (n, constructorRoles c) | c <- inductiveConstructors d, let GlobalName n = constructorName c ]
  Nothing -> []

-- ---------------------------------------------------------------------------
-- The oracle

-- | Free variables, from the roles.
freeVars :: [(String, [ArgRole])] -> Tm -> [String]
freeVars roles (Tm c fs) = nub (concat (zipWith go (roleList roles c) fs))
  where
    go r f = case (r, f) of
      (Occurrence, Name s) -> [s]
      (Plain, Sub t) -> freeVars roles t
      (Scope bs, Sub t) -> filter (`notElem` [ n | i <- bs, Name n <- [fs !! i] ]) (freeVars roles t)
      _ -> []

roleList :: [(String, [ArgRole])] -> String -> [ArgRole]
roleList roles c = fromMaybe [] (lookup c roles)

-- | De Bruijn form: a binder's name is erased, and an occurrence is the index
-- of the innermost binder of that name in scope, or free by name.
data DB = DVar Int | DFree String | DNode String [DField]
  deriving (Eq, Show)

data DField = DBinder | DSub DB | DKept
  deriving (Eq, Show)

nameless :: [(String, [ArgRole])] -> [String] -> Tm -> DB
nameless roles stack (Tm c fs) = case (roleList roles c, fs) of
  ([Occurrence], [Name s]) -> maybe (DFree s) DVar (elemIndex s stack)
  (rs, _) -> DNode c (zipWith field rs fs)
  where
    field r f = case (r, f) of
      (Binder, _) -> DBinder
      (Scope bs, Sub t) -> DSub (nameless roles (reverse [ n | i <- bs, Name n <- [fs !! i] ] ++ stack) t)
      (_, Sub t) -> DSub (nameless roles stack t)
      _ -> DKept

-- | Substitution without names: nothing can be captured, because a
-- replacement has no index in it to be captured by.
namelessSubst :: [(String, [ArgRole])] -> [(String, Tm)] -> DB -> DB
namelessSubst roles sigma t = case t of
  DFree s -> maybe t (nameless roles []) (lookup s sigma)
  DVar _ -> t
  DNode c fs -> DNode c [ case f of DSub u -> DSub (namelessSubst roles sigma u); _ -> f | f <- fs ]

-- ---------------------------------------------------------------------------
-- Generators

names :: [String]
names = ["x", "y", "x'", "z"]

genLC :: Gen Tm
genLC = sized go
  where
    go 0 = var <$> elements names
    go k = oneof
      [ var <$> elements names
      , (\x e -> Tm "abs" [Name x, Other base, Sub e]) <$> elements names <*> go (k `div` 2)
      , (\a b -> Tm "app" [Sub a, Sub b]) <$> go (k `div` 2) <*> go (k `div` 2)
      ]
    var x = Tm "var" [Name x]

genLB :: Gen Tm
genLB = sized go
  where
    go 0 = var <$> elements names
    go k = oneof
      [ var <$> elements names
      , (\x y p -> Tm "lam2" [Name x, Name y, Sub p]) <$> elements names <*> elements names <*> go (k `div` 2)
      , (\x y p q -> Tm "half" [Name x, Name y, Sub p, Sub q])
          <$> elements names <*> elements names <*> go (k `div` 3) <*> go (k `div` 3)
      , (\a b -> Tm "bapp" [Sub a, Sub b]) <$> go (k `div` 2) <*> go (k `div` 2)
      ]
    var x = Tm "bvar" [Name x]

genMap :: Gen Tm -> Gen [(String, Tm)]
genMap g = listOf ((,) <$> elements names <*> g)

-- ---------------------------------------------------------------------------

declared :: IO GlobalEnv -> [TestTree]
declared io =
  [ testCase (f ++ " : " ++ ty) $ do
      env <- io
      case lookupDefinition (GlobalName f) env of
        Nothing -> assertFailure (f ++ " was not declared")
        Just d -> (unlevelled (renderCore 0 [] (definitionType d)), length (definitionLevels d))
                    @?= (ty, levels)
  -- **A level parameter for every level nothing fixes**: List and And are
  -- polymorphic and a list of names is a list at any level, so the functions
  -- that mention them are too. Nothing is defaulted (his ruling), so this is
  -- what the type is, and it is asserted rather than printed away.
  | (f, ty, levels) <-
      [ ("LC-fresh", "String -> List String -> String", 1)
      , ("LC-fv", "LC -> List String", 1)
      , ("LC-subst-all", "LC -> List (And String LC) -> LC", 3)
      , ("LC-subst", "LC -> String -> LC -> LC", 0)
      , ("LB-subst", "LB -> String -> LB -> LB", 0)
      ]
  ]
    ++ [ testCase "a language with no occurrence gets none" $ do
           env <- io
           map (\f -> isNothing (lookupDefinition (GlobalName f) env))
               ["Ty-fresh", "Ty-fv", "Ty-subst-all", "Ty-subst"]
             @?= [True, True, True, True]
       ]

-- | A printed type with its level arguments taken out: @List {ℓ₇} String@
-- is @List String@. The count is asserted beside it.
unlevelled :: String -> String
unlevelled s = case break (== '{') s of
  (before, _ : rest) -> before ++ unlevelled (drop 2 (dropWhile (/= '}') rest))
  (before, []) -> before

worked :: IO GlobalEnv -> [TestTree]
worked io =
  [ subst "a free occurrence is replaced" (abs' "y" (app' (var "x") (var "y"))) "x" (var "z")
      (abs' "y" (app' (var "z") (var "y")))
  , subst "a binder that would capture is primed" (abs' "y" (app' (var "x") (var "y"))) "x" (var "y")
      (abs' "y'" (app' (var "y") (var "y'")))
  , subst "and primed again past a name already taken"
      (abs' "y" (abs' "y'" (app' (var "x") (app' (var "y") (var "y'"))))) "x" (var "y")
      (abs' "y'" (abs' "y''" (app' (var "y") (app' (var "y'") (var "y''")))))
  , subst "a bound occurrence is not replaced" (abs' "x" (var "x")) "x" (var "y") (abs' "x" (var "x"))
  , testCase "a list is simultaneous: x and y swap" $ do
      env <- io
      fromCore env (call env "LC-subst-all"
                      [toCore (app' (var "x") (var "y")), substMap env "LC" [("x", var "y"), ("y", var "x")]])
        @?= Just (app' (var "y") (var "x"))
  , testCase "of two pairs for one name, the first is the one taken" $ do
      env <- io
      fromCore env (call env "LC-subst-all"
                      [toCore (var "x"), substMap env "LC" [("x", var "y"), ("x", var "z")]])
        @?= Just (var "y")
  -- Two binders in one production: x must be primed, and its first priming is
  -- the second binder's own name. Taking it would put two x' round a body
  -- that means two different things by them.
  , testCase "a primed binder does not take a later binder's name" $ do
      env <- io
      let t = Tm "lam2" [Name "x", Name "x'", Sub (bapp (bvar "x") (bapp (bvar "x'") (bvar "z")))]
      fromCore env (call env "LB-subst" [toCore t, Primitive (LString "z"), toCore (bvar "x")])
        @?= Just (Tm "lam2" [Name "x''", Name "x'", Sub (bapp (bvar "x''") (bapp (bvar "x'") (bvar "x")))])
  , testCase "free variables, each once here, bound ones not at all" $ do
      env <- io
      listOfStrings env (call env "LC-fv" [toCore (abs' "y" (app' (var "x") (var "y")))]) @?= Just ["x"]
  , testCase "a fresh name is the first priming not taken" $ do
      env <- io
      map (\avoid -> whnf env [] (call env "LC-fresh" [Primitive (LString "x"), stringList env avoid]))
          [[], ["y"], ["x"], ["x", "x'"], ["x'", "x"]]
        @?= map (Primitive . LString) ["x", "x", "x'", "x''", "x''"]
  -- The kernel gap found building this phase: refl at a closed String.
  , testCase "a module can state a substitution's answer, and refl proves it" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource s0 source
          (s2, r) = loadProofSource s1 (unlines
            [ "module Worked where"
            , ""
            , "captured : Eq LC (LC-subst (abs \"y\" base (var \"x\")) \"x\" (var \"y\")) (abs \"y'\" base (var \"y\"))"
            , "captured = refl LC (abs \"y'\" base (var \"y\"))"
            , ""
            , "named : Eq String \"a\" \"a\""
            , "named = refl String \"a\""
            ])
      unwords (renderResponse s2 r) @?= "module Worked   declared captured   declared named"
  , testCase "and a wrong answer is refused" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource s0 source
          (_, r) = loadProofSource s1 (unlines
            [ "module Wrong where"
            , ""
            , "captured : Eq LC (LC-subst (abs \"y\" base (var \"x\")) \"x\" (var \"y\")) (abs \"y\" base (var \"y\"))"
            , "captured = refl LC (abs \"y\" base (var \"y\"))"
            ])
      case r of
        ProofLoaded {} -> assertFailure "a capturing answer was accepted"
        _ -> pure ()
  ]
  where
    subst what t x n want = testCase what $ do
      env <- io
      fromCore env (call env "LC-subst" [toCore t, Primitive (LString x), toCore n]) @?= Just want
    var x = Tm "var" [Name x]
    abs' x e = Tm "abs" [Name x, Other base, Sub e]
    app' a b = Tm "app" [Sub a, Sub b]
    bvar x = Tm "bvar" [Name x]
    bapp a b = Tm "bapp" [Sub a, Sub b]

crossing :: IO GlobalEnv -> [TestTree]
crossing io =
  [ namelessly "LC" 300 genLC
  , namelessly "LB" 100 genLB
  , testProperty "LC: a binder keeps its name unless keeping it would capture" $
      withNumTests 300 $ forAll ((,,) <$> elements names <*> genLC <*> genMap genLC) $ \(x, e, sigma) ->
        ioProperty $ do
          env <- io
          let roles = rolesOf env "LC"
              t = Tm "abs" [Name x, Other base, Sub e]
              image w = maybe [w] (freeVars roles) (lookup w sigma)
              avoid = concatMap image (freeVars roles t)
              want = until (`notElem` avoid) (++ "'") x
          -- Only the binder is read: the body is the crossing's business.
          pure $ case whnf env [] (call env "LC-subst-all" [toCore t, substMap env "LC" sigma]) of
            Canonical (GlobalName "abs") _ (z : _) -> whnf env [] z === Primitive (LString want)
            other -> counterexample (show other) False
  , testProperty "LC: the free variables are the free variables" $
      withNumTests 300 $ forAll genLC $ \t -> ioProperty $ do
        env <- io
        pure $ fmap (sort . nub) (listOfStrings env (call env "LC-fv" [toCore t]))
          === Just (sort (freeVars (rolesOf env "LC") t))
  ]
  where
    -- **Bounded in size**, because reading a value back is whnf under every
    -- constructor with no sharing between them, and a random map under two
    -- binders a production made that minutes. The kernel is not the slow part:
    -- a refl proof six binders deep is checked in a fifth of a second.
    namelessly lang n gen =
      testProperty (lang ++ ": named substitution is nameless substitution") $
        withNumTests n $ forAll (resize 8 ((,) <$> gen <*> genMap gen)) $ \(t, sigma) -> ioProperty $ do
          env <- io
          let roles = rolesOf env lang
              got = fromCore env (call env (lang ++ "-subst-all") [toCore t, substMap env lang sigma])
          pure $ counterexample (show got) $
            fmap (nameless roles []) got === Just (namelessSubst roles sigma (nameless roles [] t))

-- ---------------------------------------------------------------------------

-- | What §4.7 needs of a language before it can generate, each refused with its
-- message. A fresh session each, so nothing one declares is in the next.
refused :: [TestTree]
refused =
  [ refusal "binders and no variable production"
      ["language L, M where", "  lam : x as binder -> ( \955 x . M[x] )"]
      "refused: in the grammar of L: it has binders, so it needs a production \8249x\8250 as occurrence for a renamed binder to become"
  , refusal "two variable productions"
      ["language L, M where", "  v1 : x as occurrence -> x", "  v2 : x as occurrence -> $ x"]
      "refused: in the grammar of L: v1, v2 all declare an occurrence, and a language has one variable production"
  , refusal "an occurrence beside something else"
      ["language L, M where", "  v : x as occurrence -> x ^ M"]
      "refused: in the grammar of L, production v: the occurrence x must be the production's only argument, because substitution replaces the whole of it"
  , refusal "a binder free in another language"
      [ "language K, A where", "  k -> k", ""
      , "language L, M where", "  v : x as occurrence -> x", "  bind : x as binder -> ( \955 x . A[x] )" ]
      "refused: in the grammar of L, production bind: a binder is free in A, which is not of this language, so substitution could not rename in it"
  , refusal "a generated name already declared"
      ["L-fv : String", "L-fv = \"taken\"", "", "language L, M where", "  v : x as occurrence -> x"]
      "refused: L's substitution function L-fv is already declared"
  ]
  where
    refusal what body want = testCase what $ do
      (s0, _) <- startingSession
      let (s1, r) = loadProofSource s0 (unlines
            (["module Refused where", "", "x : Token String", "x = /[a-z]+/", ""] ++ body))
      last (renderResponse s1 r) @?= want

-- ---------------------------------------------------------------------------
-- Following the decision (MS6 phase 109a, ms6/CLOSEOUT.md 32)

-- | **What @decString@ was for.** At @var y@ the generated code eliminates
-- @decString y x@; a proof about a name it does not know eliminates the same
-- term, and each branch hands it the evidence it needs. With @eqString@ there
-- the @same@ branch had no @Eq String y x@ and neither lemma could be stated
-- and proved. These are the base case of the substitution lemma phase 109b
-- builds.
followed :: [TestTree]
followed =
  [ testCase "x[x -> N] is N, and y[x -> N] is y when y is not x, for names nobody knows" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 (source ++ unlines lemmas) of
        (_, ProofLoaded {}) -> pure ()
        (s1, other) -> assertFailure (unlines (renderResponse s1 other))
  ]
  where
    lemmas =
      [ ""
      , "absurdly : forall (C : Type\8320) (e : Empty) -> C"
      , "absurdly = \\ C e -> elim Empty () (\\ t -> C) () () e"
      , ""
      , "varHit : forall (x : String) (N : LC) -> Eq LC (LC-subst (var x) x N) N"
      , "varHit = \\ x N ->"
      , "  elim Dec ((Eq String x x))"
      , "    (\\ d -> Eq LC (elim Dec ((Eq String x x)) (\\ d -> LC) ((\\ p -> N) (\\ n -> var x)) () d) N)"
      , "    ((\\ p -> refl LC N) (\\ n -> absurdly (Eq LC (var x) N) (n (refl String x))))"
      , "    () (decString x x)"
      , ""
      , "varMiss : forall (y : String) (x : String) (N : LC) (ne : Eq String y x -> Empty) -> Eq LC (LC-subst (var y) x N) (var y)"
      , "varMiss = \\ y x N ne ->"
      , "  elim Dec ((Eq String y x))"
      , "    (\\ d -> Eq LC (elim Dec ((Eq String y x)) (\\ d -> LC) ((\\ p -> N) (\\ n -> var y)) () d) (var y))"
      , "    ((\\ p -> absurdly (Eq LC N (var y)) (ne p)) (\\ n -> refl LC (var y)))"
      , "    () (decString y x)"
      ]

