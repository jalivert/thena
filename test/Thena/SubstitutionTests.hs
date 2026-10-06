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
import Thena.Driver
  ( Response (..)
  , machineOf
  , loadProofSource
  )
import Thena.Errors (Warning (..))
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
import Thena.Files (startingSession)
import Thena.Render ( Rendering (..)
  ,renderCore, renderResponse)

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
      , testGroup "a class that refuses a prime (MS6 closeout 23)" primed
      , testGroup "more than one class (MS8 phase 155)" classes
      ]

-- ---------------------------------------------------------------------------
-- The priming character (MS6 closeout 23, phase 146)

-- | A language whose identifier class refuses @'@ — the case the closeout item
-- is about. @L-fresh@ used to append @'@ unconditionally, so a binder renamed to
-- avoid capture became a name the notation could not write: it printed inside a
-- splice, and an object grammar has no splice production, so the printed term
-- could not be read back at all.
--
-- **The two definitions at the end are the assertions, and the load is what runs
-- them.** Conversion reduces @PL-fresh-n@ fully, so @mintsALetter@ type-checks only
-- if the generated code appends a character @\/[a-z]+\/@ accepts; and
-- @readsBack@ type-checks only if the notation can write that name, which is the
-- half that was lost.
primedSource :: String
primedSource =
  unlines
    [ "module Primed where"
    , ""
    , "n : Token String"
    , "n = /[a-z]+/"
    , ""
    , "language PL, M, N, E where"
    , "  pvar : n as occurrence -> n"
    , "  pabs : n as binder     -> ( lam n . E[n] )"
    , "  papp                   -> ( M N )"
    , ""
    , "mintsALetter : Eq String (PL-fresh-n \"y\" (cons String \"y\" (nil String))) \"ya\""
    , "mintsALetter = refl String \"ya\""
    , ""
    , "readsBack : Eq PL (pabs \"ya\" (pvar \"y\")) PL`( lam ya . y )`"
    , "readsBack = refl PL PL`( lam ya . y )`"
    ]

-- | A class no single character extends: nothing may follow @a1@. The generated
-- code keeps @'@ and says so, rather than refusing the language.
unprimeableSource :: String
unprimeableSource =
  unlines
    [ "module Unprimeable where"
    , ""
    , "f : Token String"
    , "f = /[a-z][0-9]/"
    , ""
    , "language K, P, Q, R where"
    , "  kvar : f as occurrence -> f"
    , "  kabs : f as binder     -> ( lam f . R[f] )"
    ]

primed :: [TestTree]
primed =
  [ testCase "the generated fresh mints a name the class accepts, and it reads back" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 primedSource of
        (_, ProofLoaded {}) -> pure ()
        (s1, other) -> assertFailure (unlines (renderResponse s1 other))
  , -- **A warning, not a refusal** — his second principle. The language works and
    -- its substitution is correct; only printing a renamed binder is lost.
    testCase "a class no character extends warns rather than being refused" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 unprimeableSource of
        (_, ProofLoaded _ _ _ ws)
          | any isUnprimeable ws -> pure ()
          | otherwise -> assertFailure ("loaded, but did not warn: " ++ show ws)
        (s1, other) -> assertFailure (unlines (renderResponse s1 other))
  ]
  where
    isUnprimeable w = case w of
      UnprimeableClass _ _ _ -> True
      _ -> False

-- ---------------------------------------------------------------------------
-- More than one class (MS8 phase 155, `~tmnrr` and `~5k3mg`)

-- | **One language, two notions of a variable** — `~tmnrr`'s half. Two
-- occurrence productions at two different classes, which MS6 refused outright
-- and which is now one substitution family per class over one simultaneous
-- @D-subst-all@.
twoOwnSource :: String
twoOwnSource =
  unlines
    [ "module TwoOwn where"
    , ""
    , "x : Token String"
    , "x = /[a-z]+/"
    , ""
    , "i : Token String"
    , "i = /[A-Z]+/"
    , ""
    , "language D, M where"
    , "  dvar : x as occurrence -> x"
    , "  dlab : i as occurrence -> ' i"
    , "  dabs : x as binder     -> ( lam x . M[x] )"
    , "  dlev : i as binder     -> ( lev i . M[i] )"
    ]

-- | **F-sub in miniature** — `~5k3mg`'s half, and the reason the milestone has
-- this item. @Ty@ owns the type class @X@; @Tm@ owns the term class @x@ and
-- /binds/ @X@ from a term production, while every occurrence of @X@ is in a
-- type. So @Tm@ reaches a class it does not own, and @Tm-subst-X@ — type
-- substitution into a term — is the function POPLMark part 2A is written with.
--
-- **The three definitions at the end are the assertions and the load runs
-- them.** @captured@ is his own counterexample of 2026-10-04: substituting a
-- term whose free /type/ variable is @X@ under a binder of @X@ must rename that
-- binder, and renaming only the term binders would capture it.
fsubSource :: String
fsubSource =
  unlines
    [ "module Fsub where"
    , ""
    , "x : Token String"
    , "x = /[a-z][a-zA-Z0-9']*/"
    , ""
    , "X : Token String"
    , "X = /[A-Z][a-zA-Z0-9']*/"
    , ""
    , "language Ty, T, S where"
    , "  tvar : X as occurrence -> X"
    , "  top                    -> Top"
    , "  fun                    -> ( T -> S )"
    , "  poly : X as binder     -> ( forall X <: T . S[X] )"
    , ""
    , "language Tm, M, N where"
    , "  var  : x as occurrence -> x"
    , "  abs  : x as binder     -> ( lam x : T . M[x] )"
    , "  tabs : X as binder     -> ( Lam X <: T . M[X] )"
    , "  tapp                   -> ( M @ T )"
    , ""
    , "captured : Eq Tm (Tm-subst-x (tabs \"X\" top (var \"z\")) \"z\" (abs \"y\" (tvar \"X\") (var \"y\")))"
    , "                 (tabs \"X'\" top (abs \"y\" (tvar \"X\") (var \"y\")))"
    , "captured = refl Tm (tabs \"X'\" top (abs \"y\" (tvar \"X\") (var \"y\")))"
    , ""
    , "untouched : Eq Tm (Tm-subst-x (tabs \"X\" top (var \"z\")) \"z\" (var \"w\"))"
    , "                  (tabs \"X\" top (var \"w\"))"
    , "untouched = refl Tm (tabs \"X\" top (var \"w\"))"
    , ""
    , "intoTheType : Eq Tm (Tm-subst-X (abs \"y\" (tvar \"Z\") (var \"y\")) \"Z\" top)"
    , "                    (abs \"y\" top (var \"y\"))"
    , "intoTheType = refl Tm (abs \"y\" top (var \"y\"))"
    ]

classes :: [TestTree]
classes =
  [ testCase "two occurrence productions at two classes install, one family each" $ do
      env <- loadedFrom twoOwnSource
      [ typeOf env f | f <- [ "D-fresh-x", "D-fresh-i", "D-fv-x", "D-fv-i"
                            , "D-subst-all", "D-subst-x", "D-subst-i" ] ]
        @?= [ Just "String -> List String -> String"
            , Just "String -> List String -> String"
            , Just "D -> List String"
            , Just "D -> List String"
            , Just "D -> List (And String D) -> List (And String D) -> D"
            , Just "D -> String -> D -> D"
            , Just "D -> String -> D -> D"
            ]
    -- **The headline of the phase**: a map per class, and the class's map is a
    -- map into the language that OWNS it, so substituting @X@ into a term takes
    -- a type.
    -- **Two unrelated languages may read one token class**, each the owner for
    -- itself, and that is the ordinary case: @x : Token String@ is declared once
    -- and every language in the file uses it.
  , testCase "two languages that do not hold each other may read one class" $ do
      env <- loadedFrom (unlines
        [ "module Shared where", ""
        , "x : Token String", "x = /[a-z]+/", ""
        , "language K, A where", "  kvar : x as occurrence -> x", ""
        , "language L, M where", "  lvar : x as occurrence -> x" ])
      [ typeOf env f | f <- ["K-subst-x", "L-subst-x"] ]
        @?= [Just "K -> String -> K -> K", Just "L -> String -> L -> L"]
  , testCase "a class another language owns gives a substitution into that language" $ do
      env <- loadedFrom fsubSource
      [ typeOf env f | f <- [ "Tm-subst-all", "Tm-subst-x", "Tm-subst-X", "Tm-fv-X"
                            , "Tm-fresh-X", "Ty-fresh-X", "Ty-subst-all" ] ]
        @?= [ Just "Tm -> List (And String Tm) -> List (And String Ty) -> Tm"
            , Just "Tm -> String -> Tm -> Tm"
            , Just "Tm -> String -> Ty -> Tm"
            , Just "Tm -> List String"
              -- Minting a name of a class belongs to the language that owns it.
            , Nothing
            , Just "String -> List String -> String"
            , Just "Ty -> List (And String Ty) -> Ty"
            ]
  ]
  where
    -- The load is the assertion for @fsubSource@: its three definitions do not
    -- type-check unless the generated functions compute what they must.
    loadedFrom src = do
      (s0, _) <- startingSession
      case loadProofSource s0 src of
        (s1, ProofLoaded {}) -> pure (globals (machineOf s1))
        (s1, other) -> assertFailure (unlines (renderResponse s1 other))
    typeOf env f =
      unlevelled . renderCore (Rendering [] 0) [] . definitionType
        <$> lookupDefinition (GlobalName f) env

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
    (s1, ProofLoaded {}) -> pure (globals (machineOf s1))
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

-- | Free variables **at one class**, from the roles (class-aware at MS8 phase
-- 155). A binder of another class binds none of these: a class is a namespace,
-- and that is the whole of what the class on a role is for.
freeVars :: [(String, [ArgRole])] -> GlobalName -> Tm -> [String]
freeVars roles cls (Tm c fs) = nub (concat (zipWith go (roleList roles c) fs))
  where
    go r f = case (r, f) of
      (Occurrence k, Name s) | k == cls -> [s]
      (Plain, Sub t) -> freeVars roles cls t
      (Scope bs, Sub t) -> filter (`notElem` boundAt roles c fs cls bs) (freeVars roles cls t)
      _ -> []

-- | The names a scope's binder positions bind **at one class**.
boundAt :: [(String, [ArgRole])] -> String -> [Field] -> GlobalName -> [Int] -> [String]
boundAt roles c fs cls bs =
  [ n | i <- bs, Binder k <- [roleList roles c !! i], k == cls, Name n <- [fs !! i] ]

roleList :: [(String, [ArgRole])] -> String -> [ArgRole]
roleList roles c = fromMaybe [] (lookup c roles)

-- | De Bruijn form: a binder's name is erased, and an occurrence is the index
-- of the innermost binder of that name in scope, or free by name.
data DB = DVar GlobalName Int | DFree GlobalName String | DNode String [DField]
  deriving (Eq, Show)

data DField = DBinder | DSub DB | DKept
  deriving (Eq, Show)

-- | **One stack per class** (MS8 phase 155): an occurrence at class @k@ is the
-- index of the innermost class-@k@ binder of that name, and a binder of another
-- class is not on that stack at all. With one stack this said that
-- @λλ a z . bvar z@ bound its @z@ whichever class the second binder was at,
-- which is the conflation @BinderClassUnowned@ used to warn about.
nameless :: [(String, [ArgRole])] -> [(GlobalName, [String])] -> Tm -> DB
nameless roles stacks (Tm c fs) = case (roleList roles c, fs) of
  ([Occurrence k], [Name s]) ->
    maybe (DFree k s) (DVar k) (elemIndex s (fromMaybe [] (lookup k stacks)))
  (rs, _) -> DNode c (zipWith field rs fs)
  where
    field r f = case (r, f) of
      (Binder _, _) -> DBinder
      (Scope bs, Sub t) -> DSub (nameless roles (foldr push stacks (classesOf bs)) t)
        where
          classesOf js = nub [ k | i <- js, Binder k <- [roleList roles c !! i] ]
          push k ss = (k, reverse (boundAt roles c fs k bs) ++ fromMaybe [] (lookup k ss))
                        : filter ((/= k) . fst) ss
      (_, Sub t) -> DSub (nameless roles stacks t)
      _ -> DKept

-- | Substitution at one class, without names: nothing can be captured, because a
-- replacement has no index in it to be captured by.
namelessSubst :: [(String, [ArgRole])] -> GlobalName -> [(String, Tm)] -> DB -> DB
namelessSubst roles cls sigma t = case t of
  DFree k s | k == cls -> maybe t (nameless roles []) (lookup s sigma)
  DNode c fs ->
    DNode c [ case f of DSub u -> DSub (namelessSubst roles cls sigma u); _ -> f | f <- fs ]
  _ -> t

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
        Just d -> (unlevelled (renderCore (Rendering [] 0) [] (definitionType d)), length (definitionLevels d))
                    @?= (ty, levels)
  -- **A level parameter for every level nothing fixes**: List and And are
  -- polymorphic and a list of names is a list at any level, so the functions
  -- that mention them are too. Nothing is defaulted (his ruling), so this is
  -- what the type is, and it is asserted rather than printed away.
  | (f, ty, levels) <-
      [ ("LC-fresh-x", "String -> List String -> String", 1)
      , ("LC-fv-x", "LC -> List String", 1)
      , ("LC-subst-all", "LC -> List (And String LC) -> LC", 3)
      , ("LC-subst-x", "LC -> String -> LC -> LC", 0)
      , ("LB-subst-x", "LB -> String -> LB -> LB", 0)
      ]
  ]
    ++ [ testCase "a language that reaches no class gets none" $ do
           env <- io
           map (\f -> isNothing (lookupDefinition (GlobalName f) env))
               ["Ty-fresh-x", "Ty-fv-x", "Ty-subst-all", "Ty-subst-x"]
             @?= [True, True, True, True]
         -- **A class only ever bound gets nothing** (MS8 phase 155): @LB@'s
         -- @y@ is a second binder class that no occurrence production reads, so
         -- nothing can occur at it, a map into it would be a map into no
         -- language's terms, and a @y@ binder is never renamed. This is the case
         -- @BinderClassUnowned@ warned about, correct rather than said.
       , testCase "a class that is only bound gets none, and is not renamed" $ do
           env <- io
           map (\f -> isNothing (lookupDefinition (GlobalName f) env))
               ["LB-fresh-y", "LB-fv-y", "LB-subst-y"]
             @?= [True, True, True]
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
      fromCore env (call env "LB-subst-x" [toCore t, Primitive (LString "z"), toCore (bvar "x")])
        @?= Just (Tm "lam2" [Name "x''", Name "x'", Sub (bapp (bvar "x''") (bapp (bvar "x'") (bvar "x")))])
  , testCase "free variables, each once here, bound ones not at all" $ do
      env <- io
      listOfStrings env (call env "LC-fv-x" [toCore (abs' "y" (app' (var "x") (var "y")))]) @?= Just ["x"]
  , testCase "a fresh name is the first priming not taken" $ do
      env <- io
      map (\avoid -> whnf env [] (call env "LC-fresh-x" [Primitive (LString "x"), stringList env avoid]))
          [[], ["y"], ["x"], ["x", "x'"], ["x'", "x"]]
        @?= map (Primitive . LString) ["x", "x", "x'", "x''", "x''"]
  -- The kernel gap found building this phase: refl at a closed String.
  , testCase "a module can state a substitution's answer, and refl proves it" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource s0 source
          (s2, r) = loadProofSource s1 (unlines
            [ "module Worked where"
            , ""
            , "captured : Eq LC (LC-subst-x (abs \"y\" base (var \"x\")) \"x\" (var \"y\")) (abs \"y'\" base (var \"y\"))"
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
            , "captured : Eq LC (LC-subst-x (abs \"y\" base (var \"x\")) \"x\" (var \"y\")) (abs \"y\" base (var \"y\"))"
            , "captured = refl LC (abs \"y\" base (var \"y\"))"
            ])
      case r of
        ProofLoaded {} -> assertFailure "a capturing answer was accepted"
        _ -> pure ()
  ]
  where
    subst what t x n want = testCase what $ do
      env <- io
      fromCore env (call env "LC-subst-x" [toCore t, Primitive (LString x), toCore n]) @?= Just want
    var x = Tm "var" [Name x]
    abs' x e = Tm "abs" [Name x, Other base, Sub e]
    app' a b = Tm "app" [Sub a, Sub b]
    bvar x = Tm "bvar" [Name x]
    bapp a b = Tm "bapp" [Sub a, Sub b]

crossing :: IO GlobalEnv -> [TestTree]
crossing io =
  [ namelessly "LC" "x" 300 genLC
  , namelessly "LB" "x" 100 genLB
  , testProperty "LC: a binder keeps its name unless keeping it would capture" $
      withNumTests 300 $ forAll ((,,) <$> elements names <*> genLC <*> genMap genLC) $ \(x, e, sigma) ->
        ioProperty $ do
          env <- io
          let roles = rolesOf env "LC"
              t = Tm "abs" [Name x, Other base, Sub e]
              image w = maybe [w] (freeVars roles (GlobalName "x")) (lookup w sigma)
              avoid = concatMap image (freeVars roles (GlobalName "x") t)
              want = until (`notElem` avoid) (++ "'") x
          -- Only the binder is read: the body is the crossing's business.
          pure $ case whnf env [] (call env "LC-subst-all" [toCore t, substMap env "LC" sigma]) of
            Canonical (GlobalName "abs") _ (z : _) -> whnf env [] z === Primitive (LString want)
            other -> counterexample (show other) False
  , testProperty "LC: the free variables are the free variables" $
      withNumTests 300 $ forAll genLC $ \t -> ioProperty $ do
        env <- io
        pure $ fmap (sort . nub) (listOfStrings env (call env "LC-fv-x" [toCore t]))
          === Just (sort (freeVars (rolesOf env "LC") (GlobalName "x") t))
  ]
  where
    -- **Bounded in size**, because reading a value back is whnf under every
    -- constructor with no sharing between them, and a random map under two
    -- binders a production made that minutes. The kernel is not the slow part:
    -- a refl proof six binders deep is checked in a fifth of a second.
    namelessly lang cls n gen =
      testProperty (lang ++ ": named substitution is nameless substitution") $
        withNumTests n $ forAll (resize 8 ((,) <$> gen <*> genMap gen)) $ \(t, sigma) -> ioProperty $ do
          env <- io
          let roles = rolesOf env lang
              got = fromCore env (call env (lang ++ "-subst-all") [toCore t, substMap env lang sigma])
          pure $ counterexample (show got) $
            fmap (nameless roles []) got
              === Just (namelessSubst roles (GlobalName cls) sigma (nameless roles [] t))

-- ---------------------------------------------------------------------------

-- | What §4.7 needs of a language before it can generate, each refused with its
-- message. A fresh session each, so nothing one declares is in the next.
refused :: [TestTree]
refused =
    -- **Two occurrence productions at ONE class** (narrowed at MS8 phase 155):
    -- at two different classes they are two notions of a variable, which is the
    -- point of the phase, and the install case below is the pair of this one.
  [ refusal "two variable productions at one class"
      ["language L, M where", "  v1 : x as occurrence -> x", "  v2 : x as occurrence -> $ x"]
      "refused: in the grammar of L: v1, v2 all declare an occurrence at x, and a language has one variable production per class"
    -- **A class a grammar reaches belongs to one of the languages it reaches**
    -- (MS8 phase 155): what a renamed name of the class becomes is that
    -- language's variable production, and the map substituting for it is a map
    -- into that language's terms, so reaching two leaves both undetermined.
    -- **Two unrelated languages reading one class is ordinary** and is the test
    -- below this list; it is holding a slot of the other that refuses.
  , refusal "a class reached through two languages that both read it"
      [ "language K, A where", "  kvar : x as occurrence -> x", ""
      , "language L, M where", "  v : x as occurrence -> x", "  box -> ( box A )" ]
      "refused: in the grammar of L: L and K both read an occurrence at x, and this grammar reaches both, so a substitution for x has no one language to replace a name with"
  , refusal "an occurrence beside something else"
      ["language L, M where", "  v : x as occurrence -> x ^ M"]
      "refused: in the grammar of L, production v: the occurrence x must be the production's only argument, because substitution replaces the whole of it"
    -- **Narrowed at MS8 phase 154** (`~5k3mg`): a binder free in another
    -- language's argument is refused only where that language reaches no
    -- occurrence at the binder's class, as @K@ does not here — so there is
    -- nothing in an @A@ that could ever be at @x@. Where it does reach the
    -- class the block installs and warns instead, which
    -- "Thena.GrammarTests" pins.
  , refusal "a binder free in a language that reaches no such class"
      [ "language K, A where", "  k -> k", ""
      , "language L, M where", "  v : x as occurrence -> x", "  bind : x as binder -> ( \955 x . A[x] )" ]
      "refused: in the grammar of L, production bind: a binder is free in A, which is of K, and nothing K reaches occurs at x, so there is nothing there to rename"
  , refusal "a generated name already declared"
      ["L-fv-x : String", "L-fv-x = \"taken\"", "", "language L, M where", "  v : x as occurrence -> x"]
      "refused: L's substitution function L-fv-x is already declared"
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
      , "varHit : forall (x : String) (N : LC) -> Eq LC (LC-subst-x (var x) x N) N"
      , "varHit = \\ x N ->"
      , "  elim Dec ((Eq String x x))"
      , "    (\\ d -> Eq LC (elim Dec ((Eq String x x)) (\\ d -> LC) ((\\ p -> N) (\\ n -> var x)) () d) N)"
      , "    ((\\ p -> refl LC N) (\\ n -> absurdly (Eq LC (var x) N) (n (refl String x))))"
      , "    () (decString x x)"
      , ""
      , "varMiss : forall (y : String) (x : String) (N : LC) (ne : Eq String y x -> Empty) -> Eq LC (LC-subst-x (var y) x N) (var y)"
      , "varMiss = \\ y x N ne ->"
      , "  elim Dec ((Eq String y x))"
      , "    (\\ d -> Eq LC (elim Dec ((Eq String y x)) (\\ d -> LC) ((\\ p -> N) (\\ n -> var y)) () d) (var y))"
      , "    ((\\ p -> absurdly (Eq LC N (var y)) (ne p)) (\\ n -> refl LC (var y)))"
      , "    () (decString y x)"
      ]

