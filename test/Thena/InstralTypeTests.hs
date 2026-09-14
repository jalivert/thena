-- | @instral@'s type language and the signature table (MS5 phase 66b).
--
-- **What is checked here is the readable half**: that a type spells the way a
-- rule author would write it, and that a representative op says what it takes.
-- The two structural properties — a signature's arity agreeing with
-- 'Thena.Instral.Ops.operandsOf', and 'Thena.Instral.Ops.produces' agreeing with the result
-- column — are not tested, because neither can fail: both are derived from one
-- case split (see 'Thena.Instral.Ops.operandTypes'). What the table's result column
-- /is/ checked against is the engine, in @RulesTests@' @produces agrees with
-- the engine@ group, which now also asserts the value's shape.
module Thena.InstralTypeTests (tests) where

import Data.List (nub)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?), (@?=))
import Test.Tasty.QuickCheck (Gen, elements, forAll, oneof, resize, sized, testProperty, (===))

import Thena.Instral.Concrete
  ( RawGItem (..)
  , RawLanguage (..)
  , RawProduction (..)
  , RawSignature (..)
  , RawTy (..)
  )
import Thena.Syntax.Lexer (lexTokens)
import Thena.Syntax.Parser (parseInstralTy)

import Thena.Instral.Type
  ( Signature (..)
  , fits
  , Ty (..)
  , renderSignature
  , renderTy
  , typeVarsIn
  )
import Thena.Instral.Ops (AnswerKind (..), Op (..), Operand (..), Value (..), signatureOf)
import qualified Thena.Instral.Ops as Op
import Thena.Instral.Ops (Test (..))
import Thena.Rules (RuleError (..), builtInTypes, opWords, resolveLanguage, resolveSignature, resolveTy, testTypes)

tests :: TestTree
tests =
  testGroup
    "Thena.Instral.Type"
    [ renderTests
    , signatureTests
    , headTests
    , fitting
    , roundTrip
    , theBuiltInTypes
    , injectivity
    ]

-- --------------------------------------------------------------------------
-- Rendering tells types apart (2026-09-12)
-- --------------------------------------------------------------------------

-- | **Two types that are not the same must not print the same.**
--
-- Every error @instral@ reports is a rendered 'Ty', so a rendering that
-- collapses two types produces a message that says nothing —
-- @wanted String, got String@, which this milestone's review met three times
-- from three unrelated causes: collapsed scheme variables, a nullary function
-- type printing as its own result, and a grammar that had taken the name
-- @String@. Each was fixed where it was found; none of them was checked.
--
-- **Exhaustive, not random**: the set below is every shape 'Ty' has, over a
-- small alphabet, one and two constructors deep. A collapse is a collision
-- between two /shapes/, which is what an enumeration finds and what a pair of
-- independently generated types almost never does.
injectivity :: TestTree
injectivity =
  testGroup
    "rendering tells two types apart"
    [ testCase "no two of the one-deep shapes print alike" $
        collisions oneDeep @?= []
    , testCase "nor any of the two-deep ones" $
        collisions twoDeep @?= []
      -- A signature is a type and an arity, and the arity is not in the type:
      -- @String -> (String -> String)@ and @String -> String -> String@ are
      -- different callables. That collapse shipped.
    , testCase "and no two signatures do either" $
        [ (renderSignature a, renderSignature b)
        | (i, a) <- zip [0 :: Int ..] signatures
        , b <- take i signatures
        , a /= b
        , renderSignature a == renderSignature b
        ] @?= []
    ]
  where
    collisions ts =
      [ (renderTy a, renderTy b)
      | (i, a) <- zip [0 :: Int ..] ts
      , b <- take i ts
      , a /= b
      , renderTy a == renderTy b
      ]

    -- Two atoms of each kind that has a kind: a constructor, a variable, and an
    -- object language's brand, which is the one whose name is not Thena's.
    alphabet = [TString, TCore, TVar 0, TVar 1, TObject "Tm"]

    shapesOver us =
      us
        ++ [ TList a | a <- us ]
        ++ [ TOption a | a <- us ]
        ++ [ TPair a b | a <- us, b <- us ]
        ++ [ TFun [] a | a <- us ]
        ++ [ TFun [a] b | a <- us, b <- us ]
        ++ [ TFun [a, b] c | a <- us, b <- us, c <- us ]

    oneDeep = shapesOver alphabet
    twoDeep = shapesOver (take 3 alphabet ++ take 3 (drop (length alphabet) oneDeep))

    signatures =
      [ Signature ps r
      | ps <- [] : [ [a] | a <- small ] ++ [ [a, b] | a <- small, b <- small ]
      , r  <- Nothing : map Just small
      ]
    small = [TString, TCore, TFun [] TString, TFun [TString] TString, TVar 0]

-- --------------------------------------------------------------------------
-- The built-in type names (2026-09-12)
-- --------------------------------------------------------------------------

-- | **'Thena.Rules.builtInTypes' is a list, so it is crossed with the code that
-- is supposed to agree with it.**
--
-- Two readers: 'Thena.Rules.resolveTyIn'\'s @constructor@, a @case@ with a
-- fallthrough that the compiler cannot make total, and
-- 'Thena.Rules.resolveLanguage', which refuses a grammar that would take one of
-- these names. A name in the list that @constructor@ does not know would be an
-- 'UnknownType' the arity check never reaches; a name @constructor@ knows that
-- is not in the list would be a language name left free to shadow it.
theBuiltInTypes :: TestTree
theBuiltInTypes =
  testGroup
    "every built-in type name"
    [ testCase "resolves as a type, at the arity it takes" $
        mapM_ resolves builtInTypes
    , testCase "is refused as a grammar's name" $
        mapM_ refusedAsALanguage builtInTypes
      -- The other direction: a name @constructor@ knows must be in the list, or
      -- it is a name a grammar may take and shadow. Asking at an arity nothing
      -- has separates /known/ from /unknown/, which is the split the list makes.
    , testCase "and a name outside the list is unknown, not merely misapplied" $
        resolveTy [] "q" (RawTyCon "Trm" []) @?= Left (UnknownType "q" "Trm")

      -- **The list, written out a second time on purpose.** Walking
      -- 'builtInTypes' can only check the names that are in it, so a name
      -- DROPPED from it — which would leave a grammar free to shadow that type —
      -- passes every test above by disappearing from them. This is the third
      -- party: 'renderTy' prints exactly these words and
      -- 'Thena.Rules.resolveTyIn' reads exactly these words, and a change to
      -- either has to come here and say so.
    , testCase "and the list is exactly these ten" $
        builtInTypes
          @?= [ "String", "Name", "Int", "Char", "Bool", "Surface", "Core"
              , "Development", "List", "Option"
              ]
    , testCase "…which is what renderTy prints for each of them" $
        map renderTy
            [ TString, TName, TInt, TChar, TBool, TSurface, TCore, TDevelopment
            , TList TInt, TOption TInt
            ]
          @?= [ "String", "Name", "Int", "Char", "Bool", "Surface", "Core"
              , "Development", "List Int", "Option Int"
              ]
    ]
  where
    resolves n = case (resolveTy [] "q" (RawTyCon n []), resolveTy [] "q" (RawTyCon n [RawTyCon "Core" []])) of
      (Right (Just _), _) -> pure ()
      (_, Right (Just _)) -> pure ()
      (a, b) -> assertFailure (n ++ ": " ++ show a ++ " / " ++ show b)

    refusedAsALanguage n =
      resolveLanguage (RawLanguage n [RawProduction "var" [GWord "name"]])
        @?= Left [BuiltInType n]

-- --------------------------------------------------------------------------
-- Rendering and reading are inverse (2026-09-12)
-- --------------------------------------------------------------------------

-- | **A rendered signature must read back as the same signature.**
--
-- The invariant is checked by different code from the code that maintains it,
-- which is phase 5's standing lesson: 'renderSignature' writes the arrow chain
-- and 'Thena.Rules.resolveSignature' splits one, and neither consults the
-- other. Both of this milestone's signature defects break it —
-- @a -> b -> ()@ rendering and reading back as @a -> a -> ()@ (the collapsed
-- scheme variables), and @String -> (String -> String)@ printing without its
-- parentheses and reading back at arity two.
--
-- **Up to renaming**, because the numbering is positional on both sides:
-- 'Thena.Instral.Ops.signatureOf' numbers a scheme's variables however the table wrote
-- them and 'resolveSignature' numbers them by first appearance. 'renumbered'
-- puts both in the second form.
roundTrip :: TestTree
roundTrip =
  testGroup
    "a rendered signature reads back"
    [ -- Every op there is, which is the corpus that matters: the table in
      -- "Thena.Instral.Ops" is what a reader meets through @:accepts@.
      testCase "for every op the parser knows" $
        mapM_ (returns . signatureOf . snd) opWords

      -- …and the shapes no op happens to have. A function result, a function
      -- inside a list, a pair of functions, an option of one.
    , testCase "and for the shapes no op has" $
        mapM_ returns
          [ Signature [TString] (Just (TFun [TString] TString))
          , Signature [] (Just (TFun [TVar 0] (TFun [TVar 1] (TVar 0))))
          , Signature [TList (TFun [TVar 0] TBool)] (Just (TList (TVar 0)))
          , Signature [TPair (TFun [TCore] TCore) (TFun [TSurface] TSurface)] Nothing
          , Signature [TOption (TFun [TBool] TName)] (Just (TFun [TInt, TChar] TBool))
          ]

      -- **The one type with no syntax** (@ms5\/CLOSEOUT.md@ 23). @\\ -> e@ is
      -- writable and builds a closure of no arguments, but the type language
      -- has no spelling for one — an arrow chain always has a left-hand side.
      -- So it does not read back, and what matters is only that it does not
      -- print as its own result: a clash between the two used to say
      -- /wanted String, got String/.
    , testCase "a function of no arguments prints distinctly, though it cannot be read" $ do
        renderTy (TFun [] TString) @?= "-> String"
        renderTy (TList (TFun [] TString)) @?= "List (-> String)"

    , testProperty "for any signature at all" $
        forAll genSignature $ \sg ->
          readBack (renderSignature sg) === Right (renumbered sg)
    ]
  where
    returns sg = case readBack (renderSignature sg) of
      Right got | got == renumbered sg -> pure ()
      other -> assertFailure
        (renderSignature sg ++ ": " ++ show other ++ " /= " ++ show (renumbered sg))

-- | Render's inverse: lex the text, parse a type, split the chain.
readBack :: String -> Either String Signature
readBack src = case lexTokens src of
  Left e   -> Left (show e)
  Right ts -> case parseInstralTy ts of
    Left e  -> Left (show e)
    Right t -> case resolveSignature [] (RawSignature "f" t) of
      Left e       -> Left (show e)
      Right (_, s) -> Right (renumbered s)

-- | A signature's variables, numbered by where they first appear.
renumbered :: Signature -> Signature
renumbered (Signature ps r) = Signature (map go ps) (fmap go r)
  where
    table = zip (nub (concatMap typeVarsIn (ps ++ maybe [] pure r))) [0 ..]
    go t = case t of
      TVar i    -> maybe t TVar (lookup i table)
      TList a   -> TList (go a)
      TOption a -> TOption (go a)
      TPair a b -> TPair (go a) (go b)
      TFun as q -> TFun (map go as) (go q)
      _         -> t

-- | A generated signature.
--
-- **No 'TObject'** — an object language's name is a type only where that
-- language is declared, and 'readBack' declares none. **And no empty 'TFun'**,
-- which the type language cannot write at all (@ms5\/CLOSEOUT.md@ 23).
genSignature :: Gen Signature
genSignature = sized $ \n -> do
  k  <- elements [0 .. 3]
  ps <- mapM (const (genTy (n `div` 2))) [1 .. k :: Int]
  r  <- oneof [pure Nothing, Just <$> genTy (n `div` 2)]
  pure (Signature ps r)

genTy :: Int -> Gen Ty
genTy n
  | n <= 0 = genAtom
  | otherwise =
      oneof
        [ genAtom
        , TList <$> smaller
        , TOption <$> smaller
        , TPair <$> smaller <*> smaller
        , do k  <- elements [1 .. 3]
             as <- mapM (const smaller) [1 .. k :: Int]
             TFun as <$> smaller
        ]
  where
    smaller = resize (n `div` 2) (genTy (n `div` 2))

genAtom :: Gen Ty
genAtom =
  oneof
    [ elements [TString, TName, TInt, TChar, TBool, TSurface, TCore, TDevelopment]
    , TVar <$> elements [0 .. 3]
    ]

-- | The relation @:accepts@ and @:produces@ ask (MS5 phase 71).
--
-- **One-way**: a scheme's variable may move, the asked type's may not.
fitting :: TestTree
fitting =
  testGroup
    "fits"
    [ testCase "a type fits itself" $ fits TCore TCore @?= True
    , testCase "and not another" $ fits TCore TSurface @?= False
      -- **The point of the relation.** @:accepts Core@ must list a rule whose
      -- parameter is @a@, because such a rule does accept a Core.
    , testCase "a scheme variable fits anything" $ fits (TVar 0) TCore @?= True
      -- …and the other way round it does not: asking about @a@ is asking about a
      -- variable, which only a variable answers.
    , testCase "but not the other way round" $ fits TCore (TVar 0) @?= False
      -- **Repeated variables must agree**, so @a -> a@ fits @Core -> Core@ and
      -- not @Core -> Surface@.
    , testCase "a repeated variable must agree" $
        fits (TFun [TVar 0] (TVar 0)) (TFun [TCore] TCore) @?= True
    , testCase "and disagreeing is a miss" $
        fits (TFun [TVar 0] (TVar 0)) (TFun [TCore] TSurface) @?= False
    , testCase "it goes under a constructor" $
        fits (TList (TVar 0)) (TList TInt) @?= True
    , testCase "and the constructor has to match" $
        fits (TList (TVar 0)) (TOption TInt) @?= False
      -- Arity is part of a function type (MS5 phase 68b).
    , testCase "a function of one does not fit a function of two" $
        fits (TFun [TVar 0] (TVar 1)) (TFun [TCore, TCore] TCore) @?= False
    ]

-- | Exact strings, not a round trip. Phase 2's standing lesson: a round-trip
-- property passes while a self-consistent error agrees with itself.
renderTests :: TestTree
renderTests =
  testGroup
    "rendering"
    [ testCase "the ground set" $
        map renderTy [TString, TName, TInt, TChar, TBool]
          @?= ["String", "Name", "Int", "Char", "Bool"]
    , testCase "the abstract four" $
        map renderTy [TSurface, TCore, TDevelopment]
          @?= ["Surface", "Core", "Development"]
      -- **@Name@ is not @String@ and prints as itself** — his ruling,
      -- 2026-09-12. If these two ever render the same the distinction is
      -- invisible in every message the type system will produce.
    , testCase "a name does not print as a string" $
        (renderTy TName /= renderTy TString) @?= True
    , testCase "a scheme variable is a letter" $
        map (renderTy . TVar) [0, 1, 25, 26] @?= ["a", "b", "z", "a1"]
    , testCase "a list and an option" $
        map renderTy [TList TInt, TOption TCore] @?= ["List Int", "Option Core"]
      -- A one-parameter constructor is the only place a type nests without a
      -- bracket of its own, so it is the only place parentheses are needed.
    , testCase "nesting takes parentheses" $
        renderTy (TList (TOption TInt)) @?= "List (Option Int)"
    , testCase "and a pair brings its own" $
        renderTy (TList (TPair TName TCore)) @?= "List (Name, Core)"
    , testCase "a pair needs none inside a pair" $
        renderTy (TPair (TList TInt) TBool) @?= "(List Int, Bool)"
      -- **An op that produces nothing ends in @()@**, so that the absence is
      -- something you can see rather than a word that seems to be missing.
    , testCase "no result prints as unit" $
        renderSignature (Signature [TCore] Nothing) @?= "Core -> ()"
    , testCase "and no arguments either" $
        renderSignature (Signature [] (Just TCore)) @?= "Core"
      -- **A function-typed parameter takes parentheses** (MS5 phase 73). Without
      -- them this prints as a signature of three arguments rather than two, and
      -- arity is the one thing a reader takes from a listing.
    , testCase "a function-typed parameter is parenthesised" $
        renderSignature (Signature [TFun [TString] TString, TString] (Just TString))
          @?= "(String -> String) -> String -> String"
      -- **…and so does a function-typed RESULT** (2026-09-12). Bare, the two
      -- signatures below print the same text while being different callables:
      -- one takes a @String@ and gives a function, the other takes two.
    , testCase "a function-typed result is parenthesised too" $
        renderSignature (Signature [TString] (Just (TFun [TString] TString)))
          @?= "String -> (String -> String)"
    , testCase "so the two do not print alike" $
        renderSignature (Signature [TString] (Just (TFun [TString] TString)))
          /= renderSignature (Signature [TString, TString] (Just TString))
          @? "a function result and one more argument print the same"
    , testCase "the variables a type mentions, in order" $
        typeVarsIn (TPair (TList (TVar 3)) (TOption (TVar 1))) @?= [3, 1]
    ]

-- | One op per interesting shape, pinned as the string a reader would write.
--
-- Not all 79: the table is total and @-Wall@ makes a new op answer it, so what
-- is worth pinning is the /kinds/ of answer, and the ones a later phase is most
-- likely to disturb.
signatureTests :: TestTree
signatureTests =
  testGroup
    "signatures"
    [ sig "claim"        (Claim r r)                    "Name -> Core -> Core"
    , sig "assume"       (Assume r r)                   "Name -> Core -> Core"
    , sig "quantify"     (Op.Quantify r r)              "Name -> Core -> ()"
      -- **The two halves of what was one op** (this phase). One took either a
      -- variable or a name and so had no signature at all; these are why the
      -- word was split.
    , sig "goto"         (Goto r)                       "Core -> ()"
    , sig "goto-named"   (Op.GotoNamed r)               "Name -> ()"
      -- **The coercion the shipped base needs** — @ask … name@ gives a Name and
      -- @concat@ wants a String.
    , sig "name-text"    (Op.NameText r)                "Name -> String"
    , sig "concat"       (Concat r r)                   "String -> String -> String"
    , sig "say"          (Say r)                        "String -> ()"
      -- **The kind decides what @ask@ hands back**, which is the one place a
      -- field and not an operand changes a signature.
    , sig "ask … text"   (Ask r AText)                  "String -> String"
    , sig "ask … name"   (Ask r AName)                  "String -> Name"
      -- **Core in, Core out** — his ruling: the type system does not tell an
      -- unresolved written term from a resolved one.
    , sig "resolve-core" (Op.ResolveCore r)             "Core -> Core"
    , sig "surface-name" (Op.SurfaceNameOf r)           "Surface -> Name"
    , sig "lambda-tail"  (Op.LambdaTail r)              "Surface -> Surface"
    , sig "resolve-name" (Op.ResolveName r)             "Name -> Core"
    , sig "apply-next"   (Op.ApplyNext r r)             "Core -> Name -> Core"
    , sig "here"         Here                           "Core"
    , sig "goal"         Goal                           "Core"
    , sig "prim-attack"  Attack                         "()"
      -- The data structures are where the scheme variables are.
      -- Its arity is the table's even though its types are inference's.
      --
      -- **The parentheses say it takes nothing and gives a function**
      -- (2026-09-12). Bare, this printed as @b -> a@ — the spelling of an op
      -- that takes a @b@ and gives an @a@, which is a different signature.
    , sig "lambda, one parameter"
                         (Op.Lambda [Op.PVar "x"] [])           "(b -> a)"
    , sig "some"         (Op.Some r)                    "a -> Option a"
    , sig "none"         Op.None                        "Option a"
      -- **A call says nothing**, and cannot: which clauses a name has is not
      -- known when a body is read, so every argument and the result are their
      -- own variable until phase 66c takes them from the rule.
    , sig "call, two arguments"
                         (Call "f" [r, r]) "a -> b -> c"
      -- **A variadic op is not a special shape**, because the table takes the
      -- 'Op' and not a tag: an @intro@ with a name and one without are two
      -- values, so they simply have two signatures.
    , sig "prim-lambda, named"   (IntroPi (Just r))     "Name -> ()"
    , sig "prim-lambda, unnamed" (IntroPi Nothing)      "()"
    ]
  where
    r = Lit (VText "x")
    sig label o expected =
      testCase label (renderSignature (signatureOf o) @?= expected)

-- | A head test's operands (MS5 phase 66b) — where a rule's parameters get
-- their types, and the reason this table exists before inference does.
headTests :: TestTree
headTests =
  testGroup
    "head tests"
    [ testCase "a focus question asks about nothing" $
        map snd (testTypes FocusIsHole) @?= []
    , testCase "a surface question wants a surface term" $
        map snd (testTypes (SurfaceIsLambda r)) @?= [TSurface]
    , testCase "and so does every other one" $
        map snd (testTypes (AppHeadIsName r)) @?= [TSurface]
      -- **Every head test asks about a SURFACE node now** (MS5 phase 86). The
      -- four that asked about @instral@'s own data — @list-is-empty@,
      -- @list-is-cons@, @option-is-some@, @option-is-none@ — are gone: a
      -- parameter pattern says the same thing and binds the pieces while it is
      -- at it. @PatternTests@ is where that is asserted.
    ]
  where
    r = Lit (VText "x")
