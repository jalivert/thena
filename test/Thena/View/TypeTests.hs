-- | An @instral@ type, as a frontend sees it (MS7 phase 133).
--
-- **The crossing is the whole test, and its shape is phase 132's.**
-- 'redrawType' below rebuilds 'Thena.Instral.Type.renderTy''s exact output from
-- a 'TypeView' — and it does so **with no precedence flag of its own**, which
-- is the property under test. 'Thena.Instral.Type.renderTy' carries a @Bool@
-- that says "this type stands inside another's argument" and fences on it;
-- if the view really has the fences in the tree, a redraw that cannot see that
-- flag must still agree byte for byte. Any disagreement is exactly the
-- frontend-re-derives-precedence bug @ms7\/CLOSEOUT.md@ 27 exists to prevent.
--
-- **The corpus is 'Thena.Rules.opWords' — every op in the language, with the
-- signature its table gives it.** That is the one corpus that exercises the
-- type language: measured on this branch, the shipped rule bases declare 21
-- signatures in five distinct shapes, all of them ground
-- (@Core -> Core -> Surface -> ()@ is the widest), with no function-typed
-- parameter and no scheme variable anywhere — so a crossing over rules alone
-- would be green without ever building a fence. The rule bases are still
-- crossed, because they are what a frontend actually receives; they are just
-- not what proves the fencing.
module Thena.View.TypeTests (tests) where

import Data.List (intercalate, nub)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase)

import Thena.Driver (machineOf)
import Thena.Engine (Machine (..))
import Thena.Files (startingSession)
import Thena.Instral.Ops (signatureOf)
import Thena.Instral.Type
  ( Signature (..)
  , Ty (..)
  , renderSignature
  , renderTy
  )
import Thena.Rules (allSignatures, opWords)
import Thena.View.Type
  ( SignatureView (..)
  , TypeView (..)
  , displaySignature
  , displayType
  )

tests :: TestTree
tests =
  testGroup
    "Thena.View.Type"
    [ testCase "every op's signature redraws to the text the printer writes" ops
    , testCase "and every signature a shipped rule file declares does too" declared
    , testCase "and the rule files really declared some" declaredNotVacuous
    , testCase "and the op table really holds a scheme variable and a nesting" notVacuous
    , testCase "every constructor, and every nesting that fences" battery
    , testCase "and the battery really builds the fences no real signature has" fencesBuilt
    ]

-- ---------------------------------------------------------------------------
-- The redraw — deliberately flag-free

-- | 'Thena.Instral.Type.renderSignature''s arrow chain, from the view.
redrawSignature :: SignatureView -> String
redrawSignature (SignatureView ps r) =
  intercalate " -> " (map redrawType ps ++ [maybe "()" redrawType r])

-- | 'Thena.Instral.Type.renderTy', from the view — **and note what is not
-- here**: no @Bool@, no notion of "nested", no case that asks what its parent
-- was. 'AFenced' is the only parenthesis, apart from 'APair''s own notation.
redrawType :: TypeView -> String
redrawType v = case v of
  AString        -> "String"
  AName          -> "Name"
  AnInt          -> "Int"
  AChar          -> "Char"
  ABool          -> "Bool"
  ASurface       -> "Surface"
  ACore          -> "Core"
  ADevelopment   -> "Development"
  ALevel         -> "Level"
  AList a        -> "List " ++ redrawType a
  AnOption a     -> "Option " ++ redrawType a
  APair a b      -> "(" ++ redrawType a ++ ", " ++ redrawType b ++ ")"
  AFunction as r -> intercalate " -> " (map redrawType as ++ [redrawType r])
  ASchemeVar l   -> l
  AFenced a      -> "(" ++ redrawType a ++ ")"

-- ---------------------------------------------------------------------------
-- The corpora

-- | Every op in the language, with the signature its own table gives it —
-- 'Thena.Rules.opWords' is the enumeration @RuleSyntaxTests@ and
-- @InstralTypeTests@ already hold the vocabulary to.
opSignatures :: [Signature]
opSignatures = map (signatureOf . snd) opWords

-- | Every signature the shipped rule files declare in so many words.
declaredSignatures :: IO [Signature]
declaredSignatures = do
  s <- fst <$> startingSession
  pure (map snd (allSignatures (rules (machineOf s))))

-- ---------------------------------------------------------------------------
-- The tests

ops :: IO ()
ops = crossSignatures opSignatures

declared :: IO ()
declared = declaredSignatures >>= crossSignatures

-- | **'declared' passes on an empty list, and that is not hypothetical.**
-- 'startingSession' reads the prelude and the standard rules through
-- @Paths_thena@, whose data directory is only set when @cabal test@ sets
-- @thena_datadir@ — run the built binary directly and the session boots with
-- nothing in it, 'declaredSignatures' is @[]@, and the crossing is green over
-- no data at all. Measured at MS7 phase 133: the shipped bases declare 21.
declaredNotVacuous :: IO ()
declaredNotVacuous = do
  sgs <- declaredSignatures
  if length sgs >= 10 then pure ()
    else assertFailure ("only " <> show (length sgs) <> " declared signatures in the corpus")

crossSignatures :: [Signature] -> IO ()
crossSignatures sgs =
  case [ unwords ["view:", show (redrawSignature (displaySignature sg))
                 , "printer:", show (renderSignature sg)]
       | sg <- sgs
       , redrawSignature (displaySignature sg) /= renderSignature sg
       ] of
    []    -> pure ()
    e : _ -> assertFailure e

-- | **A green crossing over ground types alone would prove nothing**, since the
-- fence is the only thing that can go wrong and a signature of @Core -> Core@
-- has none.
--
-- This caught a real one when it was first written: the corpus was the rule
-- bases' own signatures, and it fenced nothing and mentioned no scheme
-- variable, so the crossing that looked like the strong test was proving only
-- that @Core -> ()@ renders as @Core -> ()@. Hence 'opSignatures'.
--
-- **And the op table does not fence either, which is a fact about the system
-- and not about this test.** Measured at MS7 phase 133 over all 71 ops: the
-- richest shapes are @Option a@ and @a -> ()@, and **no signature anywhere in
-- the shipped system takes a function-typed parameter** — no op, and none of
-- the 21 signatures the rule files declare. So the parenthesis
-- 'Thena.Instral.Type.renderSignature' exists to write is exercised by no real
-- data at all, and 'fencesBuilt' below is what holds that coverage up. Nothing
-- is wrong; @instral@ has lambdas and a rule file may declare
-- @(a -> b) -> a -> b@, the shipped bases simply do not.
notVacuous :: IO ()
notVacuous =
  if length schemes >= 1 && nested >= 2
    then pure ()
    else
      assertFailure
        ( "the op table mentions " <> show (length schemes)
            <> " scheme variables and nests " <> show nested
            <> " types; it must exercise both"
        )
  where
    schemes = nub [ l | sg <- opSignatures, t <- slotsOf sg, l <- varsOf t ]
    nested  = length [ () | sg <- opSignatures, t <- slotsOf sg, deep t ]
    deep t = case t of
      TList _   -> True
      TOption _ -> True
      TPair _ _ -> True
      TFun _ _  -> True
      _         -> False

-- | The battery is the only corpus that fences, so a battery that quietly
-- stopped fencing would take the fencing crossing with it and stay green.
fencesBuilt :: IO ()
fencesBuilt =
  if atTop >= 3 && within >= 4
    then pure ()
    else
      assertFailure
        ( "the battery fences " <> show atTop
            <> " signature parameters and " <> show within
            <> " nested types; it must do both"
        )
  where
    atTop =
      length [ () | t <- handBuilt
                  , SignatureView ps r <- [displaySignature (asParameter t)]
                  , AFenced _ <- ps ++ maybe [] (: []) r ]
    within = length [ () | t <- handBuilt, fencesInside (displayType t) ]
    fencesInside v = case v of
      AFenced _      -> True
      AList a        -> fencesInside a
      AnOption a     -> fencesInside a
      APair a b      -> fencesInside a || fencesInside b
      AFunction as r -> any fencesInside as || fencesInside r
      _              -> False

slotsOf :: Signature -> [Ty]
slotsOf sg = sigParams sg ++ maybe [] (: []) (sigResult sg)

varsOf :: Ty -> [Int]
varsOf t = case t of
  TVar i     -> [i]
  TList a    -> varsOf a
  TOption a  -> varsOf a
  TPair a b  -> varsOf a ++ varsOf b
  TFun as r  -> concatMap varsOf as ++ varsOf r
  _          -> []

-- | Every constructor of 'Thena.Instral.Type.Ty', and every nesting in which
-- 'Thena.Instral.Type.renderTy' fences — because no shipped rule has
-- 'Thena.Instral.Type.TDevelopment' (its own haddock says so) and none happens
-- to nest an option inside a list.
--
-- Crossed against 'Thena.Instral.Type.renderTy' at the top level, which is
-- 'Thena.View.Type.displayType''s own claim, and then against
-- 'Thena.Instral.Type.renderSignature' with each as a parameter, which is the
-- other fencing rule.
battery :: IO ()
battery =
  case [ e | t <- handBuilt, Just e <- [wrong t] ] of
    []    -> pure ()
    e : _ -> assertFailure e
  where
    wrong t
      | redrawType (displayType t) /= renderTy t =
          Just (unwords ["type", show t, "view:", show (redrawType (displayType t))
                        , "printer:", show (renderTy t)])
      | redrawSignature (displaySignature (asParameter t))
          /= renderSignature (asParameter t) =
          Just (unwords ["as a parameter", show t
                        , "view:", show (redrawSignature (displaySignature (asParameter t)))
                        , "printer:", show (renderSignature (asParameter t))])
      | otherwise = Nothing

-- | The battery as a signature: the type as a parameter, as a result, and
-- beside a ground one — the two places 'displaySignature' fences.
asParameter :: Ty -> Signature
asParameter t = Signature [t, TCore] (Just t)

handBuilt :: [Ty]
handBuilt =
      [ TString, TName, TInt, TChar, TBool
      , TSurface, TCore, TDevelopment, TLevel
      , TVar 0, TVar 25, TVar 26, TVar 51
      , TList TCore
      , TOption TCore
      , TPair TCore TString
        -- The nestings that fence: a function, a list and an option standing
        -- inside another type's argument.
      , TList (TFun [TCore] TCore)
      , TOption (TList TCore)
      , TList (TOption TCore)
      , TFun [TList TCore] (TOption TCore)
      , TFun [TFun [TCore] TCore] TCore
      , TPair (TFun [TCore] TCore) (TList TCore)
      , TList (TPair TCore TString)
      , TFun [TCore, TString] (TPair TCore (TList TName))
      , TOption (TFun [TCore, TCore] (TVar 0))
      ]
