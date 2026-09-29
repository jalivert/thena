-- | The Core display representation (MS7 phase 115a).
--
-- **The test is the whole argument for the design.** 'Thena.View.Redraw'
-- is what an editor would be: it takes only a 'Display' — no session, no
-- context, no globals, no grammars — and produces text. If that text is what
-- 'Thena.Render.renderCore' produces for the same term, then the display really
-- does carry everything the editor needs, and the seam in
-- @discussion\/editor-display.md@ §1 falls where that document says it does.
--
-- **It is a crossing and not a round trip.** 'Thena.View.Redraw.redraw'
-- and `renderCore` are two independent walks over two different structures;
-- nothing here reads the other one's table, so agreeing is evidence rather
-- than tautology.
module Thena.View.CoreTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Term (Core (..), GlobalName (..), Literal (..))
import Thena.Global.Env
  ( Constant (..)
  , Definition (..)
  , GlobalEnv (..)
  )
import Thena.Driver
  ( Response (..)
  , machineOf
  , loadProofSource
  )
import Thena.Engine (Machine (..))
import Thena.Language.Grammar (Grammar)
import Thena.View.Address (Address (..))
import Thena.View.Core
  ( Budget (..)
  , Display (..)
  , ObjectItem (..)
  , Shape (..)
  , displayCore
  )
import Thena.View.Redraw (redraw)
import Thena.Files (startingSession)
import Thena.Render (renderCore)

tests :: TestTree
tests =
  testGroup
    "Thena.View.Core"
    [ testCase "the display carries everything the printer needed" corpus
    , testCase "and the corpus really holds terms" notVacuous
    , testGroup "a modelled language's notation (phase 115b)" objectCases
    , testGroup "where a tagged literal begins (phase 132)" regionCases
    ]

-- | Every term the prelude and the standard base leave in the environment.
termsOf :: GlobalEnv -> [Core]
termsOf gs =
  [definitionType d | (_, d) <- definitions gs]
    <> [definitionBody d | (_, d) <- definitions gs]
    <> [constantType c | (_, c) <- constants gs]

corpus :: IO ()
corpus = do
  ts <- termsOf . globals . machineOf . fst <$> startingSession
  case [e | Just e <- map mismatch ts] of
    [] -> pure ()
    e : _ -> assertFailure e

mismatch :: Core -> Maybe String
mismatch t
  | shown == drawn = Nothing
  | otherwise = Just ("printed: " <> shown <> "\n  drawn:   " <> drawn)
  where
    shown = renderCore [] 0 [] t
    drawn = redraw (displayCore [] (Budget 200) [] [] 0 (Address []) t)

-- | A green test over an empty corpus would prove nothing.
notVacuous :: IO ()
notVacuous = do
  n <- length . termsOf . globals . machineOf . fst <$> startingSession
  if n >= 50 then pure () else assertFailure ("only " <> show n <> " terms in the corpus")

-- ---------------------------------------------------------------------------
-- Object-language notation (MS7 phase 115b)
-- ---------------------------------------------------------------------------

-- | Three languages, exactly `Thena.PrintTests`'s fixture: one that brackets
-- its productions, one that does not, and one whose token class matches its
-- own terminals — so a term needs fencing to read back. Duplicated rather
-- than imported: the two test modules check different layers (text there,
-- structure here) and are free to drift on their own fixtures.
source :: String
source =
  unlines
    [ "module Displaying where"
    , ""
    , "w : Token String"
    , "w = /[a-z][a-zA-Z0-9']*/"
    , ""
    , "c : Token String"
    , "c = /[a-z]/"
    , ""
    , "language Ty, T, S where"
    , "  base  -> \953"
    , "  arrow -> ( T -> S )"
    , ""
    , "language LC, M, N, E where"
    , "  var : w as occurrence -> w"
    , "  abs : w as binder     -> ( \955 w : T . E[w] )"
    , "  app                   -> ( M N )"
    , ""
    , "language Ex, U, V where"
    , "  ref  : w as occurrence -> w"
    , "  juxt                   -> U V"
    , ""
    , "language Coll, P, Q where"
    , "  cref  : c as occurrence -> c"
    , "  cjux                    -> P Q"
    , "  clet  : c as binder     -> l c = P i Q[c]"
    ]

loaded :: IO [Grammar]
loaded = do
  (s0, _) <- startingSession
  case loadProofSource s0 source of
    (s1, ProofLoaded {}) -> pure (grammars (machineOf s1))
    (_, other) -> assertFailure (show other) >> pure []

con :: String -> [Core] -> Core
con name = foldl App (Global (GlobalName name) [])

str :: String -> Core
str = Primitive . LString

-- | 'redraw' against 'Thena.Render.renderCore', for terms
-- `Thena.PrintTests` already established the printed form of: a bracketed
-- production, a bare juxtaposition, a foreign splice, a foreign splice that
-- is itself a region, an unreadable token spliced, both directions of
-- deepest-first fencing, and a term the grammar reads flat next to the one
-- character away from it that needs a fence. Between them: every
-- 'ObjectItem' — 'ObjectText', 'ObjectToken', an unfenced 'ObjectChild' and a
-- fenced one by both routes ('DForeign' and a settled 'DFenced').
objectCases :: [TestTree]
objectCases =
  [ agree "a bracketed production needs no fence"
      (con "abs" [str "x", con "base" [], con "var" [str "x"]])
  , agree "bare juxtaposition, no brackets in the grammar"
      (con "juxt" [con "ref" [str "f"], con "ref" [str "a"]])
  , agree "what the notation cannot write is a foreign splice"
      (con "app" [Global (GlobalName "twice") [], con "var" [str "y"]])
  , agree "a foreign splice that is itself a region"
      (con "app" [con "var" [Global (GlobalName "nom") []], con "var" [str "y"]])
  , agree "a name the class would not read back is spliced"
      (con "var" [str "a b"])
  , agree "the left operand of a juxtaposition is fenced"
      (con "juxt" [con "juxt" [con "ref" [str "f"], con "ref" [str "a"]], con "ref" [str "b"]])
  , agree "and the right operand, rather than both"
      (con "juxt" [con "ref" [str "f"], con "juxt" [con "ref" [str "a"], con "ref" [str "b"]]])
  , agree "a term the grammar reads one way is written flat"
      (con "clet" [str "f", con "cjux" [con "cref" [str "a"], con "cref" [str "b"]], con "cref" [str "c"]])
  , agree "the same term with a variable spelled like a terminal is fenced"
      (con "clet" [str "f", con "cjux" [con "cref" [str "a"], con "cref" [str "i"]], con "cref" [str "b"]])
  ]
  where
    agree name t = testCase name $ do
      gs <- loaded
      redraw (displayCore gs (Budget 200) [] [] 0 (Address []) t) @?= renderCore gs 0 [] t

-- ---------------------------------------------------------------------------
-- Where a literal begins — MS7 phase 132

-- | **'ARegion' marks a literal's boundary, and only a boundary.**
--
-- His ask of 2026-09-29 is that a frontend draw the tag, the production
-- qualifier and the backticks only when the cursor is inside the literal, and
-- draw the same term seamlessly otherwise. That needs the view to say where a
-- literal /starts/, which is what phase 132 added: reaching an object term from
-- a Core position opens one, an inline slot continues the one already open, and
-- a splice holding a literal of its own opens another.
--
-- 'Thena.View.Redraw' crossing green against 'Thena.Render.renderCore' already
-- proves the wrapper sits exactly where @printTerm@ writes a tag — these say
-- the shape is what a compositional frontend can use, which a crossing on the
-- final string cannot.
regionCases :: [TestTree]
regionCases =
  [ testCase "an object term reached from Core opens a literal" $ do
      sh <- shapeOf (con "juxt" [con "ref" [str "f"], con "ref" [str "a"]])
      case sh of
        ARegion inner -> case displayShape inner of
          AnObjectTerm lang prod _ -> (lang, prod) @?= ("Ex", "juxt")
          other -> assertFailure ("ARegion wrapped " <> show other)
        other -> assertFailure ("not a region: " <> show other)

  , testCase "and an inline slot continues it rather than opening another" $ do
      sh <- shapeOf (con "juxt" [con "ref" [str "f"], con "ref" [str "a"]])
      case sh of
        ARegion inner -> case displayShape inner of
          AnObjectTerm _ _ items ->
            [ () | ObjectChild False d <- items, ARegion {} <- [displayShape d] ] @?= []
          other -> assertFailure ("ARegion wrapped " <> show other)
        other -> assertFailure ("not a region: " <> show other)

  , testCase "and a nested one really is inline, so the check is not vacuous" $ do
      sh <- shapeOf (con "juxt" [con "ref" [str "f"], con "ref" [str "a"]])
      case sh of
        ARegion inner -> case displayShape inner of
          AnObjectTerm _ _ items ->
            length [ () | ObjectChild False d <- items
                        , AnObjectTerm {} <- [displayShape d] ] @?= 2
          other -> assertFailure ("ARegion wrapped " <> show other)
        other -> assertFailure ("not a region: " <> show other)

  , testCase "a splice holding a literal of its own opens a second one" $ do
      -- 'Thena.PrintTests' established this term's printed form: the splice's
      -- own argument is a region, so it is written @${LC`…`}@.
      sh <- shapeOf (con "app" [con "var" [Global (GlobalName "nom") []], con "var" [str "y"]])
      case sh of
        ARegion inner -> case displayShape inner of
          AnObjectTerm _ _ items ->
            length [ () | ObjectChild True d <- items
                        , ARegion {} <- [displayShape d] ] @?= 1
          other -> assertFailure ("ARegion wrapped " <> show other)
        other -> assertFailure ("not a region: " <> show other)

  , testCase "a term with no notation opens none" $ do
      sh <- shapeOf (Global (GlobalName "twice") [])
      case sh of
        ARegion {} -> assertFailure "a plain global was taken for a literal"
        _          -> pure ()

  , testCase "the seamless form is the expanded one without tag or fences" $ do
      gs <- loaded
      let t = con "juxt" [con "ref" [str "f"], con "ref" [str "a"]]
          d = displayCore gs (Budget 200) [] [] 0 (Address []) t
      expanded <- pure (redraw d)
      case displayShape d of
        ARegion inner -> case displayShape inner of
          AnObjectTerm lang _ _ ->
            -- What a frontend does to hide the tag: draw the wrapper as
            -- nothing. The seamless text is the expanded text minus exactly the
            -- tag and the two backticks, which is the whole of his ask.
            expanded @?= lang <> "`" <> redraw inner <> "`"
          other -> assertFailure ("ARegion wrapped " <> show other)
        other -> assertFailure ("not a region: " <> show other)
  ]
  where
    shapeOf t = do
      gs <- loaded
      pure (displayShape (displayCore gs (Budget 200) [] [] 0 (Address []) t))
