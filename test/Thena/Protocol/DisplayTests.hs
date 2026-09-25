-- | The Core display representation (MS7 phase 115a).
--
-- **The test is the whole argument for the design.** 'Thena.Protocol.Redraw'
-- is what an editor would be: it takes only a 'Display' — no session, no
-- context, no globals, no grammars — and produces text. If that text is what
-- 'Thena.Repl.renderCore' produces for the same term, then the display really
-- does carry everything the editor needs, and the seam in
-- @discussion\/editor-display.md@ §1 falls where that document says it does.
--
-- **It is a crossing and not a round trip.** 'Thena.Protocol.Redraw.redraw'
-- and `renderCore` are two independent walks over two different structures;
-- nothing here reads the other one's table, so agreeing is evidence rather
-- than tautology.
module Thena.Protocol.DisplayTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Term (Core (..), GlobalName (..), Literal (..))
import Thena.Global.Env
  ( Constant (..)
  , Definition (..)
  , GlobalEnv (..)
  )
import Thena.Driver (Response (..), Session (..), loadProofSource)
import Thena.Engine (Machine (..))
import Thena.Language.Grammar (Grammar)
import Thena.Protocol.Address (Address (..))
import Thena.Protocol.Display (Budget (..), displayCore)
import Thena.Protocol.Redraw (redraw)
import Thena.Repl (renderCore, startingSession)

tests :: TestTree
tests =
  testGroup
    "Thena.Protocol.Display"
    [ testCase "the display carries everything the printer needed" corpus
    , testCase "and the corpus really holds terms" notVacuous
    , testGroup "a modelled language's notation (phase 115b)" objectCases
    ]

-- | Every term the prelude and the standard base leave in the environment.
termsOf :: GlobalEnv -> [Core]
termsOf gs =
  [definitionType d | (_, d) <- definitions gs]
    <> [definitionBody d | (_, d) <- definitions gs]
    <> [constantType c | (_, c) <- constants gs]

corpus :: IO ()
corpus = do
  ts <- termsOf . globals . sessionMachine . fst <$> startingSession
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
  n <- length . termsOf . globals . sessionMachine . fst <$> startingSession
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
    (s1, ProofLoaded {}) -> pure (grammars (sessionMachine s1))
    (_, other) -> assertFailure (show other) >> pure []

con :: String -> [Core] -> Core
con name = foldl App (Global (GlobalName name) [])

str :: String -> Core
str = Primitive . LString

-- | 'redraw' against 'Thena.Repl.renderCore', for terms
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
