-- | A running machine's protocol view (MS7 phase 115f).
--
-- **The crossing, at the fidelity that exists.** 'redrawMachine' draws only
-- what 'Thena.Protocol.Machine.displayMachine' hands it; 115d's own
-- 'redrawStatement'/'redrawOperand'/'redrawSkeleton'/'redrawValue' are
-- reused verbatim here rather than re-proven, since the per-statement and
-- per-value crossing is already 'Thena.Protocol.InstralTests''s job — what
-- is new here is only the three-pane wrapping ('pc'\/'env'\/'stack')
-- 'Thena.Repl.renderMachine' does around them.
--
-- **Hand-built, not a corpus, and said so.** Nothing shipped runs the
-- machine mid-call in a way a test can reach without stepping it there
-- itself, and 'renderMachine's own frame line touches only two fields
-- shared by 'Thena.Engine.Call' and 'Thena.Engine.Choice' — so a
-- hand-built 'Thena.Engine.Call' exercises everything the crossing needs
-- without a live rule dispatch to produce one.
module Thena.Protocol.MachineTests (tests) where

import Data.List (intercalate)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase)

import Thena.Driver (Session (..))
import Thena.Engine (Exec (..), Frame (..), Machine (..))
import Thena.Instral.Ops (Instr (..), Op (Assume), Operand (..), Value (..))
import Thena.Instral.Pattern (Pattern (..))
import Thena.Language.Grammar (Grammar)
import Thena.Protocol.Address (Address (..))
import Thena.Protocol.Display (Budget (..))
import Thena.Protocol.Instral
  ( OperandView (..)
  , SkeletonView (..)
  , StatementDetail (..)
  , StatementView (..)
  , ValueView (..)
  )
import Thena.Protocol.Machine (FrameView (..), MachineView (..), displayMachine)
import Thena.Protocol.Redraw (redraw)
import Thena.Repl (renderMachine, startingSession)

tests :: TestTree
tests =
  testGroup
    "Thena.Protocol.Machine"
    [ testCase "an idle machine — everything empty" (mismatchMachine [] =<< idle)
    , testCase "a live pc, bindings, and a stack with a returned frame" (mismatchMachine [] =<< busy)
    ]

-- | Any real 'Session's machine, its own state stripped out and replaced —
-- the globals\/rules\/grammars a real session carries are what
-- 'Thena.Engine.Machine' needs to exist at all, and none of them are what
-- this phase displays.
base :: IO Machine
base = sessionMachine . fst <$> startingSession

idle :: IO Machine
idle = do
  m <- base
  pure m { exec = Exec { pc = [], env = [], stack = [] } }

busy :: IO Machine
busy = do
  m <- base
  pure m
    { exec =
        Exec
          { pc =
              [ Bind (PVar "x") Nothing (Assume (Lit (VText "x")) (Lit (VText "S")))
              , Do (Assume (Lit (VText "y")) (Lit (VText "T")))
              ]
          , env = [("a", VInt 3), ("b", VBool True)]
          , stack =
              [ Call { resume = [Do (Assume (Lit (VInt 1)) (Lit (VInt 2)))], resumeEnv = [], destination = Nothing, returned = False }
              , Call { resume = [], resumeEnv = [], destination = Nothing, returned = True }
              ]
          }
    }

mismatchMachine :: [Grammar] -> Machine -> IO ()
mismatchMachine gs m
  | shown == drawn = pure ()
  | otherwise = assertFailure ("printed:\n" ++ unlines shown ++ "drawn:\n" ++ unlines drawn)
  where
    shown = renderMachine gs 500 [] m
    drawn = redrawMachine (displayMachine gs (Budget 200) [] [] 500 (Address []) m)

-- ---------------------------------------------------------------------------
-- What an editor is, for a machine

redrawMachine :: MachineView -> [String]
redrawMachine mv =
  ["pc"] ++ indented (zipWith instruction [0 :: Int ..] (machinePc mv))
    ++ ["env"] ++ indented (map binding (machineEnv mv))
    ++ ["stack"] ++ indented (map frame (machineStack mv))
  where
    indented [] = ["  (empty)"]
    indented xs = map ("  " ++) xs
    instruction i sv = show i ++ "  " ++ redrawStatement sv
    binding (x, vv) = x ++ " = " ++ redrawValue vv
    frame fv =
      "call, " ++ show (frameResumeCount fv) ++ " instruction(s) to resume"
        ++ if frameReturned fv then " (returned)" else ""

-- | 115d's own redraw, unchanged — see the module header for why it is
-- copied rather than shared.
redrawStatement :: StatementView -> String
redrawStatement sv = bind <> word <> operandsText <> detailText
  where
    bind = case (statementBind sv, statementAnnotation sv) of
      (Nothing, _)      -> ""
      (Just p, Nothing) -> p <> " = "
      (Just p, Just ty) -> p <> " : " <> ty <> " ; " <> p <> " = "

    word = statementWord sv

    operandsText = case statementDetail sv of
      Just (Calls nm)    -> " " <> nm <> operandsAfter
      Just (Declares nm) -> " " <> nm <> operandsAfter
      _                  -> operandsAfter
    operandsAfter = concatMap ((" " <>) . redrawOperand) (statementOperands sv)

    detailText = case statementDetail sv of
      Just (AsksFor k) -> " " <> k
      Just (Crosses w) -> " " <> w
      _                -> ""

redrawOperand :: OperandView -> String
redrawOperand o = case o of
  OpndRef x -> x
  OpndLiteral v -> redrawValue v
  OpndList os -> "[" <> intercalate ", " (map redrawOperand os) <> "]"
  OpndPair a b -> "(" <> redrawOperand a <> ", " <> redrawOperand b <> ")"
  OpndObject sk -> redrawSkeleton redrawOperand sk

redrawSkeleton :: (a -> String) -> SkeletonView a -> String
redrawSkeleton at sk = case sk of
  SkelNode nm [] -> nm
  SkelNode nm kids -> nm <> "(" <> intercalate ", " (map (redrawSkeleton at) kids) <> ")"
  SkelLiteral t -> t
  SkelHole a -> "$" <> "{" <> at a <> "}"

redrawValue :: ValueView -> String
redrawValue v = case v of
  ValText s -> s
  ValInt k -> show k
  ValChar t -> t
  ValBool True -> "true"
  ValBool False -> "false"
  ValList vs -> "[" <> intercalate ", " (map redrawValue vs) <> "]"
  ValNone -> "none"
  ValSome u -> "some " <> redrawValue u
  ValPair a b -> "(" <> redrawValue a <> ", " <> redrawValue b <> ")"
  ValLevel l -> l
  ValTerm d -> "\8988" <> redraw d <> "\8989"
  ValOpaque other -> "\8249" <> other <> "\8250"
