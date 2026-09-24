module Main (main) where

import Test.Tasty (defaultMain, testGroup)

import qualified Thena.Core.ConvertTests
import qualified Thena.Core.LevelTests
import qualified Thena.Core.ReduceTests
import qualified Thena.Core.PrimitiveTests
import qualified Thena.Core.TermTests
import qualified Thena.Core.TypingTests
import qualified Thena.Core.UnifyTests
import qualified Thena.CursorTests
import qualified Thena.Protocol.AddressTests
import qualified Thena.Protocol.ConcreteTests
import qualified Thena.Protocol.DisplayTests
import qualified Thena.Protocol.ProjectTests
import qualified Thena.Protocol.ServerTests
import qualified Thena.Protocol.SocketTests
import qualified Thena.Protocol.WireTests
import qualified Thena.Protocol.TextTests
import qualified Thena.Protocol.JsonTests
import qualified Thena.Protocol.MessageTests
import qualified Thena.DependentIndexTests
import qualified Thena.CanonicalTests
import qualified Thena.DeterminacyTests
import qualified Thena.NormalTests
import qualified Thena.PreservationTests
import qualified Thena.PrintTests
import qualified Thena.ProgressTests
import qualified Thena.ProductTests
import qualified Thena.DispatchTests
import qualified Thena.ElaborateTests
import qualified Thena.DevelopmentTests
import qualified Thena.DriverTests
import qualified Thena.SurfaceTests
import qualified Thena.SurfaceZipperTests
import qualified Thena.EliminateTests
import qualified Thena.EliminatorTests
import qualified Thena.EngineTests
import qualified Thena.GlobalTests
import qualified Thena.KernelTests
import qualified Thena.LexerTests
import qualified Thena.RegexTests
import qualified Thena.GrammarTests
import qualified Thena.EarleyTests
import qualified Thena.BuildTests
import qualified Thena.SubstitutionTests
import qualified Thena.ContextTests
import qualified Thena.JudgmentTests
import qualified Thena.ExamplesTests
import qualified Thena.ObjectTermTests
import qualified Thena.TokenTests
import qualified Thena.LoadTests
import qualified Thena.ManualTests
import qualified Thena.NoConfusionTests
import qualified Thena.InstralInferTests
import qualified Thena.InstralTypeTests
import qualified Thena.RulesTests
import qualified Thena.PatternTests
import qualified Thena.RuleSyntaxTests
import qualified Thena.RuleFileTests
import qualified Thena.CallTests
import qualified Thena.ReadTests
import qualified Thena.GoldenTests
import qualified Thena.SessionTests
import qualified Thena.SyntaxTests

main :: IO ()
main =
  defaultMain $
    testGroup
      "thena"
      [ Thena.Core.ConvertTests.tests
      , Thena.Core.LevelTests.tests
      , Thena.Core.ReduceTests.tests
      , Thena.Core.PrimitiveTests.tests
      , Thena.Core.TermTests.tests
      , Thena.Core.TypingTests.tests
      , Thena.Core.UnifyTests.tests
      , Thena.Protocol.JsonTests.tests
      , Thena.Protocol.ConcreteTests.tests
      , Thena.Protocol.DisplayTests.tests
      , Thena.Protocol.ProjectTests.tests
      , Thena.Protocol.ServerTests.tests
      , Thena.Protocol.SocketTests.tests
      , Thena.Protocol.WireTests.tests
      , Thena.Protocol.TextTests.tests
      , Thena.Protocol.AddressTests.tests
      , Thena.Protocol.MessageTests.tests
      , Thena.CursorTests.tests
      , Thena.DependentIndexTests.tests
      , Thena.CanonicalTests.tests
      , Thena.DeterminacyTests.tests
      , Thena.NormalTests.tests
      , Thena.PreservationTests.tests
      , Thena.PrintTests.tests
      , Thena.ProgressTests.tests
      , Thena.ProductTests.tests
      , Thena.DispatchTests.tests
      , Thena.ElaborateTests.tests
      , Thena.DevelopmentTests.tests
      , Thena.DriverTests.tests
      , Thena.SurfaceTests.tests
      , Thena.SurfaceZipperTests.tests
      , Thena.EliminateTests.tests
      , Thena.EliminatorTests.tests
      , Thena.EngineTests.tests
      , Thena.GlobalTests.tests
      , Thena.KernelTests.tests
      , Thena.LexerTests.tests
      , Thena.RegexTests.tests
      , Thena.GrammarTests.tests
      , Thena.EarleyTests.tests
      , Thena.BuildTests.tests
      , Thena.SubstitutionTests.tests
      , Thena.ContextTests.tests
      , Thena.JudgmentTests.tests
      , Thena.ExamplesTests.tests
      , Thena.ObjectTermTests.tests
      , Thena.TokenTests.tests
      , Thena.LoadTests.tests
  , Thena.ManualTests.tests
      , Thena.NoConfusionTests.tests
      , Thena.InstralInferTests.tests
      , Thena.InstralTypeTests.tests
      , Thena.RulesTests.tests
      , Thena.PatternTests.tests
      , Thena.RuleSyntaxTests.tests
      , Thena.RuleFileTests.tests
      , Thena.CallTests.tests
      , Thena.ReadTests.tests
      , Thena.GoldenTests.tests
      , Thena.SessionTests.tests
      , Thena.SyntaxTests.tests
      ]
