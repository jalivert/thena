-- | Object-language blocks, read and validated (MS6 phase 101; @ms6\/SPEC.md@
-- §4.1–4.5, §5.1, §7.0).
--
-- Three layers, each tested on its own and then through a module load:
--
-- * the lexer takes a @language@ or @context@ block at column 1 of a module
--   whole, as raw text, and only in a module;
-- * "Thena.Language.Reader" gives its shape — header, productions, metadata,
--   items, binding forms;
-- * "Thena.Language.Grammar" gives its meaning, against what is declared —
--   and every refusal of §4.5 is asserted as its structured value, the golden
--   pinning the words.
--
-- **The roles are asserted production by production** for the spec's own STLC
-- grammar, because they are what phase 103 will put on the constructors and
-- generated substitution will read: a wrong role here is a wrong substitution
-- there, three phases away.
module Thena.GrammarTests (tests) where

import Data.ByteString.Builder (stringUtf8, toLazyByteString)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Term (GlobalName (..))
import Thena.Driver (Response (..), Session (..), Stop (..), loadProofSource)
import Thena.Engine (Machine (..))
import Thena.Errors (SyntaxError (..), Warning (..))
import Thena.Global.Declare (DeclareError (..))
import Thena.Language.Grammar
import Thena.Language.Reader
import Thena.Repl (renderResponse, startingSession)
import Thena.Syntax.Lexer
  (BlockKind (..), Located (..), Token (..), isIdentifier, lexModule, lexTokens)

tests :: TestTree
tests =
  testGroup
    "object-language blocks"
    [ testGroup "the lexer takes a block whole, in a module" lexing
    , testGroup "the reader gives its shape" reading
    , testGroup "the checker gives its meaning" meaning
    , testGroup "and refuses what §4.5 refuses" refusals
    , goldenVsString "grammars" "test/golden/grammars.golden" $ do
        (s0, problems) <- startingSession
        let run (title, src) =
              let (s1, r) = loadProofSource s0 src
               in ("-- " ++ title) : renderResponse s1 r
        pure (toLazyByteString (stringUtf8
          (unlines (problems ++ concatMap run (("the spec's STLC", stlc) : map fst refused ++ unreadable)))))
    ]

-- ---------------------------------------------------------------------------

lexing :: [TestTree]
lexing =
  [ testCase "a block at column 1 is one token, keyword excluded" $
      tokens lexModule "language L, M where\n  f -> ( M )\n"
        @?= Right [TBlock LanguageBlock " L, M where\n  f -> ( M )\n"]
  , testCase "it ends at the next line with anything in column 1" $
      tokens lexModule "context C, G where\n  e -> .\n\n  f -> G ,\nx : T\n"
        @?= Right [ TBlock ContextBlock " C, G where\n  e -> .\n\n  f -> G ,\n"
                  , TIdent "x", TColon, TIdent "T" ]
  , testCase "characters Thena reserves are just text inside it" $
      tokens lexModule "language L where\n  f -> [ λ ⌜ ] /\n"
        @?= Right [TBlock LanguageBlock " L where\n  f -> [ λ ⌜ ] /\n"]
  , testCase "outside a module the keyword is a keyword and nothing more" $
      tokens lexTokens "language L" @?= Right [TLanguage, TIdent "L"]
  , testCase "and not at column 1 it is not a block either" $
      tokens lexModule "  context C" @?= Right [TContext, TIdent "C"]
  , -- His ruling, 2026-09-19: both words are reserved, as language is.
    testCase "context and judgment are no longer names" $
      map isIdentifier ["context", "judgment", "contexts"] @?= [False, False, True]
  ]
  where
    tokens lexer src = map (\(Located _ t) -> t) <$> lexer src

-- ---------------------------------------------------------------------------

reading :: [TestTree]
reading =
  [ testCase "a header, and a production of each shape" $
      readBlock LanguageBlock 1
        " LC, M, N where\n  var : x as occurrence -> x\n  app -> ( M N )\n"
        @?= Right
          (Block LanguageBlock "LC" ["M", "N"]
             [ Production 2 "var" (Just (AsOccurrence "x")) [Word "x"]
             , Production 3 "app" Nothing (map Word ["(", "M", "N", ")"])
             ])
  , testCase "the three metadata forms" $
      map (fmap (map productionMetadata . blockProductions) . readBlock LanguageBlock 1)
        [ " L where\n  f : x as binder -> x\n"
        , " L where\n  f : { x, y } as binders -> x y\n"
        , " L where\n  f : {x,y} as binders -> x y\n"
        ]
        @?= map (Right . (: []) . Just) [AsBinders ["x"], AsBinders ["x", "y"], AsBinders ["x", "y"]]
  , testCase "a binding form reads across the spaces in its bracket" $
      items " L where\n  f -> E[x, y] ( E [ x ] )\n"
        @?= Right [ Binding "E" ["x", "y"], Word "(", Word "E", Word "[", Word "x", Word "]", Word ")" ]
  , testCase "a deeper line continues the production, and -- starts a comment" $
      items " L where\n  f -> a b -- not an item\n       c\n"
        @?= Right (map Word ["a", "b", "c"])
  , testCase "-> after the first is a terminal" $
      items " Ty, T where\n  arrow -> T -> T\n" @?= Right (map Word ["T", "->", "T"])
  , testCase "-->, not a comment, is a terminal too" $
      items " L where\n  f -> a --> b\n" @?= Right (map Word ["a", "-->", "b"])
  ]
  where
    items src = concatMap productionItems . blockProductions <$> readBlock LanguageBlock 1 src

unreadable :: [(String, String)]
unreadable =
  [ ("no where", "module M where\n\nlanguage L M\n  f -> a\n")
  , ("metadata that is none of the three", "module M where\n\nlanguage L where\n  f : x as whatever -> x\n")
  , ("a production with no arrow", "module M where\n\nlanguage L where\n  f a b\n")
  , ("a bracket never closed", "module M where\n\nlanguage L, M where\n  f -> M[b c\n")
  , ("a line indented less", "module M where\n\nlanguage L where\n    f -> a\n  g -> b\n")
  ]

-- ---------------------------------------------------------------------------

-- | The spec's own grammars (§4.6, §5.2), with a vacuous binder added.
stlc :: String
stlc =
  unlines
    [ "module STLC where"
    , ""
    , "x : Token String"
    , "x = /[a-z][a-zA-Z0-9']*/"
    , ""
    , "language Ty, T, S where"
    , "  base  -> \953"
    , "  arrow -> T -> S"
    , ""
    , "language LC, M, N, E where"
    , "  var : x as occurrence -> x"
    , "  abs : x as binder     -> ( \955 x : T . E[x] )"
    , "  app                   -> ( M N )"
    , "  repeat                -> { M M }"
    , "  vacuous : { x } as binders -> let x = M in N"
    , ""
    , "context Ctx, \915 where"
    , "  empty  -> \183"
    , "  extend -> \915 , x : T"
    ]

meaning :: [TestTree]
meaning =
  [ testCase "the module loads, with the vacuous binder's warning" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 stlc of
        (_, ProofLoaded _ names _ ws) -> do
          names @?= ["x", "Ty", "LC", "Ctx"]
          ws @?= [VacuousBinder LanguageBlock "LC" "vacuous" "x"]
        (_, other) -> assertFailure (show other)
  , testCase "the arguments and roles of LC, production by production" $ do
      gs <- installed stlc
      case [ g | g <- gs, grammarName g == GlobalName "LC" ] of
        [g] ->
          map (\p -> (gproductionName p, gproductionArguments p)) (grammarProductions g)
            @?= [ (GlobalName "var", [Argument "x" str Occurrence])
                , (GlobalName "abs", [ Argument "x" str Binder
                                     , Argument "T" (lang "Ty") Plain
                                     , Argument "E" (lang "LC") (Scope [0]) ])
                , (GlobalName "app", [Argument "M" (lang "LC") Plain, Argument "N" (lang "LC") Plain])
                  -- §4.3: a name written twice is one argument.
                , (GlobalName "repeat", [Argument "M" (lang "LC") Plain])
                , (GlobalName "vacuous", [ Argument "x" str Binder
                                         , Argument "M" (lang "LC") Plain
                                         , Argument "N" (lang "LC") Plain ])
                ]
        other -> assertFailure (show (length other) ++ " grammars called LC")
  , testCase "a later module may use an earlier one's metavariables" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource s0 stlc
      case loadProofSource s1 "module More where\n\nlanguage P, Q where\n  tuple -> ( M , T )\n" of
        (_, ProofLoaded {}) -> pure ()
        (_, other) -> assertFailure (show other)
  , testCase "and may not declare a language of the same name" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource s0 stlc
      case loadProofSource s1 "module Again where\n\nlanguage LC, P where\n  f -> P\n" of
        (_, Ran _ _ (Refused (GrammarRefused e))) -> e @?= GrammarError LanguageBlock "LC" NameTaken
        (_, other) -> assertFailure (show other)
  ]
  where
    str = OfClass (GlobalName "x") (GlobalName "String")
    lang = OfLanguage . GlobalName
    installed src = do
      (s0, _) <- startingSession
      pure (grammars (sessionMachine (fst (loadProofSource s0 src))))

-- ---------------------------------------------------------------------------

-- | One module per refusal, with the value each must refuse with. Every module
-- has the classes @x : Token String@ and @n : Token Int@ above its block.
refused :: [((String, String), GrammarError)]
refused =
  [ inProduction "a binding form's head is not a metavariable"
      "language L, M where\n  bad -> q[x] M" "bad" (NotAMetavariable "q")
  , inProduction "a binder that is not a String"
      "language L, M where\n  num : n as binder -> n M[n]" "num" (BinderNotString "n" int)
  , inProduction "an occurrence that is not a String"
      "language L, M where\n  num : n as occurrence -> n" "num" (OccurrenceNotString "n" int)
  , inProduction "a bracket naming what is not an argument"
      "language L, M where\n  f -> ( M[x] )" "f" (NotAnArgument "x")
  , inProduction "a bracket naming an occurrence"
      "language L, M where\n  f : x as occurrence -> x M[x]" "f" (OccurrenceBinds "x")
  , inProduction "a bracket naming what the declared binders do not"
      "language L, M where\n  f : { x } as binders -> x n M[n]" "f" (NotADeclaredBinder "n")
  , inProduction "metadata naming what is not written"
      "language L, M where\n  f : x as occurrence -> M" "f" (NotAnArgument "x")
  , inProduction "one argument written with two scopes"
      "language L, M where\n  f -> M M[x] x" "f" (ScopesDiffer "M")
  , inProduction "a production with no items"
      "language L, M where\n  f ->" "f" NoItems
  , block "a metavariable named twice" "language L, M, M where\n  f -> M" (MetavariableRepeated "M")
  , block "a metavariable that is already a token class" "language L, x where\n  f -> x" (MetavariableTaken "x")
  , block "a language named like something declared" "language x where\n  f -> a" NameTaken
  , block "a constructor named like something declared" "language L, M where\n  x -> a" (ConstructorTaken "x")
  , block "two productions of one name" "language L, M where\n  f -> a\n  f -> b" (ConstructorTaken "f")
  , contextBlock "a context without one empty and one extension production"
      "context C, G where\n  e -> \183\n  f -> G G" ContextShape
  ]
  where
    int = OfClass (GlobalName "n") (GlobalName "Int")
    wrap body =
      "module M where\n\nx : Token String\nx = /[a-z]+/\n\nn : Token Int\nn = /[0-9]+/\n\n" ++ body ++ "\n"
    inProduction title body p why = ((title, wrap body), GrammarError LanguageBlock "L" (InProduction p why))
    block title body problem = ((title, wrap body), GrammarError LanguageBlock (nameOf body) problem)
    contextBlock title body problem = ((title, wrap body), GrammarError ContextBlock "C" problem)
    nameOf body = takeWhile (`notElem` ", ") (drop (length "language ") body)

refusals :: [TestTree]
refusals =
  [ testCase title $ do
      (s0, _) <- startingSession
      case loadProofSource s0 src of
        (_, Ran _ _ (Refused (GrammarRefused e))) -> e @?= want
        (_, other) -> assertFailure (show other)
  | ((title, src), want) <- refused
  ]
  ++
  [ testCase ("unreadable: " ++ title) $ do
      (s0, _) <- startingSession
      case loadProofSource s0 src of
        (_, Failed (BlockUnreadable e)) -> e @?= want
        (_, other) -> assertFailure (show other)
  | ((title, src), want) <-
      zip unreadable
        [ HeaderWithoutWhere 3
        , MetadataMalformed 4 "x as whatever"
        , ProductionWithoutArrow 4
        , BindingMalformed 4 ""
        , IndentedLess 5
        ]
  ]
