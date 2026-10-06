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

import Thena.Core.Term (GlobalName (..), Ident (..))
import Thena.Driver
  ( Response (..)
  , RuleFileError (..)
  , machineOf
  , Stop (..)
  , loadProofSource
  , loadRuleBases
  , newSession
  )
import Thena.Engine (Machine (..))
import Thena.Errors (Skipped (..), SyntaxError (..), Warning (..))
import Thena.Global.Declare (DeclareError (..))
import Thena.Language.Grammar
import Thena.Language.Reader
import Thena.Language.Regex (Regex, parseRegex)
import Thena.Files (startingSession)
import Thena.Render (renderTrouble, renderResponse)
import Thena.Syntax.Lexer
  (BlockKind (..), Located (..), Token (..), isIdentifier, lexModule, lexTokens)

tests :: TestTree
tests =
  testGroup
    "object-language blocks"
    [ testGroup "the lexer takes a block whole, in a module" lexing
    , testGroup "the reader gives its shape" reading
    , testGroup "the checker gives its meaning" meaning
    , testGroup "and says which classes a grammar reaches" reaching
    , testGroup "and refuses what §4.5 refuses" refusals
    , goldenVsString "grammars" "test/golden/grammars.golden" $ do
        (s0, trouble) <- startingSession
        let run (title, src) =
              let (s1, r) = loadProofSource s0 src
               in ("-- " ++ title) : renderResponse s1 r
        pure (toLazyByteString (stringUtf8
          (unlines (concatMap (renderTrouble s0) trouble ++ concatMap run (("the spec's STLC", stlc) : map fst refused ++ unreadable)))))
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
             ] [])
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
-- | **One language, two name classes** (MS8 phase 153). @x@ is the class @L@
-- reads an occurrence at; @X@ is bound by @big@ and occurs nowhere, which is
-- F-sub's shape in miniature — there @Λ X <: T . t@ binds a type variable from
-- a term production and every occurrence of it is in a type. The class @X@
-- belonging to another grammar is `~5k3mg`; recording which class a binder
-- binds at is what makes that expressible at all.
twoClasses :: String
twoClasses =
  unlines
    [ "module Two where"
    , ""
    , "x : Token String"
    , "x = /[a-z][a-zA-Z0-9']*/"
    , ""
    , "X : Token String"
    , "X = /[A-Z][a-zA-Z0-9']*/"
    , ""
    , "language L, M, N where"
    , "  var : x as occurrence -> x"
    , "  abs : x as binder     -> ( lam x . M[x] )"
    , "  big : X as binder     -> ( all X . M[X] )"
    ]

-- | **A binder of one language free in a slot of another** (MS8 phase 154).
-- @P@ reads an occurrence at @x@, so @P@ reaches the class @f@'s binder binds
-- at and the block installs — it is what `~5k3mg` exists for. Refused until
-- phase 154, and still refused when @P@ reaches no @x@.
foreignScope :: String
foreignScope =
  unlines
    [ "module Foreign where"
    , ""
    , "x : Token String"
    , "x = /[a-z][a-zA-Z0-9']*/"
    , ""
    , "language P, R where"
    , "  pvar : x as occurrence -> x"
    , ""
    , "language L, M where"
    , "  var : x as occurrence -> x"
    , "  f : x as binder       -> ( let x = M in R[x] )"
    ]

-- | **Three languages in a chain** (MS8 phase 154). @P@ reads an occurrence at
-- @x@ and nothing else does; @Q@ holds an @R@, and @L@ holds an @S@ — so the
-- class @L@ reaches it reaches through two slots and names nowhere itself.
chained :: String
chained =
  unlines
    [ "module Chain where"
    , ""
    , "x : Token String"
    , "x = /[a-z][a-zA-Z0-9']*/"
    , ""
    , "language P, R where"
    , "  pvar : x as occurrence -> x"
    , ""
    , "language Q, S where"
    , "  pwrap -> ( R )"
    , ""
    , "language L, M where"
    , "  lpair -> ( S M )"
    ]

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
          -- The second is the context's generated lookup (phase 107): its
          -- @ne@ premise depends on earlier arguments, which the no-confusion
          -- generator states no equation for (@ms6\/CLOSEOUT.md@ 25).
          ws @?= [ VacuousBinder LanguageBlock "LC" "vacuous" "x"
                 , NoConfusionSkipped (GlobalName "Ctx-in")
                     (DependentArguments (GlobalName "Ctx-there") 6 (Ident "ne")) ]
        (_, other) -> assertFailure (show other)
  , testCase "the arguments and roles of LC, production by production" $ do
      gs <- installed stlc
      case [ g | g <- gs, grammarName g == GlobalName "LC" ] of
        [g] ->
          map (\p -> (gproductionName p, gproductionArguments p)) (grammarProductions g)
            @?= [ (GlobalName "var", [Argument "x" str (Occurrence (GlobalName "x"))])
                , (GlobalName "abs", [ Argument "x" str (Binder (GlobalName "x"))
                                     , Argument "T" (lang "Ty") Plain
                                     , Argument "E" (lang "LC") (Scope [0]) ])
                , (GlobalName "app", [Argument "M" (lang "LC") Plain, Argument "N" (lang "LC") Plain])
                  -- §4.3: a name written twice is one argument.
                , (GlobalName "repeat", [Argument "M" (lang "LC") Plain])
                , (GlobalName "vacuous", [ Argument "x" str (Binder (GlobalName "x"))
                                         , Argument "M" (lang "LC") Plain
                                         , Argument "N" (lang "LC") Plain ])
                ]
        other -> assertFailure (show (length other) ++ " grammars called LC")
    -- **Two classes in one grammar** (MS8 phase 153, `~tmnrr` and `~5k3mg`).
    -- The whole of what this phase adds is that the two binders are recorded at
    -- the two different classes rather than both saying only "binder" — so a
    -- generator can tell them apart, which phase 155 is what needs it.
  , testCase "a binder at a second class is recorded at that class" $ do
      gs <- installed twoClasses
      case [ g | g <- gs, grammarName g == GlobalName "L" ] of
        [g] ->
          [ (gproductionName p, map argumentRole (gproductionArguments p))
          | p <- grammarProductions g ]
            @?= [ (GlobalName "var", [Occurrence (GlobalName "x")])
                , (GlobalName "abs", [Binder (GlobalName "x"), Scope [0]])
                , (GlobalName "big", [Binder (GlobalName "X"), Scope [0]])
                ]
        other -> assertFailure (show (length other) ++ " grammars called L")
    -- **It installs, and it warns** — the second principle: a grammar binding a
    -- class it does not read is what `~5k3mg` is for, so it is not refused, but
    -- until the generator is class-aware @L-subst-all@ renames that binder as
    -- one of @L@'s own variables, and an author should see that said.
  , testCase "and the block installs with a warning, because the generator is not class-aware yet" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 twoClasses of
        (_, ProofLoaded _ names _ ws) -> do
          names @?= ["x", "X", "L"]
          ws @?= [BinderClassUnowned LanguageBlock "L" "big" "X"]
        (_, other) -> assertFailure (show other)
    -- **A binder scoping into another language installs now** (MS8 phase 154),
    -- where the refusal was unconditional before, and warns for the same reason
    -- the one above does: a method of @L-subst-all@ is given a recursive result
    -- only for an argument of its own language, so @R@ is rebuilt as written
    -- while the binder beside it is renamed.
  , testCase "a binder free in another language's slot installs, and warns" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 foreignScope of
        (_, ProofLoaded _ names _ ws) -> do
          names @?= ["x", "P", "L"]
          ws @?= [ScopeUnwalked LanguageBlock "L" "f" "R"]
        (_, other) -> assertFailure (show other)
  , testCase "a later module may use an earlier one's metavariables" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource s0 stlc
      case loadProofSource s1 "module More where\n\nlanguage P, Q where\n  tuple -> ( M , T )\n" of
        (_, ProofLoaded {}) -> pure ()
        (_, other) -> assertFailure (show other)
  -- Written out a second time: a name DROPPED from 'builtInTags' would pass
  -- the walk in 'refused' by disappearing from it.
  , testCase "the built-in tags are exactly these two" $
      builtInTags @?= ["surface", "core"]
    -- **The MS5 form is gone with no trace** (phase 106, his ruling): in a rule
    -- file @language@ is a reserved word that nothing reads, so it is a plain
    -- syntax error and not a message about where languages went.
  , testCase "a rule file may not declare a language" $
      case snd (loadRuleBases newSession
                  [("t.thena.rules", "rule base t where\nlanguage Tm where { var : name }\n")]) of
        RuleFileRefused _ (RuleSyntaxError _) -> pure ()
        other -> assertFailure (show other)
  , testCase "and may not declare a language of the same name" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource s0 stlc
      case loadProofSource s1 "module Again where\n\nlanguage LC, P where\n  f -> P\n" of
        (_, Ran _ _ (Refused (GrammarRefused e))) -> e @?= GrammarError LanguageBlock "LC" NameTaken
        (_, other) -> assertFailure (show other)
  ]
  where
    str = OfClass (GlobalName "x") (GlobalName "String") (regex "[a-z][a-zA-Z0-9']*")
    lang = OfLanguage . GlobalName
    installed src = do
      (s0, _) <- startingSession
      pure (grammars (machineOf (fst (loadProofSource s0 src))))

-- ---------------------------------------------------------------------------

-- | **Which classes a grammar reaches** (MS8 phase 154, `~5k3mg`): the classes
-- its own roles name, and everything the grammars in its slots reach. The
-- generator of phase 155 indexes a substitution by this set, so what is pinned
-- here is the set and its order — this grammar's own first, then first
-- encountered.
--
-- **The cyclic case is the whole reason it is a fixpoint and not a walk in
-- declaration order — his ruling, 2026-10-04.** No source can declare two
-- mutually dependent grammars today (`~m5dvd`), so the graph is built here by
-- hand: a walk that trusted the order, or one with no visited set, would not
-- come back from it.
reaching :: [TestTree]
reaching =
  [ testCase "a class a role of the grammar itself names" $ do
      gs <- installedIn twoClasses
      map (classesReached gs) [grammarCalled gs "L"]
        @?= [[GlobalName "x", GlobalName "X"]]
  , testCase "and nothing for a grammar whose roles name none" $ do
      gs <- installedIn stlc
      classesReached gs (grammarCalled gs "Ty") @?= []
  , testCase "a class reached through two slots, named by neither grammar between" $ do
      gs <- installedIn chained
      map (map nameString . classesReached gs . grammarCalled gs) ["P", "Q", "L"]
        @?= [["x"], ["x"], ["x"]]
      map (map nameString . classesNamed . grammarCalled gs) ["P", "Q", "L"]
        @?= [["x"], [], []]
  , testCase "and two grammars that reach each other terminate at the union" $
      map (map nameString . classesReached cyclic) cyclic
        @?= [["u", "v"], ["v", "u"]]
  ]
  where
    -- Loudly, because a module that did not load leaves no grammars at all and
    -- every assertion below would then be about the empty list.
    installedIn src = do
      (s0, _) <- startingSession
      case loadProofSource s0 src of
        (s1, ProofLoaded {}) -> pure (grammars (machineOf s1))
        (s1, other) -> do
          _ <- assertFailure (unlines (renderResponse s1 other))
          pure []
    grammarCalled gs n = case [ g | g <- gs, grammarName g == GlobalName n ] of
      g : _ -> g
      [] -> error ("no grammar called " ++ n)
    nameString (GlobalName n) = n

-- | Two grammars, each with a slot of the other: @A@ reads @u@ and @B@ reads
-- @v@, so each reaches both. Written out because no module can declare it.
cyclic :: [Grammar]
cyclic = [one "A" "u" "B", one "B" "v" "A"]
  where
    one l cls other =
      Grammar LanguageBlock (GlobalName l) [l, l ++ "'"]
        [ GProduction (GlobalName (l ++ "var")) [Slot cls (klass cls) []]
            [Argument cls (klass cls) (Occurrence (GlobalName cls))]
        , GProduction (GlobalName (l ++ "in")) [Slot other (OfLanguage (GlobalName other)) []]
            [Argument other (OfLanguage (GlobalName other)) Plain]
        ]
    klass cls = OfClass (GlobalName cls) (GlobalName "String") (regex "[a-z]+")

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
    -- MS7 phase 127, his ruling of 2026-09-28: the placeholder's glyph is
    -- reserved, and a grammar that could write it or read it is refused so that
    -- one glyph never means two things in one buffer.
  , inProduction "a terminal that writes the placeholder"
      "language L, M where\n  f -> \9608 M" "f" (ReservedTerminal "\9608")
  , inProduction "a terminal that merely contains it"
      "language L, M where\n  f -> a\9608b M" "f" (ReservedTerminal "a\9608b")
    -- **The narrowed refusal** (MS8 phase 154): @P@ has no occurrence at all, so
    -- nothing inside an @R@ can ever be at the class @f@'s binder binds at, and
    -- there is nothing there for substitution to do.
  , ( ( "a binder free in a language that reaches no such class"
      , "module M where\n\nx : Token String\nx = /[a-z]+/\n\n"
          ++ "language P, R where\n  base -> o\n\n"
          ++ "language L, M where\n  var : x as occurrence -> x\n"
          ++ "  f : x as binder -> ( let x = M in R[x] )\n"
      )
    , GrammarError LanguageBlock "L"
        (InProduction "f" (ScopeElsewhere "R" (GlobalName "P") (GlobalName "x")))
    )
  , ( ( "a token class that would read it"
      , "module M where\n\nany : Token String\nany = /./\n\nlanguage L, M where\n  f -> any M\n"
      )
    , GrammarError LanguageBlock "L" (InProduction "f" (ReservedClass "any"))
    )
  ]
    -- **A built-in tag may not name a language** (moved here from MS5's
    -- grammars at phase 106). A rule base reads an installed grammar's tag
    -- first, so @language core@ took every later @core`…`@ for its own. It walks
    -- 'builtInTags' so that a third tag cannot be added to the list alone.
    ++ [ block ("a language named like the built-in tag " ++ t)
               ("language " ++ t ++ ", M where\n  f -> a") BuiltInTag
       | t <- builtInTags ]
  where
    int = OfClass (GlobalName "n") (GlobalName "Int") (regex "[0-9]+")
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

regex :: String -> Regex
regex = either (error . show) id . parseRegex
