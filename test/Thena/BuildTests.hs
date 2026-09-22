-- | What a @language@ block generates, and terms of it (MS6 phase 103;
-- @ms6\/SPEC.md@ §4.6, §4.7).
--
-- **The round trip is the load-bearing test**: a random term of the generated
-- datatype, built by a generator that knows nothing of the grammar, is printed
-- by 'printTerm', parsed by the Earley parser, and built back by 'buildTerm' —
-- and must be the term it started as. Printer against parser, each written
-- without the other.
--
-- The rest assert what the block generated: the constructors and their
-- argument types, which are §4.6's, and the roles on them, which are §4.7's
-- and which generated substitution will read in phase 105.
module Thena.BuildTests (tests) where

import Test.Tasty (TestTree, testGroup, withResource)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import Test.Tasty.QuickCheck
  (Gen, counterexample, elements, forAll, ioProperty, oneof, property, sized, testProperty, withNumTests, (===))

import Thena.Core.Context (entryType)
import Thena.Core.Reduce (whnf)
import Thena.Core.Term (Core (..), GlobalName (..), Literal (..))
import Thena.Core.Typing (infer)
import Thena.Driver (Response (..), Session (..), Stop (..), loadProofSource)
import Thena.Engine (Machine (..))
import Thena.Global.Env
  ( ArgRole (..)
  , ConstructorDefinition (..)
  , GlobalEnv
  , InductiveDefinition (..)
  , definitionBody
  , lookupDefinition
  , lookupInductive
  )
import Thena.Errors (ObjectError (..), BuildError (..), FailReason (..))
import Thena.Language.Build (buildTerm, printRegion)
import Thena.Language.Earley (parse, pieces)
import qualified Thena.Language.Earley as Earley
import Thena.Language.Grammar (Grammar, earleyRules)
import Thena.Repl (renderCore, startingSession)

tests :: TestTree
tests =
  testGroup
    "a language's datatype and its terms"
    [ testGroup "what the block generated (§4.6)" generated
    , testGroup "the roles on the constructors (§4.7)" roles
    , testGroup "a reading becomes a term, and back (§8)" terms
    , testGroup "a tagged term literal elaborates (§8)" literals
    , roundTrip
    ]

-- ---------------------------------------------------------------------------

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
    , "  arrow -> ( T -> S )"
    , ""
    , "language LC, M, N, E where"
    , "  var : x as occurrence -> x"
    , "  abs : x as binder     -> ( \955 x : T . E[x] )"
    , "  app                   -> ( M N )"
    , "  paren                 -> [ LC ]"
    , "  twice                 -> { M M }"
    , ""
    , "context Ctx, \915 where"
    , "  empty  -> \183"
    , "  extend -> \915 , x : T"
    ]

-- | The session with it loaded: the environment and the grammars.
loaded :: IO (GlobalEnv, [Grammar])
loaded = do
  (s0, _) <- startingSession
  case loadProofSource s0 stlc of
    (s1, ProofLoaded {}) -> pure (globals (sessionMachine s1), grammars (sessionMachine s1))
    (_, other) -> assertFailure (show other)

datatypeOf :: String -> IO InductiveDefinition
datatypeOf name = do
  (env, _) <- loaded
  maybe (assertFailure (name ++ " was not declared")) pure (lookupInductive (GlobalName name) env)

-- ---------------------------------------------------------------------------

generated :: [TestTree]
generated =
  [ testCase "LC's constructors are §4.6's, arguments in order of first appearance" $ do
      d <- datatypeOf "LC"
      map shape (inductiveConstructors d)
        @?= [ ("var", ["String"])
            , ("abs", ["String", "Ty", "LC"])
            , ("app", ["LC", "LC"])
              -- A slot named like its own language: the binder is renamed, the
              -- argument's type is the datatype.
            , ("paren", ["LC"])
              -- §4.3: a name written twice is one argument.
            , ("twice", ["LC"])
            ]
  , testCase "a context's datatype is generated too" $ do
      d <- datatypeOf "Ctx"
      map shape (inductiveConstructors d) @?= [("empty", []), ("extend", ["Ctx", "String", "Ty"])]
  , testCase "the language it refers to is generated as well" $ do
      d <- datatypeOf "Ty"
      map shape (inductiveConstructors d) @?= [("base", []), ("arrow", ["Ty", "Ty"])]
  ]
  where
    shape c =
      ( case constructorName c of GlobalName n -> n
      , [ typeName (entryType e) | e <- constructorArguments c ]
      )
    typeName t = case t of
      Global (GlobalName n) _ -> n
      Canonical (GlobalName n) _ _ -> n
      _ -> show t

roles :: [TestTree]
roles =
  [ testCase "abs binds its name in its body, var's name is an occurrence" $ do
      d <- datatypeOf "LC"
      map constructorRoles (inductiveConstructors d)
        @?= [[Occurrence], [Binder, Plain, Scope [0]], [Plain, Plain], [Plain], [Plain]]
  , testCase "a datatype written by hand has none of it" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 "module W where\n\ndata Pair : Type\8320 where\n  mk : String -> String -> Pair\n" of
        (s1, ProofLoaded {}) ->
          case lookupInductive (GlobalName "Pair") (globals (sessionMachine s1)) of
            Just d -> map constructorRoles (inductiveConstructors d) @?= [[Plain, Plain]]
            Nothing -> assertFailure "Pair was not declared"
        (_, other) -> assertFailure (show other)
  ]

-- ---------------------------------------------------------------------------

-- | @abs "x" base (var "x")@, as elaboration would build it.
identity :: Core
identity = con "abs" [Primitive (LString "x"), con "base" [], con "var" [Primitive (LString "x")]]

con :: String -> [Core] -> Core
con name = foldl App (Global (GlobalName name) [])

terms :: [TestTree]
terms =
  [ testCase "a reading becomes the constructor application" $ do
      (_, gs) <- loaded
      readTerm gs "( \955 x : \953 . x )" @?= Right identity
  , testCase "and the term type checks as an LC" $ do
      (env, _) <- loaded
      case infer env [] 0 identity of
        (Right t, _, _) -> t @?= Global (GlobalName "LC") []
        (Left e, _, _) -> assertFailure (show e)
  , testCase "the term prints as the text" $ do
      (_, gs) <- loaded
      printRegion gs host identity @?= Just "( \955 x : \953 . x )"
  , testCase "a name written twice is one argument, and prints twice" $ do
      (_, gs) <- loaded
      let t = con "twice" [con "var" [Primitive (LString "a")]]
      (readTerm gs "{ a a }", printRegion gs host t) @?= (Right t, Just "{ a a }")
  , testCase "a hole is not a term" $ do
      (_, gs) <- loaded
      readTerm gs "( \955 ? : \953 . x )" @?= Left (Incomplete "x")
  , testCase "a name the class would not read back is spliced instead" $ do
      (_, gs) <- loaded
      printRegion gs host (con "var" [Primitive (LString "a b")])
        @?= Just "${\"a b\"}"
  , testCase "nor does a term that is not a constructor of a grammar" $ do
      (_, gs) <- loaded
      printRegion gs host (Primitive (LString "x")) @?= Nothing
  ]

-- ---------------------------------------------------------------------------

-- | The host\'s printer, for what a splice holds. The real one, so that a
-- spliced term is written the way a reader would take it back.
host :: Core -> String
host = renderCore [] 0 []

-- | What a definition written with a tagged term literal elaborated to, or why
-- the load stopped (MS6 phase 104).
--
-- **The whole load and not the op alone**, because what §8 claims is that
-- @LC`( \955 x : \953 . x )`@ /is/ @abs "x" base (var "x")@ — the application the
-- op writes out has still to elaborate, and its splices with it. The body is
-- reduced because elaboration leaves a chain of @let@s (@ms4\/CLOSEOUT.md@ 8).
elaborated :: String -> IO (Either FailReason Core)
elaborated decls = do
  (s0, _) <- startingSession
  case loadProofSource s0 (stlc ++ "\n" ++ decls ++ "\n") of
    (s1, ProofLoaded {}) ->
      let env = globals (sessionMachine s1)
       in case lookupDefinition (GlobalName "t") env of
            Just d  -> pure (Right (whnf env [] (definitionBody d)))
            Nothing -> assertFailure "t was not declared"
    (_, Ran _ _ (Halted why)) -> pure (Left why)
    (_, other) -> assertFailure (show other)

-- | @t = \8249literal\8250@, and nothing else.
elaboratedTerm :: String -> IO (Either FailReason Core)
elaboratedTerm src = elaborated ("t : LC\nt = " ++ src)

literals :: [TestTree]
literals =
  [ -- **The wrapper applied, and reduced**, which is what elaborating any
    -- application gives: 'buildTerm' writes the same term unreduced, and
    -- 'printTerm' takes either.
    testCase "the text is parsed with the language's grammar" $
      elaboratedTerm ("LC" ++ region "( \955 x : \953 . x )")
        >>= (@?= Right (canon "abs" [Primitive (LString "x"), con "base" [], con "var" [Primitive (LString "x")]]))
    -- **Elaboration against the printer**, which is MS6's done-when 3: the
    -- term a literal elaborates to writes back as the text it was written as.
  , testCase "and it prints back as the text it was written as" $ do
      (_, gs) <- loaded
      r <- elaboratedTerm ("LC" ++ region "( \955 x : \953 . x )")
      fmap (printRegion gs host) r @?= Right (Just "( \955 x : \953 . x )")
  , testCase "a splice supplies the slot it stands in" $ do
      r <- elaborated
             ("u : LC\nu = LC[var]" ++ region "q"
                ++ "\n\nt : LC\nt = LC" ++ region "( ${u} ${u} )")
      r @?= Right (canon "app" [Global (GlobalName "u") [], Global (GlobalName "u") []])
    -- **A class slot takes one too**, and what it supplies is the literal: the
    -- constructor's argument there is a @String@, so the splice elaborates at
    -- that type like any other term.
  , testCase "including a slot that is a token class" $ do
      r <- elaboratedTerm ("LC[var]" ++ region "${\"hi\"}")
      r @?= Right (canon "var" [Primitive (LString "hi")])
    -- The region scanner stacks its modes, so a literal inside a splice inside
    -- a literal reads — which is what makes a splice a term and not a name.
  , testCase "and a splice may hold another literal" $ do
      r <- elaboratedTerm
             ("LC" ++ region ("( ${LC[var]" ++ region "a" ++ "} ${LC[var]" ++ region "b" ++ "} )"))
      r @?= Right (canon "app" [con "var" [Primitive (LString "a")], con "var" [Primitive (LString "b")]])
    -- **The brackets really do restrict**, which is the whole of what
    -- @LC[var]@ is for: text that reads as a term does not read as a variable.
  , testCase "a production in brackets starts the parse there, and only there" $ do
      r <- elaboratedTerm ("LC[var]" ++ region "( \955 x : \953 . x )")
      case r of
        Left (ObjectFailed (ObjectNotParsed "LC" _ (Earley.Stuck 0 _)))  -> pure ()
        other -> assertFailure (show other)
    -- **A splice is one column to the parser and several characters to a
    -- reader**, so a position it reports is moved to where that column begins
    -- in the text the message shows.
  , testCase "a position after a splice is reported where the splice is written" $ do
      r <- elaboratedTerm ("LC" ++ region ("( ${LC[var]" ++ region "a" ++ "} @ )"))
      case r of
        Left (ObjectFailed (ObjectNotParsed "LC" text (Earley.Stuck p _)))  -> (text, p) @?= ("( ${\8230} @ )", 7)
        other -> assertFailure (show other)
  , testCase "a tag naming no language is refused" $
      elaboratedTerm ("Nope" ++ region "x") >>= (@?= Left (ObjectFailed (NoSuchObjectLanguage "Nope")))
  , testCase "so is a production the language does not have" $
      elaboratedTerm ("LC[nope]" ++ region "x") >>= (@?= Left (ObjectFailed (NoSuchObjectProduction "LC" "nope")))
    -- **A @?@ is an ordinary character here** (§7.6): MS6 gives a hole no
    -- surface syntax, so this is text the grammar cannot read rather than a
    -- hole that could not be built.
  , testCase "a ? in a literal is a character, not a hole" $ do
      r <- elaboratedTerm ("LC" ++ region "?")
      case r of
        Left (ObjectFailed (ObjectNotParsed "LC" "?" (Earley.Stuck 0 _)))  -> pure ()
        other -> assertFailure (show other)
  ]
  where
    region txt = [toEnum 96] ++ txt ++ [toEnum 96]

-- | A constructor applied, as 'whnf' leaves the head of an elaborated term.
--
-- **Only the head**, which is why the arguments below are written with 'con':
-- weak head normal form reduces the wrapper it is given and nothing under it.
canon :: String -> [Core] -> Core
canon name = Canonical (GlobalName name) []

readTerm :: [Grammar] -> String -> Either BuildError Core
readTerm gs src = case parse (earleyRules gs) (Earley.StartAt "LC") (pieces src) of
  Left why -> Left (NoSuchProduction (show why))
  Right tree -> buildTerm gs tree

-- ---------------------------------------------------------------------------

-- | Terms of the generated datatype, built without the grammar.
genTerm :: Gen Core
genTerm = sized (go (0 :: Int))
  where
    go _ 0 = (\x -> con "var" [Primitive (LString x)]) <$> name
    go d k = oneof
      [ (\x -> con "var" [Primitive (LString x)]) <$> name
      , (\x ty e -> con "abs" [Primitive (LString x), ty, e]) <$> name <*> genTy <*> go d (k `div` 2)
      , (\a b -> con "app" [a, b]) <$> go d (k `div` 2) <*> go d (k `div` 2)
      , (\a -> con "paren" [a]) <$> go d (k `div` 2)
      ]
    name = elements ["x", "y", "foo", "a1"]

genTy :: Gen Core
genTy = sized go
  where
    go 0 = pure (con "base" [])
    go k = oneof [pure (con "base" []), (\a b -> con "arrow" [a, b]) <$> go (k `div` 2) <*> go (k `div` 2)]

-- | **Loaded once for the property**, not per case: 'startingSession' reads
-- the prelude and the rule base, and two hundred of those is a minute.
roundTrip :: TestTree
roundTrip =
  withResource loaded (const (pure ())) $ \io ->
    testProperty "printed and read back, a term is itself" $
      withNumTests 200 $ forAll genTerm $ \t -> ioProperty $ do
        (_, gs) <- io
        pure $ case printRegion gs host t of
          Nothing -> counterexample "it did not print" (property False)
          Just src -> counterexample src (readTerm gs src === Right t)
