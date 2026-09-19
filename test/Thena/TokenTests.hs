-- | Token classes (MS6 phase 100; @ms6\/SPEC.md@ §3).
--
-- A token class is an ordinary definition whose type is @Token T@ and whose
-- body is a regex literal. The literal's type is @∀ (T : Type₀) -> Token T@, so
-- elaboration applies it to a hole and unification finds @T@ in the goal — his
-- ruling of 2026-09-19. What the kernel accepts, @\/[a-z]+\/ Char@ included, is
-- then judged at declaration ('Thena.Driver.checkedTokenClass').
--
-- **Each refusal is asserted as the structured value**, not as its sentence:
-- the golden pins the wording, and these pin what it is about — the name, the
-- text, the type, the witness.
module Thena.TokenTests (tests) where

import Data.ByteString.Builder (stringUtf8, toLazyByteString)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Reduce (whnf)
import Thena.Core.Term (Core (..), GlobalName (..), Literal (..))
import Thena.Driver (Response (..), Session (..), Stop (..), loadProofSource)
import Thena.Engine (Machine (..))
import Thena.Global.Declare (DeclareError (..), TokenClassError (..))
import Thena.Global.Env (definitionBody, lookupDefinition)
import Thena.Language.Regex (RegexError (..))
import Thena.Repl (renderResponse, startingSession, transcriptFrom)
import Thena.Syntax.Lexer (Located (..), Token (..), lexTokens)

tests :: TestTree
tests =
  testGroup
    "token classes"
    [ testGroup "the regex literal is a lexeme" lexing
    , testGroup "a class is elaborated like any definition" accepted
    , testGroup "and refused at declaration when it is not a class" refusals
    , goldenVsString "tokens" "test/golden/tokens.golden" $ do
        (s0, problems) <- startingSession
        let run (title, src) =
              let (s1, r) = loadProofSource s0 src
               in ("-- " ++ title) : renderResponse s1 r
        pure (toLazyByteString (stringUtf8
          (unlines (problems ++ concatMap run (good : bad)) ++ transcriptFrom s0 prompt)))
    ]

-- | The same checks reached from @qed@, which admits a definition by the other
-- route into 'Thena.Global.Env.addDefinition' — and a refused class leaves the
-- proof standing, as a level failure does, so it can be repaired. Then the
-- literal at the prompt: in the DC with @T@ written, and in the surface with @T@
-- found — or, with nothing to find it from, not found.
prompt :: [String]
prompt =
  [ ":theorem d : Token Char"
  , "fill \8988 /[a-z]+/ Char \8989"
  , "solve"
  , "qed"
  , ":abandon"
  , ":theorem e : Token Char"
  , "fill \8988 /[a-z]/ Char \8989"
  , "solve"
  , "qed"
  , ":show e"
  , ":core /a\\/b/ Comparison"
  , ":infer (/[a-z]/ : Token Char)"
  , ":infer /[a-z]/"
  ]

-- ---------------------------------------------------------------------------

lexing :: [TestTree]
lexing =
  [ lexes "a literal is the text between the slashes" "/[a-z]+/" [TRegex "[a-z]+"]
  , lexes "an escaped slash does not close it, and stays escaped" "/a\\/b/" [TRegex "a\\/b"]
  , lexes "reserved characters inside are just text" "/(λ|[x])/" [TRegex "(\955|[x])"]
  , lexes "it is a token among others" "x = /a/ ;" [TIdent "x", TEquals, TRegex "a", TSemi]
  , lexes "a slash inside a name is still a name" "\8706f/\8706x" [TIdent "\8706f/\8706x"]
  , testCase "an empty literal is not a token" $
      case lexTokens "//" of
        Left _ -> pure ()
        Right ts -> assertFailure ("lexed as " ++ show (map unLoc ts))
  ]
  where
    lexes name src want = testCase name $ case lexTokens src of
      Left e -> assertFailure (show e)
      Right ts -> map unLoc ts @?= want
    unLoc (Located _ t) = t

-- ---------------------------------------------------------------------------

good :: (String, String)
good =
  ( "a module of classes"
  , unlines
      [ "module Good where"
      , ""
      , "ident : Token String"
      , "ident = /[a-z][a-zA-Z0-9']*/"
      , ""
      , "digit : Token Char"
      , "digit = /[0-9]/"
      , ""
      , "numeral : Token Int"
      , "numeral = /-?[1-9][0-9]*|0/"
      , ""
      , "again : Token String"
      , "again = ident"
      , ""
      , "Name : Type\8320"
      , "Name = String"
      , ""
      , "var : Token Name"
      , "var = /[a-z]+/"
      ]
  )

accepted :: [TestTree]
accepted =
  [ testCase "the module loads" $ do
      (s0, _) <- startingSession
      case loadProofSource s0 (snd good) of
        (_, ProofLoaded {}) -> pure ()
        (_, other) -> assertFailure (show other)
  , -- The point of the ruling: T is not in the literal, it is the argument
    -- unification found — and found from the annotation, not defaulted.
    testCase "T is the argument, and it came from the annotation" $ do
      (s0, _) <- startingSession
      let (s1, _) = loadProofSource s0 (snd good)
          env = globals (sessionMachine s1)
          value g = whnf env [] . definitionBody <$> lookupDefinition (GlobalName g) env
      map value ["ident", "digit", "numeral", "again"]
        @?= map Just
          [ App (Primitive (LRegex "[a-z][a-zA-Z0-9']*")) (named "String")
          , App (Primitive (LRegex "[0-9]")) (named "Char")
          , App (Primitive (LRegex "-?[1-9][0-9]*|0")) (named "Int")
          , App (Primitive (LRegex "[a-z][a-zA-Z0-9']*")) (named "String")
          ]
  ]
  where
    named g = Global (GlobalName g) []

-- ---------------------------------------------------------------------------

-- | One module per check, in §3.2's order, with the value each must refuse with.
bad :: [(String, String)]
bad = map fst refused

refused :: [((String, String), DeclareError)]
refused =
  [ klass "T is not one of the three"
      [ "data Bool : Type\8320 where"
      , "  true : Bool"
      , "  false : Bool"
      , ""
      , "t : Token Bool"
      , "t = /x/"
      ]
      (TokenClassRefused (GlobalName "t") (TokenTypeUnsupported (Canonical (GlobalName "Bool") [] [])))
  , klass "the regex does not parse: a stray metacharacter"
      ["f : Token String", "f = /a{3}/"]
      (refusedRegex "f" "a{3}" (RegexUnexpected 1 '{'))
  , klass "the regex does not parse: it ends too soon"
      ["g : Token String", "g = /(ab/"]
      (refusedRegex "g" "(ab" RegexUnexpectedEnd)
  , klass "the regex does not parse: an escape other dialects have"
      ["c : Token String", "c = /\\S+/"]
      (refusedRegex "c" "\\S+" (RegexUnsupportedEscape 1 'S'))
  , klass "the regex does not parse: a reversed range"
      ["d : Token String", "d = /[z-a]/"]
      (refusedRegex "d" "[z-a]" (RegexReversedRange 3 'z' 'a'))
  , klass "it matches the empty string"
      ["b : Token String", "b = /a*/"]
      (TokenClassRefused (GlobalName "b") (TokenMatchesEmpty "a*"))
  , klass "it accepts something that is not a Char"
      ["e : Token Char", "e = /ab|c/"]
      (TokenClassRefused (GlobalName "e") (TokenNotIncluded "ab|c" (GlobalName "Char") "ab"))
  , klass "it accepts something that is not an Int, and says the shortest"
      ["n : Token Int", "n = /[a-z]+/"]
      (TokenClassRefused (GlobalName "n") (TokenNotIncluded "[a-z]+" (GlobalName "Int") "a"))
  ]
  where
    klass title body e = ((title, unlines ("module M where" : "" : body)), e)
    refusedRegex g src r = TokenClassRefused (GlobalName g) (TokenRegexRefused src r)

refusals :: [TestTree]
refusals =
  [ testCase title $ do
      (s0, _) <- startingSession
      case loadProofSource s0 src of
        (_, Ran _ _ (Refused e)) -> e @?= want
        (_, other) -> assertFailure (show other)
  | ((title, src), want) <- refused
  ]
