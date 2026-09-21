-- | A context's lookup relation (MS6 phase 107; @ms6\/SPEC.md@ §5.3).
--
-- **The proofs are the load-bearing tests.** A lookup at the top of a context
-- is @Ctx-here@; one under a later binding of a different name is @Ctx-there@,
-- whose @ne@ is proved with no axiom from @eqString@ alone, which is what
-- §2.1 promised and what phase 109's proofs will have to do. And a lookup
-- that would skip a binding of the /same/ name is refused, because @ne@ has no
-- proof — that is the shadowing §5.3 generates @ne@ for.
--
-- Around them: what is declared, the notation read and printed back through
-- the same grammar machinery as any object term, where the separator goes when
-- the context slot is last, and what a context must have to be given a lookup.
module Thena.ContextTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Term (Core (..), GlobalName (..), Literal (..))
import Thena.Driver (Response (..), Session (..), command, loadProofSource)
import Thena.Engine (Machine (..))
import Thena.Language.Build (buildTerm, printTerm)
import Thena.Language.Earley (parse, pieces)
import qualified Thena.Language.Earley as Earley
import Thena.Language.Grammar (earleyRules)
import Thena.Repl (renderResponse, startingSession)

tests :: TestTree
tests =
  testGroup
    "a context's lookup relation"
    [ testGroup "what is declared (§5.3)" declared
    , testGroup "the notation is a grammar" notation
    , testGroup "proofs of lookups" proofs
    , testGroup "what a context needs" refused
    ]

-- ---------------------------------------------------------------------------

header :: [String]
header =
  [ "module Ctx where"
  , ""
  , "x : Token String"
  , "x = /[a-z][a-zA-Z0-9']*/"
  , ""
  , "language Ty, T, S where"
  , "  base  -> \953"
  , "  arrow -> ( T -> S )"
  , ""
  , "context Ctx, \915 where"
  , "  empty  -> \183"
  , "  extend -> \915 , x : T"
  , ""
  ]

-- | @x ≠ y@, from @eqString@ and nothing else: the motive sends a string to
-- @Unit@ when it is @"x"@ and to @Empty@ otherwise, and @Eq@'s eliminator
-- carries @unit@ from one side to the other.
xNotY :: [String]
xNotY =
  [ "xNotY : Eq String \"x\" \"y\" -> Empty"
  , "xNotY = \\ q ->"
  , "  elim Eq (String)"
  , "    (\\ a b r -> elim Comparison () (\\ c -> Type\8320) ((Unit) (Empty)) () (eqString \"x\" a)"
  , "                -> elim Comparison () (\\ c -> Type\8320) ((Unit) (Empty)) () (eqString \"x\" b))"
  , "    ((\\ a d -> d))"
  , "    (\"x\" \"y\") q unit"
  , ""
  ]

-- | Load a module and answer with the session, or the refusal's last line.
load :: [String] -> IO (Either String Session)
load body = do
  (s0, _) <- startingSession
  pure $ case loadProofSource s0 (unlines body) of
    (s1, ProofLoaded {}) -> Right s1
    (s1, other) -> Left (last (renderResponse s1 other))

loaded :: [String] -> IO Session
loaded body = load body >>= either assertFailure pure

said :: Session -> String -> [String]
said s line = let (s', r) = command s line in renderResponse s' r

-- ---------------------------------------------------------------------------

declared :: [TestTree]
declared =
  [ testCase ":show prints the relation and both constructors" $ do
      s <- loaded header
      said s ":show Ctx-in" @?=
        [ "data Ctx-in : String -> Ty -> Ctx -> Type\8320 where"
        , "  { Ctx-here : \8704 (\915 : Ctx) (x : String) (T : Ty) -> Ctx-in x T (extend \915 x T)"
        , "  ; Ctx-there : \8704 (\915 : Ctx) (x : String) (T : Ty) (x' : String) (T' : Ty)"
            ++ " -> (Eq {0} String x x' -> Empty {0}) -> Ctx-in x T \915 -> Ctx-in x T (extend \915 x' T') }"
        ]
  ]

notation :: [TestTree]
notation =
  [ testCase "the notation is read and built as the relation applied" $ do
      s <- loaded header
      let gs = grammars (sessionMachine s)
      case parse (earleyRules gs) (Earley.StartAt "Ctx-in") (pieces "x : \953 \8712 \183 , y : \953") of
        Left why -> assertFailure (show why)
        Right tree -> buildTerm gs tree @?= Right
          (apps "Ctx-in" [str "x", con "base", apps "extend" [con "empty", str "y", con "base"]])
  , testCase "and prints back as the text it was read from" $ do
      s <- loaded header
      let m = sessionMachine s
      printTerm (globals m) (grammars m)
          (apps "Ctx-in" [str "x", con "base", apps "extend" [con "empty", str "x", con "base"]])
        @?= Just "x : \953 \8712 \183 , x : \953"
  , testCase "a lookup literal is a type" $ do
      s <- loaded header
      said s ":infer Ctx-in`x : \953 \8712 \183`" @?= ["Ctx-in`x : \953 \8712 \183` : Type\8320"]
    -- **The separator is the terminals between the context slot and its
    -- neighbouring slot** — the next one, or the previous when it is last.
  , testCase "a context written with its slot last loses the separator before it" $ do
      s <- loaded
        [ "module Last where", "", "x : Token String", "x = /[a-z]+/", ""
        , "language Ty, T where", "  base -> \953", ""
        , "context D, \916 where", "  none -> \949", "  push -> x : T ; \916", "" ]
      said s ":show D-in" !! 0 @?= "data D-in : String -> Ty -> D -> Type\8320 where"
      case parse (earleyRules (grammars (sessionMachine s))) (Earley.StartAt "D-in")
                 (pieces "x : \953 \8712 x : \953 ; \949") of
        Left why -> assertFailure (show why)
        Right _ -> pure ()
  ]
  where
    str = Primitive . LString
    con n = Global (GlobalName n) []
    apps f = foldl App (con f)

proofs :: [TestTree]
proofs =
  [ testCase "a lookup at the top is Ctx-here" $ do
      _ <- loaded (header ++
        [ "found : Ctx-in`x : \953 \8712 \183, x : \953`"
        , "found = Ctx-here empty \"x\" base" ])
      pure ()
  , testCase "one under a later binding of another name is Ctx-there, with ne proved" $ do
      _ <- loaded (header ++ xNotY ++
        [ "under : Ctx-in`x : \953 \8712 \183, x : \953, y : \953`"
        , "under = Ctx-there (extend empty \"x\" base) \"x\" base \"y\" base xNotY (Ctx-here empty \"x\" base)" ])
      pure ()
  , testCase "Ctx-here does not reach under a later binding" $ do
      r <- load (header ++
        [ "wrong : Ctx-in`x : \953 \8712 \183, x : \953, y : \953`"
        , "wrong = Ctx-here (extend empty \"x\" base) \"x\" base" ])
      either (const (pure ())) (const (assertFailure "Ctx-here was accepted under y")) r
    -- The shadowing: to reach the earlier x past a later x, ne must prove
    -- x ≠ x, and xNotY is a proof of something else.
  , testCase "and Ctx-there cannot skip a binding of the same name" $ do
      r <- load (header ++ xNotY ++
        [ "shadowed : Ctx-in`x : \953 \8712 \183, x : \953, x : ( \953 -> \953 )`"
        , "shadowed = Ctx-there (extend empty \"x\" base) \"x\" base \"x\" (arrow base base) xNotY (Ctx-here empty \"x\" base)" ])
      either (const (pure ())) (const (assertFailure "a shadowed binding was reached")) r
    -- And what it would take is exactly a refutation of refl: reaching the
    -- earlier x needs Eq String "x" "x" -> Empty, which applied to refl is
    -- Empty. So the shadowed binding cannot be reached by any term.
  , testCase "what it would take is a proof that x is not x" $ do
      _ <- loaded (header ++
        [ "needs : (Eq String \"x\" \"x\" -> Empty) -> Ctx-in`x : \953 \8712 \183, x : \953, x : ( \953 -> \953 )`"
        , "needs = \\ ne -> Ctx-there (extend empty \"x\" base) \"x\" base \"x\" (arrow base base) ne (Ctx-here empty \"x\" base)"
        , ""
        , "absurdly : (Eq String \"x\" \"x\" -> Empty) -> Empty"
        , "absurdly = \\ ne -> ne (refl String \"x\")" ])
      pure ()
  ]

refused :: [TestTree]
refused =
  [ refusal "an extension with no name"
      ["context C, G where", "  e -> \183", "  f -> G , T"]
      "refused: in the context C: its extension needs exactly one name to look up, and it has none"
  , refusal "an extension with two"
      ["y : Token String", "y = /[a-z]+/", "", "context C, G where", "  e -> \183", "  f -> G , x = y : T"]
      "refused: in the context C: its extension needs exactly one name to look up, and it has x, y"
  , refusal "a lookup name already declared"
      ["C-here : Ty", "C-here = base", "", "context C, G where", "  e -> \183", "  f -> G , x : T"]
      "refused: C's lookup C-here is already declared"
  ]
  where
    refusal what body want = testCase what $ do
      r <- load (take 9 header ++ body)
      either (@?= want) (const (assertFailure "it loaded")) r
