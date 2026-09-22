-- | **Printing a term in its own language's notation, and reading it back**
-- (MS6 phase 110; @ms6\/CLOSEOUT.md@ 11 and 30).
--
-- **The crossing is printer against reader, and the reader is the real one.**
-- A printed term is a tagged term literal with splices in it, which the object
-- grammar alone cannot read — a splice is the host's syntax. So what reads the
-- printer's output back here is 'parseCore', the development calculus's own
-- reader, which is exactly what the phase added so that a goal can be typed
-- back.
--
-- What the cases assert that the property cannot: **where the fences land**.
-- Any set of fences that reads back is correct, so a property can only say
-- that the printer is honest; only a case can say it writes what a person
-- would write.
module Thena.PrintTests (tests) where

import Test.Tasty (TestTree, testGroup, withResource)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import Test.Tasty.QuickCheck
  (Gen, counterexample, elements, forAll, ioProperty, oneof, property, sized, testProperty, withNumTests, (===))

import Thena.Core.Term (Core (..), GlobalName (..), Literal (..))
import Thena.Driver (Response (..), Session (..), loadProofSource, parseCore)
import Thena.Engine (Machine (..))
import Thena.Errors (ObjectError (..), ResolveError (..), SyntaxError (..))
import Thena.Global.Env (GlobalEnv)
import Thena.Language.Build (printTerm)
import Thena.Language.Grammar (Grammar)
import Thena.Repl (renderCore, startingSession)

tests :: TestTree
tests =
  testGroup
    "a term prints in its language's notation"
    [ testGroup "notation, and what cannot be written in it" notation
    , testGroup "fences, where the grammar leaves a term ambiguous" fences
    , testGroup "the development calculus reads a region back" reading
    , roundTrip
    ]

-- ---------------------------------------------------------------------------

-- | Three languages: one that brackets its productions, one that does not, and
-- one whose token class matches its own terminals.
--
-- **@Coll@ is contrived on purpose.** Its identifiers are one letter and its
-- keywords are @l@ and @i@, so that a variable can be spelled like a terminal
-- without the language also being ambiguous about where one identifier ends —
-- which a class of longer words would be, under bare juxtaposition. What it
-- stands for is the real case: nothing is reserved inside an object language,
-- so @let f = a in in b@ is a term someone can write.
source :: String
source =
  unlines
    [ "module Printing where"
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
    , "judgment written = U ! where"
    , ""
    , "  W:  -----"
    , "      U !"
    , ""
    , "language Coll, P, Q where"
    , "  cref  : c as occurrence -> c"
    , "  cjux                    -> P Q"
    , "  clet  : c as binder     -> l c = P i Q[c]"
    ]

loaded :: IO (GlobalEnv, [Grammar])
loaded = do
  (s0, _) <- startingSession
  case loadProofSource s0 source of
    (s1, ProofLoaded {}) -> pure (globals (sessionMachine s1), grammars (sessionMachine s1))
    (_, other) -> assertFailure (show other)

-- | A constructor applied, as the reader leaves it.
con :: String -> [Core] -> Core
con name = foldl App (Global (GlobalName name) [])

str :: String -> Core
str = Primitive . LString

-- | The host's printer, for what a splice holds.
host :: Core -> String
host = renderCore [] 0 []

printed :: [Grammar] -> Core -> IO String
printed gs t = maybe (assertFailure "it did not print") pure (printTerm gs host t)

-- ---------------------------------------------------------------------------

notation :: [TestTree]
notation =
  [ testCase "a bracketed grammar needs no fences" $ do
      (_, gs) <- loaded
      t <- printed gs (con "abs" [str "x", con "base" [], con "var" [str "x"]])
      t @?= "LC`( \955 x : \953 . x )`"
  , testCase "a term of one application, in a grammar that brackets nothing" $ do
      (_, gs) <- loaded
      t <- printed gs (con "juxt" [con "ref" [str "f"], con "ref" [str "a"]])
      t @?= "Ex`f a`"
    -- The printer prints what is there: a global stands for itself rather than
    -- being unfolded into the term it is defined as.
  , testCase "what the notation cannot write goes in a splice" $ do
      (_, gs) <- loaded
      t <- printed gs (con "app" [Global (GlobalName "twice") [], con "var" [str "y"]])
      t @?= "LC`( ${twice} y )`"
    -- A class prints its match only if the class would read it back.
    -- **A term whose own name is not object text nests a region inside a
    -- splice** — the shape a goal shows for @var x@ when @x@ is not a literal.
    -- Inline it would be @( ${nom} y )@, which says the /term/ slot holds
    -- @nom@, and @nom@ is a 'String' where the grammar wants an @LC@.
  , testCase "a name that is not a literal makes a region inside a splice" $ do
      (_, gs) <- loaded
      t <- printed gs (con "app" [con "var" [Global (GlobalName "nom") []], con "var" [str "y"]])
      t @?= "LC`( ${LC`${nom}`} y )`"
  , testCase "a name the class would not read back is spliced" $ do
      (_, gs) <- loaded
      t <- printed gs (con "var" [str "a b"])
      t @?= "LC`${\"a b\"}`"
  , testCase "a term of no language does not print" $ do
      (_, gs) <- loaded
      printTerm gs host (str "x") @?= Nothing
  ]

fences :: [TestTree]
fences =
  [ -- @examples/05@ writes both of these by hand; the printer writes the same.
    testCase "the left operand of a juxtaposition is fenced" $ do
      (_, gs) <- loaded
      t <- printed gs (con "juxt" [con "juxt" [con "ref" [str "f"], con "ref" [str "a"]], con "ref" [str "b"]])
      t @?= "Ex`${Ex`f a`} b`"
    -- **The order of fencing is what this asserts.** Fencing the leftmost
    -- child first would settle it too, as @${Ex`f`} ${Ex`a b`}@ — correct, and
    -- not what anyone would write.
  , testCase "and the right operand, rather than both" $ do
      (_, gs) <- loaded
      t <- printed gs (con "juxt" [con "ref" [str "f"], con "juxt" [con "ref" [str "a"], con "ref" [str "b"]]])
      t @?= "Ex`f ${Ex`a b`}`"
    -- **Deepest first, which is what a judgment's argument shows.** Fencing
    -- the outermost subterm would settle this too, as @${Ex`${Ex`f a`} b`} !@:
    -- the whole argument wrapped for the sake of its left half.
  , testCase "a fence is as small as the disagreement, not as big as the slot" $ do
      (_, gs) <- loaded
      t <- printed gs (con "written"
             [con "juxt" [con "juxt" [con "ref" [str "f"], con "ref" [str "a"]], con "ref" [str "b"]]])
      t @?= "written`${Ex`f a`} b !`"
  , testCase "a term the grammar reads one way is written flat" $ do
      (_, gs) <- loaded
      t <- printed gs (con "clet" [str "f", con "cjux" [con "cref" [str "a"], con "cref" [str "b"]], con "cref" [str "c"]])
      t @?= "Coll`l f = a b i c`"
    -- **The same position and the same child production, fenced** — because of
    -- the text, which no table over the grammar's shape could see: the bound
    -- occurrence is spelled like the keyword that ends the first slot.
  , testCase "the same term with a variable spelled like a terminal is fenced" $ do
      (_, gs) <- loaded
      t <- printed gs (con "clet" [str "f", con "cjux" [con "cref" [str "a"], con "cref" [str "i"]], con "cref" [str "b"]])
      t @?= "Coll`l f = ${Coll`a i`} i b`"
  ]

reading :: [TestTree]
reading =
  [ testCase "what the printer wrote is what the reader reads" $ do
      (env, gs) <- loaded
      let t = con "juxt" [con "ref" [str "f"], con "juxt" [con "ref" [str "a"], con "ref" [str "b"]]]
      src <- printed gs t
      fmap fst (parseCore gs env [] 0 src) @?= Right t
  , testCase "including the fenced one, whose splices are regions again" $ do
      (env, gs) <- loaded
      let t = con "clet" [str "f", con "cjux" [con "cref" [str "a"], con "cref" [str "i"]], con "cref" [str "b"]]
      src <- printed gs t
      fmap fst (parseCore gs env [] 0 src) @?= Right t
  , testCase "a splice may hold any term, not only a region" $ do
      (env, gs) <- loaded
      fmap fst (parseCore gs env [] 0 "LC`( ${app LC`x` LC`y`} z )`")
        @?= Right (con "app" [ con "app" [con "var" [str "x"], con "var" [str "y"]]
                             , con "var" [str "z"] ])
  , testCase "a tag naming no language is refused, as it is in the surface" $ do
      (env, gs) <- loaded
      parseCore gs env [] 0 "Nope`x`"
        @?= Left (ResolveFailed (NotAnObjectTerm (NoSuchObjectLanguage "Nope")))
  , testCase "and a production the language does not have" $ do
      (env, gs) <- loaded
      parseCore gs env [] 0 "LC[nope]`x`"
        @?= Left (ResolveFailed (NotAnObjectTerm (NoSuchObjectProduction "LC" "nope")))
  , testCase "text that is not one term of the language says where it stuck" $ do
      (env, gs) <- loaded
      case parseCore gs env [] 0 "LC`( )`" of
        Left (ResolveFailed (NotAnObjectTerm (ObjectNotParsed "LC" "( )" _))) -> pure ()
        other -> assertFailure (show (fmap fst other))
  ]

-- ---------------------------------------------------------------------------

-- | Terms of the bracket-free language, built without the grammar.
--
-- **One-letter names**, because @Ex@'s class reads longer words and its
-- juxtaposition is bare, so @ab@ would be two readings of one text and no
-- fence could settle it — a grammar's own ambiguity, not the printer's.
genEx :: Gen Core
genEx = sized go
  where
    go 0 = (\x -> con "ref" [str x]) <$> name
    go k = oneof
      [ (\x -> con "ref" [str x]) <$> name
      , (\a b -> con "juxt" [a, b]) <$> go (k `div` 2) <*> go (k `div` 2)
      ]
    name = elements ["f", "a", "b", "g"]

-- | **Printed and read back, a term is itself** — through the development
-- calculus's reader, so the splices the printer writes are part of the claim.
roundTrip :: TestTree
roundTrip =
  withResource loaded (const (pure ())) $ \io ->
    testProperty "printed and read back by the DC reader, a term is itself" $
      withNumTests 200 $ forAll genEx $ \t -> ioProperty $ do
        (env, gs) <- io
        pure $ case printTerm gs host t of
          Nothing -> counterexample "it did not print" (property False)
          Just src -> counterexample src (fmap fst (parseCore gs env [] 0 src) === Right t)
