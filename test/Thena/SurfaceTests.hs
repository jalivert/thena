{-# LANGUAGE OverloadedLists #-}

-- | The surface language's tree and its parser (MS4 phase 39).
--
-- **Exact trees, not round trips.** The standing lesson from phases 2–5 is that
-- @parse . render == id@ can pass while a real bug hides, because a
-- self-consistent error agrees with itself. So every case here either builds
-- the tree by hand and compares, or pins an exact string — and the round trip
-- is a third check on top, over a fixed corpus, never the only one.
-- **'genSurface' is exported** so that @SurfaceZipperTests@ walks the same
-- corpus (2026-09-13). A second copy of a generator drifts.
module Thena.SurfaceTests (tests, genSurface) where

import Data.List.NonEmpty (NonEmpty (..))
import Data.List (intercalate)
import Data.List.NonEmpty (nonEmpty)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertFailure, testCase, (@?=))
import Test.Tasty.QuickCheck
  ( Gen, counterexample, elements, forAll, frequency, listOf, listOf1, oneof, property
  , resize, sized, testProperty, withNumTests, (===) )

import Thena.Core.TermTests (genLiteral)
import Thena.Driver (parseCore, parseSurfaceModule, parseSurfaceTerm)
import Thena.Syntax.Concrete (Raw (..))
import Thena.Syntax.Lexer (lexTokens)
import Thena.Surface.Layout (layout)
import Thena.Instral.Concrete
  ( RawInstr (..)
  , RawBody (..)
  , RawOp (..)
  , RawOperand (..)
  , RawRhs (..)
  , RawRule (..)
  )
import Thena.Syntax.Parser (parseRule)
import Thena.Global.Env (emptyGlobals)
import Thena.Repl (renderSurface)
import Thena.Surface.Concrete
  ( ObjectPiece (..)
  , Plicity (..)
  , Surface (..)
  , SurfaceArg (..)
  , SurfaceBinder (..)
  )

tests :: TestTree
tests =
  testGroup
    "the surface language (MS4)"
    [ testGroup "application is a spine" spineTests
    , testGroup "placeholders and holes" holeTests
    , testGroup "binders" binderTests
    , testGroup "precedence" precedenceTests
    , testGroup "it prints as it was written" renderTests
    , testGroup "layout (phase 40)" layoutTests
    , testGroup "proof modules (phase 43)" moduleTests
    , testGroup "comments (phase 43)" commentTests
    , testGroup "do blocks (phase 45)" blockTests
    , printerAndParser
    , layoutAgainstBraces
    ]

-- --------------------------------------------------------------------------
-- The offside rule, against an independently written brace-inserter (2026-09-13)
-- --------------------------------------------------------------------------

-- | **His condition — /if implicit works, explicit has to work too/ — over
-- generated programs rather than nine fixtures.**
--
-- 'layoutTests' above states each rule of the offside algorithm with a pair of
-- spellings. What a fixture pair cannot say is that the rules /compose/: a
-- @let@ inside a @let@ inside a @do@ block, each opening its context at a
-- different column, is where an off-by-one in "Thena.Surface.Layout"'s
-- @closesBlock@ or in the column it records would live, and no fixture nests.
--
-- **The oracle is 'braced'**, which writes the same tree with the braces and
-- semicolons written out. It is a second renderer, written here and sharing
-- nothing with the layout pass — which is the only reason agreeing means
-- anything.
layoutAgainstBraces :: TestTree
layoutAgainstBraces =
  testGroup
    "layout and explicit braces are one language"
    [ testProperty "a generated program means the same both ways" $
        withNumTests 400 $ forAll (genBlocky 3) $ \b ->
          let a = braced b
              c = unlines (laidOut 0 b)
           in counterexample (a ++ "\n--- vs ---\n" ++ c) $
                case (parseSurfaceTerm a, parseSurfaceTerm c) of
                  (Right x, Right y) -> property (x == y)
                  (x, y) -> counterexample (show x ++ "\n" ++ show y) False
    ]

-- | A term made of the two things that carry a layout context — @let@ and a
-- @do@ block — nested inside each other.
data Blocky
  = Leaf String
  | BLet [(String, Blocky)] Blocky
  | BDo [String]
  deriving (Show)   -- QuickCheck only

genBlocky :: Int -> Gen Blocky
genBlocky n
  | n <= 0 = leaf
  | otherwise =
      frequency
        [ (2, leaf)
        , (3, BLet <$> bindings <*> genBlocky (n - 1))
        , (1, BDo <$> listOf1 (elements ["attack", "intro", "prove", "back"]))
        ]
  where
    leaf = Leaf <$> elements ["a", "b", "f a", "f a b", "zero"]
    bindings = do
      k <- elements [1, 2, 3 :: Int]
      mapM (\i -> (,) ("x" ++ show i) <$> genBlocky (n - 2)) [1 .. k]

-- | The braces and semicolons written out, on one line.
braced :: Blocky -> String
braced b = case b of
  Leaf t     -> t
  BDo is     -> "do { " ++ intercalate " ; " is ++ " }"
  BLet bs body ->
    "let { " ++ intercalate " ; " [ x ++ " = " ++ braced v | (x, v) <- bs ]
      ++ " } in " ++ braced body

-- | The same tree, laid out. @col@ is the column this term starts at.
--
-- **Every line but the first carries its own absolute indentation**, and the
-- first is placed by the caller. Getting that convention wrong is how the first
-- draft of this renderer double-indented a nested binding, which is worth
-- recording: the oracle has to be right before disagreement means anything.
--
-- A block's items all begin one indent in from the keyword, and the token that
-- closes the block sits strictly left of them — the offside rule written as a
-- renderer instead of as a reader.
laidOut :: Int -> Blocky -> [String]
laidOut col b = case b of
  Leaf t -> [t]
  BDo is -> case is of
    []         -> ["do { }"]
    (i : rest) -> ("do " ++ i) : [ pad (col + 3) ++ j | j <- rest ]
  BLet bs body ->
    case bs of
      [] -> ["let { } in " ++ headOf bodyLines] ++ restOf bodyLines
      (b0 : more) ->
        let (h0, t0) = binding b0
         in [ "let " ++ h0 ]
              ++ t0
              ++ concat [ (pad inner ++ h) : t | (h, t) <- map binding more ]
              ++ [ pad (col + 1) ++ "in " ++ headOf bodyLines ]
              ++ restOf bodyLines
    where
      inner = col + 4
      bodyLines = laidOut (col + 4) body
      binding (x, v) =
        let ls = laidOut (inner + length x + 3) v
         in (x ++ " = " ++ headOf ls, restOf ls)

headOf :: [String] -> String
headOf (l : _) = l
headOf []      = ""

restOf :: [String] -> [String]
restOf (_ : ls) = ls
restOf []       = []

pad :: Int -> String
pad k = replicate k ' '

-- --------------------------------------------------------------------------
-- The printer and the parser, crossed over generated terms (2026-09-12)
-- --------------------------------------------------------------------------

-- | **@parse . render@ is the identity on a surface term.**
--
-- Every other group here is a fixture, which is right — this module's header
-- says why a round trip is not enough on its own, and it is not the only check
-- here. What a fixture corpus cannot say is that the printer and the parser
-- agree on every /combination/, and the two are written by different code in
-- different modules: "Thena.Repl"\'s @renderSurface@ decides where a
-- parenthesis goes, @Surface.Parser@\'s precedence decides what one means.
--
-- The direction is the tree's and not the string's, deliberately: one Π is
-- representable two ways (@ms4\/CLOSEOUT.md@ 18), so the printer picks a
-- spelling and @render . parse@ over strings is not a law.
printerAndParser :: TestTree
printerAndParser =
  testGroup
    "the printer and the parser agree"
    [ testProperty "parse . render is the identity on a surface term" $
        withNumTests 200 $
          forAll genSurface $ \t -> readBackSurface (renderSurface t) === Right t
    ]

readBackSurface :: String -> Either String Surface
readBackSurface src = case parseSurfaceTerm src of
  Left e  -> Left (show e)
  Right t -> Right t

-- | A generated surface term.
--
-- **No @do@ block and no @elim@.** A block's operands are the instruction
-- language, which @blockTests@ above crosses over its own total table; @elim@\'s
-- five argument groups are 'SurfaceElim'\'s and are pinned by fixture. What is
-- generated is the term language proper, where the parenthesisation lives.
genSurface :: Gen Surface
genSurface = sized go
  where
    go n
      | n <= 1 = leaf
      | otherwise =
          frequency
            [ (2, leaf)
              -- **A spine's head is never itself a spine.** @spine@ flattens on
              -- construction and @discussion\/application-representation.md@
              -- says it must stay so, so a nested 'SurfaceApp' is representable
              -- and not well formed, exactly as an unannotated Π binder is.
            , (2, SurfaceApp <$> nonSpine <*> args)
            , (1, SurfaceLam <$> binders <*> smaller)
              -- **A Π binder always carries its type.** The grammar has no
              -- spelling for one that does not — @'(' Names ':' Term ')'@ and
              -- its braced twin are the only two productions — and nothing in
              -- @src@ builds one either, so an unannotated Π binder is
              -- representable and not well formed (§3.4's line). Generating one
              -- would only assert that the printer prints something for a term
              -- the language cannot write.
            , (1, SurfacePi <$> typedBinders <*> smaller)
            , (1, SurfaceArrow <$> smaller <*> smaller)
            , (1, SurfaceLet <$> name <*> annotation <*> smaller <*> smaller)
            , (1, SurfaceAnnot <$> smaller <*> smaller)
              -- A tagged term literal (MS6 phase 104), in the shared generator
              -- for 'SurfaceLiteral'\'s reason: the printer has to escape a
              -- region's text the way the region scanner reads it back, and a
              -- splice holds a whole term, so the two printers meet here.
            , (1, genObject smaller)
            ]
      where
        smaller    = resize (n `div` 2) genSurface
        nonSpine   = do
          h <- smaller
          pure (case h of SurfaceApp g _ -> g; _ -> h)
        annotation = oneof [pure Nothing, Just <$> smaller]
        args       = neOr (SurfaceArg Explicit (SurfaceName "a"))
                       (listOf1 (SurfaceArg <$> plicity <*> smaller))
        binders    = neOr (SurfaceBinder Explicit "x" Nothing)
                       (listOf1 (SurfaceBinder <$> plicity <*> name <*> annotation))
        typedBinders = neOr (SurfaceBinder Explicit "x" (Just SurfaceUniverseOpen))
                         (listOf1 (SurfaceBinder <$> plicity <*> name <*> (Just <$> smaller)))

    leaf =
      oneof
        [ SurfaceName <$> name
        , SurfaceUniverse <$> elements [0, 1, 2]
        , pure SurfaceUniverseOpen
        , pure SurfacePlaceholder
        , SurfaceHole <$> name
        -- A literal is a leaf (MS6 phase 97c), and it goes in the shared
        -- generator so the printer-and-parser property sees one in every
        -- position a term can stand — which is what caught that a printed
        -- string has to be escaped the way the lexer reads it back.
        , SurfaceLiteral <$> genLiteral
        ]

    name    = elements ["x", "y", "f", "A"]
    plicity = elements [Explicit, Implicit]

    -- @listOf1@ can still hand back an empty list under a tiny size, and a
    -- spine is never empty.
    neOr d g = maybe (d :| []) id . nonEmpty <$> g

-- | A tagged term literal, with pieces that could have been written.
--
-- **Nothing here is object-language text**: the term is never elaborated in
-- this module, so what is generated is exactly what the printer and the reader
-- must agree about — the tag, the production if one is written, and the
-- region's pieces.
--
-- **The pieces alternate, and that is not a convenience.** The lexer emits one
-- chunk per run of text between escapes and drops an empty one, so two
-- 'ObjectText' pieces in a row are not something it can produce; generating a
-- pair would be asserting that the printer can write a distinction the reader
-- has no way to keep.
genObject :: Gen Surface -> Gen Surface
genObject inner =
  SurfaceObject
    <$> elements ["LC", "Ty"]
    <*> oneof [pure Nothing, Just <$> elements ["var", "app"]]
    <*> (alternate <$> listOf (oneof [ObjectText <$> chunk, ObjectSplice <$> inner]))
  where
    chunk = elements ["x", "( \955 x . x )", "a" ++ [toEnum 96] ++ "b", "$", "\\", "?", " ", "a${b"]
    alternate ps = case ps of
      ObjectText a : ObjectText b : rest -> alternate (ObjectText (a ++ b) : rest)
      ObjectText "" : rest -> alternate rest
      p : rest -> p : alternate rest
      [] -> []

-- --------------------------------------------------------------------------
-- The spine
-- --------------------------------------------------------------------------

spineTests :: [TestTree]
spineTests =
  [ -- **One node, two arguments — not two nested nodes.** This is the decision
    -- the whole AST turns on: phase 44's @EXPAND@ needs the argument list whole
    -- to know where the implicit positions fall.
    parses "f a b"
      (SurfaceApp (SurfaceName "f")
         (SurfaceArg Explicit (SurfaceName "a") :| [SurfaceArg Explicit (SurfaceName "b")]))

    -- **Parentheses are not represented**, so these are the same term and the
    -- tree says so. Two application constructors would have made them two
    -- forms of one thing.
  , testCase "and (f a) b is the same tree as f a b" $
      tree "(f a) b" >>= \a -> tree "f a b" >>= \b -> a @?= b

    -- **An empty argument list is not constructible**, which is his ruling:
    -- a head with no arguments is the head.
  , parses "f" (SurfaceName "f")

  , parses "f (g a)"
      (SurfaceApp (SurfaceName "f")
         [SurfaceArg Explicit
            (SurfaceApp (SurfaceName "g") [SurfaceArg Explicit (SurfaceName "a")])])

    -- The head may be anything, which is why one constructor is enough.
  , parses "(\\ x -> x) a"
      (SurfaceApp (SurfaceLam [SurfaceBinder Explicit "x" Nothing] (SurfaceName "x"))
         [SurfaceArg Explicit (SurfaceName "a")])

  , parses "f {A} a"
      (SurfaceApp (SurfaceName "f")
         (SurfaceArg Implicit (SurfaceName "A") :| [SurfaceArg Explicit (SurfaceName "a")]))
  ]

-- --------------------------------------------------------------------------
-- _ and ?foo
-- --------------------------------------------------------------------------

holeTests :: [TestTree]
holeTests =
  [ parses "_" SurfacePlaceholder
  , parses "?goal" (SurfaceHole "goal")

    -- **Neither is a lexer rule**, and this is what that buys: a name may still
    -- contain both characters. @_@ alone is the placeholder and @_foo@ is a
    -- name, exactly as @PLAN-interface.md@ §2.6 says a name may start with @_@.
  , parses "_foo" (SurfaceName "_foo")
  , parses "foo?" (SurfaceName "foo?")

    -- @?@ cannot start an identifier, so this really is two tokens and the
    -- grammar puts them together. Spaced, it means the same thing.
  , testCase "?goal and ? goal are the same tree" $
      tree "?goal" >>= \a -> tree "? goal" >>= \b -> a @?= b

  , refuses "?"
  ]

-- --------------------------------------------------------------------------
-- Binders
-- --------------------------------------------------------------------------

binderTests :: [TestTree]
binderTests =
  [ -- **The main thing the surface has that the development calculus does
    -- not.** His ruling: lambdas only — @let@, @∀@ and a signature keep theirs.
    parses "\\ x -> x"
      (SurfaceLam [SurfaceBinder Explicit "x" Nothing] (SurfaceName "x"))
  , refuses "∀ x -> x"

  , parses "\\ (x : A) -> x"
      (SurfaceLam [SurfaceBinder Explicit "x" (Just (SurfaceName "A"))] (SurfaceName "x"))

    -- A group is a spelling, not a structure: it expands, **in order**.
  , parses "∀ (x y : A) -> x"
      (SurfacePi (SurfaceBinder Explicit "x" (Just (SurfaceName "A"))
                    :| [SurfaceBinder Explicit "y" (Just (SurfaceName "A"))])
         (SurfaceName "x"))

  , parses "\\ {A} x -> x"
      (SurfaceLam (SurfaceBinder Implicit "A" Nothing
                     :| [SurfaceBinder Explicit "x" Nothing])
         (SurfaceName "x"))
  , parses "∀ {A : Type} -> A"
      (SurfacePi [SurfaceBinder Implicit "A" (Just SurfaceUniverseOpen)] (SurfaceName "A"))

    -- @let@ keeps its annotation optional here and required in the development
    -- calculus, where there is nothing to infer it with.
  , parses "let x = a in x"
      (SurfaceLet "x" Nothing (SurfaceName "a") (SurfaceName "x"))
  , parses "let x : A = a in x"
      (SurfaceLet "x" (Just (SurfaceName "A")) (SurfaceName "a") (SurfaceName "x"))
  ]

-- --------------------------------------------------------------------------
-- Precedence
-- --------------------------------------------------------------------------

precedenceTests :: [TestTree]
precedenceTests =
  [ -- **Ascription binds loosest**, which is the reading Agda and Haskell both
    -- give it: the lambda is ascribed, not its body.
    parses "\\ x -> x : A"
      (SurfaceAnnot (SurfaceLam [SurfaceBinder Explicit "x" Nothing] (SurfaceName "x"))
         (SurfaceName "A"))

  , parses "A -> B -> C"
      (SurfaceArrow (SurfaceName "A")
         (SurfaceArrow (SurfaceName "B") (SurfaceName "C")))

  , parses "f a -> b"
      (SurfaceArrow
         (SurfaceApp (SurfaceName "f") [SurfaceArg Explicit (SurfaceName "a")])
         (SurfaceName "b"))

  , parses "Type₀ -> Type"
      (SurfaceArrow (SurfaceUniverse 0) SurfaceUniverseOpen)
  ]

-- --------------------------------------------------------------------------
-- Layout
-- --------------------------------------------------------------------------

-- | The offside rule, and the condition it has to meet.
--
-- **A multi-line surface term cannot be typed at the REPL**, which reads one
-- line — so until files arrive at phase 43 these are the only thing exercising
-- layout at all. They go through 'parseSurfaceTerm', which is what a file will
-- go through too.
layoutTests :: [TestTree]
layoutTests =
  [ -- **HIS CONDITION**: /"if implicit works, explicit has to work too."/ The
    -- grammar sees only braces and semicolons, so the two spellings must give
    -- one tree, and this is the test that says so.
    testCase "explicit braces and the offside rule agree" $
      same "let { x = a ; y = b } in c"
           "let x = a\n    y = b\n in c"

    -- The Report's @parse-error(t)@ case, replaced by 'closesBlock': nothing
    -- about @in@'s column ends the block, only that @in@ arrived.
  , testCase "in closes a block opened on the same line" $
      same "let { x = a } in x" "let x = a in x"

  , testCase "a second binding at the same column is a second binding" $
      same "let { x = a ; y = b } in c" "let x = a\n    y = b\n in c"

    -- A more-indented line continues the item it is under. Without this rule a
    -- wrapped binding would become two.
  , testCase "a more indented line continues the binding" $
      same "let { x = f a b } in x"
           "let x = f a\n          b\n in x"

  , testCase "a less indented token closes the block" $
      same "let { x = a } in x" "let x = a\n in x"

  , testCase "blocks nest" $
      same "let { x = let { y = a } in y } in x"
           "let x = let y = a\n            in y\n in x"

    -- **A bracket opened inside a block does not close it** (MS4 phase 43).
    -- 'Thena.Surface.Layout.closesBlock' used to name @)@ and @}@, so any close
    -- ended the block it was in — and the first real proof module found it at
    -- once: the @)@ of @elim Nat ()@ closed the module. Invisible until then,
    -- because layout had only ever run on a @let@ and on one REPL argument.
  , testCase "a balanced bracket inside a block does not close it" $
      same "let { x = f (g a) ; y = b } in c"
           "let x = f (g a)\n    y = b\n in c"

    -- **The exact shape that found it.** An eliminator's field groups are
    -- bracketed and may be empty, so a @let@ over an @elim@ has closing
    -- brackets in the middle of a block and nothing else does.
  , testCase "an eliminator's empty field groups do not close it" $
      same "let { x = elim Nat () (\\ k -> Nat) (a b) () m ; y = b } in c"
           "let x = elim Nat () (\\ k -> Nat) (a b) () m\n    y = b\n in c"

    -- The other half: a bracket opened *outside* the block still closes it, and
    -- closes as many as it has to.
  , testCase "a bracket opened outside closes the block" $
      same "(let { x = a } in x)" "(let x = a\n in x)"

  , testCase "and closes every block it has to" $
      same "(let { x = let { y = a } in y } in x)"
           "(let x = let y = a\n             in y\n  in x)"

    -- An explicit brace may not be closed by the offside rule, nor may an
    -- implicit block be closed by a brace the user wrote.
  , refuses "let { x = a in x"
  , refuses "let x = a } in x"

    -- **Layout is the surface language's alone**, which is his ruling of
    -- 2026-08-21: /"doing all that for a parser for the development calculus is
    -- a massive overkill."/ The two share a lexer, so the check worth having is
    -- that the development calculus never meets this pass — a line break means
    -- nothing there, and no brace is inserted.
  , testCase "the development calculus is not laid out" $
      case ( parseCore emptyGlobals [] 0 "let x = Type\8320 : Type\8321 in x"
           , parseCore emptyGlobals [] 0 "let x = Type\8320 : Type\8321\n  in x"
           ) of
        (Right (a, _), Right (b, _)) -> b @?= a
        (other, _)                   -> assertFailure (show other)
  ]

-- --------------------------------------------------------------------------
-- Rendering
-- --------------------------------------------------------------------------

-- | Exact strings, and then the round trip on the same corpus.
--
-- The round trip is the weaker of the two and is here as a second opinion: it
-- would pass on a printer and parser that agreed with each other and with
-- nothing else, which the exact strings above rule out.
renderTests :: [TestTree]
renderTests =
  concatMap
    (\src -> [ testCase ("renders: " ++ src) (rendered src src)
             , testCase ("round trips: " ++ src) (roundTrips src)
             ])
    corpus

corpus :: [String]
corpus =
  [ "f a b"
  , "f (g a)"
  , "f {A} a"
  , "λ x (y : A) -> x"
  , "λ {A} (x : A) -> x"
  , "∀ (A : Type) (B : Type) -> A -> B"
  , "∀ {A : Type₀} -> A -> A"
  , "let x = a in x"
  , "let x : A = a in x"
  , "x : A -> A"
  , "(λ x -> x) a"
  , "f _ ?goal"
    -- **An ascription in a body position keeps its parentheses** (2026-09-12).
    -- Ascription binds looser than every one of these, so without them the
    -- printer produced a string that read back as a different term — and
    -- @a : b : c@, which does not read back at all. Found by
    -- 'printerAndParser'; kept here by name because that is the shape to
    -- recognise.
  , "λ x -> (x : A)"
  , "∀ (x : A) -> (x : A)"
  , "A -> (x : A)"
  , "let x = a in (x : A)"
  , "a : (b : c)"
  , "elim Nat () (λ (z : Nat) -> Nat) (zero (λ k ih -> ih)) () n"
  ]

-- --------------------------------------------------------------------------
-- Helpers
-- --------------------------------------------------------------------------

-- | Read a surface term **exactly as the REPL does** — lex, lay out, parse.
--
-- Through 'parseSurfaceTerm' and not through the three steps composed here, so
-- that a test cannot pass on a composition the program does not use. Phase 40
-- is why: before it, these tests called the parser directly and would have gone
-- on passing after layout made the grammar require braces.
tree :: String -> IO Surface
tree src = case parseSurfaceTerm src of
  Left e  -> assertFailure (src ++ ": " ++ show e)
  Right t -> pure t

parses :: String -> Surface -> TestTree
parses src expected = testCase src (tree src >>= (@?= expected))

refuses :: String -> TestTree
refuses src = testCase ("refused: " ++ src) $
  case parseSurfaceTerm src of
    Left _  -> pure ()
    Right t -> assertFailure ("accepted it: " ++ show t)

-- | Two spellings, one tree.
same :: String -> String -> Assertion
same a b = do
  ta <- tree a
  tb <- tree b
  tb @?= ta

rendered :: String -> String -> Assertion
rendered src expected = tree src >>= \t -> renderSurface t @?= expected

roundTrips :: String -> Assertion
roundTrips src = do
  t  <- tree src
  t' <- tree (renderSurface t)
  t' @?= t

-- --------------------------------------------------------------------------
-- Proof modules (MS4 phase 43)
-- --------------------------------------------------------------------------

-- | A module is a header and a block of declarations, and the block obeys the
-- same layout rule everything else does.
--
-- **The condition is still his**: implicit and explicit must agree. That is
-- what these check, one construct at a time, because a module is the first
-- thing whose block is more than one line in practice.
moduleTests :: [TestTree]
moduleTests =
  [ testCase "a module's block lays out" $
      sameModule "module M where { f : A ; f = a }"
                 "module M where\nf : A\nf = a"

  , testCase "the name is kept" $
      fmap fst (parseSurfaceModule "module Arith where { f : A ; f = a }")
        @?= Right "Arith"

  , -- A datatype's own @where@ opens a block inside the module's, so the two
    -- offside levels have to nest rather than collide.
    testCase "a datatype's block nests inside the module's" $
      sameModule
        "module M where { data D : Type\8320 where { c : D } ; f : D ; f = c }"
        "module M where\ndata D : Type\8320 where\n  c : D\nf : D\nf = c"

  , -- The regression the first real file found, at module scale.
    testCase "a bracket in a declaration does not close the module" $
      sameModule
        "module M where { f : A ; f = g (h a) ; k : A ; k = b }"
        "module M where\nf : A\nf = g (h a)\nk : A\nk = b"

  , -- **A layout keyword at the very end of the file** (MS4 phase 54). The
    -- Report's @{n}@ takes the column of the next token and there is none, so
    -- no block opened at all and the module's own @}@ arrived where the grammar
    -- wanted a @{@ — @0:0: unexpected }@. Found writing the prelude as a
    -- module, where @data Empty : Type where@ has no constructors.
    testCase "a datatype with no constructors at the end of the file" $
      sameModule
        "module M where { f : A ; f = a ; data D : Type\8320 where { } }"
        "module M where\nf : A\nf = a\ndata D : Type\8320 where"

  , testCase "a module with no declarations is refused" $
      case parseSurfaceModule "module M where { }" of
        Left _  -> pure ()
        Right r -> assertFailure ("admitted: " ++ show r)
  ]
  where
    -- Compare the **items**, not the module name, so a test says only what it
    -- is about.
    sameModule a b = case (parseSurfaceModule a, parseSurfaceModule b) of
      (Right (_, x), Right (_, y)) -> show y @?= show x
      (x, y) -> assertFailure (show x ++ "\n" ++ show y)

-- --------------------------------------------------------------------------
-- Comments (MS4 phase 43)
-- --------------------------------------------------------------------------

-- | @--@ **followed by a space**, to the end of the line, in every language
-- the lexer serves — his ruling, 2026-09-02: /"Better they are uniform than
-- three different ones."/
--
-- **The space is the whole of the rule.** @-@ is an @$idchar@ but not an
-- @$idstart@, so nothing is written @--@-first today; requiring the space means
-- nothing ever has to be given up, and it is what these cases pin.
commentTests :: [TestTree]
commentTests =
  [ testCase "a trailing comment is not part of the term" $
      same "\\ x -> x" "\\ x -> x -- the identity"

  , testCase "a comment on its own line is skipped" $
      same "let { x = a ; y = b } in c"
           "let x = a\n-- about y\n    y = b\n in c"

  , -- The one that says the rule is about the space, not about @--@.
    testCase "-- without a space is not a comment" $
      case parseSurfaceTerm "\\ x -> x --oops" of
        Left _  -> pure ()
        Right t -> assertFailure ("read as a term: " ++ show t)

  , testCase "and neither is an arrow" $
      same "A -> B" "A -> B  -- a function"

  , -- A comment line carries no tokens, so it contributes no column and cannot
    -- move the offside rule.
    testCase "a comment does not open or close a block" $
      same "let { x = a } in x"
           "let x = a\n-- not a second binding\n in x"
  ]

-- --------------------------------------------------------------------------
-- do blocks (MS4 phase 45)
-- --------------------------------------------------------------------------

-- | A block of the **instruction** language inside a surface term.
--
-- **The cross-grammar check is the important one here.** Happy cannot share
-- productions between two files, so @Thena.Surface.Parser@ mirrors
-- @Thena.Syntax.Parser@\'s five instruction nonterminals, and that duplication
-- is this phase\'s judgement call. What makes it safe is not that it is
-- fourteen lines: it is that the same text is parsed through both and the two
-- @[RawInstr]@ compared. A mirror nothing crosses is the mistake the @:help@
-- audit had just found one phase earlier.
blockTests :: [TestTree]
blockTests =
  [ testCase "a block parses and prints back" $
      roundTrip "do { attack ; intro }"

  , testCase "a binding in a block round-trips too" $
      roundTrip "do { h = here ; goto h }"

  , testCase "operands may be numbers and strings" $
      roundTrip "do { arg 2 ; say \"done\" }"

    -- **The two operand grammars are §7b's registered duplication** — Happy
    -- cannot share a non-terminal, because a block is embedded in a surface
    -- term — so they are levelled by hand and drift is what the register
    -- exists to catch. Phase 68b added lambdas to the rule-file grammar and
    -- not to this one; phase 73 found it and this is what pins it.
  , testCase "a lambda is writable in a block, as it is in a rule file" $
      roundTrip "do { f = \\ z -> concat z z ; m = f \"a\" }"
  , testCase "and a literal, and a pair" $
      roundTrip "do { p = (1, true) ; l = [1, 2, 3] }"
    -- **A block-bodied lambda prints with its braces** (MS5 phase 75b): the
    -- printer cannot emit an indented block, because layout is a pass its
    -- reader runs before the grammar and this test is the printer crossed
    -- against that reader.
  , testCase "and a lambda whose body is a block" $
      roundTrip "do { f = \\ z -> do { p = concat z z ; return p } ; m = f \"a\" }"

  , -- Layout, like everything else the surface language has.
    testCase "a block lays out" $
      same "do { attack ; intro }" "do attack\n   intro"

  , testCase "and it is an atom, so an argument run takes it unparenthesised" $
      same "f (do { attack })" "f do { attack }"

  , -- **The duplication, crossed.**
    testCase "the surface grammar reads a block exactly as the rule grammar does" $
      mapM_ crossed
        ([ "attack"
        , "attack ; intro"
        , "h = here ; goto h"
        , "arg 2 ; say \"done\" ; try-core x"
        , "x = fresh-name \"a\" ; claim x y ; prove"
          -- **The form MS5 phase 75b added**, crossed in the same phase that
          -- added it rather than two phases later, which is what §7b's register
          -- is for.
        , "f = \\ z -> do { p = concat z z ; return p }"
        ] :: [String])

    -- **Crossed for EVERY operand form, not five hand-picked bodies**
    -- (2026-09-12). Hand-picked is how both drifts got through: phase 68b's
    -- lambda, and the tagged region, which was still missing from this grammar
    -- when this case was written — @do { f surface`x` }@ did not parse while
    -- the same body in a rule file did. 'spellingFor' is a case over
    -- 'RawOperand', so @-Wall@ names a form that has no spelling here.
  , testCase "every operand form reads the same through both grammars" $
      mapM_ (crossed . ("f " ++)) writableOperands

    -- The same forms again on the right of an @=@, which is 'RawRhs''s own
    -- three-way split and its own mirrored nonterminal.
  , testCase "and the same on the right of a binding" $
      mapM_ (crossed . ("x = " ++)) writableOperands

    -- **A lambda's PARAMETERS, crossed for every pattern form** (MS5 phase 82).
    -- @InstrParams@ became a run of patterns in this grammar too, which is
    -- §7b's registered duplication for the third time — and for the third time
    -- it is crossed in the phase that added it rather than found drifted two
    -- phases later. The list is 'Thena.PatternTests.everyPattern''s spellings,
    -- and that list is kept total against 'Pattern' there.
  , testCase "a lambda takes the same patterns through both grammars" $
      mapM_ (\src -> crossed ("f = \\ " ++ src ++ " -> do { return " ++ src ++ " }"))
            (["x", "_", "3", "'c'", "true", "false", "[]", "(x, y)", "none"] :: [String])

  , testCase "…including the list forms, whose tail token is new" $
      mapM_ (\src -> crossed ("f = \\ " ++ src ++ " -> attack"))
            ([ "[a]", "[a, b]", "[a, ...rest]", "[a, ..._]", "[a, ...[]]"
             , "[...xs]", "((a, b), c)", "(some x)", "(some [a])"
             ] :: [String])

    -- The spelling has to exercise the form it claims, or the case above
    -- crosses two grammars over the same wrong tree and says nothing.
  , testCase "each spelling really writes the form it is listed under" $
      mapM_ writes operandForms
  ]
  where
    -- | A written spelling for every 'RawOperand' constructor.
    --
    -- **Exhaustive on purpose** — a new operand form leaves @-Wall@ with an
    -- incomplete pattern here, which is the only thing that makes the crossing
    -- above total rather than another hand-picked list. 'Nothing' is a form the
    -- surface grammar cannot write, and there is exactly one.
    spellingFor :: RawOperand -> Maybe String
    spellingFor o = case o of
      RawRef{}     -> Just "y"
      RawPos{}     -> Just "2"
      RawText{}    -> Just "\"done\""
      RawChar{}    -> Just "'c'"
      RawList{}    -> Just "[1, 'c', \"s\"]"
      RawPairOf{}  -> Just "(1, y)"
      RawNested{}  -> Just "(concat y y)"
      RawLambda{}  -> Just "(\\ z -> concat z z)"
      RawRegion{}  -> Just "surface`\\ x -> x`"
      -- **Corners are the one form a @do@ block cannot write, and levelling
      -- them is a decision rather than a line** (@ms5\/CLOSEOUT.md@ 22).
      -- @⌜ t ⌝@ carries a parsed 'Thena.Syntax.Concrete.Raw', so the production
      -- is @'[|' Term '|]'@ and the surface grammar would need the whole
      -- development-calculus term grammar as a third copy. A @core@ region says
      -- the same thing — 'Thena.Rules.operandOf' sends both to @VRaw@ — so
      -- nothing is unsayable, only unsayable in that spelling.
      RawQuoted{}  -> Nothing

    -- One value per constructor, to apply 'spellingFor' to. It is a mirror, and
    -- the exhaustive case above is what stops it going quietly out of date.
    operandForms :: [RawOperand]
    operandForms =
      [ RawRef "y"
      , RawPos 2
      , RawText "done"
      , RawChar 'c'
      , RawList []
      , RawPairOf (RawPos 1) (RawRef "y")
      , RawNested "concat" []
      , RawLambda [] (BodyRhs (RhsOp (RawOp "concat" [])))
      , RawRegion "surface" Nothing "x"
      , RawQuoted (RawName "x")
      ]

    writableOperands :: [String]
    writableOperands = [ w | Just w <- map spellingFor operandForms ]

    -- Parse the spelling and check the operand it yields is the form it was
    -- listed under, by asking 'spellingFor' the question in reverse.
    writes :: RawOperand -> Assertion
    writes form = case spellingFor form of
      Nothing -> pure ()
      Just w  -> case viaRule ("f " ++ w) of
        Just [RawDo (RawOp "f" [got])] -> spellingFor got @?= Just w
        other -> assertFailure (w ++ ": " ++ show other)

    roundTrip :: String -> Assertion
    roundTrip src = case parseSurfaceTerm src of
      Left e  -> assertFailure (src ++ ": " ++ show e)
      Right t -> renderSurface t @?= src

    -- The same body, through the surface grammar and through the rule grammar.
    crossed :: String -> Assertion
    crossed body = case (viaSurface body, viaRule body) of
      (Just a, Just b) -> a @?= b
      (a, b) -> assertFailure (body ++ ": " ++ show a ++ " / " ++ show b)

    viaSurface :: String -> Maybe [RawInstr]
    viaSurface body = case parseSurfaceTerm ("do { " ++ body ++ " }") of
      Right (SurfaceDo is) -> Just is
      _                    -> Nothing

    viaRule :: String -> Maybe [RawInstr]
    -- **Laid out first** (MS5 phase 75): @then@ opens a block now, so a rule
    -- written on one line gets its braces from the offside rule exactly as a
    -- rule file does. The surface side has been laid out since MS4 phase 40.
    viaRule body = case lexTokens ("rule r :- when focus-is-hole do " ++ body) of
      Left _   -> Nothing
      Right ts0 -> case layout ts0 of
       Left _  -> Nothing
       Right ts -> case parseRule ts of
        Right (RawRule _ _ _ is) -> Just is
        Left _                   -> Nothing
