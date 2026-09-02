{-# LANGUAGE OverloadedLists #-}

-- | The surface language's tree and its parser (MS4 phase 39).
--
-- **Exact trees, not round trips.** The standing lesson from phases 2–5 is that
-- @parse . render == id@ can pass while a real bug hides, because a
-- self-consistent error agrees with itself. So every case here either builds
-- the tree by hand and compares, or pins an exact string — and the round trip
-- is a third check on top, over a fixed corpus, never the only one.
module Thena.SurfaceTests (tests) where

import Data.List.NonEmpty (NonEmpty (..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertFailure, testCase, (@?=))

import Thena.Driver (parseCore, parseSurfaceModule, parseSurfaceTerm)
import Thena.Global.Env (emptyGlobals)
import Thena.Repl (renderSurface)
import Thena.Surface.Concrete
  ( Plicity (..)
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
    ]

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
