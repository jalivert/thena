-- | Inaccessible patterns — the dot (MS9 phase 228, on his ruling of
-- 2026-10-19).
--
-- A dot binds nothing and __asserts__: this position is determined, and by this
-- term. The ruling is that it is __optional and may never be made mandatory__,
-- so every group here has a named counterpart that is still legal — the
-- notation adds a check and takes nothing away.
--
-- Three things are asked by different code from the code that answers them:
--
--   * 'notationTests' — the grammar and the printer, which never reach the
--     engine. @.n@ and @.(s n)@ are the two written forms and they round-trip.
--   * 'acceptedTests' — what a dot may say in a position the split really
--     forced, including a compound term and @._@.
--   * 'refusedTests' — the whole of what the notation buys. A dot on a position
--     the split left free, a dot on the wrong term, and a dot at the wrong
--     type, each refused and each by a different mechanism.
--   * 'namingTests' — __and these are not about dots at all__ (@~v9fbj@, MS9
--     phase 236). A refusal that compares two terms has to name the one the
--     user wrote; a dot on a compound term is only the first feature that makes
--     two written terms meet, which is why the defect surfaced here. The second
--     case in that group has no dot in it.
module Thena.DotPatternTests (tests) where

import Data.List (isInfixOf)
import Data.List.NonEmpty (NonEmpty (..))

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, assertFailure, testCase, (@?=))

import Thena.Driver (Response (..), loadProofSource, parseSurfaceTerm)
import Thena.Files (loadProofFile, startingSession)
import Thena.Render (renderResponse)
import Thena.Surface.Concrete
  ( Plicity (..)
  , Surface (..)
  , SurfaceArg (..)
  , SurfaceArm (..)
  , SurfacePattern (..)
  )
import Thena.Syntax.Lexer (Located (..), Token (..), lexTokens)
import Thena.Syntax.Print (renderSurface)

tests :: TestTree
tests =
  testGroup
    "inaccessible patterns"
    [ testGroup "the notation" notationTests
    , testGroup "a position the split forced" acceptedTests
    , testGroup "and what the dot refuses" refusedTests
    , testGroup "a refusal names the term the user wrote" namingTests
    ]

-- --------------------------------------------------------------------------
-- The notation
-- --------------------------------------------------------------------------

-- | __Two written forms and no more__: a bare name takes no brackets and
-- anything larger does. The printer's rule is the grammar's, so a pattern that
-- round-trips is a pattern both halves agree about.
notationTests :: [TestTree]
notationTests =
  [ testCase "a dot on a name" $
      armPattern "case v of { c .n a -> a }"
        @?= Just (PatternName "c" [PatternDot (SurfaceName "n"), PatternName "a" []])
  , testCase "a dot on a term needs the brackets" $
      armPattern "case v of { c .(s n) a -> a }"
        @?= Just
              (PatternName "c"
                 [ PatternDot (SurfaceApp (SurfaceName "s") (arg (SurfaceName "n") :| []))
                 , PatternName "a" []
                 ])
  , -- __@._@ is a dot on a placeholder, not a wildcard pattern.__ A wildcard
    -- asks for no name; this asserts the position is determined and declines to
    -- say by what, which is a different claim.
    testCase "a dot on a placeholder" $
      armPattern "case v of { c ._ a -> a }"
        @?= Just (PatternName "c" [PatternDot SurfacePlaceholder, PatternName "a" []])
  , testCase "a bare name is still a bare name" $
      armPattern "case v of { c n a -> a }"
        @?= Just (PatternName "c" [PatternName "n" [], PatternName "a" []])
  , testCase "a dot on a name round-trips" $
      roundTrips "case v of { c .n a -> a }"
  , testCase "a dot on a term round-trips" $
      roundTrips "case v of { c .(s n) a -> a }"
  , -- __@...@ still wins__, which is the one thing adding the token could have
    -- broken: the lexer takes the longest match, so the list-pattern tail
    -- marker is still one token and never three of these.
    testCase "the spread token is untouched" $
      lexed "... . .n a...b"
        @?= Right [TSpread, TDot, TDot, TIdent "n", TIdent "a...b"]
  ]

-- | What the lexer made of a line, the positions dropped.
lexed :: String -> Either String [Token]
lexed src = case lexTokens src of
  Left e   -> Left (show e)
  Right ts -> Right [t | Located _ t <- ts]

-- --------------------------------------------------------------------------
-- What a dot may say
-- --------------------------------------------------------------------------

-- | __Every one of these has a named counterpart that still loads__, which is
-- the ruling: the dot is information a user may supply, never a replacement for
-- naming.
acceptedTests :: [TestTree]
acceptedTests =
  [ testCase "a dot on the term the equation forced" $
      loads (vecPreamble ++ vtail "vcons .m a as")
  , testCase "the same position named instead" $
      loads (vecPreamble ++ vtail "vcons n a as")
  , testCase "and asked for by no name at all" $
      loads (vecPreamble ++ vtail "vcons _ a as")
  , -- A position forced to a COMPOUND term: splitting a @Vec A (s (s m))@
    -- forces @vcons@'s own length to @s m@. Either option can name it or ignore
    -- it; neither can destructure it, an inaccessible position binding nothing.
    testCase "a dot on a compound term" $
      loads
        (vecPreamble
           ++ [ "vtailTwo : forall (A : Type\8320) (m : N) (xs : Vec A (s (s m))) -> Vec A (s m)"
              , "vtailTwo = \\ A m xs -> case xs of { vnil -> ; vcons .(s m) a as -> as }"
              ])
  , -- __A placeholder elaborates to a hole and unification solves it__, so
    -- @._@ costs nothing beyond the assertion it makes.
    testCase "a dot that declines to say by what" $
      loads (vecPreamble ++ vtail "vcons ._ a as")
  , testCase "the example file runs to the end" $ do
      (s, _) <- startingSession
      (_, _, stopped) <- loadProofFile s "examples/dot-patterns.thena"
      assertBool (unlines (map show stopped)) (null stopped)
  ]

-- --------------------------------------------------------------------------
-- And what it refuses
-- --------------------------------------------------------------------------

-- | __This is the whole of what the notation buys__, and §5 of
-- @.jalivert\/discussion\/forced-positions-and-dot-patterns.md@ is the argument:
-- under a name alone the same text means a binder or a definition, and which is
-- decided by a unification the user never sees.
refusedTests :: [TestTree]
refusedTests =
  [ -- __The split generalises a plain-variable index__, so @vcons@'s own length
    -- SURVIVES as a binder and there is nothing determined to assert. The rule
    -- has one clause, for a position that really is forced, and none for
    -- @none@ — @case-must-vanish@'s idiom, so the refusal is the complaint.
    testCase "a dot on a position nothing forced" $
      refusedWith "dotted-position-is-forced"
        (vecPreamble
           ++ [ "len : forall (A : Type\8320) (m : N) (xs : Vec A m) -> N"
              , "len = \\ A m xs -> induction xs of"
              , "        { vnil -> z ; vcons .m a as -> s m }"
              ])
  , -- The assertion itself: the written term is unified with the term the
    -- equation forced, and a mismatch is the unification failing.
    testCase "a dot on a term that is not the one" $
      refusedWith "cannot be made equal"
        (vecPreamble
           ++ [ "vtailW : forall (A : Type\8320) (m : N) (xs : Vec A (s (s m))) -> Vec A (s m)"
              , "vtailW = \\ A m xs -> case xs of { vnil -> ; vcons .m a as -> as }"
              ])
  , -- __And the TYPE is checked first__, because the term is elaborated at the
    -- type the position has rather than anywhere: @.A@ where an @N@ was
    -- determined never reaches the unification.
    testCase "a dot at the wrong type" $
      refusedWith "Type\8320 and N cannot be made equal"
        (vecPreamble ++ vtail "vcons .A a as")
  , -- __A dot heads no arm.__ The grammar lets one stand anywhere an atom may,
    -- and @arm-for@ wants a constructor's name — an arm is for a case, and
    -- @.e ->@ names none.
    testCase "a dot where an arm's head should be" $
      refusedWith "a pattern written as a word"
        (vecPreamble ++ vtail ".m")
  ]

-- --------------------------------------------------------------------------
-- The name in the message
-- --------------------------------------------------------------------------

-- | __The message may not name a variable that is in no source file__
-- (@~v9fbj@, MS9 phase 236).
--
-- @fill@ parks every elaborated argument in a @=@-binding, so a written @s q@
-- is carried as @s a@ with @a = q@ beside it, and the one message whose job is
-- to say which term the user got wrong used to name the @a@. These pin the
-- names rather than a substring, because the defect was a /name/ and a
-- substring check is exactly what did not catch it: @"cannot be made equal"@
-- passed throughout.
--
-- __The second case has no dot in it__, which is the point. Nothing about the
-- notation caused this; a dot on a compound term is just the first feature that
-- makes two terms the user wrote meet each other.
namingTests :: [TestTree]
namingTests =
  [ testCase "a dot on a compound term that is not the one" $
      refusedWith "s q and p cannot be made equal"
        (vecPreamble
           ++ [ "vq : forall (A : Type\8320) (p : N) (q : N) (xs : Vec A (s p)) -> Vec A p"
              , "vq = \\ A p q xs -> case xs of { vnil -> ; vcons .(s q) hd tl -> tl }"
              ])
  , testCase "an ordinary application, with no dot anywhere" $
      refusedWith "kk and s kk cannot be made equal"
        (vecPreamble
           ++ [ "vp : forall (A : Type\8320) (kk : N) (a : A) (xs : Vec A kk) -> Vec A kk"
              , "vp = \\ A kk a xs -> vcons A (s kk) a xs"
              ])
  ]

-- --------------------------------------------------------------------------
-- Plumbing
-- --------------------------------------------------------------------------

-- | @Vec@ over its own @N@, which is the family every forced position in this
-- module comes out of.
vecPreamble :: [String]
vecPreamble =
  [ "module Dotted where"
  , "data N : Type\8320 where"
  , "  z : N"
  , "  s : N -> N"
  , "data Vec (A : Type) : N -> Type where"
  , "  vnil : Vec A z"
  , "  vcons : forall (n : N) (a : A) (as : Vec A n) -> Vec A (s n)"
  ]

-- | @vtail@ over a @Vec A (s m)@, with the @vcons@ arm written as given. The
-- @vnil@ case vanishes — @z@ against @s m@ is a conflict — so its arm has no
-- body.
vtail :: String -> [String]
vtail armText =
  [ "vtail : forall (A : Type\8320) (m : N) (xs : Vec A (s m)) -> Vec A m"
  , "vtail = \\ A m xs -> case xs of { vnil -> ; " ++ armText ++ " -> as }"
  ]

arg :: Surface -> SurfaceArg
arg = SurfaceArg Explicit

-- | The first arm's pattern of a written split, or nothing if it did not parse.
armPattern :: String -> Maybe SurfacePattern
armPattern src = case parseSurfaceTerm src of
  Right (SurfaceSplit _ _ (SurfaceArm p _ : _)) -> Just p
  _ -> Nothing

roundTrips :: String -> Assertion
roundTrips src = case parseSurfaceTerm src of
  Left e -> assertFailure (show e)
  Right t -> case parseSurfaceTerm (renderSurface t) of
    Left e -> assertFailure (renderSurface t ++ ": " ++ show e)
    Right t' -> t' @?= t

loads :: [String] -> Assertion
loads ls = do
  (s0, _) <- startingSession
  case loadProofSource s0 (unlines ls) of
    (_, ProofLoaded {}) -> pure ()
    (s1, other) -> assertFailure (unwords (renderResponse s1 other))

refusedWith :: String -> [String] -> Assertion
refusedWith what ls = do
  (s0, _) <- startingSession
  case loadProofSource s0 (unlines ls) of
    (_, ProofLoaded {}) -> assertFailure "loaded, and it should not have"
    (s1, other)
      | what `isInfixOf` unwords (renderResponse s1 other) -> pure ()
      | otherwise -> assertFailure (unwords (renderResponse s1 other))
