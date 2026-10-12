-- | The numbered example programs load, in order (his request, 2026-09-21).
--
-- @examples/NN-*.thena@ and @examples/NN-*.thena.rules@ are the series he reads
-- to see what the language can do as each feature lands, so a file that has
-- gone stale is a false picture of the language. **The directory is walked, not
-- listed here**, so a new example is loaded by this test the day it is written
-- and nobody has to remember to add it.
--
-- Modules are loaded into one session, in name order, because that is how the
-- README tells a reader to load them and because a later one uses what an
-- earlier one declared. A rule file is loaded beside the shipped base and
-- every numbered rule file before it, as @:load rules@ would be — a load
-- replaces the list.
--
-- A numbered file of any other kind is a failure rather than a skip, so that a
-- new kind of example is a decision somebody makes.
module Thena.ExamplesTests (tests) where

import Data.Char (isDigit)
import Data.List (isSuffixOf, sort)
import System.Directory (listDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Driver
  ( Response (..)
  , Session
  , command
  , loadProofSource
  , loadRuleBases
  )
import Thena.Files (loadFile, rulesPath, startingSession)
import Thena.Render (renderResponse)

tests :: TestTree
tests =
  testGroup
    "the example programs"
    [ testCase "every numbered example loads, in order" $ do
        files <- sort . filter numbered <$> listDirectory "examples"
        if null files then assertFailure "no numbered examples were found" else pure ()
        (s0, _) <- startingSession
        standard <- rulesPath >>= \p -> (,) p <$> readFile p
        sEnd <- go s0 [standard] files
        -- **THE HEADLINE STATEMENTS ARE PINNED IN THE WALK'S OWN SESSION, not
        -- in sessions of their own** (MS8 phase 163, at his instruction). Each
        -- used to reload the prefix it needed from scratch, and the walk had
        -- already loaded all of it: measured 7.4 s for `07`'s pin, 13.5 s for
        -- `08`'s and 37 s for `10`'s, against 25.8 s for the walk itself.
        -- Pinning them here costs nothing, and @go@ returning its session is
        -- the whole of what it took.
        let pin cmd expected =
              let (s', r) = command sEnd cmd in renderResponse s' r @?= expected
        -- **MS6's done-when** (phase 109b): preservation for STLC, in the
        -- surface language, for closed terms (his choice, ms6/CLOSEOUT.md 32).
        pin ":infer preservation"
          [ "preservation : ∀ (M : LC) (M1 : LC) (T : Ty) -> typing`· ⊢ ${M} : ${T}` -> step`${M} --> ${M1}` -> typing`· ⊢ ${M1} : ${T}`" ]
        -- **And by tactics** (his ruling, 2026-09-21: both ways). `08` proves
        -- every lemma again with attack, intro, eliminate-core and elaborate
        -- and ends at the same statement; the walk runs that script, so this
        -- only has to check where it ended.
        pin ":infer preservation-tactics"
          [ "preservation-tactics : ∀ (M : LC) (M1 : LC) (T : Ty) -> typing`· ⊢ ${M} : ${T}` -> step`${M} --> ${M1}` -> typing`· ⊢ ${M1} : ${T}`" ]
        -- **MS8 phase 162**: the same theorem for ANY context, on one trusted law.
        pin ":infer preservationAny"
          [ "preservationAny : ∀ (G : Ctx) (M : LC) (M1 : LC) (T : Ty) -> typing`${G} ⊢ ${M} : ${T}` -> step`${M} --> ${M1}` -> typing`${G} ⊢ ${M1} : ${T}`" ]
    -- **MS8's done-when** (phase 161): POPLMark problem 1A over F-sub.
    -- @examples/poplmark/@ is its OWN set and is deliberately unnumbered: the
    -- numbered series above loads into one session and declares its own @Ty@,
    -- which F-sub's would clash with (@refused: Ty is already declared@).
    --
    -- Transitivity is proved under one hypothesis — plain weakening between
    -- well-formed contexts — and that hypothesis is refuted in the same file,
    -- because a derivation's own quantifier may bind a name the larger context
    -- declares. Both statements are pinned here: the theorem must keep its
    -- hypothesis, and the refutation must keep refuting it.
    , testCase "POPLMark 1A is proved for F-sub, at its statement" $ do
        (s0, _) <- startingSession
        s <- foldl (\ms p -> ms >>= \s1 -> readFile p >>= \src -> case loadProofSource s1 src of
                               (s2, ProofLoaded {}) -> pure s2
                               (s2, other) -> refused p s2 other)
               (pure s0)
               [ "examples/poplmark/01-syntax.thena", "examples/poplmark/02-contexts.thena"
               , "examples/poplmark/03-wellformed.thena", "examples/poplmark/04-subtyping.thena"
               , "examples/poplmark/05-typing.thena", "examples/poplmark/06-transitivity.thena" ]
        let (s', r) = command s ":infer transitivity"
        renderResponse s' r @?=
          [ "transitivity : (∀ (Q : Ty) (G : Ctx) (Xn : String) (D : Ctx) (P : Ty) -> ok`⊢ ${G} , ${Xn} <: ${P} , ${D} ok` -> sub`${G} ⊢ ${P} <: ${Q}` -> sub`${G} , ${Xn} <: ${P} , ${D} ⊢ ${P} <: ${Q}`) -> ∀ (G : Ctx) (S : Ty) (Q : Ty) (T : Ty) -> sub`${G} ⊢ ${S} <: ${Q}` -> sub`${G} ⊢ ${Q} <: ${T}` -> sub`${G} ⊢ ${S} <: ${T}`" ]
        let (s'', r') = command s ":infer wkIsFalse"
        renderResponse s'' r' @?=
          [ "wkIsFalse : (∀ (G : Ctx) (Xn : String) (D : Ctx) (P : Ty) -> ok`⊢ ${G} , ${Xn} <: ${P} , ${D} ok` -> sub`${G} ⊢ ${P} <: ( ∀ Z <: ⊤ . ⊤ )` -> sub`${G} , ${Xn} <: ${P} , ${D} ⊢ ${P} <: ( ∀ Z <: ⊤ . ⊤ )`) -> Empty {0}" ]
    ]
  where
    numbered f = case f of
      a : b : '-' : _ -> isDigit a && isDigit b
      _ -> False

    go :: Session -> [(FilePath, String)] -> [FilePath] -> IO Session
    go s _ [] = pure s
    go s bases (f : more) = do
      let path = "examples/" ++ f
      src <- readFile path
      if ".thena.rules" `isSuffixOf` f
        then do
          let bases' = bases ++ [(path, src)]
          case loadRuleBases s bases' of
            (s', BasesLoaded _) -> go s' bases' more
            (s', other) -> refused path s' other
        else if ".thena" `isSuffixOf` f
          then case loadProofSource s src of
            (s', ProofLoaded {}) -> go s' bases more
            (s', other) -> refused path s' other
          -- A script of command lines (phase 109c), run as `:load` runs one:
          -- it fails if any line stops.
          else if ".thena.script" `isSuffixOf` f
            then do
              (s', out, stopped) <- loadFile s path
              if null stopped then go s' bases more
                else assertFailure
                       (unlines ((path ++ " stopped:")
                                  : concatMap (renderResponse s') out))
            else assertFailure (path ++ " is a numbered example of a kind this test does not load")

refused :: FilePath -> Session -> Response -> IO a
refused path s r = assertFailure (unlines ((path ++ " did not load:") : renderResponse s r))
