-- | The numbered example programs load, in order (his request, 2026-09-21).
--
-- @examples/StlcNN*.thena@ and @examples/StlcNN*.thena.rules@ are the series he
-- reads to see what the language can do as each feature lands, so a file that
-- has gone stale is a false picture of the language. **The directory is walked,
-- not listed here**, so a new example is loaded by this test the day it is
-- written and nobody has to remember to add it.
--
-- The numbers are his (2026-09-21) and the @Stlc@ prefix is his ruling of
-- 2026-11-05: a step of a module name begins with a letter and holds no hyphen,
-- so @01-stlc-syntax@ could be reached by no name at all. Zero-padding is what
-- keeps 'sort' the reading order. **Every other example was renamed the same
-- way in phase 281**, after his ruling that a module sees only what
-- it imports: a file no module name reaches can state no dependency.
--
-- Modules are loaded into one session, in name order, because that is how the
-- README tells a reader to load them. **Each one now states its own
-- dependencies** (MS11 phase 279), so the order is no longer what makes them
-- work — every surface file in the series loads on its own — and the walk's
-- own deduplication is what keeps one session from elaborating anything twice.
-- A rule file is loaded beside the shipped base and every numbered rule file
-- before it, as @:load rules@ would be — a load replaces the list.
--
-- **Everything goes through "Thena.Files", not through the pure doors.** A
-- module that imports anything cannot be elaborated by 'loadProofSource' at all
-- (§12 invariant 4: that door has no disk), and a rule base that imports cannot
-- be read by 'loadRuleBases'. Using them here would test the series against a
-- loader no user has.
--
-- A numbered file of any other kind is a failure rather than a skip, so that a
-- new kind of example is a decision somebody makes.
module Thena.ExamplesTests (tests) where

import Data.Char (isDigit)
import Data.List (isSuffixOf, sort, stripPrefix)
import System.Directory (listDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Driver
  ( Response (..)
  , Session
  , command
  )
import Thena.Files
  ( Trouble
  , loadFile
  , loadProofFile
  , loadRuleFiles
  , rulesPath
  , startingSession
  )
import Thena.Render (renderResponse, renderTrouble)

tests :: TestTree
tests =
  testGroup
    "the example programs"
    [ testCase "every numbered example loads, in order" $ do
        files <- sort . filter numbered <$> listDirectory "examples"
        if null files then assertFailure "no numbered examples were found" else pure ()
        (s0, _) <- startingSession
        standard <- rulesPath
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
        -- **The same door the numbered series goes through**, and for the same
        -- reason: this is how a reader loads them. **Each one states its own
        -- dependencies** (MS11 phase 281), so the order is no longer
        -- what makes them work and any one of them loads on its own; they are
        -- still loaded in order because that is what
        -- @examples\/poplmark\/README.md@ tells a reader to do, and the walk's
        -- deduplication is what keeps one session from elaborating anything
        -- twice.
        s <- foldl (\ms p -> ms >>= \s1 -> do
                      (s2, out, trouble) <- loadProofFile s1 p
                      if null trouble then pure s2 else stopped p s2 out trouble)
               (pure s0)
               [ "examples/poplmark/Fsub01Syntax.thena", "examples/poplmark/Fsub02Contexts.thena"
               , "examples/poplmark/Fsub03Wellformed.thena", "examples/poplmark/Fsub04Subtyping.thena"
               , "examples/poplmark/Fsub05Typing.thena", "examples/poplmark/Fsub06Transitivity.thena" ]
        let (s', r) = command s ":infer transitivity"
        renderResponse s' r @?=
          [ "transitivity : (∀ (Q : Ty) (G : Ctx) (Xn : String) (D : Ctx) (P : Ty) -> ok`⊢ ${G} , ${Xn} <: ${P} , ${D} ok` -> sub`${G} ⊢ ${P} <: ${Q}` -> sub`${G} , ${Xn} <: ${P} , ${D} ⊢ ${P} <: ${Q}`) -> ∀ (G : Ctx) (S : Ty) (Q : Ty) (T : Ty) -> sub`${G} ⊢ ${S} <: ${Q}` -> sub`${G} ⊢ ${Q} <: ${T}` -> sub`${G} ⊢ ${S} <: ${T}`" ]
        let (s'', r') = command s ":infer wkIsFalse"
        renderResponse s'' r' @?=
          [ "wkIsFalse : (∀ (G : Ctx) (Xn : String) (D : Ctx) (P : Ty) -> ok`⊢ ${G} , ${Xn} <: ${P} , ${D} ok` -> sub`${G} ⊢ ${P} <: ( ∀ Z <: ⊤ . ⊤ )` -> sub`${G} , ${Xn} <: ${P} , ${D} ⊢ ${P} <: ( ∀ Z <: ⊤ . ⊤ )`) -> Empty {0}" ]
    -- **THE DEMO SET — `examples/demo/`, its own session too.** It declares a
    -- language called @Ty@, as the numbered series does, so the two cannot be
    -- installed at once. It is here so the demo cannot rot: these files are
    -- what gets shown to a room, and nothing else loads them.
    --
    -- The script is replayed as part of the walk, because its @:theorem@s are
    -- the interactive half of the same proofs and a broken tactic line is
    -- exactly the failure this is for.
    , testCase "the demo set loads, and proves progress both ways" $ do
        (s0, _) <- startingSession
        s <- foldl (\ms p -> ms >>= \s1 -> do
                      (s2, out, trouble) <- loadProofFile s1 p
                      if null trouble then pure s2 else stopped p s2 out trouble)
               (pure s0)
               [ "examples/demo/Demo01Expressions.thena", "examples/demo/Demo02Judgments.thena"
               , "examples/demo/Demo03Derivations.thena", "examples/demo/Demo04Progress.thena"
               , "examples/demo/Demo06Trust.thena" ]
        let script = "examples/demo/Demo05ByTactics.thena.script"
        (s', out, halted) <- loadFile s script
        if null halted then pure ()
          else assertFailure
                 (unlines ((script ++ " stopped:") : concatMap (renderResponse s') out))
        let pin cmd expected =
              let (s'', r) = command s' cmd in renderResponse s'' r @?= expected
        -- Progress, proved ahead of time in the surface language.
        pin ":infer progress"
          [ "progress : ∀ (M : Tm) (T : Ty) -> typing`⊢ ${M} : ${T}` -> Or value`${M} value` (Steps M)" ]
        -- And a lemma proved again by hand, through the interactive split.
        pin ":infer predSteps-tactics"
          [ "predSteps-tactics : ∀ (t : Tm) -> nvalue`${t} nv` -> Steps Tm`( pred ${t} )`" ]
    ]
  where
    numbered f = case stripPrefix "Stlc" f of
      Just (a : b : _) -> isDigit a && isDigit b
      _                -> False

    go :: Session -> [FilePath] -> [FilePath] -> IO Session
    go s _ [] = pure s
    go s bases (f : more) = do
      let path = "examples/" ++ f
      if ".thena.rules" `isSuffixOf` f
        then do
          let bases' = bases ++ [path]
          (s', out, trouble) <- loadRuleFiles s bases'
          if null trouble then go s' bases' more else stopped path s' out trouble
        else if ".thena" `isSuffixOf` f
          then do
            (s', out, trouble) <- loadProofFile s path
            if null trouble then go s' bases more else stopped path s' out trouble
          -- A script of command lines (phase 109c), run as `:load` runs one:
          -- it fails if any line stops.
          else if ".thena.script" `isSuffixOf` f
            then do
              (s', out, halted) <- loadFile s path
              if null halted then go s' bases more
                else assertFailure
                       (unlines ((path ++ " stopped:")
                                  : concatMap (renderResponse s') out))
            else assertFailure (path ++ " is a numbered example of a kind this test does not load")

    -- **The trouble is what says what went wrong**, since every door here reads
    -- files: an import that is not on disc, a cycle, a header that disagrees
    -- with its path, or a module that would not elaborate.
    stopped :: FilePath -> Session -> [Response] -> [Trouble] -> IO a
    stopped path s out trouble = assertFailure
      (unlines ((path ++ " did not load:")
                 : concatMap (renderTrouble s) trouble
                ++ concatMap (renderResponse s) out))
