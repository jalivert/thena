-- | A split taken interactively, at a hole — @induction-core@ and @case-core@
-- (MS9 phase 231).
--
-- @examples\/split-at-a-hole.thena.script@ is the file, and it proves two
-- theorems: @belowRefl@ over a family with a dependent index telescope, by
-- induction, and @vhead@ at a pinned index, by cases. **The end-to-end judge is
-- @qed@**, which runs 'Thena.Kernel.certify' over the finished development, so a
-- goal the tactic shaped wrongly cannot be proved past.
--
-- __WHY IT IS A SCRIPT AND NOT A MODULE__, which is the opposite of
-- "Thena.DependentIndexTests"\'s reason for being a module: the thing being
-- exercised here IS the hand-driven path. A written @case … of@ never reaches
-- @induction-core@, because elaboration goes through @split-elaborate@ and
-- claims the arms itself.
--
-- __What is pinned here that the script alone does not say.__ That a case the
-- specialiser closed leaves the author NO subgoal — the @no subgoals@ the
-- engine says for @vnil@ against the @subgoals: vconsCase@ it says for @vcons@
-- one line later — and that the theorem admitted at the end computes from the
-- binder its case bound rather than from anything ambient.
--
-- __The claim's own line comes first and is the same for both words.__
-- @prim-eliminate@ and @prim-case@ each claim a method hole per constructor
-- before any of them is specialised, so @subgoals: vnilMethod, vconsMethod@ is
-- printed by the claim and says nothing yet about which cases survive.
module Thena.InteractiveSplitTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

import Thena.Core.Term (GlobalName (..))
import Thena.Driver (Session, command, machineOf)
import Thena.Engine (Machine (..))
import Thena.Files (loadFile, startingSession)
import Thena.Global.Env (Definition (..), lookupDefinition)
import Thena.Render (Rendering (..), renderCore, renderResponse)

-- | Relative to the package root, which is where the suite runs.
target :: FilePath
target = "examples/split-at-a-hole.thena.script"

-- | One command, and what the session said back.
step :: Session -> String -> (Session, [String])
step s cmd = let (s', r) = command s cmd in (s', renderResponse s' r)

-- | A run of commands, keeping only the last one's output: the lines that
-- matter here are the ones the split itself prints.
run :: Session -> [String] -> (Session, [String])
run s = foldl (\(s', _) cmd -> step s' cmd) (s, [])

-- | Enough of a session to split in: a length-indexed vector, and a theorem
-- attacked down to the hole where the scrutinee is in scope.
atAHole :: Session -> (Session, [String])
atAHole s =
  run s
    [ "data N : Type\8320 where { z : N ; s : N -> N }"
    , "data Vec (A : Type\8320) : forall (n : N) -> Type\8320 where \
      \{ vnil : Vec A z ; vcons : forall (n : N) (a : A) (as : Vec A n) -> Vec A (s n) }"
    , ":theorem vfirst : \8704 (A : Type\8320) (m : N) (xs : Vec A (s m)) -> A"
    , "attack", "intro", "intro", "intro", "into", "along", "along", "along"
    ]

tests :: TestTree
tests =
  testGroup
    "a split taken at a hole"
    [ testCase "the script runs to the end" $ do
        (s, _) <- startingSession
        (_, _, stopped) <- loadFile s target
        assertBool (unlines (map show stopped)) (null stopped)

      -- The statement is the one `dependent-index.thena.script` proves by
      -- hand, so the two paths are known to end in the same place.
    , testCase "and the inductive theorem is admitted at its written type" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadFile s target
        case lookupDefinition (GlobalName "belowRefl") (globals (machineOf s')) of
          Nothing -> assertFailure "belowRefl was not admitted"
          Just d ->
            renderCore (Rendering [] (names (machineOf s'))) [] (definitionType d)
              @?= "\8704 (n : Nat) (i : Fin n) -> Below n i -> Eq {0} (Fin n) i i"

      -- __And the arm really bound the constructor's own argument__: `vhead` of
      -- a one-element vector is that element. An arm handed something ambient
      -- would have the same type and would not reduce to `z`.
    , testCase "and the theorem by cases computes from the binder its case bound" $ do
        (s, _) <- startingSession
        (s', _, _) <- loadFile s target
        let (_, out) = step s' ":whnf vhead N z (vcons N z z (vnil N))"
        out @?= ["z"]

      -- __A CASE THE SPECIALISER CLOSED IS NOT SHOWN TO THE AUTHOR__, which is
      -- the one place the interactive walk decides something the written one
      -- does not have to. `vnil`'s equation is `z \8771 s m`, a conflict, so its
      -- method is filled and solved on the way past and only `vcons` is left.
    , testCase "a case that cannot arise leaves no subgoal" $ do
        (s0, _) <- startingSession
        let (s1, _) = atAHole s0
            (_, out) = step s1 "case-core core`xs`"
        out
          @?= [ "subgoals: vnilMethod, vconsMethod"
              , "no subgoals"
              , "subgoals: vconsCase"
              ]

      -- The same split by the other word: `induction` hands each method a
      -- hypothesis per recursive argument, so `vcons`'s case has one more
      -- binder than it does above — and the subgoal it leaves is still one.
    , testCase "and the inductive word leaves the same one subgoal" $ do
        (s0, _) <- startingSession
        let (s1, _) = atAHole s0
            (_, out) = step s1 "induction-core core`xs`"
        out
          @?= [ "subgoals: vnilMethod, vconsMethod"
              , "no subgoals"
              , "subgoals: vconsCase"
              ]
    ]
