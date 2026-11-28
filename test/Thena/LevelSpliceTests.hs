-- | A rule that reads the LEVEL out of its own goal (MS12 phase 361,
-- @~bkrvn@).
--
-- A level argument used to be a numeral and nothing else, anywhere in the
-- development calculus, so a clause could only say @Eq {0} …@ — pinned at one
-- level — and a rule that wanted the level its goal was stated at had no way
-- to ask. @DECISIONS.md@ published the spelling that fixes it, @{${l}}@, and
-- nothing parsed it.
--
-- __The judge is @qed@__, which runs 'Thena.Kernel.certify' over the finished
-- development: the level the head read is the level the body wrote into
-- @refl@, and a term at the wrong level could not be proved past.
--
-- __And the control is the same rule with the numeral written__. It proves the
-- goal at level zero and is stuck at level one, which is the whole of what was
-- missing said in two lines.
module Thena.LevelSpliceTests (tests) where

import Data.List (isInfixOf)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase)

import Thena.Driver
  ( Response (..)
  , Session
  , command
  , consultRuleTexts
  )
import Thena.Files (startingSession)
import Thena.Render (renderResponse)

-- | The rule under test: whatever level the equation is stated at, the
-- reflexivity proof is written at that level.
spliced :: String
spliced =
  unlines
    [ "rule base levels where"
    , ""
    , "by-reflexivity : ()"
    , "rule by-reflexivity at ? _ : core`Eq {${l}} ${A} ${a} ${b}` :-"
    , "  do t = resolve-core core`refl {${l}} ${A} ${a}`"
    , "     ; fill t"
    , "     ; solve"
    ]

-- | The same clause with the level written down — what a rule base could say
-- before this phase, and all it could say.
pinned :: String
pinned =
  unlines
    [ "rule base pinned where"
    , ""
    , "at-zero : ()"
    , "rule at-zero at ? _ : core`Eq {0} ${A} ${a} ${b}` :-"
    , "  do t = resolve-core core`refl {0} ${A} ${a}`"
    , "     ; fill t"
    , "     ; solve"
    ]

-- | A started session with one of the two bases pushed on top of it.
--
-- **The prelude has to be there**, which is why this starts where a real
-- session does: @Eq@ and @refl@ are declared in it, and a core pattern is
-- resolved when the base is READ, so a clause naming @Eq@ is refused by a
-- session that has not loaded it.
sessionWith :: String -> IO Session
sessionWith src = do
  (s0, _) <- startingSession
  case consultRuleTexts s0 [("levels.thena.rules", src)] of
    (s, BasesLoaded _ _) -> pure s
    (_, other) -> fail ("the fixture's base did not load: " ++ show other)

-- | A run of commands, keeping the last one's output.
run :: Session -> [String] -> [String]
run s = snd . foldl (\(s', _) c -> let (s'', r) = command s' c in (s'', renderResponse s'' r)) (s, [])

-- | @Nat@, and nothing else done.
withNat :: [String] -> [String]
withNat more =
  [ "data Nat : Type\8320 where { zero : Nat ; succ : Nat -> Nat }"
  , "open Nat"
  ] ++ more

-- | The proof, at a level the caller picks.
proof :: String -> String -> [String]
proof rule lvl =
  withNat
    [ ":theorem t : Eq {" ++ lvl ++ "} Nat zero zero"
    , rule
    , "qed"
    ]

tests :: TestTree
tests =
  testGroup
    "a rule that reads its goal's level (MS12 phase 361)"
    [ testCase "the level the head read is the level the proof is written at" $ do
        s <- sessionWith spliced
        let out = run s (proof "by-reflexivity" "1")
        assertBool (unlines out)
          (any ("t : Eq {1} Nat zero zero" `isInfixOf`) out)

    , testCase "…and the same clause proves the same theorem at level zero" $ do
        s <- sessionWith spliced
        let out = run s (proof "by-reflexivity" "0")
        assertBool (unlines out)
          (any ("t : Eq {0} Nat zero zero" `isInfixOf`) out)

      -- The two cases below are the item in two lines: what a base could
      -- already say, and where it stopped.
    , testCase "a written numeral proves it at the level it names" $ do
        s <- sessionWith pinned
        let out = run s (proof "at-zero" "0")
        assertBool (unlines out)
          (any ("t : Eq {0} Nat zero zero" `isInfixOf`) out)

    , testCase "…and is stuck one level up" $ do
        s <- sessionWith pinned
        let out = run s (withNat
                          [ ":theorem t : Eq {1} Nat zero zero"
                          , "at-zero"
                          ])
        assertBool (unlines out)
          (any ("no clause of at-zero applies" `isInfixOf`) out)
    ]
