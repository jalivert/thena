-- | The development display representation (MS7 phase 115c;
-- @discussion\/editor-display.md@ §5).
--
-- **The crossing**, exactly 115a's and 115b's own argument: 'chainText'
-- draws only what 'Thena.View.Development.displayDevelopment' hands it —
-- no session, no cursor, no fixture — and if that text is what
-- 'Thena.Repl.renderPartial' prints for the same development, the display
-- carries what the printer needed. 'Thena.Fixtures' already covers the
-- interesting shapes (a guess, a constraint with a non-empty Ξ, one link of
-- each kind, shadowing both ways, every core field, a binder at the end), so
-- this reuses them rather than building its own.
--
-- **What text cannot check** — whether a guess is pure, whether a hole is
-- blocked, and which link is focused — is checked directly instead.
module Thena.View.DevelopmentTests (tests) where

import Data.Foldable (toList)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Core.Level (Level (..))
import Thena.Core.Term (Core (..), Ident (..), fresh)
import Thena.Development.Component (Component (..))
import Thena.Development.Cursor (along, enter, focus, into, prefix)
import Thena.Development.Partial (Partial (..))
import Thena.Fixtures
  ( allFour
  , guessShadowing
  , idMidway
  , richTypes
  , shadowedBinders
  , trailingLam
  , withConstraint
  )
import Thena.View.Address (Address (..))
import Thena.View.Development
  ( LinkShape (..)
  , LinkView (..)
  , displayDevelopment
  )
import Thena.View.Core (Budget (..))
import Thena.View.Redraw (chainText)
import Thena.Render (renderPartial)

tests :: TestTree
tests =
  testGroup
    "Thena.View.Development"
    [ testGroup "the display carries everything the printer needed" crossingCases
    , testGroup "pure and blocked, which no text shows" flagCases
    , testGroup "which link is the focus" focusCases
    ]

-- ---------------------------------------------------------------------------
-- The crossing
-- ---------------------------------------------------------------------------

crossingCases :: [TestTree]
crossingCases =
  [ agree "the running example, a guess with a hole inside it" idMidway
  , agree "a constraint, with a non-empty Ξ" withConstraint
  , agree "one link of each kind" allFour
  , agree "shadowed identifiers across two links" shadowedBinders
  , agree "a guess whose body shadows the hole itself" guessShadowing
  , agree "every core field a component's type can have" richTypes
  , agree "a trailing term that is itself a binder" trailingLam
  ]
  where
    agree name p =
      testCase name $
        chainText (displayDevelopment [] (Budget 200) 500 (Address []) Nothing p)
          @?= renderPartial [] 500 [] p

-- ---------------------------------------------------------------------------
-- Pure and blocked
-- ---------------------------------------------------------------------------

-- | A guess or claim link, wherever it sits — a top-level link, or one inside
-- another guess's own body.
allLinks :: [LinkView] -> [LinkView]
allLinks = concatMap expand
  where
    expand lv@(LinkView _ _ AGuessLink {guessBody = body}) = lv : allLinks body
    expand lv = [lv]

-- | @allFour@'s guess (@g@) has a trailing body with no holes and no
-- constraints — pure by inspection, and 'extract' agrees; its own hole is
-- used by the guess right after it, so it is blocked.
--
-- @idMidway@'s guess (@id'@) has an unresolved @Claim@ (@h@) inside its own
-- body — not pure — and is likewise used right after it. That same @h@,
-- inside the body, is blocked for the same reason: the body's own trailing
-- term uses it immediately.
--
-- Neither fixture has an unblocked hole — everything built there is used
-- immediately, which is why it was built that way — so one is constructed
-- here: a claim whose type mentions nothing that follows it.
flagCases :: [TestTree]
flagCases =
  [ testCase "a guess with nothing left to solve is pure, and is used" $
      guessFlags "g" allFour @?= Just (True, True)
  , testCase "a guess with an unresolved hole inside it is not pure" $
      guessFlags "id'" idMidway @?= Just (False, True)
  , testCase "a hole used right after it is blocked" $
      claimFlag "h" idMidway @?= Just True
  , testCase "a hole nothing after it mentions is not blocked" $
      claimFlag "h" unblocked @?= Just False
  ]
  where
    linksOf p = allLinks (displayDevelopment [] (Budget 200) 500 (Address []) Nothing p)

    guessFlags name p =
      case [s | LinkView _ _ s@AGuessLink {guessName = n} <- linksOf p, n == name] of
        AGuessLink {guessPure = pu, guessBlocked = bl} : _ -> Just (pu, bl)
        _ -> Nothing

    claimFlag name p =
      case [s | LinkView _ _ s@AClaimLink {claimName = n} <- linksOf p, n == name] of
        AClaimLink {claimBlocked = bl} : _ -> Just bl
        _ -> Nothing

    unblocked :: Partial
    unblocked =
      let (v, _) = fresh 0
       in Under (Claim v (Ident "h") (Universe LZero)) (Trailing (Universe LZero))

-- ---------------------------------------------------------------------------
-- Focus — chain-link precision, not term precision
-- ---------------------------------------------------------------------------

focusCases :: [TestTree]
focusCases =
  [ testCase "the third link, and no other, is marked" $ do
      cur <- unwrap (along =<< along (enter allFour))
      let route = Just (toList (prefix cur), focus cur)
          links = displayDevelopment [] (Budget 200) 500 (Address []) route allFour
      map linkFocus links @?= [False, False, True, False, False]
  , testCase "inside a guess's own body, the guess link itself is not marked" $ do
      -- One `along` reaches the guess; `into` enters its body, where
      -- `idMidway`'s own `Assume a` is the first link.
      cur <- unwrap (into =<< along (enter idMidway))
      let route = Just (toList (prefix cur), focus cur)
          links = displayDevelopment [] (Budget 200) 500 (Address []) route idMidway
      map linkFocus links @?= [False, False, False]
      case links of
        [_, LinkView _ _ AGuessLink {guessBody = body}, _] ->
          map linkFocus body @?= [True, False, False]
        _ -> assertFailure "idMidway's second link was not the guess"
  ]
  where
    unwrap (Right c) = pure c
    unwrap (Left e)  = assertFailure (show e) >> error "unreachable"
