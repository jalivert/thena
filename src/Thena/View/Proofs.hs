-- | What the session is holding and has put down, for the editor (MS12 phase
-- 310).
--
-- **HIS RULING OF 2026-11-11, and it is why this module exists**: /"make sure
-- that TUI has a principled way to consume the @:proofs@. Perhaps a view if
-- there is not one already. Because I will want TUI to have a pane for them to
-- show them at all times."/ There was none. @Thena.Driver.parked@ and
-- @Thena.Driver.workingOn@ were the only reads, and both hand out an
-- @Attempt@ — whose claim is a 'Thena.Core.Term.Core' term, which a frontend
-- may not draw, since drawing one needs the spelling, the grammars and a depth
-- budget as every other view does. The alternative was a pane reading
-- @Thena.Render@'s text back, which is the seam this module closes.
--
-- **A parked proof and a parked import are ONE list under ONE word** — his, and
-- the words are /"one list one word"/. So there is one list here too, and
-- nothing in it says which kind a row is other than what the row has to show:
-- a proof has a statement and an import does not. **Do not read 'QuestView' as
-- two panes**; it is one pane with two kinds of row.
--
-- **Nothing here is an operation.** A pane on this picks a row up by submitting
-- @:resume ‹word›@, which is the same line a user types, because unparking is a
-- step and never automatic (his ruling of 2026-11-11).
module Thena.View.Proofs
  ( ProofsView (..)
  , QuestView (..)
  , QuestClaim (..)
  , displayProofs
  ) where

import Thena.Core.Term (Spelling)
import Thena.Driver (Attempt (..), Importing (..), Parked (..), Quest (..), questWord)
import Thena.Language.Grammar (Grammar)
import Thena.View.Address (Address (..))
import Thena.View.Core (Budget, Display, displayCore)

-- | The quest the session is on, and the ones it has put down.
--
-- **The live one is a field and not the head of the list**, because a pane
-- draws it differently — it is the thing @qed@, @:suspend@ and @:abandon@ act
-- on without an argument — and a frontend splitting a list to find out would be
-- deciding which row that is, which is the engine's rule
-- ('Thena.Driver.currentQuest': innermost first).
data ProofsView = ProofsView
  { proofsViewOn     :: Maybe QuestView
    -- ^ what the session is on: the open proof, or the import standing in a
    -- @yield@ when there is no proof. 'Nothing' when it is on neither.
  , proofsViewParked :: [QuestView]
    -- ^ what has been put down, **most recently put down first**, which is the
    -- order @:proofs@ prints and the order 'Thena.Driver.parked' promises.
  }
  deriving (Eq, Show)

-- | One quest, as the editor sees it.
data QuestView = QuestView
  { questViewWord  :: String
    -- ^ **what @:resume@ takes, exactly as typed** — a theorem's name, or the
    -- header's text an import was reached by. The one word his ruling means, so
    -- a pane never has to build the line it submits out of two fields.
  , questViewClaim :: QuestClaim
  }
  deriving (Eq, Show)

-- | What a quest is, and what there is to show of it.
--
-- **A named case rather than a @Maybe Display@** — phase 37's correction, the
-- same one @Thena.Driver.Working@ carries: @Nothing@ would read as /this one
-- has no statement/ when it means /this one is not a theorem/, and a pane
-- drawing an empty row is the shape that mistake takes here.
data QuestClaim
  = AStatement Display
    -- ^ a theorem, and what @qed@ will certify against.
  | AnImportStanding String
    -- ^ **a module's load that reached a @yield@**, and the header's text
    -- again. There is no statement: an import is a program that stopped, and
    -- nothing will certify it — @yield@ carries it on and @:abandon@ gives it
    -- up. The text is repeated rather than left to 'questViewWord' so that a
    -- row can be drawn from this alone.
  deriving (Eq, Show)

-- | Build the view.
--
-- **A claim is displayed at the ROOT address and in no context.** A theorem's
-- statement is a closed term that is not a subterm of anything in the
-- development the session is standing in — for a parked one, not even of the
-- same development — so there is nothing to point at. 'Thena.View.Trust' hands
-- its claims the focus's address because they are what the focus rests on; a
-- parked quest's statement is not, and giving it that address would invite a
-- @goto@ into the wrong proof.
displayProofs
  :: Spelling
  -> [Grammar]
  -> Budget
  -> Int
  -> Maybe Quest
  -> [Parked]
  -> ProofsView
displayProofs spelling grammars budget counter on ps =
  ProofsView
    { proofsViewOn     = fmap one on
    , proofsViewParked = map (one . parkedQuest) ps
    }
  where
    one q =
      QuestView
        { questViewWord  = questWord q
        , questViewClaim = case q of
            AProof att   -> AStatement (display (attemptClaim att))
            AnImport imp -> AnImportStanding (importingText imp)
        }

    display = displayCore spelling grammars budget [] [] counter (Address [])
