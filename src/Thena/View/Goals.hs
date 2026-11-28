-- | __Every goal the development is holding, and the word that reaches it__
-- (MS12 phase 324).
--
-- **His request, 2026-11-19**: the goals pane is to show, beside each goal, the
-- variable it is bound to — and to list guesses as goals as well as holes. The
-- variable is the point: a typed line now starts with every hole and guess
-- bound ('Thena.Engine.goalEnv'), so @goto ‹that word›@ is the exact move to it,
-- and a pane that shows the word is showing something a reader can act on rather
-- than a label.
--
-- **Why a view of its own and not a shape of 'Thena.View.Development.LinkView'.**
-- A link is a position in a chain, nested as the chain nests; a goal list is
-- flat, because what a reader wants from it is /what is left to prove/ and that
-- question has no nesting in it. A guess's body holds goals and the guess is one
-- too, so a pane walking links has to decide how to flatten — which is a
-- decision the engine already makes, in 'Thena.Development.Cursor.goalsIn', and
-- should not make twice.
--
-- **It is DERIVED from the link list and that is deliberate.** The types and the
-- addresses have to be the ones the development view prints, and printing a
-- component's type apart from the chain it sits in gives @‹Var 3›@ where the
-- reader sees @T@ — the de Bruijn names are resolved by the walk, not by the
-- component. One walk, so the two cannot disagree about either.
module Thena.View.Goals
  ( GoalView (..)
  , GoalKind (..)
  , goalsOf
  ) where

import Thena.View.Address (Address)
import Thena.View.Core (Display)
import Thena.View.Development (LinkShape (..), LinkView (..))

-- | A hole or a guess — the two components that are goals.
--
-- **A guess is a goal, and that is his ruling of 2026-11-19.** It had been left
-- out of the pane, which is what made a proof of @∀ (T : Type) -> T -> T@ look
-- as though it had one goal and then none: the outer @attack@ had turned the
-- root into a guess, and a guess was invisible. It is unfinished, so it is left
-- to prove, so it is listed.
data GoalKind
  = AHole   -- ^ @? x : S@ — nothing stands in it yet
  | AGuess  -- ^ @? x ≐ g : S@ — something does, and it is not committed
  deriving (Eq, Show)

-- | One goal: the word to type, what kind it is, its type, where it is.
data GoalView = GoalView
  { goalViewVar :: String
    -- ^ **the word @goto@ takes.** A typed line binds every goal under the
    -- identifier the development prints it by, so this is both the label and
    -- the thing to write; 'Thena.Core.Cursor.freshIdent' makes it unique in the
    -- development, so one word is one goal.
  , goalViewKind :: GoalKind
  , goalViewType :: Display
    -- ^ what it has to be proved at, printed in the context it stands in.
  , goalViewAt :: Address
    -- ^ the moves that reach it from the root, for a click. @goto@ reaches it in
    -- one word; this is the other door and both are ordinary programs.
  , goalViewFocus :: Bool
    -- ^ does the cursor stand on it — chain-link precision, as
    -- 'Thena.View.Development.linkFocus' means it.
  , goalViewBlocked :: Bool
    -- ^ does anything later in the development still mention it. The field a
    -- pane needs to say why @abandon@ would refuse.
  }
  deriving (Eq, Show)

-- | Flatten a development's links into its goals, outermost first.
--
-- **A guess comes before the goals inside it**, which is the order the chain is
-- written in and the order 'Thena.Development.Cursor.goalsIn' answers, so a
-- pane and the prompt agree about which goal is first.
goalsOf :: [LinkView] -> [GoalView]
goalsOf = concatMap goal
  where
    goal l = case linkShape l of
      AClaimLink nm ty blocked ->
        [ GoalView nm AHole ty (linkAt l) (linkFocus l) blocked ]
      AGuessLink nm ty _ blocked body ->
        GoalView nm AGuess ty (linkAt l) (linkFocus l) blocked : goalsOf body
      _ -> []
