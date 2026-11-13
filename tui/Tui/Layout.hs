-- | **Which panes are on screen, and where** — `~fxc89`, his instruction of
-- 2026-11-12: /"I wonder if we ought to introduce some feature of the TUI that
-- allows us to manage them… Let's say we work with 6 positions like we have
-- now, each one given a number… So we can do @:pane modules open 1@ or
-- @:pane usage close@ and so."/
--
-- **Six positions, two columns of three, numbered across**:
--
-- > 1 2
-- > 3 4
-- > 5 6
--
-- so the odd ones are the left column and the even ones the right. The
-- numbering is row-major and the layout is column-major; 'columnsOf' is the
-- whole of that translation and nothing else in the TUI does it.
--
-- **This module is pure and knows nothing about brick**, which is what lets
-- `thena-tui-test` hold the two operations to their results without a terminal
-- — and they are the half of `~fxc89` worth testing, the drawing being the
-- pty's business as always.
--
-- **A position is an address and not a rectangle held open.** Close the pane at
-- 3 and the panes below it move up a row on screen, because 'columnsOf' lists
-- only what is placed; but @output@ is still at 5, so
-- @:pane proofs open 3@ puts the new pane back between them. Renumbering on a
-- close would mean every address he had learned moved under him.
module Tui.Layout
  ( Pane (..)
  , allPanes
  , paneName
  , paneByName
  , Position
  , positions
  , Layout
  , defaultLayout
  , paneAt
  , positionOf
  , placedPanes
  , columnsOf
  , openPane
  , closePane
  ) where

import qualified Data.Map.Strict as Map

-- | The panes a position can hold, **and nothing else of the screen** — the
-- document is not one of these, which is the point: it takes whatever the
-- panes leave, so it has no width of its own and no position either.
--
-- **The names are the ones they already go by** — his instruction: /"I think
-- we can use the ones they already go by."/ They were the titles drawn at the
-- head of each pane before they were a vocabulary, so nothing he reads on
-- screen had to change to make this command typeable.
data Pane
  = Globals
  | Modules
  | Output
  | ProofTerm
  | Goals
  | Machine
  | Quests
    -- ^ **the parked proofs, and the import standing in a @yield@** —
    -- `~76zrr`. **Called @Quests@ here and drawn as @proofs@ on screen, on
    -- purpose**: the engine's word for both of the things this pane lists is a
    -- quest, because a module's load that stopped is not a proof and nothing
    -- will ever certify it, while the words he asked in were /"a pane with
    -- parked proofs"/. 'paneName' is the one place the two meet.
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Every pane there is, placed or not. **The width map is built over this and
-- not over what is on screen**, so a pane that is closed and opened again comes
-- back the width it was pulled to.
allPanes :: [Pane]
allPanes = [minBound .. maxBound]

-- | What a pane is called — on screen, in @:pane@, and in the completion. One
-- function, so the title and the word he types cannot drift apart.
paneName :: Pane -> String
paneName p = case p of
  Globals -> "globals"
  Modules -> "modules"
  Output -> "output"
  ProofTerm -> "proofterm"
  Goals -> "goals"
  Machine -> "machine"
  Quests -> "proofs"

paneByName :: String -> Maybe Pane
paneByName w = lookup w [(paneName p, p) | p <- allPanes]

-- | One of 'positions'. **Not an index into anything** — see the module note:
-- it is the pane's address, and a pane keeps it until he moves the pane.
type Position = Int

-- | @[1 .. 6]@. **Six because three panes to a column is what the vertical
-- room allows**: a column of four on a forty-row terminal gives each pane ten
-- rows, which is a heading and eight names.
positions :: [Position]
positions = [1 .. 6]

-- | Which pane is at which position. **A pane appears at most once** — every
-- operation here removes it from where it was before placing it, so there is no
-- state in which one pane is drawn in two columns.
newtype Layout = Layout (Map.Map Position Pane)
  deriving (Eq, Show)

-- | **Exactly the screen as it was before this command existed**, so nothing
-- moves until he types @:pane@. 'Quests' is the seventh pane and starts closed;
-- `~76zrr` is the item, and @:pane proofs open 6@ is the line that fetches it.
defaultLayout :: Layout
defaultLayout =
  Layout
    (Map.fromList
       [ (1, Globals)
       , (3, Modules)
       , (5, Output)
       , (2, ProofTerm)
       , (4, Goals)
       , (6, Machine)
       ])

paneAt :: Position -> Layout -> Maybe Pane
paneAt n (Layout m) = Map.lookup n m

positionOf :: Pane -> Layout -> Maybe Position
positionOf p (Layout m) =
  case [n | (n, q) <- Map.toAscList m, q == p] of
    n : _ -> Just n
    [] -> Nothing

-- | Every pane on screen, in position order.
placedPanes :: Layout -> [Pane]
placedPanes (Layout m) = Map.elems m

-- | **The two columns, each in position order** — odd positions left, even
-- right. A column holds only the panes actually placed in it, so a closed
-- position is one fewer row rather than a gap of backdrop.
columnsOf :: Layout -> ([Pane], [Pane])
columnsOf (Layout m) =
  ( [p | (n, p) <- Map.toAscList m, odd n]
  , [p | (n, p) <- Map.toAscList m, even n]
  )

-- | **Put a pane at a position, and say what that cost.**
--
-- The second component is the pane that was closed to make room, if any, so the
-- caller can tell him rather than leave him to notice. There are three cases
-- and only the third closes anything:
--
--   * the position is free — the pane moves there from wherever it was;
--   * the position is taken and the pane being opened is already on screen —
--     **the two swap**. @:pane goals open 1@ with @globals@ at 1 and @goals@ at
--     4 leaves goals at 1 and globals at 4. Refusing instead would mean no two
--     panes could ever trade places without a free position to stage through;
--   * the position is taken and the pane being opened is closed — the occupant
--     has nowhere to go, so **it is closed**, and it is named in the answer.
--
-- A pane opened onto the position it already holds is left alone.
openPane :: Pane -> Position -> Layout -> (Layout, Maybe Pane)
openPane p n layout@(Layout m)
  | n `notElem` positions = (layout, Nothing)
  | otherwise = case Map.lookup n m of
      Just q | q == p -> (layout, Nothing)
      Just q -> case positionOf p layout of
        Just was -> (Layout (Map.insert was q (Map.insert n p m)), Nothing)
        Nothing -> (Layout (Map.insert n p m), Just q)
      Nothing -> (Layout (Map.insert n p (without p m)), Nothing)

-- | Take a pane off the screen. **Its width is not forgotten** — that map is
-- keyed by pane and built over 'allPanes', so re-opening restores the width he
-- pulled it to.
closePane :: Pane -> Layout -> Layout
closePane p (Layout m) = Layout (without p m)

without :: Pane -> Map.Map Position Pane -> Map.Map Position Pane
without p = Map.filter (/= p)
