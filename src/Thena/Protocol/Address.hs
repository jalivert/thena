-- | Where a thing is, said in the system's own words.
--
-- The editor has to be able to point at a component, a constraint or a subterm
-- and say /that one/ — to focus it, to ask about it, to highlight it. It cannot
-- hold the thing itself: a 'Cursor' carries the whole development along its
-- path, so shipping one would ship the development twice over, and the editor
-- could not read it anyway.
--
-- **So a position is named by the moves that reach it from the root**, and the
-- moves are the ones the user already types — @along@, @into@, @cross type@,
-- @cross val@, @down@. Nothing is minted, nothing is registered, and no table
-- has to be invalidated when the development changes: an 'Address' is a
-- question the development answers, and a stale one is refused rather than
-- silently wrong.
--
-- The two directions are 'addressOf' — read the address of where a cursor
-- stands — and 'follow', which walks one from the root. Phase 111's own test is
-- that they agree: @follow (addressOf c)@ returns to @c@, for every position
-- any sequence of moves can reach.
module Thena.Protocol.Address
  ( Address (..)
  , Move (..)
  , addressOf
  , follow
  , AddressError (..)
  ) where

import Data.Foldable (toList)

import Thena.Development.Cursor
  ( Crossing (..)
  , Cursor
  , Focus (..)
  , Part (..)
  , Slot (..)
  , Step (..)
  , TermStep (..)
  , along
  , crossType
  , crossValue
  , down
  , enter
  , focus
  , into
  , prefix
  , rebuild
  )
import Thena.Errors (MoveError)

-- | A position, as the moves that reach it from the root of the development.
--
-- Root-first, which is the order 'follow' walks and the order the breadcrumb
-- reads. The empty address is the root.
newtype Address = Address [Move]
  deriving (Eq, Show)

-- | One move. These are exactly the cursor's descents (§4.3) and nothing else:
-- @back@ is history rather than structure, and @goto@ and @goto-named@ are
-- absolute jumps that any 'Address' can already express.
--
-- 'GoAlong' serves both a component and a constraint, because from outside the
-- development /advance one link/ is one move and the chain knows which kind of
-- link it passed. The address says how far; the development says what is there.
data Move
  = GoAlong        -- ^ past the head of the focus — a component or a constraint
  | GoInto         -- ^ into the focused guess's body
  | GoCrossType    -- ^ to a component's type
  | GoCrossValue   -- ^ to a definition's value
  | GoDown Part    -- ^ into a named field of a core term (§4.7)
  deriving (Eq, Show)

-- | Why an address did not lead anywhere.
--
-- 'NoSuchPosition' carries how many moves were taken before the refusal, so a
-- client can be told where its address stopped matching rather than only that
-- it did. A stale address is the ordinary case, not a bug: the editor drew a
-- term, the development changed underneath it, and the click arrived late.
data AddressError = NoSuchPosition Int MoveError
  deriving (Eq, Show)

-- | The address of where a cursor stands.
--
-- Read off the cursor's own path and focus, so it cannot disagree with the
-- position it describes.
addressOf :: Cursor -> Address
addressOf cur = Address (spine <> core)
  where
    spine = map ofStep (toList (prefix cur))

    ofStep s = case s of
      Along     _     -> GoAlong
      Past      _     -> GoAlong
      IntoGuess{}     -> GoInto

    -- A core focus is reached either by walking off the end of the chain — in
    -- which case the last 'Along' already accounts for it — or by crossing into
    -- a component's field, which is one further move.
    core = case focus cur of
      OnComponent  _        -> []
      OnConstraint _        -> []
      OnTerm crossing ts _  -> ofCrossing crossing <> map (GoDown . partOf) (toList ts)

    ofCrossing c = case c of
      TrailingTerm -> []
      InSlot slot _ -> case slot of
        TypeOfAssume{}   -> [GoCrossType]
        TypeOfDefine{}   -> [GoCrossType]
        TypeOfClaim{}    -> [GoCrossType]
        TypeOfGuess{}    -> [GoCrossType]
        TypeOfQuantify{} -> [GoCrossType]
        ValueOfDefine{}  -> [GoCrossValue]

-- | Which 'Part' names the field a 'TermStep' descended into.
--
-- The inverse of 'down'\'s table, and the positional fields are read from it
-- rather than guessed: 'down' splits a list with a **one-based** @pick@, so the
-- index is the length of what came before plus one.
partOf :: TermStep -> Part
partOf s = case s of
  IntoFun      _           -> Fun
  IntoArg      _           -> Arg
  IntoPiDom    _ _         -> Dom
  IntoPiCod    _ _ _       -> Cod
  IntoLamDom   _ _         -> Dom
  IntoLamBody  _ _ _       -> Body
  IntoLetValue _ _ _       -> Val
  IntoLetType  _ _ _       -> Type
  IntoLetBody  _ _ _ _     -> Body
  IntoCanonArg _ _ bs _            -> CanonArg (length bs + 1)
  IntoElimParam  _ _ bs _ _ _ _ _  -> Param  (length bs + 1)
  IntoElimMotive _ _ _    _ _ _    -> Motive
  IntoElimMethod _ _ _ _ bs _ _ _  -> Method (length bs + 1)
  IntoElimIndex  _ _ _ _ _ bs _ _  -> Index  (length bs + 1)
  IntoElimTarget _ _ _ _ _ _       -> Target

-- | Walk an address from the root of the development the cursor belongs to.
--
-- The counter is the session's name supply: descending under a core binder
-- mints a fresh variable, exactly as @down@ does when the user types it, so
-- following an address is not observationally different from typing the moves.
-- The counter that comes back is the one to keep.
follow :: Address -> Int -> Cursor -> Either AddressError (Cursor, Int)
follow (Address ms) n0 cur = go 0 (enter (rebuild cur)) n0 ms
  where
    go _ c n []       = Right (c, n)
    go k c n (m : ms') = case step m c n of
      Left e          -> Left (NoSuchPosition k e)
      Right (c', n')  -> go (k + 1) c' n' ms'

    step m c n = case m of
      GoAlong      -> (,) <$> along      c <*> pure n
      GoInto       -> (,) <$> into       c <*> pure n
      GoCrossType  -> (,) <$> crossType  c <*> pure n
      GoCrossValue -> (,) <$> crossValue c <*> pure n
      GoDown part  -> down part n c
