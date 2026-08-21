-- | Breaks the Component/Partial import cycle (§2.5).
--
-- 'Component'\'s @Guess@ field is a 'Partial' and 'Partial'\'s @Under@ field is
-- a 'Component', so the two modules import each other. This file is what lets
-- them stay separate: "Thena.Development.Component" imports it with
-- @{-# SOURCE #-}@ and sees 'Partial' abstractly.
--
-- The two instance declarations are not decoration. 'Component' derives 'Eq'
-- and 'Show', and a derived instance calls @==@ and @showsPrec@ on every
-- field — so without them the deriving fails on the @Guess@ field with a bare
-- \"No instance for 'Eq Partial'\".
module Thena.Development.Partial where

data Partial

instance Eq Partial
instance Show Partial
