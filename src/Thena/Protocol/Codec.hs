-- | Turning values into 'Json' and back (phase 112).
--
-- **One shape, and it is an array whose head is the constructor's name:**
-- @[\"SurfaceName\",\"foo\"]@, @[\"SurfaceArrow\", a, b]@. A record is a
-- constructor with fields and is written the same way, in declaration order.
--
-- Why positional rather than an object of named fields: it is one rule for
-- every type instead of two, it is a third of the bytes, and it is still
-- readable in a file. **Adding a field to a record changes the arity**, which
-- 'wrongArity' catches loudly at the first old document — a silently missing
-- field is the failure this shape rules out.
--
-- **Hand-written instances, not derived.** The decision, and it is reversible:
-- the types below the protocol include abstract ones whose constructors are
-- deliberately hidden ('Thena.Core.Term.Scope', 'Thena.Development.Cursor'),
-- and generic derivation cannot see inside them without opening what §3.4 keeps
-- shut. Deriving the plain types and hand-writing the rest would be two
-- mechanisms; this is one. The round trip is what keeps a hand-written pair
-- honest — a field dropped by 'toJson' cannot be recovered by 'fromJson', so
-- the property fails rather than passing quietly.
module Thena.Protocol.Codec
  ( ToJson (..)
  , FromJson (..)
  , CodecError (..)
    -- * Writing an instance
  , tagged
  , untagged
  , wrongShape
  , noSuchCase
  ) where

import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE

import Thena.Protocol.Json (Json (..))

class ToJson a where
  toJson :: a -> Json

class FromJson a where
  fromJson :: Json -> Either CodecError a

-- | Why a 'Json' value was not the thing it was being read as.
--
-- Structured, never a message (§12). 'WrongShape' names what was expected
-- rather than quoting a grammar, because the caller knows which type it asked
-- for and the value is carried beside it.
data CodecError
  = WrongShape String Json
    -- ^ what was expected, and what was there
  | NoSuchCase String String Int
    -- ^ the type, the tag, and how many fields it came with.
    --
    -- **One error for an unknown tag and for a known tag at the wrong arity**,
    -- because to a reader they are the same fact: this type has no such case.
    -- It is also the one that fires when a record grows a field and an old
    -- document is read, which is the drift this encoding is shaped to catch.
  deriving (Eq, Show)

-- | Write a constructor: its name, then its fields in order.
tagged :: String -> [Json] -> Json
tagged t as = JArray (JString t : as)

-- | Read a constructor. The type name is carried only so a failure can say
-- which read failed.
untagged :: String -> Json -> Either CodecError (String, [Json])
untagged what v = case v of
  JArray (JString t : as) -> Right (t, as)
  _                       -> Left (WrongShape what v)

wrongShape :: String -> Json -> Either CodecError a
wrongShape what = Left . WrongShape what

-- | The last line of every 'fromJson' below: the tag did not match any case of
-- this type at that number of fields.
noSuchCase :: String -> String -> [Json] -> Either CodecError a
noSuchCase ty t as = Left (NoSuchCase ty t (length as))

-- --------------------------------------------------------------------------
-- The primitives
-- --------------------------------------------------------------------------

instance ToJson Int where
  toJson = JInt . fromIntegral

-- | **Range-checked, because 'Json' carries an 'Integer' and this does not.**
-- A document holding a number too large for a machine word is refused rather
-- than wrapped into a small one — a silently truncated level or position would
-- be a wrong proof rather than a failed read.
instance FromJson Int where
  fromJson v@(JInt n)
    | n >= fromIntegral (minBound :: Int) && n <= fromIntegral (maxBound :: Int) =
        Right (fromIntegral n)
    | otherwise = wrongShape "Int" v
  fromJson v = wrongShape "Int" v

instance ToJson Integer where
  toJson = JInt

instance FromJson Integer where
  fromJson (JInt n) = Right n
  fromJson v        = wrongShape "Integer" v

instance ToJson Bool where
  toJson = JBool

instance FromJson Bool where
  fromJson (JBool b) = Right b
  fromJson v         = wrongShape "Bool" v

instance ToJson Char where
  toJson c = JString [c]

instance FromJson Char where
  fromJson (JString [c]) = Right c
  fromJson v             = wrongShape "Char" v

-- | @String@ is @[Char]@, and it is the one type where the list instance would
-- be wrong: a name must be a JSON string, not an array of one-character
-- strings. @{-# OVERLAPPING #-}@ is what makes @String@ win over @[a]@, and it
-- is the only overlap in this module.
instance {-# OVERLAPPING #-} ToJson String where
  toJson = JString

instance {-# OVERLAPPING #-} FromJson String where
  fromJson (JString s) = Right s
  fromJson v           = wrongShape "String" v

instance ToJson a => ToJson [a] where
  toJson = JArray . map toJson

instance FromJson a => FromJson [a] where
  fromJson (JArray xs) = traverse fromJson xs
  fromJson v           = wrongShape "list" v

-- | @Nothing@ is @null@; @Just x@ is @x@ itself.
--
-- **Only correct because nothing this protocol carries is a @Maybe@ of
-- something that can itself be @null@** — no field below is
-- @Maybe (Maybe a)@, and none is a @Maybe Json@. If one ever is, this instance
-- is where the ambiguity would live and it must become tagged instead.
instance ToJson a => ToJson (Maybe a) where
  toJson Nothing  = JNull
  toJson (Just x) = toJson x

instance FromJson a => FromJson (Maybe a) where
  fromJson JNull = Right Nothing
  fromJson v     = Just <$> fromJson v

instance (ToJson a, ToJson b) => ToJson (a, b) where
  toJson (a, b) = JArray [toJson a, toJson b]

instance (FromJson a, FromJson b) => FromJson (a, b) where
  fromJson (JArray [a, b]) = (,) <$> fromJson a <*> fromJson b
  fromJson v               = wrongShape "pair" v

-- | A non-empty list is a JSON array, and reading one back refuses an empty
-- array rather than making a list that the type says cannot exist.
instance ToJson a => ToJson (NonEmpty a) where
  toJson = JArray . map toJson . NE.toList

instance FromJson a => FromJson (NonEmpty a) where
  fromJson v = case v of
    JArray (x : xs) -> (:|) <$> fromJson x <*> traverse fromJson xs
    JArray []       -> wrongShape "non-empty list" v
    _               -> wrongShape "non-empty list" v
