{-# OPTIONS_GHC -Wno-orphans #-}

-- | The protocol's own messages, as JSON (MS7 phase 114).
--
-- **Everything a client sends, and everything the server says that does not
-- carry a term.** A 'Thena.Driver.Response' mentioning a @Core@ term is not here
-- and is not an oversight — what a term looks like on the wire is
-- @ms7\/CLOSEOUT.md@ 5, and building a codec for it before that is decided would
-- be building the wrong one.
--
-- The orphan note in "Thena.Protocol.Concrete" applies here for the same reason
-- and is not repeated; @ms7\/CLOSEOUT.md@ 2 is the item.
module Thena.Protocol.Wire () where

import Thena.Protocol.Codec (FromJson (..), ToJson (..), noSuchCase, tagged, untagged)

import qualified Thena.Development.Cursor as C
import qualified Thena.Errors as E
import qualified Thena.Protocol.Address as A
import qualified Thena.Protocol.Codec as K
import qualified Thena.Protocol.Json as J
import qualified Thena.Protocol.Message as M

instance ToJson E.MoveError where
  toJson x = case x of
    E.AtRoot -> tagged "AtRoot" []
    E.NotOnTheSpine -> tagged "NotOnTheSpine" []
    E.NotInCore -> tagged "NotInCore" []
    E.NotAGuess -> tagged "NotAGuess" []
    E.NotADefinition -> tagged "NotADefinition" []
    E.StillReferenced -> tagged "StillReferenced" []
    E.NoCrossingIntoAConstraint -> tagged "NoCrossingIntoAConstraint" []
    E.NoSuchHole -> tagged "NoSuchHole" []
    E.NoSuchPart -> tagged "NoSuchPart" []

instance FromJson E.MoveError where
  fromJson v = untagged "MoveError" v >>= \case
    ("AtRoot", []) -> Right E.AtRoot
    ("NotOnTheSpine", []) -> Right E.NotOnTheSpine
    ("NotInCore", []) -> Right E.NotInCore
    ("NotAGuess", []) -> Right E.NotAGuess
    ("NotADefinition", []) -> Right E.NotADefinition
    ("StillReferenced", []) -> Right E.StillReferenced
    ("NoCrossingIntoAConstraint", []) -> Right E.NoCrossingIntoAConstraint
    ("NoSuchHole", []) -> Right E.NoSuchHole
    ("NoSuchPart", []) -> Right E.NoSuchPart
    (t, as) -> noSuchCase "MoveError" t as

instance ToJson C.Part where
  toJson x = case x of
    C.Fun -> tagged "Fun" []
    C.Arg -> tagged "Arg" []
    C.Dom -> tagged "Dom" []
    C.Cod -> tagged "Cod" []
    C.Val -> tagged "Val" []
    C.Type -> tagged "Type" []
    C.Body -> tagged "Body" []
    C.Motive -> tagged "Motive" []
    C.Target -> tagged "Target" []
    (C.Param a0) -> tagged "Param" [toJson a0]
    (C.Method a0) -> tagged "Method" [toJson a0]
    (C.Index a0) -> tagged "Index" [toJson a0]
    (C.CanonArg a0) -> tagged "CanonArg" [toJson a0]

instance FromJson C.Part where
  fromJson v = untagged "Part" v >>= \case
    ("Fun", []) -> Right C.Fun
    ("Arg", []) -> Right C.Arg
    ("Dom", []) -> Right C.Dom
    ("Cod", []) -> Right C.Cod
    ("Val", []) -> Right C.Val
    ("Type", []) -> Right C.Type
    ("Body", []) -> Right C.Body
    ("Motive", []) -> Right C.Motive
    ("Target", []) -> Right C.Target
    ("Param", [a0]) -> C.Param <$> fromJson a0
    ("Method", [a0]) -> C.Method <$> fromJson a0
    ("Index", [a0]) -> C.Index <$> fromJson a0
    ("CanonArg", [a0]) -> C.CanonArg <$> fromJson a0
    (t, as) -> noSuchCase "Part" t as

instance ToJson A.Move where
  toJson x = case x of
    A.GoAlong -> tagged "GoAlong" []
    A.GoInto -> tagged "GoInto" []
    A.GoCrossType -> tagged "GoCrossType" []
    A.GoCrossValue -> tagged "GoCrossValue" []
    (A.GoDown a0) -> tagged "GoDown" [toJson a0]

instance FromJson A.Move where
  fromJson v = untagged "Move" v >>= \case
    ("GoAlong", []) -> Right A.GoAlong
    ("GoInto", []) -> Right A.GoInto
    ("GoCrossType", []) -> Right A.GoCrossType
    ("GoCrossValue", []) -> Right A.GoCrossValue
    ("GoDown", [a0]) -> A.GoDown <$> fromJson a0
    (t, as) -> noSuchCase "Move" t as

instance ToJson A.Address where
  toJson x = case x of
    (A.Address a0) -> tagged "Address" [toJson a0]

instance FromJson A.Address where
  fromJson v = untagged "Address" v >>= \case
    ("Address", [a0]) -> A.Address <$> fromJson a0
    (t, as) -> noSuchCase "Address" t as

instance ToJson A.AddressError where
  toJson x = case x of
    (A.NoSuchPosition a0 a1) -> tagged "NoSuchPosition" [toJson a0, toJson a1]

instance FromJson A.AddressError where
  fromJson v = untagged "AddressError" v >>= \case
    ("NoSuchPosition", [a0, a1]) -> A.NoSuchPosition <$> fromJson a0 <*> fromJson a1
    (t, as) -> noSuchCase "AddressError" t as

instance ToJson M.JobId where
  toJson x = case x of
    (M.JobId a0) -> tagged "JobId" [toJson a0]

instance FromJson M.JobId where
  fromJson v = untagged "JobId" v >>= \case
    ("JobId", [a0]) -> M.JobId <$> fromJson a0
    (t, as) -> noSuchCase "JobId" t as

instance ToJson M.ProtocolError where
  toJson x = case x of
    M.NotAtTheWheel -> tagged "NotAtTheWheel" []
    (M.BadAddress a0) -> tagged "BadAddress" [toJson a0]
    (M.VersionMismatch a0 a1) -> tagged "VersionMismatch" [toJson a0, toJson a1]
    (M.NoSuchJob a0) -> tagged "NoSuchJob" [toJson a0]
    M.NotServedYet -> tagged "NotServedYet" []
    (M.Unreadable a0) -> tagged "Unreadable" [toJson a0]
    (M.Malformed a0) -> tagged "Malformed" [toJson a0]

instance FromJson M.ProtocolError where
  fromJson v = untagged "ProtocolError" v >>= \case
    ("NotAtTheWheel", []) -> Right M.NotAtTheWheel
    ("BadAddress", [a0]) -> M.BadAddress <$> fromJson a0
    ("VersionMismatch", [a0, a1]) -> M.VersionMismatch <$> fromJson a0 <*> fromJson a1
    ("NoSuchJob", [a0]) -> M.NoSuchJob <$> fromJson a0
    ("NotServedYet", []) -> Right M.NotServedYet
    ("Unreadable", [a0]) -> M.Unreadable <$> fromJson a0
    ("Malformed", [a0]) -> M.Malformed <$> fromJson a0
    (t, as) -> noSuchCase "ProtocolError" t as

instance ToJson M.FromClient where
  toJson x = case x of
    (M.Line a0) -> tagged "Line" [toJson a0]
    (M.Focus a0) -> tagged "Focus" [toJson a0]
    M.ClaimKeys -> tagged "ClaimKeys" []
    M.ReleaseKeys -> tagged "ReleaseKeys" []
    (M.Terminate a0) -> tagged "Terminate" [toJson a0]
    M.Save -> tagged "Save" []

instance FromJson M.FromClient where
  fromJson v = untagged "FromClient" v >>= \case
    ("Line", [a0]) -> M.Line <$> fromJson a0
    ("Focus", [a0]) -> M.Focus <$> fromJson a0
    ("ClaimKeys", []) -> Right M.ClaimKeys
    ("ReleaseKeys", []) -> Right M.ReleaseKeys
    ("Terminate", [a0]) -> M.Terminate <$> fromJson a0
    ("Save", []) -> Right M.Save
    (t, as) -> noSuchCase "FromClient" t as

-- | A 'Json' value inside a message is itself.
--
-- 'Thena.Protocol.Codec.WrongShape' carries the value it could not read, and
-- sending it back is how a client is told what the server actually saw.
instance ToJson J.Json where
  toJson = id

instance FromJson J.Json where
  fromJson = Right

instance ToJson J.JsonError where
  toJson x = case x of
    (J.Unexpected a0 a1) -> tagged "Unexpected" [toJson a0, toJson a1]
    (J.UnexpectedEnd a0) -> tagged "UnexpectedEnd" [toJson a0]
    (J.NotAnInteger a0) -> tagged "NotAnInteger" [toJson a0]
    (J.BadEscape a0 a1) -> tagged "BadEscape" [toJson a0, toJson a1]
    (J.BadHex a0 a1) -> tagged "BadHex" [toJson a0, toJson a1]
    (J.DuplicateKey a0 a1) -> tagged "DuplicateKey" [toJson a0, toJson a1]
    (J.TrailingInput a0) -> tagged "TrailingInput" [toJson a0]

instance FromJson J.JsonError where
  fromJson v = untagged "JsonError" v >>= \case
    ("Unexpected", [a0, a1]) -> J.Unexpected <$> fromJson a0 <*> fromJson a1
    ("UnexpectedEnd", [a0]) -> J.UnexpectedEnd <$> fromJson a0
    ("NotAnInteger", [a0]) -> J.NotAnInteger <$> fromJson a0
    ("BadEscape", [a0, a1]) -> J.BadEscape <$> fromJson a0 <*> fromJson a1
    ("BadHex", [a0, a1]) -> J.BadHex <$> fromJson a0 <*> fromJson a1
    ("DuplicateKey", [a0, a1]) -> J.DuplicateKey <$> fromJson a0 <*> fromJson a1
    ("TrailingInput", [a0]) -> J.TrailingInput <$> fromJson a0
    (t, as) -> noSuchCase "JsonError" t as

instance ToJson K.CodecError where
  toJson x = case x of
    (K.WrongShape a0 a1) -> tagged "WrongShape" [toJson a0, toJson a1]
    (K.NoSuchCase a0 a1 a2) -> tagged "NoSuchCase" [toJson a0, toJson a1, toJson a2]

instance FromJson K.CodecError where
  fromJson v = untagged "CodecError" v >>= \case
    ("WrongShape", [a0, a1]) -> K.WrongShape <$> fromJson a0 <*> fromJson a1
    ("NoSuchCase", [a0, a1, a2]) -> K.NoSuchCase <$> fromJson a0 <*> fromJson a1 <*> fromJson a2
    (t, as) -> noSuchCase "CodecError" t as
