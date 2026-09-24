-- | The protocol's messages, through JSON and back (MS7 phase 114).
--
-- **Exhaustive by construction, not by sampling.** Every constructor of every
-- type encoded here appears in the list below, so a constructor added later
-- fails this test by being absent rather than by being unlucky — which a
-- generator would not give, and which matters more here than variety does:
-- these types are small and their shapes are fixed.
module Thena.Protocol.WireTests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Development.Cursor (Part (..))
import Thena.Errors (MoveError (..))
import Thena.Protocol.Address (Address (..), AddressError (..), Move (..))
import Thena.Protocol.Codec (FromJson (..), ToJson (..))
import Thena.Protocol.Json (Json, decode, encode)
import Thena.Protocol.Codec (CodecError (..))
import Thena.Protocol.Json (JsonError (..))
import Thena.Protocol.Message (FromClient (..), JobId (..), ProtocolError (..))
import Thena.Protocol.Wire ()

tests :: TestTree
tests =
  testGroup
    "Thena.Protocol.Wire"
    [ testCase "every client message round trips" clients
    , testCase "every protocol error round trips" errors
    , testCase "and the text is what a client would send" written
    ]

-- | Encode, print, read, decode — the whole path, not only the codec.
through :: (ToJson a, FromJson a, Eq a, Show a) => a -> IO ()
through x = case decode (encode (toJson x :: Json)) of
  Left e -> assertFailure (show x <> ": the printed JSON did not read back: " <> show e)
  Right j -> case fromJson j of
    Left e -> assertFailure (show x <> ": decoding failed: " <> show e)
    Right y | y == x -> pure ()
            | otherwise -> assertFailure (show x <> ": came back as " <> show y)

everyMove :: [Move]
everyMove =
  [GoAlong, GoInto, GoCrossType, GoCrossValue]
    <> [ GoDown p
       | p <-
           [ Fun, Arg, Dom, Cod, Val, Type, Body, Motive, Target
           , Param 1, Method 2, Index 3, CanonArg 4
           ]
       ]

clients :: IO ()
clients =
  mapM_
    through
    ( [ Line "", Line "attack", Line "a line with \"quotes\" and ℓ and a\ttab"
      , ClaimKeys, ReleaseKeys, Save, Terminate (JobId 0), Terminate (JobId 7)
      , Focus (Address [])
      , Focus (Address everyMove)
      ]
        <> [Focus (Address [m]) | m <- everyMove]
    )

errors :: IO ()
errors =
  mapM_
    through
    ( [ NotAtTheWheel, NotServedYet, VersionMismatch 0 1, NoSuchJob (JobId 3)
      , Unreadable (Unexpected 1 'o'), Unreadable (UnexpectedEnd 4)
      , Unreadable (BadHex 3 "12"), Unreadable (DuplicateKey 7 "a")
      , Malformed (NoSuchCase "FromClient" "Nope" 0)
      , Malformed (WrongShape "Int" (toJson "no"))
      ]
        <> [ BadAddress (NoSuchPosition k e)
           | k <- [0, 5]
           , e <-
               [ AtRoot, NotOnTheSpine, NotInCore, NotAGuess, NotADefinition
               , StillReferenced, NoCrossingIntoAConstraint, NoSuchHole, NoSuchPart
               ]
           ]
    )

-- | One message written out, so the encoding is pinned and not merely
-- self-consistent. A client is a different program and this is the contract.
written :: IO ()
written = do
  encode (toJson (Line "attack")) @?= "[\"Line\",\"attack\"]"
  encode (toJson ClaimKeys) @?= "[\"ClaimKeys\"]"
  encode (toJson (Focus (Address [GoAlong, GoDown (Param 2)])))
    @?= "[\"Focus\",[\"Address\",[[\"GoAlong\"],[\"GoDown\",[\"Param\",2]]]]]"
