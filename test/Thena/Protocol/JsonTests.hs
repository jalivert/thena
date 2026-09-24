-- | The hand-rolled JSON layer (phase 112).
--
-- **A round trip through a printer and its own parser is the weak test**, and it
-- is only half of what is here. The other half is what crosses it:
--
-- * **exact output**, asserted against strings written by hand, so the encoding
--   is pinned rather than merely self-consistent;
-- * **input the encoder never produces** — whitespace, @\\/@, @\\u0041@, minus
--   zero — so the parser is exercised by something that did not come out of the
--   printer. A client is a different program and will send these.
--
-- The generator deliberately includes what this project actually contains:
-- identifiers are not ASCII here (@ℓ@, @≐@, @⌜@), and §2.6 lets one hold almost
-- anything, so a printer that escaped too eagerly or too little would be caught
-- by the round trip only if the generator produces those characters.
module Thena.Protocol.JsonTests (tests) where

import Data.List (nub)

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import Test.Tasty.QuickCheck (Gen, elements, forAll, oneof, sized, testProperty, vectorOf, (===))

import Thena.Protocol.Json (Json (..), JsonError (..), decode, encode)

tests :: TestTree
tests =
  testGroup
    "Thena.Protocol.Json"
    [ testGroup "encode, written out" encodeTests
    , testGroup "decode of text we never emit" decodeTests
    , testGroup "refusals" refusalTests
    , testGroup "round trip" [roundTrip]
    ]

-- | Values shaped like the ones this protocol carries.
genJson :: Gen Json
genJson = sized go
  where
    go n
      | n <= 0 = leaf
      | otherwise =
          oneof
            [ leaf
            , JArray <$> shortListOf (go (n `div` 3))
            , JObject <$> genMembers (n `div` 3)
            ]
    -- **Bounded by length as well as by depth.** Reducing the argument to 'go'
    -- bounds how deep a value nests, but 'listOf' draws its length from
    -- QuickCheck's ambient size, which that does not touch — so a size-100 run
    -- built lists of a hundred values each holding a hundred more, and the
    -- suite hung rather than failing. Depth and breadth both have to shrink.
    shortListOf g = do
      k <- elements [0, 1, 2, 3]
      vectorOf k g
    -- **Distinct keys, because a duplicate is not a well-formed value here.**
    -- 'encode' will print one and 'decode' refuses it, which is the
    -- representable-but-not-well-formed line §3.4 draws on purpose — the round
    -- trip is a statement about valid values and the refusal is tested
    -- separately. The generator first found this by producing @body@ twice.
    genMembers n = do
      k <- elements [0, 1, 2, 3]
      ks <- nub <$> vectorOf k genKey
      traverse (\key -> (,) key <$> go n) ks
    leaf =
      oneof
        [ pure JNull
        , JBool <$> elements [True, False]
        , JInt <$> elements [0, 1, -1, 42, -7, 1000, toInteger (minBound :: Int), toInteger (maxBound :: Int), 2 ^ (200 :: Int)]
        , JString <$> genText
        ]
    -- Keys are the field names we write, so they are tame.
    genKey = elements ["tag", "name", "args", "body", "ℓ", "type"]
    -- Values are not: a Thena identifier may hold almost anything (§2.6).
    genText = do
      k <- elements [0, 1, 2, 3, 4, 5, 8]
      vectorOf k (elements "abzAZ09 \"\\\n\r\t\b\f/ℓ≐⌜⌝λΠ∀→{}[]:,€𝕀")

roundTrip :: TestTree
roundTrip =
  testProperty "decode . encode is the identity" $
    forAll genJson $ \v -> decode (encode v) === Right v

encodeTests :: [TestTree]
encodeTests =
  [ testCase "null, booleans, integers" $
      encode (JArray [JNull, JBool True, JBool False, JInt 0, JInt (-7)])
        @?= "[null,true,false,0,-7]"
  , testCase "an object keeps the order it was given" $
      encode (JObject [("b", JInt 1), ("a", JInt 2)]) @?= "{\"b\":1,\"a\":2}"
  , testCase "empty array and object" $
      encode (JArray []) <> encode (JObject []) @?= "[]{}"
  , testCase "only what the grammar requires is escaped" $
      encode (JString "a\"b\\c\nd\te") @?= "\"a\\\"b\\\\c\\nd\\te\""
  , testCase "a Thena identifier goes through as itself" $
      encode (JString "ℓ≐⌜x⌝") @?= "\"ℓ≐⌜x⌝\""
  , testCase "a control character becomes \\u with four digits" $
      encode (JString "\SOH") @?= "\"\\u0001\""
  , testCase "a forward slash is not escaped" $
      encode (JString "a/b") @?= "\"a/b\""
  ]

decodeTests :: [TestTree]
decodeTests =
  [ testCase "whitespace everywhere" $
      decode " { \"a\" : [ 1 , 2 ] , \"b\" : null } "
        @?= Right (JObject [("a", JArray [JInt 1, JInt 2]), ("b", JNull)])
  , testCase "an escaped solidus, which we never emit" $
      decode "\"a\\/b\"" @?= Right (JString "a/b")
  , testCase "a \\u escape, which we emit only for control characters" $
      decode "\"\\u0041\\u2113\"" @?= Right (JString "A\8467")
  , testCase "negative zero" $
      decode "-0" @?= Right (JInt 0)
  , testCase "a nested empty structure" $
      decode "[[],{},[{}]]" @?= Right (JArray [JArray [], JObject [], JArray [JObject []]])
  ]

refusalTests :: [TestTree]
refusalTests =
  [ testCase "a fraction is refused rather than rounded" $
      decode "1.5" @?= Left (NotAnInteger 1)
  , testCase "an exponent is refused too" $
      decode "1e3" @?= Left (NotAnInteger 1)
  , testCase "a duplicate key is refused" $
      decode "{\"a\":1,\"a\":2}" @?= Left (DuplicateKey 7 "a")
  , -- The asymmetry, stated rather than left to be discovered: 'encode' is
    -- total and will print a value 'decode' will not take back. That is the
    -- §3.4 line, and it is why 'genJson' generates distinct keys.
    testCase "and encode will happily print one" $
      encode (JObject [("a", JInt 1), ("a", JInt 2)]) @?= "{\"a\":1,\"a\":2}"
  , testCase "text after a complete value is refused" $
      decode "1 2" @?= Left (TrailingInput 2)
  , testCase "a value that stops in the middle" $
      decode "[1," @?= Left (UnexpectedEnd 3)
  , testCase "an unknown escape" $
      decode "\"\\q\"" @?= Left (BadEscape 2 'q')
  , testCase "a short \\u" $
      decode "\"\\u12\"" @?= Left (BadHex 3 "12\"")
  ]
