{-# LANGUAGE OverloadedStrings #-}

-- | A thin client for TypeSafe's Jev, used to rank the completion dropdown
-- (`~cs736` in ".jalivert/discussion/ai-integration.md"; his ruling in
-- "editor-protocol.md" 5.6 — "client-side ranking of the match list, no
-- protocol change"). Jev never adds, removes, or inserts a candidate; it
-- only answers which of the candidates `Tui.App` already built is most
-- likely, and `Tui.App` is the only thing that acts on that answer. A
-- missing key, a failed call, or a timeout all mean exactly the same thing
-- to the caller: no scores, so the dropdown keeps the order it already
-- had.
module Tui.Jev
  ( JevConfig (..)
  , loadJevConfig
  , rankCandidates
  ) where

import Control.Exception (SomeException, try)
import Data.Aeson (FromJSON (..), Value, eitherDecode, encode, object, toJSON, withObject, (.:), (.=))
import qualified Data.ByteString.Lazy as BL
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TE
import Network.HTTP.Client
  ( ManagerSettings (managerResponseTimeout)
  , RequestBody (RequestBodyLBS)
  , httpLbs
  , method
  , newManager
  , parseRequest
  , requestBody
  , requestHeaders
  , responseBody
  , responseTimeoutMicro
  )
import Network.HTTP.Client.TLS (tlsManagerSettings)
import System.Environment (lookupEnv)

-- | 'jevModel' defaults to @jev-latest@ — see ".jalivert/CLOSEOUT.md" if
-- this ever needs pinning to a dated model instead.
data JevConfig = JevConfig
  { jevApiKey :: Text
  , jevModel  :: Text
  }

-- | 'Nothing' when @TYPESAFE_API_KEY@ isn't set. That is not an error —
-- the feature is simply off, the same as it is for anyone without a key.
loadJevConfig :: IO (Maybe JevConfig)
loadJevConfig = do
  key <- lookupEnv "TYPESAFE_API_KEY"
  modelOverride <- lookupEnv "TYPESAFE_MODEL"
  pure $ mkConfig modelOverride <$> key
  where
    mkConfig modelOverride k =
      JevConfig (Text.pack k) (maybe "jev-latest" Text.pack modelOverride)

-- | One 'Choice' question, naming every candidate once as a criterion, the
-- line typed so far as the whole of the state. Returns a probability per
-- candidate name, read out of the one answer's @probabilities@ — never
-- throws; a connection failure, a timeout, and a malformed response all
-- come back as 'Left' for the caller to treat identically.
--
-- **Deliberately one call, not one per candidate** (contrast the
-- re-ranking cookbook's per-item 'Noul', which fits a shortlist that
-- isn't mutually exclusive) — the dropdown's candidates are, you accept
-- exactly one, so a single 'Choice' over all of them in one request is
-- both the right shape and the one that bills once.
rankCandidates :: JevConfig -> Text -> [(Text, Text)] -> IO (Either String (Map.Map Text Double))
rankCandidates cfg typedSoFar candidates =
  either (Left . show) id <$> (try go :: IO (Either SomeException (Either String (Map.Map Text Double))))
  where
    go :: IO (Either String (Map.Map Text Double))
    go = do
      manager <- newManager tlsSettings
      req0 <- parseRequest "https://api.typesafe.ai/v1/systemone"
      let req =
            req0
              { method = "POST"
              , requestHeaders =
                  [ ("Authorization", "Bearer " <> TE.encodeUtf8 (jevApiKey cfg))
                  , ("Content-Type", "application/json")
                  ]
              , requestBody = RequestBodyLBS (encode (requestPayload cfg typedSoFar candidates))
              }
      resp <- httpLbs req manager
      pure (parseRankAnswer (responseBody resp))

    -- 1.5s: generous next to the documented 70-300ms, strict enough that a
    -- hung connection can never outlive the dropdown it was scoring for.
    tlsSettings = tlsManagerSettings { managerResponseTimeout = responseTimeoutMicro 1500000 }

requestPayload :: JevConfig -> Text -> [(Text, Text)] -> Value
requestPayload cfg typedSoFar candidates =
  object
    [ "model" .= jevModel cfg
    , "state" .= object ["typed_so_far" .= typedSoFar]
    , "questions"
        .= object
          [ "rank"
              .= object
                [ "type" .= ("choice" :: Text)
                , "instructions"
                    .= ( "Given `typed_so_far`, which candidate is the user most \
                         \likely about to write next?" ::
                           Text
                       )
                , "criteria" .= toJSON (Map.fromList candidates)
                ]
          ]
    ]

newtype RankAnswer = RankAnswer (Map.Map Text Double)

instance FromJSON RankAnswer where
  parseJSON = withObject "SystemOneResponse" $ \o -> do
    answers <- o .: "answers"
    rank <- answers .: "rank"
    probs <- rank .: "probabilities"
    pure (RankAnswer probs)

parseRankAnswer :: BL.ByteString -> Either String (Map.Map Text Double)
parseRankAnswer raw = (\(RankAnswer m) -> m) <$> eitherDecode raw
