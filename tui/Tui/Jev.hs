{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
  , jevLog
  , jevLogPath
  ) where

import Control.Exception (SomeException, catch, try)
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
import System.Directory (XdgDirectory (XdgCache), createDirectoryIfMissing, getXdgDirectory)
import System.Environment (lookupEnv)
import System.FilePath ((</>))

-- | Where 'jevLog' writes — exported so a cold session (or him, by hand)
-- can find it without re-deriving the path. Everything in this module
-- fails silently to the dropdown by design (see the module haddock), so
-- this file is the only way to tell "no key" from "key, but the call
-- never went out" from "went out, came back wrong" after the fact.
jevLogPath :: IO FilePath
jevLogPath = do
  dir <- getXdgDirectory XdgCache "thena"
  createDirectoryIfMissing True dir
  pure (dir </> "jev.log")

-- | Best-effort: a failure writing the log is swallowed exactly like a
-- network failure is, never surfaced, never retried, never blocking
-- whatever called it.
jevLog :: String -> IO ()
jevLog msg =
  (do
    path <- jevLogPath
    appendFile path (msg <> "\n")
  )
    `catch` (\(_ :: SomeException) -> pure ())

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
  let cfg = mkConfig modelOverride <$> key
  jevLog $ case cfg of
    Nothing -> "config: no TYPESAFE_API_KEY in this process's environment — ranking is off"
    Just c  -> "config: key found (" <> show (Text.length (jevApiKey c)) <> " chars), model=" <> Text.unpack (jevModel c)
  pure cfg
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
rankCandidates cfg typedSoFar candidates = do
  jevLog ("request: " <> show (length candidates) <> " candidates, model=" <> Text.unpack (jevModel cfg))
  result <- either (Left . show) id <$> (try go :: IO (Either SomeException (Either String (Map.Map Text Double))))
  jevLog $ case result of
    Left e  -> "answer: FAILED — " <> e
    Right m -> "answer: ok, " <> show (Map.size m) <> " scored"
  pure result
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
