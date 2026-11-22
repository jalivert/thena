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
  , JevState (..)
  , loadJevConfig
  , rankCandidates
  , jevNucleus
  , jevNucleusMass
  , jevPickLimit
  , jevLog
  , jevLogPath
  ) where

import Control.Exception (SomeException, catch, try)
import Data.List (sortOn)
import Data.Aeson (FromJSON (..), Value, eitherDecode, encode, object, toJSON, withObject, (.:), (.=))
import qualified Data.Aeson.Key as Key
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
  , responseStatus
  , responseTimeoutMicro
  )
import Network.HTTP.Types.Status (statusCode)
import Network.HTTP.Client.TLS (tlsManagerSettings)
import System.Directory (XdgDirectory (XdgCache), createDirectoryIfMissing, getXdgDirectory)
import System.Environment (lookupEnv)
import System.FilePath ((</>))
import Numeric (showFFloat)
import Data.Time.Clock.POSIX (getPOSIXTime)

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
-- whatever called it. Each line opens with seconds since the epoch —
-- plenty to see how long a round trip actually took without pulling in
-- a formatting library for a debug log nobody reads as a calendar date.
jevLog :: String -> IO ()
jevLog msg =
  (do
    path <- jevLogPath
    now <- getPOSIXTime
    appendFile path (show now <> " " <> msg <> "\n")
  )
    `catch` (\(_ :: SomeException) -> pure ())

-- | 'jevModel' defaults to @jev-latest@ — see ".jalivert/CLOSEOUT.md" if
-- this ever needs pinning to a dated model instead.
data JevConfig = JevConfig
  { jevApiKey :: Text
  , jevModel  :: Text
  }

-- | **Everything Jev is told about the situation**, as the @state@ object's
-- fields in the order they go out. `~d4qvm`, HIS instruction of 2026-11-13:
-- /"Jev needs to be given enough information to make an informed choice."/
--
-- Before that this was one hard-coded field, the characters typed so far —
-- which on an empty line is the empty string, so a question asked before a
-- tactic and the same question asked after it were byte-for-byte identical and
-- could not come back with different answers. **The fields are not this
-- module's to choose.** It is a transport: what counts as the situation is a
-- question about the proof, and 'Tui.App.jevRequest' is the one place that
-- answers it.
--
-- **A newtype and not a bare list**, because 'rankCandidates' takes a list of
-- pairs for the candidates too and the two are not interchangeable — swapping
-- them would type-check and send a well-formed, meaningless request.
newtype JevState = JevState [(Text, Text)]

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

-- | One 'Choice' question, naming every candidate once as a criterion, with
-- 'JevState' as the whole of the state. Returns a probability per
-- candidate name, read out of the one answer's @probabilities@ — never
-- throws; a connection failure, a timeout, and a malformed response all
-- come back as 'Left' for the caller to treat identically.
--
-- **Deliberately one call, not one per candidate** (contrast the
-- re-ranking cookbook's per-item 'Noul', which fits a shortlist that
-- isn't mutually exclusive) — the dropdown's candidates are, you accept
-- exactly one, so a single 'Choice' over all of them in one request is
-- both the right shape and the one that bills once.
--
-- **At most 'choiceOptionLimit' candidates go out, and that is the API's
-- rule, not ours** — see that constant.
rankCandidates :: JevConfig -> JevState -> [(Text, Text)] -> IO (Either String (Map.Map Text Double))
rankCandidates cfg st@(JevState fields) offered = do
  jevLog
    ( "request: " <> show (length candidates) <> " candidates"
        <> (if dropped > 0 then " (" <> show dropped <> " over the 255 limit, not sent)" else "")
        -- **The state's field names and their sizes, not their contents.**
        -- Which fields went out is the thing that cannot be reconstructed
        -- afterwards, and it is what `~d4qvm` turned on; the contents are the
        -- development and the match list, which would make this log unreadable
        -- and are on screen anyway.
        <> ", state=["
        <> unwords [Text.unpack k <> ":" <> show (Text.length v) | (k, v) <- fields]
        <> "], model=" <> Text.unpack (jevModel cfg)
    )
  result <- either (Left . show) id <$> (try go :: IO (Either SomeException (Either String (Map.Map Text Double))))
  jevLog $ case result of
    Left e  -> "answer: FAILED — " <> e
    -- **The kept count and the top masses, because the cut is now a
    -- judgement and a log that omits it cannot be used to check it** —
    -- `~swxcf`. @255 scored, Jev's own 3@ is the whole finding in one line.
    Right m ->
      "answer: ok, " <> show (Map.size m) <> " scored, Jev's own "
        <> show (jevNucleus (Map.elems m))
        <> " at " <> showFFloat (Just 2) jevNucleusMass ""
        <> " (top: "
        <> unwords [showFFloat (Just 4) p "" | p <- take 6 (sortOn negate (Map.elems m))]
        <> ")"
  pure result
  where
    candidates = take choiceOptionLimit offered
    dropped = length offered - length candidates

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
              , requestBody = RequestBodyLBS (encode (requestPayload cfg st candidates))
              }
      resp <- httpLbs req manager
      -- **The status is read before the body is decoded.** It was not, and
      -- that is what made a plain 422 — too many options, below — arrive in
      -- the log as @key "answers" not found@: the error body went to the
      -- answer decoder, which complained about the wrong thing entirely.
      let code = statusCode (responseStatus resp)
      pure $ if code >= 200 && code < 300
        then parseRankAnswer (responseBody resp)
        else Left ("HTTP " <> show code <> ": " <> take 400 (show (responseBody resp)))

    -- 1.5s: generous next to the documented 70-300ms, strict enough that a
    -- hung connection can never outlive the dropdown it was scoring for.
    tlsSettings = tlsManagerSettings { managerResponseTimeout = responseTimeoutMicro 1500000 }

requestPayload :: JevConfig -> JevState -> [(Text, Text)] -> Value
requestPayload cfg (JevState fields) candidates =
  object
    [ "model" .= jevModel cfg
    , "state" .= object [Key.fromText k .= v | (k, v) <- fields]
    , "questions"
        .= object
          [ "rank"
              .= object
                [ "type" .= ("choice" :: Text)
                  -- **The instructions say what the state is, because a field
                  -- name is not a definition.** @applies_here@ is the one that
                  -- cannot be guessed from its name: it is not a shortlist Jev
                  -- must stay inside, and saying so is deliberate — HIS, on
                  -- `~d4qvm`: /"I am not saying that Jev's recommendations
                  -- always have to be just a subset of `:matches`, I am saying,
                  -- Jev should have that info to make the decision."/
                , "instructions"
                    .= ( "The user is writing one line at the prompt of a proof \
                         \assistant. `state` holds what they have typed so far, \
                         \the theorem under proof, the proof term as it stands, \
                         \the goals still open, and `applies_here` — the tactics \
                         \and rules that actually apply at the current focus, \
                         \nearest first. In `proof_term` and `open_goals`, a line \
                         \starting with `>` is where the cursor stands right now \
                         \— a candidate has to apply there to be something the \
                         \user could actually type next. Any other line is a goal \
                         \open elsewhere in the proof: context for what the proof \
                         \needs eventually, not what the next word should do. \
                         \`applies_here` is evidence and not a shortlist: a \
                         \candidate outside it may still be the right answer, but \
                         \it is still an answer for the `>` position, never for a \
                         \goal elsewhere. Which candidate is the user most likely \
                         \about to write next?" ::
                           Text
                       )
                , "criteria" .= toJSON (Map.fromList candidates)
                ]
          ]
    ]

-- | **How many of the candidates Jev scored did Jev actually suggest** —
-- `~swxcf`, and it is the difference between ordering his list and
-- excluding from it.
--
-- **A 'Choice' answers a probability for EVERY option it was given, and
-- that is measured and not assumed.** His own @jev.log@, 1767 answers:
-- @request: 191 candidates@ comes back @answer: ok, 191 scored@, and 255
-- comes back 255, every single time. So /"Jev scored it"/ is true of the
-- whole list, and a suggestion pane that shows every row Jev scored is
-- showing the engine's list in Jev's order — which is the thing he
-- rejected, said five times and last of all on 2026-11-19: /"only when the
-- Jev is disabled in the settings, do I ever want to see any suggestion
-- that didn't come from Jev"/.
--
-- **So a pick is a candidate Jev put real mass on, and the cut is the
-- nucleus**: the shortest run of its ranking whose probability adds up to
-- 'jevNucleusMass' of the answer. In words he can rule on in one breath —
-- /the cells are the smallest set of candidates Jev is 90% sure the answer
-- is among/. A confident answer fills one cell, which is his own stated
-- ideal for this pane; a hedged one fills several; an answer spread thin
-- across 255 rows fills them all and is then held by 'jevPickLimit'.
--
-- **Masses are sorted here rather than required sorted.** The caller does
-- sort the rows, but a count that silently depends on its argument's order
-- is a precondition nothing checks, and this way the function is total.
--
-- **Nothing at all when the mass is nothing at all.** An answer whose
-- probabilities are all zero has named no candidate, so no cell is Jev's —
-- the honest screen is the empty one, not the top of an arbitrary order.
jevNucleus :: [Double] -> Int
jevNucleus masses
  | total <= 0 = 0
  | otherwise = min jevPickLimit (count 0 0 (sortOn negate masses))
  where
    total = sum masses
    target = jevNucleusMass * total
    count :: Int -> Double -> [Double] -> Int
    count k acc (m : ms) | acc < target = count (k + 1) (acc + m) ms
    count k _ _ = k

-- | How much of Jev's answer the cells have to cover — see 'jevNucleus'.
-- **His to retune in one word**; it is the one number in the rule.
jevNucleusMass :: Double
jevNucleusMass = 0.9

-- | **The most cells Jev's answer may claim, and the number is HIS** —
-- 2026-11-19: /"ALL of the top 12 suggestions are to be the ones that Jev
-- suggested"/, and /"the suggestion pane's 12 suggestions (or 11 because I
-- don't know if we can capture F11)"/.
--
-- It bites only on an answer so evenly spread that 'jevNucleusMass' keeps
-- most of the list; the grid draws fewer than this anyway (ten F-keys,
-- nine cells at his geometry). It is here so that /how many did Jev
-- suggest/ has a bound of his choosing rather than a bound that falls out
-- of whatever the terminal is wide enough to draw.
jevPickLimit :: Int
jevPickLimit = 12

-- | **A 'Choice' question takes at most 255 options, and the dropdown can
-- offer more.** Measured against the live API, 2026-11-11: 287 candidates
-- — the launch dropdown's own count — come back
-- @422 Dictionary should have at most 255 items after validation, not 287@,
-- so before this cap existed EVERY ranking request failed and the feature
-- was silently off for anyone with a key.
--
-- **The 255 kept are the first 255 the engine offered**, which is already a
-- relevance order (tokens before productions). The alternative — splitting
-- into several questions — is wrong rather than merely bigger: a 'Choice'
-- normalises its probabilities within its own option set, so scores from two
-- questions cannot be compared, and floating a top three across them would
-- be arithmetic on unrelated distributions.
choiceOptionLimit :: Int
choiceOptionLimit = 255

newtype RankAnswer = RankAnswer (Map.Map Text Double)

instance FromJSON RankAnswer where
  parseJSON = withObject "SystemOneResponse" $ \o -> do
    answers <- o .: "answers"
    rank <- answers .: "rank"
    probs <- rank .: "probabilities"
    pure (RankAnswer probs)

parseRankAnswer :: BL.ByteString -> Either String (Map.Map Text Double)
parseRankAnswer raw = (\(RankAnswer m) -> m) <$> eitherDecode raw
