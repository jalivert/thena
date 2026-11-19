{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | **The model behind the suggestion pane's hint region** — `~w2tk2` slice
-- 6, and his ruling of 2026-11-19 on where it runs: **in-process, called
-- the way 'Tui.Jev' is called**, not out-of-process behind a protocol. His
-- words on the alternative: it is a different product — letting an agent
-- drive Thena, open modules and write rule files — and it keeps its own
-- item rather than being decided by this slice.
--
-- **So this module only ever reads the session and answers text.** It
-- cannot write a line into a proof, cannot touch a file in the project, and
-- holds no path into 'Thena.Driver' at all: the caller assembles the state,
-- this sends it, and what comes back is a string the strip draws. That is
-- what keeps slice 6 small and it is the fork decision made concrete.
--
-- **NOTHING HERE FIRES ON ITS OWN — HIS RULING, 2026-11-19.** He first
-- asked for an automatic ask with a switch to disable it, then withdrew it
-- the same message on landing the explicit design: /"We have no autohint …
-- Everything is explicit … The user has to hit enter on the \"give me a
-- hand\"."/ There is therefore **no timer, no debounce and no generation
-- counter** in this module — the contrast with 'Tui.Jev', which has all
-- three because it fires on a keystroke, is the whole point.
--
-- **The provider is OpenRouter and the key is his own**, read from
-- @OPENROUTER_API_KEY@ exactly as Jev reads @TYPESAFE_API_KEY@. A missing
-- key is not an error: the hint region stays empty and the log says why.
module Tui.Hint
  ( HintConfig (..)
  , loadHintConfig
  , HintModel (..)
  , fetchModels
  , matchingModels
  , modelRow
  , defaultModelId
  , askHint
  , hintPlaceholder
  , hintPromptPath
  , loadHintPrompt
  , defaultHintPrompt
  , hintLog
  , hintLogPath
  ) where

import Control.Exception (SomeException, catch, try)
import Data.Aeson (FromJSON (..), Value, eitherDecode, encode, object, withObject, (.:), (.:?), (.=))
import qualified Data.ByteString.Lazy as BL
import Data.List (isInfixOf, sortOn)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
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
import Network.HTTP.Client.TLS (tlsManagerSettings)
import Network.HTTP.Types.Status (statusCode)
import System.Directory
  ( XdgDirectory (XdgCache, XdgConfig)
  , createDirectoryIfMissing
  , doesFileExist
  , getXdgDirectory
  )
import System.Environment (lookupEnv)
import System.FilePath ((</>))
import Data.Time.Clock.POSIX (getPOSIXTime)

-- | Where 'hintLog' writes. **A file of its own and not Jev's**, because
-- the two answer different questions — how often a paid model was asked,
-- against how a free ranking was ordered — and reading one out of the other
-- would mean filtering every line.
hintLogPath :: IO FilePath
hintLogPath = do
  dir <- getXdgDirectory XdgCache "thena"
  createDirectoryIfMissing True dir
  pure (dir </> "hint.log")

hintLog :: String -> IO ()
hintLog msg =
  (do
    path <- hintLogPath
    now <- getPOSIXTime
    appendFile path (show now <> " " <> msg <> "\n")
  )
    `catch` (\(_ :: SomeException) -> pure ())

-- | The key and the model to send it to. **The model is carried in rather
-- than read here**, because it is a preference in his dotfile
-- ('Tui.Config.cfgModel') and this module has no business reading that file.
data HintConfig = HintConfig
  { hintApiKey :: Text
  , hintModel  :: Text
  }

-- | 'Nothing' when @OPENROUTER_API_KEY@ isn't set — not an error, the same
-- reading 'Tui.Jev.loadJevConfig' gives a missing key.
loadHintConfig :: Text -> IO (Maybe HintConfig)
loadHintConfig model = do
  key <- lookupEnv "OPENROUTER_API_KEY"
  case key of
    Nothing -> do
      hintLog "config: no OPENROUTER_API_KEY in this process's environment — the hint region stays empty"
      pure Nothing
    Just k -> do
      hintLog ("config: key found (" <> show (length k) <> " chars), model=" <> Text.unpack model)
      pure (Just (HintConfig (Text.pack k) model))

-- | **The model he has chosen, until he chooses one** — the default that
-- ships. Cheap and fast, because a hint is one or two sentences and he will
-- be pressing this while proving rather than reading an essay; `:models`
-- changes it in one keystroke and the choice persists.
defaultModelId :: Text
defaultModelId = "anthropic/claude-sonnet-5.5"

-- | One row of OpenRouter's catalogue. **Three fields and not twenty**: the
-- listing carries benchmarks, a description, provider routing and a dozen
-- pricing variants, and none of that is what picking a model from a list
-- needs.
data HintModel = HintModel
  { mdId      :: Text
  , mdName    :: Text
  , mdContext :: Int
  , mdPrompt  :: Maybe Text  -- ^ dollars per prompt token, as the API writes it.
  }

newtype ModelList = ModelList [HintModel]

instance FromJSON ModelList where
  parseJSON = withObject "OpenRouterModels" $ \o -> do
    rows <- o .: "data"
    ModelList <$> traverse one rows
    where
      one = withObject "model" $ \m -> do
        i <- m .: "id"
        n <- m .:? "name"
        c <- m .:? "context_length"
        pricing <- m .:? "pricing"
        p <- case pricing of
          Nothing -> pure Nothing
          Just pr -> withObject "pricing" (.:? "prompt") pr
        pure (HintModel i (fromMaybe i n) (fromMaybe 0 c) p)

-- | **The catalogue, and it needs no key** — measured 2026-11-19: a bare
-- @GET@ answers @200@ with 479 models and about 900 KB. So `:models` works
-- before he has set a key at all, which is the right order: choose the
-- model, then pay for it.
fetchModels :: IO (Either String [HintModel])
fetchModels = do
  result <- either (Left . show) id <$> (try go :: IO (Either SomeException (Either String [HintModel])))
  hintLog $ case result of
    Left e -> "models: FAILED — " <> e
    Right ms -> "models: ok, " <> show (length ms) <> " offered"
  pure result
  where
    go = do
      manager <- newManager settings
      req <- parseRequest "https://openrouter.ai/api/v1/models"
      resp <- httpLbs req manager
      let code = statusCode (responseStatus resp)
      pure $
        if code >= 200 && code < 300
          then (\(ModelList ms) -> sortOn mdId ms) <$> eitherDecode (responseBody resp)
          else Left ("HTTP " <> show code <> ": " <> take 300 (show (responseBody resp)))
    -- 900 KB over a cold connection: generous, and it blocks nothing — the
    -- fetch runs off the main thread like every other call here.
    settings = tlsManagerSettings { managerResponseTimeout = responseTimeoutMicro 30000000 }

-- | **`:models ‹filter›` narrows by substring, case ignored** — 479 rows is
-- a list you scroll past rather than read, and the id is what a filter
-- naturally matches (@claude@, @gpt@, @:free@). An empty filter is every
-- row, which is what bare `:models` passes.
matchingModels :: Text -> [HintModel] -> [HintModel]
matchingModels needle ms
  | Text.null needle = ms
  | otherwise = [m | m <- ms, lower needle `isInfixOf` lower (mdId m) || lower needle `isInfixOf` lower (mdName m)]
  where
    lower = Text.unpack . Text.toLower

-- | A model as one picker row: **the id first, because the id is what
-- `:model` takes and what the dotfile stores**, then its context window and
-- what a prompt token costs. The name is left out: it is the id again in
-- prose (@anthropic/claude-haiku-5.5@ against @Anthropic: Claude Haiku
-- 5.5@) and it would push the two facts that differ off a narrow box.
modelRow :: HintModel -> (String, String)
modelRow m = (Text.unpack (mdId m), ctx <> price)
  where
    ctx
      | mdContext m <= 0 = ""
      | otherwise = show (mdContext m `div` 1000) <> "k"
    price = maybe "" (\p -> "   $" <> Text.unpack p <> "/tok") (mdPrompt m)

-- | **The dim sentence that sits in the reply row until he types over it** —
-- HIS, 2026-11-19: /"it by default has a dim line with text like \"give me
-- a hand\" and when you click it … the request is made"/.
--
-- **It is sent as part of the prompt and is not merely a placeholder** —
-- also his: /"sending the dimmed sentence makes sense to me too"/. So what
-- the model is asked is never something he cannot see on his own screen.
hintPlaceholder :: Text
hintPlaceholder = "give me a hand"

-- | @~\/.config\/thena\/hint-prompt.txt@ — **his, editable, and exactly
-- what is sent.** HIS instruction, 2026-11-19: /"make the prompt that gives
-- it a context editable … so that I can see what is it asked every single
-- time."/
--
-- **A file of its own rather than a line in the dotfile**, because the
-- dotfile is @key=value@ and this is a paragraph: a multi-line instruction
-- does not survive one line of that, and json would hand it back to him as
-- one string full of escapes, which defeats being able to read it. Plain
-- text in a file he can open is the form that keeps the promise.
hintPromptPath :: IO FilePath
hintPromptPath = do
  dir <- getXdgDirectory XdgConfig "thena"
  createDirectoryIfMissing True dir
  pure (dir </> "hint-prompt.txt")

-- | **Read on every request and never cached**, so editing the file changes
-- the next ask with no restart — that is the whole point of its being a
-- file. A missing file is written with 'defaultHintPrompt' the first time,
-- so there is always something on disc to open and edit.
loadHintPrompt :: IO Text
loadHintPrompt = do
  path <- hintPromptPath
  there <- doesFileExist path
  if there
    then TIO.readFile path `catch` (\(_ :: SomeException) -> pure defaultHintPrompt)
    else do
      TIO.writeFile path defaultHintPrompt `catch` (\(_ :: SomeException) -> pure ())
      pure defaultHintPrompt

-- | The instruction that ships. **It names each state field**, because a
-- field name is not a definition — the same reason 'Tui.Jev.requestPayload'
-- spells @applies_here@ out.
defaultHintPrompt :: Text
defaultHintPrompt =
  Text.unlines
    [ "You are helping someone prove a theorem in Thena, a proof assistant they are"
    , "driving from a terminal. They have asked you for a hand with the proof in front"
    , "of them."
    , ""
    , "The state you are given:"
    , ""
    , "  goals          the goals still open, the first one being where they stand"
    , "  proof_term     the proof term as it stands, holes included"
    , "  applies_here   the tactics and rules that apply at the current focus, nearest"
    , "                 first. Evidence, not a shortlist: something outside it may still"
    , "                 be the right move"
    , "  in_scope       the names available to them"
    , "  executed       what they have already run in this session, oldest first"
    , "  typed_so_far   the line they are part way through typing, if any"
    , ""
    , "Answer in two or three sentences of plain prose. Say what you would do next and"
    , "why it moves the proof forward. Name the command if you are confident about it."
    , "If the state does not tell you enough to be useful, say which part is missing"
    , "rather than guessing. No preamble, no restating the goal back to them, no lists."
    ]

-- | **One call, and it is the user's keystroke that caused it.** The state
-- fields and his own sentence go up together; what comes back is prose for
-- the hint region.
--
-- **The status is read before the body is decoded**, which is `~63n23`'s
-- lesson from the Jev client: a plain error body handed to the answer
-- decoder is reported as a missing field and sends the reader after the
-- wrong thing entirely.
askHint :: HintConfig -> Text -> [(Text, Text)] -> Text -> IO (Either String Text)
askHint cfg prompt fields asked = do
  hintLog
    ( "ask: model=" <> Text.unpack (hintModel cfg)
        <> ", asked=" <> show (Text.unpack asked)
        -- **The field names and their sizes, not their contents** — the
        -- same rule 'Tui.Jev.rankCandidates' logs by: which fields went out
        -- is the thing that cannot be reconstructed afterwards, and the
        -- contents are on his screen anyway.
        <> ", state=["
        <> unwords [Text.unpack k <> ":" <> show (Text.length v) | (k, v) <- fields]
        <> "]"
    )
  result <- either (Left . show) id <$> (try go :: IO (Either SomeException (Either String Text)))
  hintLog $ case result of
    Left e -> "answer: FAILED — " <> e
    Right t -> "answer: ok, " <> show (Text.length t) <> " chars"
  pure result
  where
    go = do
      manager <- newManager settings
      req0 <- parseRequest "https://openrouter.ai/api/v1/chat/completions"
      let req =
            req0
              { method = "POST"
              , requestHeaders =
                  [ ("Authorization", "Bearer " <> TE.encodeUtf8 (hintApiKey cfg))
                  , ("Content-Type", "application/json")
                  -- **Names the application and nothing about him.**
                  -- OpenRouter reads these for its own attribution; a
                  -- machine name or a path here would be telling a third
                  -- party something it did not ask for.
                  , ("X-Title", "thena")
                  ]
              , requestBody = RequestBodyLBS (encode (payload cfg prompt fields asked))
              }
      resp <- httpLbs req manager
      let code = statusCode (responseStatus resp)
      pure $
        if code >= 200 && code < 300
          then parseHintAnswer (responseBody resp)
          else Left ("HTTP " <> show code <> ": " <> take 400 (show (responseBody resp)))
    -- 60s. **Not Jev's 1.5s**: that timeout exists so a hung connection
    -- cannot outlive the dropdown it was scoring for, and a hint has no
    -- such deadline — he pressed Enter and is waiting for it.
    settings = tlsManagerSettings { managerResponseTimeout = responseTimeoutMicro 60000000 }

payload :: HintConfig -> Text -> [(Text, Text)] -> Text -> Value
payload cfg prompt fields asked =
  object
    [ "model" .= hintModel cfg
    , "messages"
        .= [ object ["role" .= ("system" :: Text), "content" .= prompt]
           , object ["role" .= ("user" :: Text), "content" .= stated]
           ]
    ]
  where
    stated =
      Text.intercalate "\n\n" ([k <> ":\n" <> v | (k, v) <- fields, not (Text.null (Text.strip v))] <> [asked])

newtype HintAnswer = HintAnswer Text

instance FromJSON HintAnswer where
  parseJSON = withObject "OpenRouterChat" $ \o -> do
    choices <- o .: "choices"
    case choices of
      [] -> fail "no choices in the answer"
      (c : _) -> do
        msg <- withObject "choice" (.: "message") c
        HintAnswer <$> withObject "message" (.: "content") msg

parseHintAnswer :: BL.ByteString -> Either String Text
parseHintAnswer raw = (\(HintAnswer t) -> Text.strip t) <$> eitherDecode raw
