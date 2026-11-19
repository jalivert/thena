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
  , resetHintPrompt
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

-- | **Rewrite the file from 'defaultHintPrompt' and answer where it is** —
-- `:hint-prompt reset`.
--
-- **It exists because the file is his and 'loadHintPrompt' will not touch
-- one that is already there.** That is the right rule — an edit of his must
-- not be overwritten by an upgrade — and it means a better default shipped
-- later would never reach him. So there is one command that takes it, and
-- taking it is his keystroke rather than ours.
resetHintPrompt :: IO FilePath
resetHintPrompt = do
  path <- hintPromptPath
  TIO.writeFile path defaultHintPrompt
  pure path

-- | The instruction that ships. **Three parts, and each is here for
-- something he said on 2026-11-19.**
--
-- **The format, and it is the strictest part** — /"It is very chatty. We
-- need to make the prompt somehow force it to really, really limit its
-- wordiness … I don't need it to narrate what I am doing. I didn't ask for
-- this."/ His own four-line answer on the identity theorem is quoted in
-- here as the worked negative example, because a rule about length lands
-- less firmly than the reply that broke it.
--
-- **The mechanics** — /"It doesn't seem to understand that we need to do
-- \`attack\` before dealing with universals and I expect it also doesn't
-- understand our other specific Oleg-based mechanics. Perhaps it should be
-- given some short brief in each prompt."/ **Every claim in that section is
-- read off @rules\/standard.thena.rules@ and not from memory**: @attack@ and
-- @intro@ are both nullary there, @attack@ fires @when focus-is-hole@ and
-- @intro@ @when focus-is-guess goal-type-is-pi@, which is exactly the
-- ordering he says it gets wrong — and @fill : Core -> ()@ is why a term
-- argument needs a @core@ fence. His model had offered @intro T@ and
-- @fill x@, and neither is spellable.
--
-- **The vocabulary is NOT here.** It rides as the @vocabulary@ state field,
-- generated from the engine's own 'Thena.Driver.commandSummary', so the one
-- part of this that could go stale cannot.
defaultHintPrompt :: Text
defaultHintPrompt =
  Text.unlines
    [ "You are the suggestion line of a proof assistant called Thena. The user is part"
    , "way through a proof and has asked what to do next."
    , ""
    , "ANSWER WITH ONE LINE AND NOTHING ELSE."
    , ""
    , "  At most twenty words. Give the next command, or the two or three that follow"
    , "  one another, separated by \" ; \"."
    , "  Do not restate the goal. Do not say what the user is doing, has done, or will"
    , "  see. Do not explain what a command does. No preamble, no closing remark, no"
    , "  lists, no markdown, no backticks around the whole answer."
    , "  If the state does not tell you enough, answer with the one command that would:"
    , "  :where or :matches."
    , "  One line is the target. `room` below is the hard ceiling, and it says how many"
    , "  lines of how many characters the box your answer is drawn in has, at the size"
    , "  the user has pulled it to right now. Anything past `room` is not shown to them"
    , "  at all, so an answer that overruns it is an answer they never read."
    , ""
    , "  For a goal of `forall (A : Type0) -> A -> A`:"
    , "    good: attack ; intro ; intro"
    , "    bad:  The goal is a plain function type, so just introduce the two binders"
    , "          and hand back the argument: run `intro T` then `intro x`, which leaves"
    , "          a goal of T with x : T in scope."
    , "  The bad one is bad for four separate reasons: it narrates, it explains, it is"
    , "  four lines, and both commands in it are unspellable."
    , ""
    , "HOW THENA WORKS. You will get these wrong without them."
    , ""
    , "  A goal is a hole in a term, and the proof is that term. Tactics build it; the"
    , "  kernel re-checks what they built."
    , "  `attack` takes no argument and turns the focused HOLE into a GUESS. It is the"
    , "  first move on every hole."
    , "  `intro` takes no argument and peels exactly ONE binder, and it only applies to"
    , "  a GUESS. So a universal needs `attack` first and then one bare `intro` per"
    , "  binder. There is no `intro x`."
    , "  A command's term argument is written in a fence: `fill core`x``, not `fill x`."
    , "  `fill` closes a HOLE; `try-core core`t`` proposes a term at a hole and `solve`"
    , "  accepts the guess."
    , "  Holes are named positions, so arms can be closed in any order: `goto-named`"
    , "  \"the-hole\"` moves to one, `goto-root` back to the top, and `along`, `into` and"
    , "  `back` walk the chain."
    , "  Several rules matching leaves a choice point; `retry` backtracks to it."
    , ""
    , "  THERE IS ONE FOCUS AND EVERY TACTIC ACTS THERE AND NOWHERE ELSE. This is the"
    , "  one that is most often got wrong: do not propose a tactic for a hole the user"
    , "  is not standing on. If the move you want needs them somewhere else, say the"
    , "  navigation first and the tactic after it, in that order."
    , "  `:where` prints the focus, its path, its context and its expected type. When"
    , "  you cannot tell where they are standing, that is the whole answer."
    , "  A development is a chain. `along`, `into` and `back` move on it; `cross type`"
    , "  and `cross val` move into a term; the field words in `vocabulary` descend into"
    , "  a field of the focused term."
    , "  Holes are named positions, so they can be closed in any order:"
    , "  `goto-named \"the-hole\"` jumps to one and `goto-root` returns to the top."
    , "  `solve` accepts the guess AT THE FOCUS. `fill` closes the hole AT THE FOCUS."
    , "  Neither reaches a goal elsewhere in the term, so neither is the next move until"
    , "  the focus is on the thing it would act on."
    , "  `qed` asks the kernel to certify and admit the proof. A refused `qed` leaves"
    , "  the proof standing."
    , ""
    , "WHAT YOU ARE GIVEN."
    , ""
    , "  goals          the goals still open, the first being where the user stands"
    , "  proof_term     the proof term as it stands, holes included"
    , "  applies_here   the rules that apply at the focus, nearest first. Evidence and"
    , "                 not a shortlist: something outside it may still be the move"
    , "  in_scope       the names available, by namespace"
    , "  executed       what has already been run this session, oldest first"
    , "  typed_so_far   the line being typed, if any"
    , "  room           how much space your answer has. Never exceed it"
    , "  vocabulary     every command the engine itself takes, one line each"
    , "  tactics        every rule in the loaded rule bases, as its head with its"
    , "                 argument shape. THIS is where attack, intro, fill, solve and"
    , "                 the rest live, and the shape is the arity: `intro` takes none,"
    , "                 `fill ‹t›` takes one. A rule not listed here does not exist"
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
