-- | **The terminal REPL's line protocol, and nothing else.**
--
-- A prompt, a line in, the lines out, and the multi-line entry the prompt
-- understands. 'turn' is the whole of a line except the reading and the
-- writing, and it is deliberately pure: the interactive loop and the golden
-- 'transcript' both go through it, so a transcript cannot drift away from the
-- loop it is supposed to be testing.
--
-- **The terminal itself left at MS7 phase 125** — @repl@, its @loop@ and its
-- @haskeline@ completion are @app\/Repl.hs@, so that nothing in the library
-- links a line editor.
--
-- **Everything that outlives the REPL left at MS7 phase 130.** Reading files is
-- "Thena.Files" and rendering is "Thena.Render"; what is here is what the old
-- REPL /is/, and it is deprecated. HIS ruling, 2026-09-28: it will be deleted.
-- So this module is **not on @thena:view@'s list** — a frontend cannot import
-- it, and nothing a frontend needs is in it.
--
-- **What still depends on it is the golden suite**, whose whole harness is
-- 'transcriptFrom' replaying a script into the text a terminal would have
-- shown, and @.claude\/bin\/manual-check@, which re-drives @docs\/MANUAL.md@.
-- Those go when this goes, and finding them a successor is the deletion
-- phase's, deliberately not this one's.
module Thena.Repl
  ( Turn (..)
  , turn
  , transcript
  , transcriptFrom
  , transcriptIO
  , entriesOf
  , prompt
  , unclosedEntry
  , opensEntry
  , closesEntry
  , tabComplete
  , tabOffer
  ) where

import Data.Char (isSpace)
import Data.List (intercalate)

import Thena.Driver
  ( Response (..)
  , Session
  , newSession
  , oneLine
  , machineOf
  , parsingLanguage
  , pendingQuestion
  )
import Thena.Engine (Machine (..), cursor, development)
import Thena.Development.Cursor (Focus (..), focus)
import Thena.Files (following)
import Thena.Language.Grammar (earleyRules)
import qualified Thena.Language.Earley as Earley
import Thena.Render (renderResponse, renderTrouble)

-- | What is said when input ends inside a @:{@.
unclosedEntry :: String
unclosedEntry = "end of input inside :{ … :} — the entry is dropped"

-- | @:{@ alone on its line opens a multi-line entry (MS5 phase 78).
opensEntry :: String -> Bool
opensEntry = (== ":{") . trimmed

-- | @:}@ alone on its line closes one.
closesEntry :: String -> Bool
closesEntry = (== ":}") . trimmed

trimmed :: String -> String
trimmed = dropWhile (== ' ') . reverse . dropWhile (== ' ') . reverse

-- | Group written lines into entries, the way the prompt does.
--
-- **The testable form of \'loop\'\'s reader** — the interactive one cannot be
-- driven without a terminal, so the rule lives here and both go through
-- \'opensEntry\' and \'closesEntry\'. A @Left@ is a problem to print instead of
-- running anything.
--
-- **It is not what a @.thena.script@ gets**, which is still a line at a time;
-- that is @ms5\/CLOSEOUT.md@\'s to decide, and nothing is lost meanwhile,
-- because a script could not write a multi-line entry before this phase either.
entriesOf :: [String] -> [Either String String]
entriesOf [] = []
entriesOf (l : ls)
  | opensEntry l = gather [] ls
  | otherwise    = Right l : entriesOf ls
  where
    gather _   []       = [Left unclosedEntry]
    gather acc (m : ms)
      | closesEntry m = Right (intercalate "\n" (reverse acc)) : entriesOf ms
      | otherwise     = gather (m : acc) ms

-- | The machine asks with the rule body's own words, so an answer prompt is
-- bare. Otherwise the prompt says which fragment the focus is in.
--
-- **Two words, and a guess body is @spine@** — asked for by the user
-- 2026-08-21 (@AGENDA.md@ item 24) and settled two-way while planning phase 5.
-- His parenthesis is the load-bearing part: being inside a guess's proposed
-- term is still the spine, so this is not a depth question and cannot be read
-- off the nesting level. It is 'Focus'\'s own distinction and nothing else. A
-- constraint focus reads as @spine@ too: it is a link in the chain.
prompt :: Session -> String
prompt s
  | Just _ <- pendingQuestion s = "> "
  | Just lang <- parsingLanguage s = "parse " ++ lang ++ "> "   -- MS6 phase 102b
  | otherwise = "thena " ++ fragment ++ "> "
  where
    fragment = case focus (cursor (development (machineOf s))) of
      OnTerm {} -> "core"
      _         -> "spine"

-- | One line in, and everything that follows from it.
--
-- **@turnPending@ went at MS7 phase 123** — whether something is asking is
-- 'Thena.Driver.pendingQuestion' on @turnSession@, so a caller that wants it
-- reads it there instead of being handed a copy to carry.
data Turn = Turn
  { turnOutput   :: [String]
  , turnSession  :: Session
  , turnQuit     :: Bool
  , turnResponse :: Response
    -- ^ kept from phase 11, because @:load@ is a response the /caller/ has to
    -- act on: the driver may not read a file (§12 invariant 4)
  }
  deriving (Eq, Show)

turn :: Session -> String -> Turn
turn s line = Turn (renderResponse s' resp) s' (resp == Quit) resp
  where
    (s', resp) = oneLine s line

-- | Replay a script through 'turn' and render what a terminal would have shown,
-- prompts included. The golden tests' whole harness (§9, "golden REPL
-- transcripts are the natural regression test for a tool whose interface is the
-- REPL").
--
-- **It starts from a bare 'newSession', where 'repl' starts from the prelude**
-- — the one place a transcript is not what the terminal would have done
-- (phase 11). Deliberate: the existing scripts declare their own @Nat@ and
-- @Empty@, and the prelude's @Empty@ would collide with phase 10's. It also
-- does not follow a @:load@, because it is pure and reading a file is not.
-- "Thena.LoadTests" covers both, against the real 'loadPrelude'.
transcript :: [String] -> String
transcript = transcriptFrom newSession

-- | **The three responses the driver cannot act on itself**: each named a file,

-- | 'transcriptFrom', in IO, so that a @:load@ is followed.
--
-- **The pure one cannot**, and says so: reading a file is not pure, so a script
-- that loads something replays as though the line did nothing. That was
-- harmless while nothing replayed a script with a load in it, and
-- @docs\/MANUAL.md@ is full of them — a manual that cannot be re-driven is
-- exactly the hand-patched transcript the standing rule is about
-- (@ms5\/CLOSEOUT.md@ 31, and @.claude\/bin\/manual-check@ is the harness).
--
-- Otherwise identical to 'transcriptFrom', through the same 'turn', so the two
-- cannot come to disagree about what a terminal would have shown.
transcriptIO :: Session -> [String] -> IO String
transcriptIO s0 = fmap unlines . replay s0
  where
    replay _ []           = pure []
    replay s (l : ls) = do
      let t    = turn s l
          echo = prompt s ++ l
      case following (turnSession t) (turnResponse t) of
        Just act | not (turnQuit t) -> do
          (s', responses, trouble) <- act
          let out = concatMap (renderResponse s') responses
                 ++ concatMap (renderTrouble s') trouble
          rest <- replay s' ls
          pure ((echo : turnOutput t ++ out) ++ rest)
        _ | turnQuit t -> pure (echo : turnOutput t)
          | otherwise  -> do
              rest <- replay (turnSession t) ls
              pure ((echo : turnOutput t) ++ rest)

-- | The same, from a session that has already had something loaded into it.
--
-- Phase 22: the rule base comes off disk now, so a transcript that uses
-- @:matches@, @prove@ or @retry@ has to start from a session that has one.
-- That makes the golden suite test the **shipped file** rather than a Haskell
-- literal, which is strictly stronger than what it tested before.
transcriptFrom :: Session -> [String] -> String
transcriptFrom s0 = unlines . replay s0
  where
    replay _ []           = []
    replay s (l : ls) =
      let t = turn s l
          rest
            | turnQuit t = []
            | otherwise  = replay (turnSession t) ls
       in (prompt s ++ l) : turnOutput t ++ rest

-- | Tab, for a frontend: what the parser has to say about the text at the
-- cursor, or 'Nothing' when the session is not reading object syntax at all.
--
-- **Added at MS7 phase 126, because the @view@ sublibrary refused to compile
-- without it.** The terminal frontend was calling 'tabComplete' itself, which
-- meant running 'earleyRules' over the session's grammars — and that needed
-- "Thena.Language.Grammar", a module a frontend has no other business with.
-- 'tabComplete' keeps its own signature, because "Thena.EarleyTests" tests it on
-- hand-built rules with no grammar to wrap them in; what moved is the plumbing,
-- not the question.
tabOffer :: Session -> (String, String) -> Maybe (String, [(String, String)])
tabOffer s input = case parsingLanguage s of
  Nothing   -> Nothing
  Just lang -> Just (tabComplete (earleyRules (grammars (machineOf s))) lang input)

-- | **Tab in @:parse@'s mode** (MS6 phase 102b, his request of 2026-09-19;
-- corrected in MS7 phase 120). Haskeline hands over the text left of the
-- cursor, reversed, and the text right of it; this answers with what to keep
-- of the left and what to insert.
--
-- * **One production is open at the cursor**: the rest of it is inserted, its
--   terminals as text and its slots as @?@ — but only as much of it as the
--   text after the cursor does not already supply. After @( λ@ that is
--   @? : ? . ? )@, and with @ )@ already written after the cursor,
--   @? : ? . ?@ ('Earley.offerRest').
-- * **One thing fits, and it is notation**: it is inserted. A lone /slot/ is
--   listed instead — writing a @?@ in front of what the user has already
--   written makes that text the hole's neighbour in a larger term, which is
--   not what Tab was asked for.
-- * **Several fit**: they are listed, and so is anything the position is
--   waiting for but cannot have ('Earley.offerWanted') — orientation beats
--   silence. Every candidate's replacement is empty, because haskeline
--   inserts the candidates' longest common prefix and lists them only if that
--   inserted nothing — two slots both inserting @?@ would otherwise put a @?@
--   in instead of showing the choice.
-- * **The cursor is just after a @?@**: the hole is what is being filled, so
--   the question is asked as if it were not there, and a single answer
--   replaces it.
--
-- Answered as @(replacement, display)@ pairs, so that it is a function of the
-- parser alone; 'tabOffer' reads the session for it and a terminal makes them
-- haskeline's.
tabComplete :: [Earley.Rule] -> String -> (String, String) -> (String, [(String, String)])
tabComplete rules lang (leftReversed, right) =
  case leftReversed of
    c : before | c == Earley.placeholderChar -> answer (reverse before) True
    _ -> answer (reverse leftReversed) False
  where
    answer before replacing =
      let o = Earley.offer rules (Earley.StartAt lang) (Earley.pieces before) (Earley.pieces right)
          spaced t = if null before || isSpace (last before) then t else ' ' : t
          single t = (reverse before, [(spaced t, t)])
          -- Filling a hole with a hole says nothing: on a @?@, only terminals.
          options = [ x | x <- Earley.offerOptions o ++ Earley.offerWanted o, not replacing || isLiteral x ]
       in case (Earley.offerRest o, options) of
            (Just rest, _) | not replacing -> single (unwords (map written rest))
            (_, [s]) | isLiteral s -> single (written s)
            (_, ss) -> (leftReversed, [ ("", shown s) | s <- ss ])
    written s = case s of
      Earley.Literal t -> t
      _ -> [Earley.placeholderChar]
    isLiteral s = case s of
      Earley.Literal _ -> True
      _ -> False
    shown s = case s of
      Earley.Literal t -> t
      Earley.Scan n _ -> "\8249" ++ n ++ "\8250"
      Earley.Nonterminal n -> "\8249" ++ n ++ "\8250"

