-- | The terminal REPL: reading a key, and writing to the screen.
--
-- **The only module in the project that touches a terminal** (§2.1, §12
-- invariant 4), and since MS7 phase 125 it is the only one that links
-- @haskeline@ — it sits in the executable rather than the library, so that a
-- frontend which is not a terminal can reuse "Thena.Repl"'s rendering without
-- dragging a line editor in with it.
--
-- Everything here except the reading and the writing is "Thena.Repl"'s:
-- 'Repl.turn' is the whole of a line, 'Repl.following' is the IO a response
-- asks for, 'Repl.prompt' is what to print, and 'Repl.opensEntry' /
-- 'Repl.closesEntry' are the multi-line entry's brackets. The golden
-- transcripts drive the same four, which is why a transcript cannot drift away
-- from the loop.
module Repl (repl) where

import Control.Monad.IO.Class (liftIO)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.List (intercalate)
import System.Console.Haskeline
  ( Completion (..)
  , InputT
  , completeFilename
  , defaultSettings
  , getInputLine
  , outputStrLn
  , runInputT
  , setComplete
  )

import Thena.Driver (Session)
import Thena.Repl
  ( Turn (..)
  , closesEntry
  , following
  , opensEntry
  , prompt
  , startingSession
  , tabOffer
  , turn
  , unclosedEntry
  )

-- | The interactive loop.
--
-- The prelude is loaded first (§9, phase 11) and **silently on success** — it
-- is three @data@ lines and announcing them at every start is noise. A failure
-- is reported and the loop starts anyway, with whatever did load: @Eq@ missing
-- makes elimination fail later with a message naming @Eq@, which is the bargain
-- §3.7 already struck, and a REPL that refuses to start would say less.
repl :: IO ()
repl = do
  (s, problems) <- startingSession
  -- **Tab reads the session through a reference** (MS6 phase 102b): haskeline
  -- fixes its completion function when the loop starts, and what Tab should do
  -- depends on the session at the moment it is pressed. The loop writes the
  -- session before every prompt; nothing else writes it.
  current <- newIORef s
  let settings = setComplete (completion current) defaultSettings
  runInputT settings (mapM_ outputStrLn problems >> loop current s)

-- | In @:parse@'s mode, the parser's 'tabComplete'; anywhere else, file names,
-- as haskeline did before.
completion :: IORef Session -> (String, String) -> IO (String, [Completion])
completion current input = do
  s <- readIORef current
  case tabOffer s input of
    Just (kept, cs) -> pure (kept, [ Completion r d False | (r, d) <- cs ])
    Nothing         -> completeFilename input

loop :: IORef Session -> Session -> InputT IO ()
loop current s = do
  liftIO (writeIORef current s)
  input <- getInputLine (prompt s)
  case input of
    Nothing   -> pure ()          -- end of input: Ctrl-D
    Just first -> gather first >>= \entry -> case entry of
      Left problem -> outputStrLn problem >> loop current s
      Right line   -> run line
  where
   run line = do
      let t = turn s line
      mapM_ outputStrLn (turnOutput t)
      case following (turnSession t) (turnResponse t) of
        Just act | not (turnQuit t) -> do
          (s', out) <- liftIO act
          mapM_ outputStrLn out
          loop current s'
        _ | turnQuit t -> pure ()
          | otherwise  -> loop current (turnSession t)

   -- | **An entry, not a line** (MS5 phase 70, rewritten at phase 78).
   --
   -- A multi-line entry is opened by @:{@ and closed by @:}@, each alone on its
   -- line — **his choice, 2026-09-13, and GHCi\'s spelling**: /"only there I
   -- want any sort of weirdness"/.
   --
   -- **It replaces phase 70\'s heuristic** — keep reading while the entry
   -- /cannot be finished/, and require every continuation to be indented — which
   -- is @ms5\/CLOSEOUT.md@ 18, answered rather than left split. An explicit
   -- bracket has no lag to trade against indentation, and it is one rule where
   -- that was two.
   --
   -- The same predicates drive 'entriesOf', which is the testable form of this.
   gather firstLine
     | opensEntry firstLine = block []
     | otherwise            = pure (Right firstLine)

   block acc = do
     more <- getInputLine continuationPrompt
     case more of
       Nothing -> pure (Left unclosedEntry)
       Just l
         | closesEntry l -> pure (Right (intercalate "\n" (reverse acc)))
         | otherwise     -> block (l : acc)

-- | The prompt a line inside @:{ … :}@ is typed at.
continuationPrompt :: String
continuationPrompt = "         ... "
