-- | JSON, by hand, for the project database's index and nothing else.
--
-- **Why there is no dependency here.** The index holds short tokens — a name, a
-- line number, sixteen hex digits, a path — and the transcripts are
-- `.thena.script` files beside it, in the format Thena already reads
-- (**his, 2026-11-11**: *"It was never intended that the transcript would be
-- stored in the json"*). So the hardest thing this ever encodes is a file path,
-- and pulling in @aeson@'s tree for that would be out of all proportion in a
-- project that declined @random@ for a filename stem and SHA-256 for a digest.
--
-- **It is deliberately small rather than complete.** It writes what
-- 'Tui.Database' writes and reads back what it wrote, plus the ordinary things
-- a person might type into the file by hand. What it does not do: floating
-- point, @\\uXXXX@ escapes in input (it writes them, and reads the ones it
-- writes), and anything about ordering or duplicate keys. **A file it cannot
-- parse is a file the TUI starts without**, the same bargain 'Tui.Config'
-- makes for the preferences dotfile — a frontend's own cache is never worth a
-- crash.
module Tui.Json
  ( Json (..)
  , renderJson
  , parseJson
  , objectField
  , stringOf
  , intOf
  , arrayOf
  ) where

import Data.Char (chr, isDigit, isHexDigit, isSpace, ord)
import Data.List (intercalate)
import Numeric (readHex, showHex)

data Json
  = JStr String
  | JInt Int
  | JArr [Json]
  | JObj [(String, Json)]
  deriving (Eq, Show)

-- * Writing

-- | **Two spaces of indent and one field per line**, because the file is meant
-- to be read and diffed by a person — it sits in their project, beside the
-- proof-scripts it indexes.
renderJson :: Json -> String
renderJson = go 0
  where
    go _ (JStr s) = quoted s
    go _ (JInt n) = show n
    go _ (JArr []) = "[]"
    go i (JArr xs) =
      "[\n"
        <> intercalate ",\n" [pad (i + 1) <> go (i + 1) x | x <- xs]
        <> "\n"
        <> pad i
        <> "]"
    go _ (JObj []) = "{}"
    go i (JObj kvs) =
      "{\n"
        <> intercalate ",\n" [pad (i + 1) <> quoted k <> ": " <> go (i + 1) v | (k, v) <- kvs]
        <> "\n"
        <> pad i
        <> "}"
    pad i = replicate (i * 2) ' '

quoted :: String -> String
quoted s = '"' : concatMap esc s <> "\""
  where
    esc c = case c of
      '"' -> "\\\""
      '\\' -> "\\\\"
      '\n' -> "\\n"
      '\r' -> "\\r"
      '\t' -> "\\t"
      _
        | ord c < 0x20 -> "\\u" <> pad4 (showHex (ord c) "")
        | otherwise -> [c]
    pad4 h = replicate (4 - length h) '0' <> h

-- * Reading

-- | 'Nothing' for anything this does not understand, including trailing
-- rubbish after the value.
parseJson :: String -> Maybe Json
parseJson src = case value (skip src) of
  Just (v, rest) | all isSpace rest -> Just v
  _ -> Nothing

skip :: String -> String
skip = dropWhile isSpace

value :: String -> Maybe (Json, String)
value s = case s of
  ('"' : rest) -> do
    (str, rest') <- string rest
    pure (JStr str, rest')
  ('[' : rest) -> array (skip rest) []
  ('{' : rest) -> object (skip rest) []
  _ -> number s

number :: String -> Maybe (Json, String)
number s =
  let (sign, s') = case s of
        ('-' : r) -> ("-", r)
        _ -> ("", s)
      (digits, rest) = span isDigit s'
   in if null digits then Nothing else Just (JInt (read (sign <> digits)), rest)

string :: String -> Maybe (String, String)
string = go ""
  where
    go acc s = case s of
      ('"' : rest) -> Just (reverse acc, rest)
      ('\\' : c : rest) -> case c of
        '"' -> go ('"' : acc) rest
        '\\' -> go ('\\' : acc) rest
        '/' -> go ('/' : acc) rest
        'n' -> go ('\n' : acc) rest
        'r' -> go ('\r' : acc) rest
        't' -> go ('\t' : acc) rest
        'b' -> go ('\b' : acc) rest
        'f' -> go ('\f' : acc) rest
        'u' -> case splitAt 4 rest of
          (hex, rest') | length hex == 4, all isHexDigit hex ->
            case readHex hex of
              [(n, "")] -> go (chr n : acc) rest'
              _ -> Nothing
          _ -> Nothing
        _ -> Nothing
      (c : rest) -> go (c : acc) rest
      [] -> Nothing

array :: String -> [Json] -> Maybe (Json, String)
array s acc = case s of
  (']' : rest) -> Just (JArr (reverse acc), rest)
  _ -> do
    (v, rest) <- value s
    case skip rest of
      (',' : more) -> array (skip more) (v : acc)
      (']' : more) -> Just (JArr (reverse (v : acc)), more)
      _ -> Nothing

object :: String -> [(String, Json)] -> Maybe (Json, String)
object s acc = case s of
  ('}' : rest) -> Just (JObj (reverse acc), rest)
  ('"' : rest) -> do
    (k, rest') <- string rest
    case skip rest' of
      (':' : afterColon) -> do
        (v, rest'') <- value (skip afterColon)
        case skip rest'' of
          (',' : more) -> object (skip more) ((k, v) : acc)
          ('}' : more) -> Just (JObj (reverse ((k, v) : acc)), more)
          _ -> Nothing
      _ -> Nothing
  _ -> Nothing

-- * Reading a value out

objectField :: String -> Json -> Maybe Json
objectField k (JObj kvs) = lookup k kvs
objectField _ _ = Nothing

stringOf :: Json -> Maybe String
stringOf (JStr s) = Just s
stringOf _ = Nothing

intOf :: Json -> Maybe Int
intOf (JInt n) = Just n
intOf _ = Nothing

arrayOf :: Json -> Maybe [Json]
arrayOf (JArr xs) = Just xs
arrayOf _ = Nothing
