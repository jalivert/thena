-- | JSON, hand-rolled (phase 112).
--
-- **Hand-rolled rather than @aeson@, by his decision of 2026-09-23.** The
-- library depends on @base@, @array@, @containers@ and @haskeline@; @aeson@ is a
-- large tree, it is @Text@-flavoured where this project is @String@ throughout
-- (§3.6), and the encoding is something we want to state exactly rather than
-- inherit. This module is the whole of the cost of that decision.
--
-- **Integers only, and that is a decision rather than an omission.** Nothing in
-- Thena is fractional — levels, variables, counters and positions are all 'Int'
-- — so a fractional literal is not something this protocol can mean, and
-- 'decode' refuses it with 'NotAnInteger' rather than rounding it into
-- something plausible. If a fractional number ever has a meaning here, this is
-- the one place that changes.
--
-- **'Integer', not 'Int', and that is forced.** A numeric literal in an object
-- language is arbitrary precision (@ms6\/SPEC.md@ §2.1,
-- 'Thena.Core.Term.LInt'), so a machine-word field here would silently truncate
-- one. JSON's own grammar puts no bound on an integer either, so this is the
-- format agreeing with both sides rather than a widening for safety.
module Thena.Protocol.Json
  ( Json (..)
  , encode
  , decode
  , JsonError (..)
  ) where

import Data.Char (chr, isControl, isDigit, isHexDigit, ord)
import Data.List (intercalate)
import Numeric (readHex, showHex)

-- | A JSON value.
--
-- 'JObject' keeps its members as a list rather than a map: order is what we
-- wrote, which makes 'encode' deterministic and a golden file possible.
-- Duplicate keys are a decode error, so the list cannot mean two things.
data Json
  = JNull
  | JBool Bool
  | JInt Integer
  | JString String
  | JArray [Json]
  | JObject [(String, Json)]
  deriving (Eq, Show)

-- | Why a string was not the JSON it claimed to be.
--
-- Structured, never a bare message (§12). Every one carries the offset it was
-- noticed at, because a client that sent us something unreadable needs to be
-- told where and a human reading a file needs the same.
data JsonError
  = Unexpected Int Char    -- ^ this character cannot start what is expected here
  | UnexpectedEnd Int      -- ^ the text stopped in the middle of a value
  | NotAnInteger Int       -- ^ a fractional or exponent literal; see the module note
  | BadEscape Int Char     -- ^ a backslash followed by something that is not an escape
  | BadHex Int String      -- ^ @\\u@ with fewer than four hex digits after it
  | DuplicateKey Int String
  | TrailingInput Int      -- ^ a complete value, and then more text
  deriving (Eq, Show)

-- --------------------------------------------------------------------------
-- Encoding
-- --------------------------------------------------------------------------

-- | Render a value. No spaces, no newlines, members in the order given.
encode :: Json -> String
encode v = case v of
  JNull      -> "null"
  JBool True -> "true"
  JBool False -> "false"
  JInt n     -> show n
  JString s  -> quoted s
  JArray xs  -> "[" <> intercalate "," (map encode xs) <> "]"
  JObject ms -> "{" <> intercalate "," (map member ms) <> "}"
  where
    member (k, x) = quoted k <> ":" <> encode x

-- | A JSON string literal.
--
-- **Escapes exactly what the grammar requires and nothing else.** A Thena
-- identifier may contain almost anything (@PLAN-interface.md@ §2.6) — @ℓ@, @≐@,
-- @⌜@ — and those are ordinary characters in a JSON string, so they go through
-- as themselves. Escaping them would be legal and would make every file
-- unreadable to a person, which is the opposite of what the textual medium is
-- protected for.
--
-- **This is deliberately not Haskell's @show@.** @ms6\/CLOSEOUT.md@ 2 is a
-- standing bug of exactly that shape: a printer that escapes with @show@ emits
-- something its own reader cannot take back.
quoted :: String -> String
quoted s = "\"" <> concatMap esc s <> "\""
  where
    esc c = case c of
      '"'  -> "\\\""
      '\\' -> "\\\\"
      '\n' -> "\\n"
      '\r' -> "\\r"
      '\t' -> "\\t"
      '\b' -> "\\b"
      '\f' -> "\\f"
      _ | isControl c -> "\\u" <> pad (showHex (ord c) "")
        | otherwise   -> [c]
    pad h = replicate (4 - length h) '0' <> h

-- --------------------------------------------------------------------------
-- Decoding
-- --------------------------------------------------------------------------

-- | Read a value, and refuse anything after it.
decode :: String -> Either JsonError Json
decode src = do
  (v, rest) <- value 0 (skip 0 src)
  case skip (fst rest) (snd rest) of
    (_, [])  -> Right v
    (i, _)   -> Left (TrailingInput i)

-- | Position-carrying input: the offset of the head, and the head.
type In = (Int, String)

skip :: Int -> String -> In
skip i (c : cs) | c `elem` " \t\r\n" = skip (i + 1) cs
skip i s = (i, s)

value :: Int -> In -> Either JsonError (Json, In)
value _ (i, s) = case s of
  []                                    -> Left (UnexpectedEnd i)
  'n' : 'u' : 'l' : 'l' : r             -> Right (JNull, skip (i + 4) r)
  't' : 'r' : 'u' : 'e' : r             -> Right (JBool True, skip (i + 4) r)
  'f' : 'a' : 'l' : 's' : 'e' : r       -> Right (JBool False, skip (i + 5) r)
  '"' : r                               -> do
    (str, r') <- stringBody (i + 1) r
    Right (JString str, skip (fst r') (snd r'))
  '[' : r                               -> array (i + 1) (skip (i + 1) r)
  '{' : r                               -> object (i + 1) (skip (i + 1) r)
  c : _ | c == '-' || isDigit c         -> number i s
        | otherwise                     -> Left (Unexpected i c)

number :: Int -> String -> Either JsonError (Json, In)
number i s =
  let (sign, s1, i1) = case s of
        '-' : r -> ("-", r, i + 1)
        _       -> ("", s, i)
      (ds, rest) = span isDigit s1
      i2 = i1 + length ds
   in case (ds, s1) of
        ("", c : _) -> Left (Unexpected i1 c)
        ("", [])    -> Left (UnexpectedEnd i1)
        _ -> case rest of
              -- Refused rather than rounded; see the module note.
              c : _ | c == '.' || c == 'e' || c == 'E' -> Left (NotAnInteger i2)
              _ -> Right (JInt (read (sign <> ds)), skip i2 rest)

stringBody :: Int -> String -> Either JsonError (String, In)
stringBody = go ""
  where
    go acc i s = case s of
      []           -> Left (UnexpectedEnd i)
      '"'  : r     -> Right (reverse acc, (i + 1, r))
      '\\' : r     -> escape acc (i + 1) r
      c    : r     -> go (c : acc) (i + 1) r

    escape acc i s = case s of
      []       -> Left (UnexpectedEnd i)
      'u' : r  -> unicode acc (i + 1) r
      c   : r  -> case c of
        '"'  -> go ('"'  : acc) (i + 1) r
        '\\' -> go ('\\' : acc) (i + 1) r
        '/'  -> go ('/'  : acc) (i + 1) r
        'n'  -> go ('\n' : acc) (i + 1) r
        'r'  -> go ('\r' : acc) (i + 1) r
        't'  -> go ('\t' : acc) (i + 1) r
        'b'  -> go ('\b' : acc) (i + 1) r
        'f'  -> go ('\f' : acc) (i + 1) r
        _    -> Left (BadEscape i c)

    unicode acc i s =
      let (h, r) = splitAt 4 s
       in if length h == 4 && all isHexDigit h
            then case readHex h of
              [(n, "")] -> go (chr n : acc) (i + 4) r
              _         -> Left (BadHex i h)
            else Left (BadHex i h)

array :: Int -> In -> Either JsonError (Json, In)
array _ (i, ']' : r) = Right (JArray [], skip (i + 1) r)
array _ start = go [] start
  where
    go acc inp = do
      (v, inp') <- value 0 inp
      case inp' of
        (i, ',' : r) -> go (v : acc) (skip (i + 1) r)
        (i, ']' : r) -> Right (JArray (reverse (v : acc)), skip (i + 1) r)
        (i, [])      -> Left (UnexpectedEnd i)
        (i, c : _)   -> Left (Unexpected i c)

object :: Int -> In -> Either JsonError (Json, In)
object _ (i, '}' : r) = Right (JObject [], skip (i + 1) r)
object _ start = go [] start
  where
    go acc inp = case inp of
      (i, '"' : r) -> do
        (k, r1) <- stringBody (i + 1) r
        case skip (fst r1) (snd r1) of
          (j, ':' : r2) -> do
            (v, r3) <- value 0 (skip (j + 1) r2)
            if any ((== k) . fst) acc
              then Left (DuplicateKey i k)
              else case r3 of
                (m, ',' : r4) -> go ((k, v) : acc) (skip (m + 1) r4)
                (m, '}' : r4) -> Right (JObject (reverse ((k, v) : acc)), skip (m + 1) r4)
                (m, [])       -> Left (UnexpectedEnd m)
                (m, c : _)    -> Left (Unexpected m c)
          (j, [])    -> Left (UnexpectedEnd j)
          (j, c : _) -> Left (Unexpected j c)
      (i, [])      -> Left (UnexpectedEnd i)
      (i, c : _)   -> Left (Unexpected i c)
