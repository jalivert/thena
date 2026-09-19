-- | The object-language block reader (MS6 phase 101; @ms6\/SPEC.md@ §4.1–4.4,
-- §5.1, §7.0).
--
-- A @language@ or @context@ block is **not lexed by Thena's lexer**: @[@, @]@,
-- @λ@ and a regex's characters are reserved there, and an object language
-- wants all of them. "Thena.Syntax.Lexer.lexModule" hands the block over as
-- raw text, and this module reads that text into a 'Block' — its header, and
-- per production a name, the metadata as written, and the items.
--
-- **It knows nothing about what a name means.** Whether @E@ is a metavariable
-- or @λ@ a terminal is "Thena.Language.Grammar"\'s question, asked against
-- what has been declared. Here a word is a word, and the one thing decided is
-- the /shape/ of an item: a word, or a binding form @E[x, y]@.
--
-- Everything this refuses is a 'ReadError', carrying the line it is about.
module Thena.Language.Reader
  ( Block (..)
  , Production (..)
  , Metadata (..)
  , RawItem (..)
  , ReadError (..)
  , readBlock
  ) where

import Data.Char (isSpace)

import Thena.Syntax.Lexer (BlockKind (..))

-- | A block as written.
data Block = Block
  { blockKind        :: BlockKind
  , blockName        :: String     -- ^ the datatype, @LC@
  , blockMetavars    :: [String]   -- ^ the rest of the head, @M, N, E@
  , blockProductions :: [Production]
  }
  deriving (Eq, Show)

-- | @abs : x as binder -> ( λ x : T . E[x] )@.
data Production = Production
  { productionLine     :: Int
  , productionName     :: String
  , productionMetadata :: Maybe Metadata
  , productionItems    :: [RawItem]
  }
  deriving (Eq, Show)

-- | What is between the @:@ and the @->@ (§4.4). The spelling is **OPEN**
-- (§9) and read as the spec writes it.
data Metadata
  = AsOccurrence String   -- ^ @x as occurrence@
  | AsBinders [String]    -- ^ @x as binder@, or @{ x, y } as binders@
  deriving (Eq, Show)

-- | One item, by shape only (§4.2).
data RawItem
  = Word String
  | Binding String [String]
    -- ^ @E[x, y]@: a word followed at once by a bracket. **The bracket must be
    -- adjacent** — @E [ x ]@ is four words — and that is what keeps @[@ and
    -- @]@ available to object languages. Inside it, whitespace is allowed.
  deriving (Eq, Show)

data ReadError
  = HeaderWithoutWhere Int
    -- ^ the block's first line does not end in @where@
  | HeaderMalformed Int
    -- ^ no name before @where@, or an empty name between commas
  | ProductionWithoutArrow Int
    -- ^ a production line with no @->@ after its name and metadata
  | MetadataMalformed Int String
    -- ^ what stood between @:@ and @->@, when it is none of §4.4's forms
  | BindingMalformed Int String
    -- ^ a binding form's @[@ with no @]@ before the end of the production, or
    -- with more written after the @]@ in the same word
  | IndentedLess Int
    -- ^ a line indented less than the first production, but not at the margin
  deriving (Eq, Show)

-- | Read a block's text: everything after its keyword, starting on the
-- keyword's own line, which is @line@.
readBlock :: BlockKind -> Int -> String -> Either ReadError Block
readBlock kind line txt = case lines' of
  [] -> Left (HeaderWithoutWhere line)
  (l0, header) : rest -> do
    names <- readHeader l0 header
    prods <- traverse readProduction =<< grouped rest
    case names of
      n : ms -> Right (Block kind n ms prods)
      []     -> Left (HeaderMalformed l0)
  where
    -- Numbered, comments gone. A comment is a word @--@ and what follows it —
    -- the one syntax for comments in every language here (his ruling of
    -- 2026-09-02), so an object language cannot have a terminal @--@; @-->@
    -- is a different word and is fine.
    lines' = [ (k, stripComment l) | (k, l) <- zip [line ..] (lines txt) ]

-- | @LC, M, N, E where@.
readHeader :: Int -> String -> Either ReadError [String]
readHeader l txt = case reverse (words txt) of
  "where" : before ->
    let names = map trim (splitOn ',' (unwords (reverse before)))
     in if null names || any null names then Left (HeaderMalformed l) else Right names
  _ -> Left (HeaderWithoutWhere l)

-- | Productions by indentation: a line at the column of the first production
-- starts one, a line indented further continues the one before it.
grouped :: [(Int, String)] -> Either ReadError [(Int, String)]
grouped ls = case [ (k, l) | (k, l) <- ls, not (all isSpace l) ] of
  [] -> Right []
  first@(_, l1) : more -> go (indent l1) [first] more
  where
    go _ acc [] = Right (reverse acc)
    go col acc ((k, l) : rest)
      | indent l == col = go col ((k, l) : acc) rest
      | indent l > col, (k0, l0) : acc' <- acc = go col ((k0, l0 ++ " " ++ l) : acc') rest
      | otherwise = Left (IndentedLess k)
    indent = length . takeWhile isSpace

-- | @name -> items@ or @name : metadata -> items@.
readProduction :: (Int, String) -> Either ReadError Production
readProduction (l, txt) = case words txt of
  name : "->" : rest -> Production l name Nothing <$> items rest
  name : ":" : rest -> case break (== "->") rest of
    (meta, "->" : rest') -> do
      m <- readMetadata l (unwords meta)
      Production l name (Just m) <$> items rest'
    _ -> Left (ProductionWithoutArrow l)
  _ -> Left (ProductionWithoutArrow l)
  where
    items = readItems l

readMetadata :: Int -> String -> Either ReadError Metadata
readMetadata l txt = case words (spaced txt) of
  [x, "as", "occurrence"] -> Right (AsOccurrence x)
  [x, "as", "binder"] -> Right (AsBinders [x])
  "{" : rest
    | (inside, "}" : ["as", "binders"]) <- break (== "}") rest
    , names <- map trim (splitOn ',' (unwords inside))
    , not (null names), all (not . null) names ->
        Right (AsBinders names)
  _ -> Left (MetadataMalformed l txt)
  where
    -- So that @{x, y}@ and @{ x, y }@ read alike.
    spaced = concatMap (\c -> if c `elem` "{}" then [' ', c, ' '] else [c])

-- | Words, with a binding form joined across the spaces inside its bracket.
readItems :: Int -> [String] -> Either ReadError [RawItem]
readItems l = go
  where
    go [] = Right []
    go (w : ws) = case break (== '[') w of
      (hd@(_ : _), '[' : after) -> do
        (inside, rest) <- closing (after : ws)
        (Binding hd (map trim (filter (not . all isSpace) (splitOn ',' inside))) :) <$> go rest
      _ -> (Word w :) <$> go ws

    -- The text up to the @]@ that ends the word it is in.
    closing ws = case ws of
      [] -> Left (BindingMalformed l "")
      w : rest -> case break (== ']') w of
        (inside, "]") -> Right (inside, rest)
        (inside, "") -> do
          (more, rest') <- closing rest
          Right (inside ++ " " ++ more, rest')
        (_, _) -> Left (BindingMalformed l w)

stripComment :: String -> String
stripComment l = case takeWhile (/= "--") (words rest) of
  [] -> ""
  ws -> indentation ++ unwords ws   -- the indentation stays: 'grouped' reads it
  where
    (indentation, rest) = span isSpace l

splitOn :: Char -> String -> [String]
splitOn c s = case break (== c) s of
  (a, _ : b) -> a : splitOn c b
  (a, [])    -> [a]

trim :: String -> String
trim = f . f where f = reverse . dropWhile isSpace
