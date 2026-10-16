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
-- A @judgment@ block (phase 108, §6.1) is read the same way down to its
-- rules: the header's notation is one production, named after the judgment,
-- and each rule is cut into its premises and its conclusion **as text**. What
-- that text says is a parse against the grammars installed when the load
-- reaches the block ("Thena.Language.Judgment"), not a question for here.
--
-- Everything this refuses is a 'ReadError', carrying the line it is about.
module Thena.Language.Reader
  ( Block (..)
  , RawRule (..)
  , Production (..)
  , Param (..)
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
    -- ^ a judgment's is its notation alone, named after the judgment
  , blockRules       :: [RawRule]
    -- ^ a judgment's rules; nothing for a language or a context
  }
  deriving (Eq, Show)

-- | One rule of a judgment (§6.1, §6.4), cut at its rule line.
data RawRule = RawRule
  { ruleLine       :: Int
  , ruleName       :: String
  , ruleQuantifier :: Maybe String
    -- ^ the annotated tier's @∀ (x : T) …@, as written and without its closing
    -- @->@; 'Nothing' in the paper tier, where quantification is implicit
  , rulePremises   :: [String]
    -- ^ the premise lines above the rule line, a continued line joined to the
    -- one it continues. **A line break ends a premise**; several on one line
    -- are separated by whitespace, and where one ends is the parser's question
  , ruleConclusion :: String
  }
  deriving (Eq, Show)

-- | @abs : x as binder -> ( λ x : T . E[x] )@.
data Production = Production
  { productionLine     :: Int
  , productionName     :: String
  , productionParams  :: [Param]
    -- ^ **The names a @notation@ production gives its own arguments** — the
    -- @G M T d@ of @notation Valid G M T d -> ⊢ G , M , T by d valid@ (MS8
    -- phase 171, his ruling of 2026-10-16).
    --
    -- **They are local, and position is what identifies the argument**: the
    -- first name is the first parameter or index of the declaration being
    -- spelled, and nothing requires it to be spelled the way the declaration
    -- spells it. A word of the layout is a slot exactly when it is one of these,
    -- and every other word is literal text.
    --
    -- **This replaces reading a slot's word out of a grammar's metavariables**,
    -- which could not say which argument it meant. @notation Valid -> ⊢ Γ , M ,
    -- T by typing valid@ named the /grammar/ @typing@ where a derivation goes,
    -- because a judgment declares no word for its derivations — and that read
    -- as a claim about the fourth argument's type while claiming nothing, so the
    -- identical line was accepted for a declaration whose fourth argument is
    -- @typing G M base@. A name claims nothing, so nothing can disagree with it;
    -- the dependence stays in the declaration, where it is already checked.
    --
    -- **A binder is ascribed with a token class, and only when it has to be.**
    -- The declaration says a slot's type, so position settles it — except for a
    -- @String@ argument, where it cannot. POPLMark declares two classes over one
    -- @String@, @X@ for capitalised type variables and @x@ for term variables,
    -- so @notIn : String -> Ctx -> Type\8320@ does not say which its first argument
    -- reads as, and a @String@ slot that names no class cannot be read at all.
    -- Hence @notation notIn (v : X) G -> v # G@: the ascription says the one
    -- thing the declaration is silent about, and nothing else may carry one.
    --
    -- **Empty for every other kind of block.** A @language@, @context@ or
    -- @judgment@ production takes its slots from the grammar's metavariables as
    -- it always has, which is why those are unchanged by this.
  , productionMetadata :: Maybe Metadata
  , productionItems    :: [RawItem]
  }
  deriving (Eq, Show)

-- | **One name a @notation@ production gives an argument of its own** (MS8
-- phase 171) — @d@, or @(v : X)@ where the argument is a @String@ and the class
-- it reads has to be said. See 'productionParams'.
data Param = Param
  { paramName  :: String
  , paramClass :: Maybe String
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
  | ParamMalformed Int String
    -- ^ a word in a @notation@ production's binder list that is neither a name
    -- nor a bracketed ascription (MS8 phase 171)
  | JudgmentHeaderMalformed Int
    -- ^ a judgment's first line is not @‹name› = ‹notation› where@
  | RuleUnnamed Int
    -- ^ a rule that starts with neither @‹name›:@ nor @rule ‹name› where@
  | RuleWithoutLine Int
    -- ^ no line of three or more @-@ between the premises and the conclusion
  | RuleWithoutConclusion Int
  | QuantifierMalformed Int
    -- ^ @rule ‹name› where@ not followed by @∀ … ->@
  | PremiseIndentedLess Int
    -- ^ a premise line indented less than the first premise
  deriving (Eq, Show)

-- | Read a block's text: everything after its keyword, starting on the
-- keyword's own line, which is @line@.
readBlock :: BlockKind -> Int -> String -> Either ReadError Block
readBlock kind line txt = case lines' of
  [] -> Left (HeaderWithoutWhere line)
  (l0, header) : rest
    | kind == JudgmentBlock -> do
        (n, notation) <- readJudgmentHeader l0 header
        items <- readItems l0 notation
        rules <- traverse readRule =<< groupedLines rest
        Right (Block kind n [] [Production l0 n [] Nothing items] rules)
    -- **A @notation@ block's header may carry the name's OWN spelling** (MS8
    -- phase 160): @notation bound -> v ◂ A ◂ Δ where@. It is read exactly as a
    -- judgment's header is, with @->@ in place of @=@, and becomes the
    -- production named after the block — which is how 'Thena.Language.Grammar'
    -- tells the type former's spelling from its constructors' and functions'.
    -- **The split is layout and not semantics** (HIS request): a type's own
    -- spelling does not belong in the list of its constructors.
    --
    -- The @->@ is the first word after the name, so a notation that contains
    -- one of its own — @( T -> S )@ — reads as it should.
    | kind == NotationBlock, Just (n, bs, notation) <- headerNotation header -> do
        items <- readItems l0 notation
        bs' <- readParams l0 bs
        prods <- traverse readProduction =<< grouped rest
        Right (Block kind n [] (Production l0 n bs' Nothing items : prods) [])
    | otherwise -> do
        names <- readHeader l0 header
        prods <- traverse readProduction =<< grouped rest
        case names of
          n : ms -> Right (Block kind n ms prods [])
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
grouped ls = map (\(k, g) -> (k, unwords (map snd g))) <$> groupedLines ls

-- | The same grouping, keeping a group's lines apart — a rule's rule line has
-- to be found among them.
groupedLines :: [(Int, String)] -> Either ReadError [(Int, [(Int, String)])]
groupedLines ls = case [ (k, l) | (k, l) <- ls, not (all isSpace l) ] of
  [] -> Right []
  first@(k1, l1) : more -> go (indent l1) [(k1, [first])] more
  where
    go _ acc [] = Right (reverse [ (k, reverse g) | (k, g) <- acc ])
    go col acc ((k, l) : rest)
      | indent l == col = go col ((k, [(k, l)]) : acc) rest
      | indent l > col, (k0, g) : acc' <- acc = go col ((k0, (k, l) : g) : acc') rest
      | otherwise = Left (IndentedLess k)
    indent = length . takeWhile isSpace

-- | @bound v A Δ -> v ◂ A ◂ Δ where@: the name, **the names it gives its own
-- arguments** (MS8 phase 171) and its own notation's words — or 'Nothing' when
-- the header is the plain @notation ‹Grammar› where@ (MS8 phase 160). A header
-- with @->@ and nothing after it is 'Nothing' too, so it is refused by the
-- ordinary path as a malformed name rather than read as a spelling with no
-- items.
headerNotation :: String -> Maybe (String, [String], [String])
headerNotation txt = case break (== "->") (words txt) of
  (n : bs, "->" : rest)
    | "where" : notation@(_ : _) <- reverse rest -> Just (n, bs, reverse notation)
  _ -> Nothing

-- | @typing = Γ ⊢ M : T where@: the judgment's name and its notation's words.
readJudgmentHeader :: Int -> String -> Either ReadError (String, [String])
readJudgmentHeader l txt = case words txt of
  n : "=" : rest
    | "where" : notation@(_ : _) <- reverse rest -> Right (n, reverse notation)
  _ -> Left (JudgmentHeaderMalformed l)

-- | A rule: @‹name›: premises / rule line / conclusion@, or the annotated tier's
-- @rule ‹name› where ∀ … ->@ in place of @‹name›:@ (§6.1, §6.4).
--
-- **A line break ends a premise line** (his ruling, 2026-09-21), and one
-- line may hold several premises, which parsing tells apart. **A line indented
-- further than the premise column continues the line above**; one indented
-- less is refused. The premise column is where the first premise starts —
-- after @T-var:@, or on the first line under an annotated tier's @∀@.
readRule :: (Int, [(Int, String)]) -> Either ReadError RawRule
readRule (l, ls) = do
  (name, quantifier, body) <- case ls of
    [] -> Left (RuleUnnamed l)
    (k0, l0) : later -> case words l0 of
      "rule" : n : "where" : more -> do
        (q, rest) <- maybe (Left (QuantifierMalformed l)) Right (readQuantifier more later)
        Right (n, Just q, rest)
      w : _
        | Just n <- colonEnded w -> Right (n, Nothing, (k0, blankUpTo (w ==) l0) : later)
      n : ":" : _ -> Right (n, Nothing, (k0, blankUpTo (== ":") l0) : later)
      _ -> Left (RuleUnnamed l)
  case break (isRuleLine . snd) body of
    (above, _ : below)
      | all (all isSpace . snd) below -> Left (RuleWithoutConclusion l)
      | otherwise -> do
          premises <- premiseLines [ kl | kl@(_, t) <- above, not (all isSpace t) ]
          Right (RawRule l name quantifier premises (squash (map snd below)))
    _ -> Left (RuleWithoutLine l)
  where
    colonEnded w = case reverse w of
      ':' : n@(_ : _) -> Just (reverse n)
      _ -> Nothing
    isRuleLine t = case filter (not . isSpace) t of
      ds@(_ : _ : _ : _) -> all (== '-') ds
      _ -> False
    squash = unwords . concatMap words

    -- The line with everything up to and including the word that ends the
    -- rule's name turned to spaces, so its premise keeps its column.
    blankUpTo ends t =
      let (lead, rest) = span isSpace t
          go acc s = case break isSpace s of
            (w, more) | ends w -> acc ++ map (const ' ') w ++ more
                      | otherwise -> let (sp, more') = span isSpace more
                                      in go (acc ++ map (const ' ') w ++ sp) more'
       in lead ++ go "" rest

    premiseLines [] = Right []
    premiseLines ((k1, t1) : more) = go [(k1, t1)] more
      where
        col = indent t1
        go acc [] = Right (reverse (map (unwords . words . snd) acc))
        go acc ((k, t) : rest)
          | indent t == col = go ((k, t) : acc) rest
          | indent t > col, (k0, t0) : acc' <- acc = go ((k0, t0 ++ " " ++ t) : acc') rest
          | otherwise = Left (PremiseIndentedLess k)
    indent = length . takeWhile isSpace

-- | @∀ (x : T) … ->@, from the words after @where@ and the lines after the
-- first: the quantifier's text, and the lines below it as written. **Its @->@
-- ends a line**, as §6.4 writes it — the first @->@ outside every bracket, so
-- a binder's own arrow type does not end it.
readQuantifier :: [String] -> [(Int, String)] -> Maybe (String, [(Int, String)])
readQuantifier firstWords laterLines = case firstWords of
  w : _ | w `elem` ["∀", "forall"] || take 1 w == "∀" -> go (0 :: Int) [] (firstWords : map (words . snd) laterLines) 0
  _ -> Nothing
  where
    go _ _ [] _ = Nothing
    go d acc (line : rest) k = case scan d acc line of
      Continue d' acc' -> go d' acc' rest (k + 1)
      Ends q -> Just (q, drop k laterLines)
      Malformed -> Nothing
    scan d acc [] = Continue d acc
    scan 0 acc ["->"] = Ends (unwords (reverse acc))
    scan d acc (w : ws)
      | w == "->" && d == 0 = Malformed   -- an @->@ with more after it on its line
      | d < 0 = Malformed                 -- a bracket closed that was never opened
      | otherwise = scan (d + depth w) (w : acc) ws
    depth w = length (filter (`elem` "([{") w) - length (filter (`elem` ")]}") w)

data Scanned = Continue Int [String] | Ends String | Malformed

-- | @name -> items@ or @name : metadata -> items@.
-- **The words before the @:@ or the @->@ are the name and then its binders**
-- (MS8 phase 171). A production with no binders reads exactly as it did, which
-- is every @language@, @context@ and @judgment@ production; a @notation@ one
-- names its arguments. 'Thena.Language.Grammar.checkNotation' is where a binder
-- is refused on a block that has no use for one.
readProduction :: (Int, String) -> Either ReadError Production
readProduction (l, txt) = case splitHead (words txt) of
  (name : bs, "->" : rest) -> do
    bs' <- readParams l bs
    Production l name bs' Nothing <$> items rest
  (name : bs, ":" : rest) -> case break (== "->") rest of
    (meta, "->" : rest') -> do
      bs' <- readParams l bs
      m <- readMetadata l (unwords meta)
      Production l name bs' (Just m) <$> items rest'
    _ -> Left (ProductionWithoutArrow l)
  _ -> Left (ProductionWithoutArrow l)
  where
    items = readItems l

    -- **The @:@ that introduces metadata is the one outside the brackets.** A
    -- parameter may be ascribed — @( v : w )@ — and that @:@ belongs to the
    -- parameter list, so the split walks the words keeping the bracket depth
    -- (MS8 phase 171).
    splitHead = go (0 :: Int) []
      where
        go _ acc [] = (reverse acc, [])
        go d acc (w : ws)
          | d == 0, w `elem` [":", "->"] = (reverse acc, w : ws)
          | otherwise = go (d + opens w) (w : acc) ws
        opens w = length (filter (== '(') w) - length (filter (== ')') w)

-- | @d@, or @( v : X )@ — a plain name, or one ascribed with the token class it
-- reads (MS8 phase 171). Brackets are required for an ascription so that a
-- binder list needs no lookahead and a @:@ inside it cannot be taken for the
-- @:@ that introduces a production's metadata.
readParams :: Int -> [String] -> Either ReadError [Param]
readParams l = go . concatMap spaced
  where
    -- @(v : X)@ and @( v : X )@ read alike, as 'readMetadata' already has it
    -- for @{ x, y }@: a bracket is its own word however it was typed.
    spaced w = words (concatMap (\c -> if c `elem` "()" then [' ', c, ' '] else [c]) w)

    go [] = Right []
    go ("(" : x : ":" : cls : ")" : rest) = (Param x (Just cls) :) <$> go rest
    go (w : rest)
      | w `notElem` ["(", ")", ":"] = (Param w Nothing :) <$> go rest
      | otherwise = Left (ParamMalformed l w)

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

-- | A line up to its comment, **spacing kept as written**: 'grouped' reads the
-- indentation, and a rule's premise column is measured inside the line
-- (phase 108). A line that is only a comment, or blank, is empty.
stripComment :: String -> String
stripComment l
  | all isSpace kept = ""
  | otherwise = kept
  where
    kept = go l
    -- Cut at a word @--@: preceded by the line's start or a space, and
    -- followed by a space or the line's end.
    go s = case s of
      [] -> []
      '-' : '-' : rest | null rest || isSpace (head' rest) -> ""
      c : rest | isSpace c -> c : go rest
      _ -> let (w, rest) = break isSpace s in w ++ go rest
    head' t = case t of
      c : _ -> c
      [] -> ' '

splitOn :: Char -> String -> [String]
splitOn c s = case break (== c) s of
  (a, _ : b) -> a : splitOn c b
  (a, [])    -> [a]

trim :: String -> String
trim = f . f where f = reverse . dropWhile isSpace
