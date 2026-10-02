-- | The two tests that make the hand-sync of the advising grammars hold
-- (MS7 phase 147).
--
-- **HIS INSTRUCTION, 2026-10-01**, ruling that surface and core get a secondary
-- generated grammar *"kept in sync on the principle that we will not be changing
-- surface that much and when we are, we will know that we have to change this
-- one parser too"* — and then, asked where that principle is written down:
-- *"Record this in the appropriate place so that we can do that when we are
-- working on it."* These are that record, executable.
--
-- __'neverWider' is the safety half.__ Enumerate the advising grammar's own
-- derivations and feed every one to the parser that actually runs. **An offer
-- the line cannot run is the one failure a frontend cannot recover from**: the
-- user takes a completion and gets a syntax error for a word the system
-- suggested. The invariant is @.claude\/RULINGS.md@'s — an advising grammar may
-- accept less than the running one and never more — and this is it checked
-- rather than asserted.
--
-- __'coversGolden' is the currency half.__ Every term argument written in the
-- 45 golden transcripts has to be a term the advising grammar reads. That is a
-- corpus of what the system is actually asked, it grows whenever a transcript
-- does, and it is what fires the day the surface gains a construct and this
-- module was not told: the construct turns up in a transcript, and the test
-- that was green goes red naming the line.
--
-- **Neither is a proof and that is said rather than hidden.** 'neverWider' is
-- bounded by a derivation depth, so it checks a finite prefix of an infinite
-- language; 'coversGolden' checks a corpus, not a grammar. Between them they
-- catch the two mistakes the hand-sync can actually make — a production written
-- too loosely, and a production not written at all.
module Thena.Language.BuiltinTests (tests) where

import Data.List (isInfixOf, isPrefixOf, nub, sort, sortOn)
import Data.Maybe (listToMaybe)
import System.Directory (listDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

import Thena.Files (startingSession)
import Thena.Language.Builtin (coreHead, coreRules, surfaceHead, surfaceRules)
import Thena.Language.Instral (instralRules)
import Thena.View (sessionGrammars, sessionRules)
import qualified Thena.Language.Earley as E
import Thena.Surface.Read (parseSurfaceText)
import Thena.Syntax.Lexer (lexTokens)
import Thena.Syntax.Parser (parseTerm)

tests :: TestTree
tests = testGroup "the advising grammars for surface and core (phase 147)"
  [ testGroup "never wider than the parser that runs"
      [ testCase "every surface derivation is a surface term" neverWiderSurface
      , testCase "every core derivation is a development-calculus term" neverWiderCore
      ]
  , testGroup "current with the languages they describe"
      [ testCase "every surface term in the golden transcripts reads" coversGoldenSurface
      , testCase "every core term in the golden transcripts reads" coversGoldenCore
      ]
  , testCase "every head is a phrase a dropdown can show" headsAreSayable
  ]

-- ---------------------------------------------------------------------------
-- Enumeration

-- | **One string per production, in the cheapest context that reaches it.**
--
-- The first cut enumerated everything to a fixed depth and did not finish: the
-- bodies are long and the heads are mutually recursive, so the product explodes
-- long before it is interesting. This generates **one witness per rule** —
-- a derivation of the public head that is forced to use that rule and takes the
-- shortest way everywhere else — so every production this phase wrote is
-- exercised exactly once, and a rule with /no/ witness is itself a failure,
-- because it would mean a production unreachable from the head a region parses
-- at.
witnesses :: [E.Rule] -> String -> [(String, String)]
witnesses rs root =
  [ (E.ruleName r, unwords w) | r <- rs, Just w <- [witness r] ]
  where
    heads' = nub (map E.ruleHead rs)
    rulesOf h = [ r | r <- rs, E.ruleHead r == h ]

    -- The shortest derivation of each head, by iteration to a fixed point. The
    -- heads are few and every one of them bottoms out in a terminal, so this
    -- settles in a handful of passes.
    shortest = fixpoint step (map (\h -> (h, Nothing)) heads')
      where
        step table = [ (h, best [ expand table (E.ruleBody r) | r <- rulesOf h ]) | h <- heads' ]
        best xs = case [ x | Just x <- xs ] of
          [] -> Nothing
          ys -> listToMaybe (sortOn length ys)

    expand table body = concat <$> traverse one body
      where
        one sym = case sym of
          E.Literal t -> Just [t]
          E.Scan n _ -> Just [sample n]
          E.Nonterminal n -> lookup n table >>= id

    -- **The descent is down a shortest path and that is what makes it
    -- terminate.** The first cut descended into any child that could still reach
    -- the rule's head, which loops forever on a head that reaches itself — every
    -- one of these heads does, since a term contains terms. Distance to the
    -- target strictly decreases instead.
    distance to = go' 0 [to] [(to, 0 :: Int)]
      where
        go' _ [] table = table
        go' k frontier table =
          let back = nub [ h | (h, ns) <- edges, n <- ns, n `elem` frontier
                             , h `notElem` map fst table ]
           in go' (k + 1) back (table ++ [ (h, k + 1) | h <- back ])

    edges = [ (h, nub [ n | r <- rulesOf h, E.Nonterminal n <- E.ruleBody r ]) | h <- heads' ]

    -- A derivation of @root@ that uses this rule.
    witness r
      | Just _ <- lookup root dist = down root
      | otherwise = Nothing
      where
        target = E.ruleHead r
        dist = distance target
        at h = lookup h dist

        down h
          | h == target = expand shortest (E.ruleBody r)
          | otherwise = case
              [ (k, n)
              | k <- rulesOf h
              , E.Nonterminal n <- E.ruleBody k
              , Just dh <- [at h], Just dn <- [at n], dn < dh
              ] of
              (k, n) : _ -> through (E.ruleBody k) n
              [] -> Nothing

        -- Only the first occurrence of the next head on the path is descended
        -- into; the rest of the body stays at its cheapest, so the string that
        -- exercises the rule is as short as the grammar allows.
        through body n = concat <$> traverse step' (tagFirst body)
          where
            tagFirst = go' False
              where
                go' _ [] = []
                go' done (sym : rest) = case (done, sym) of
                  (False, E.Nonterminal m) | m == n -> (sym, True) : go' True rest
                  _ -> (sym, False) : go' done rest
            step' (sym, chosen) = case (sym, chosen) of
              (E.Nonterminal m, True) -> down m
              _ -> expand shortest [sym]

-- | **Nesting, bounded, and built level by level.**
--
-- Witnesses exercise every production once in its cheapest context, which would
-- not notice a production made recursive where the real grammar is not — the
-- mistake this phase actually made and caught, since @Term : Arrowed \':\'
-- Arrowed@ does not nest and a flattened version would let @a : b : c@ through.
-- So a second enumeration goes deeper.
--
-- **The obvious recursive generator does not finish**, and the reason is worth a
-- sentence because it is not laziness failing to help: at the depth frontier a
-- whole subtree evaluates to the empty list, and proving it empty explores all of
-- it, so the @take@s above never get to prune anything. Built as a table of
-- levels instead — level @d@ from level @d-1@, each head's entry truncated as it
-- is stored — the work is a few hundred thousand list cells and the bound is
-- structural rather than hoped for.
nestings :: [E.Rule] -> Int -> String -> [String]
nestings rs d0 root = map unwords (atHead root (levels !! d0))
  where
    heads' = nub (map E.ruleHead rs)
    levels = iterate step [ (h, []) | h <- heads' ]

    step prev =
      [ (h, take perHead (concat [ sequences prev (E.ruleBody r) | r <- rs, E.ruleHead r == h ]))
      | h <- heads'
      ]

    sequences _ [] = [[]]
    sequences prev (s : rest) =
      [ x ++ y | x <- symbol prev s, y <- sequences prev rest ]

    symbol prev s = case s of
      E.Literal t -> [[t]]
      E.Scan n _ -> [[sample n]]
      E.Nonterminal n -> take perSymbol (atHead n prev)

    atHead h table = concat [ ds | (k, ds) <- table, k == h ]

    perHead = 40
    perSymbol = 2

-- | One string per token class these grammars scan.
--
-- **A scan is written as one sample of its class** rather than explored: what is
-- under test is the shape of the productions, and a class's own language is
-- "Thena.Language.Regex"'s business and has its own tests.
sample :: String -> String
sample n = case n of
  "name" -> "x"
  "universe" -> "Type₀"
  "string" -> "\"s\""
  "char" -> "'c'"
  "int" -> "1"
  "regex" -> "/r/"
  _ -> error ("Thena.Language.BuiltinTests: no sample for the class " ++ n)

-- | **The rule set as the system assembles it, with no object language loaded.**
--
-- @instralRules@ and not 'surfaceRules' alone, which was the first cut and was
-- wrong in a way the currency test found: a surface @do@ block's productions are
-- @instral@'s statement ones, contributed where the statement head lives, so a
-- grammar read without them cannot derive @do { attack ; intro }@ — a term that
-- is in the transcripts. **What is under test is the grammar a user meets.**
--
-- No object language, because a tagged term literal's contents are the user's
-- grammar: it has its own tests and there is nothing to enumerate from nothing.
assembled :: IO [E.Rule]
assembled = do
  (s, _) <- startingSession
  pure (instralRules (sessionGrammars s) (sessionRules s))


-- | Deep enough that a binder list inside a λ inside an arrow is reached, and
-- shallow enough that the bounded enumeration still finishes in well under a
-- second.
depth :: Int
depth = 5

readsAsSurface :: String -> Maybe String
readsAsSurface src = case parseSurfaceText src of
  Right _ -> Nothing
  Left e -> Just (show e)

readsAsCore :: String -> Maybe String
readsAsCore src = case lexTokens src of
  Left e -> Just (show e)
  Right ts -> case parseTerm ts of
    Right _ -> Nothing
    Left e -> Just (show e)

neverWiderSurface :: IO ()
neverWiderSurface = assembled >>= \rs -> checked "surface" readsAsSurface rs surfaceHead

neverWiderCore :: IO ()
neverWiderCore = assembled >>= \rs -> checked "core" readsAsCore rs coreHead

-- | Coverage first, then both generators through the running parser.
checked :: String -> (String -> Maybe String) -> [E.Rule] -> String -> IO ()
checked what parses rs root = do
  -- **Every production of this phase's has a witness.** One without is a
  -- production that cannot be reached from the head a region parses at, which is
  -- a mistake in the grammar rather than in the test. Only this phase's heads:
  -- the assembled set also holds the statement and operand productions, which
  -- are not reachable from a term and are phase 137's and 139's to cover.
  [ E.ruleName r
    | r <- rs
    , (what ++ ":") `isPrefixOf` E.ruleHead r
    , E.ruleName r `notElem` map fst ws
    ] @?= []
  refused what parses (map snd ws)
  refused what parses (nestings rs depth root)
  where ws = witnesses rs root

-- | Report every derivation the running parser refused, with its reason.
refused :: String -> (String -> Maybe String) -> [String] -> IO ()
refused what parses srcs = case [ (s, why) | s <- srcs, Just why <- [parses s] ] of
  [] | null srcs -> assertFailure ("the " ++ what ++ " enumeration is empty")
     | otherwise -> pure ()
  bad -> assertFailure . unlines $
    [ "the advising grammar for " ++ what ++ " is wider than the parser that runs."
    , show (length bad) ++ " of " ++ show (length srcs) ++ " derivations were refused:"
    ] ++ [ "  " ++ s ++ "\n    " ++ why | (s, why) <- take 12 bad ]

-- ---------------------------------------------------------------------------
-- The golden corpus

-- | Every argument written after one of these words in a transcript is a term of
-- that language. **The words are taken from @Thena.Driver.dispatch@'s own arms**,
-- which is where 'Thena.Instral.Commands.commands' took them.
surfaceWords, coreWords :: [String]
surfaceWords = [":surface"]
coreWords = [":core", ":dev", ":goal", ":whnf"]

coversGoldenSurface :: IO ()
coversGoldenSurface = do
  corpus <- goldenArguments surfaceWords
  rs <- assembled
  unread "surface" surfaceHead rs corpus

coversGoldenCore :: IO ()
coversGoldenCore = do
  corpus <- goldenArguments coreWords
  rs <- assembled
  unread "core" coreHead rs corpus

-- | The arguments the transcripts write after those words.
--
-- **A prompt line only** — @thena spine> @ — so what is collected is what a user
-- typed and not what the session printed back. Two kinds of line are dropped and
-- both are dropped for a stated reason: @:help@'s summary, which writes
-- @\‹t\›@ as a placeholder and is not a term, and anything holding a tagged term
-- literal, whose contents belong to a grammar this corpus does not load.
goldenArguments :: [String] -> IO [String]
goldenArguments ws = do
  files <- goldenFiles
  texts <- traverse readFile files
  pure . nub . sort $
    [ arg
    | t <- texts, (l, next) <- zip (lines t) (drop 1 (lines t) ++ [""])
    , Just typed <- [stripPrefix' "thena spine> " l]
    , (w : rest) <- [words typed], w `elem` ws
    , let arg = unwords rest
    , not (null arg)
    , not ("‹" `isInfixOf` arg)
    , not ("`" `isInfixOf` arg)
      -- **Only what the session accepted.** A transcript records the refusals
      -- too, on purpose: @:core Type {l}@ is in @levels.golden@ to show that
      -- level arguments are not written on a bare @Type@, and the line after it
      -- is @1:6: unexpected {@. Including it would have asked this grammar to
      -- read something the real parser rejects — the opposite of the invariant.
    , not (syntaxError next)
      -- **And not a notation that is being removed.** Corners and the @⟨…⟩@
      -- alias are tagged term literals written another way and are deliberately
      -- described by neither grammar — his instruction, 2026-10-01,
      -- @AGENDA.md@ 98. @:dev ⌜ ∀ (A : Type₀) -> A ⌝@ is in @levels.golden@ and
      -- still runs; it is not something this grammar was not told about, so
      -- failing on it would make a recorded decision look like an omission.
      -- **When 98 lands these lines go with it and this filter stops matching.**
    , not (any (`elem` "⌜⌝⟨⟩") arg)
    , not ("[|" `isInfixOf` arg)
    ]

-- | A response that is a syntax error: @\‹line\>:\‹column\>: @ and then why.
syntaxError :: String -> Bool
syntaxError l = case span (/= ':') l of
  (row, ':' : rest) | not (null row), all (`elem` ['0' .. '9']) row ->
    case span (/= ':') rest of
      (col, ':' : _) -> not (null col) && all (`elem` ['0' .. '9']) col
      _ -> False
  _ -> False

goldenFiles :: IO [FilePath]
goldenFiles = do
  let dir = "test/golden"
  names <- listDirectory dir
  pure [ dir ++ "/" ++ n | n <- sort names, ".golden" `isSuffixOf'` n ]

unread :: String -> String -> [E.Rule] -> [String] -> IO ()
unread what head' rs corpus = case [ s | s <- corpus, not (reads' s) ] of
  [] | null corpus -> assertFailure ("no " ++ what ++ " terms in the transcripts")
     | otherwise -> pure ()
  bad -> assertFailure . unlines $
    [ "the advising grammar for " ++ what ++ " does not read terms the system runs."
    , "**This is the drift test** — a construct reached a transcript and"
    , "Thena.Language.Builtin was not told about it:"
    ] ++ map ("  " ++) bad
  where
    -- **Ambiguity is a pass.** These grammars mirror Happy's strata for the
    -- string language and not for its trees, so one text having two readings is
    -- expected and says nothing about whether it reads.
    reads' s = case E.parse rs (E.StartAt head') (E.pieces s) of
      Right _ -> True
      Left (E.Ambiguous _ _) -> True
      Left (E.Unbounded _) -> True
      Left _ -> False

-- ---------------------------------------------------------------------------
-- The heads

-- | **Every head is words with spaces between them, and that is the whole of
-- the convention** (phase 148, his correction).
--
-- A language name and a metavariable are identifiers, so neither can contain a
-- space: this collides with nothing, exactly as phase 147's @\/@ did not, and
-- unlike it there is nothing to map in the view because every one of these is a
-- phrase a dropdown can show. **No punctuation**, which is what he ruled —
-- neither @:@ nor @\/@.
headsAreSayable :: IO ()
headsAreSayable =
  [ h
  | h <- nub (map E.ruleHead (surfaceRules [] ++ coreRules []))
  , any (`elem` ":/|.,;") h || null (words h) || length (words h) < 2
  ] @?= []

-- | Iterate to a fixed point, computing each step once.
fixpoint :: Eq a => (a -> a) -> a -> a
fixpoint f x = let y = f x in if y == x then x else fixpoint f y

stripPrefix' :: String -> String -> Maybe String
stripPrefix' p s
  | p `isPrefixOf` s = Just (drop (length p) s)
  | otherwise = Nothing

isSuffixOf' :: String -> String -> Bool
isSuffixOf' suf s = reverse suf `isPrefixOf` reverse s
