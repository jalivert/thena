-- | The Earley chart's own questions, as a view (MS7 phase 115e, region at 125).
--
-- **The crossing, once more.** 'redrawParse' and 'redrawOffer' draw only what
-- 'Thena.View.Chart.displayParse' and 'Thena.View.Chart.displayOffer'
-- hand them; if that agrees with what 'Thena.Render.renderTree'\/
-- 'Thena.Render.parseFailureReason' and 'Thena.Repl.tabComplete' already do with
-- the same chart, for the same text, the view carries what those two
-- existing consumers needed.
--
-- **What is not crossed.** 'Thena.View.Chart.AnAmbiguity',
-- 'Thena.View.Chart.AnUnboundedRule' and
-- 'Thena.View.Chart.ADisagreement' mirror 'Earley.Ambiguous',
-- 'Earley.Unbounded' and 'Earley.Disagrees' one constructor to one, over the
-- same 'TreeView' already crossed by the successful case — nothing in the
-- fixture grammar below is ambiguous or self-deriving, and forcing one would
-- test the mirroring function's four-line 'case', not the view. Kept total
-- rather than partial, the same call 115d made for 'Thena.View.Instral.ValOpaque'.
module Thena.View.ChartTests (tests) where

import Data.Char (isSpace)
import Data.List (intercalate)
import Data.Maybe (listToMaybe)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

import Thena.Driver
  ( Response (..)
  , loadProofSource
  , machineOf
  )
import Thena.Engine (Machine (..))
import qualified Thena.Language.Earley as Earley
import Thena.Language.Earley (placeholderChar)
import Thena.Language.Grammar (Grammar, earleyRules)
import Thena.View.Chart
  ( FailureView (..)
  , OfferProblem (..)
  , OfferView (..)
  , SymbolView (..)
  , TreeView (..)
  , ProductionView (..)
  , StuckView (..)
  , Written (..)
  , displayOffer
  , displayParse
  )
import Thena.Files (startingSession)
import Thena.Render (parseFailureReason, renderTree)
import Thena.Repl (tabComplete)
import Thena.Syntax.Print (escapeChar)

tests :: TestTree
tests =
  testGroup
    "Thena.View.Chart"
    [ testGroup "is this text one term (Earley.parse)" parseCases
    , testGroup "what may stand at the cursor (Earley.offer)" offerCases
    , testGroup "a region, text and splices (phase 125)" regionCases
    , testGroup "the productions offered whole (phase 127b)" productionCases
    , testGroup "a broken prefix says where it gave out (phase 134)" stuckCases
    ]

-- | @ms7\/CLOSEOUT.md@ 12: the text /left/ of the cursor does not read, so the
-- cursor's own column has no items and all four of the other answers are empty.
--
-- **The crossing is that the four really are empty and 'offeredStuck' really is
-- 'Just'** — one without the other would be either a silence with no
-- explanation (what this phase fixes) or an explanation beside an offer that
-- contradicts it.
stuckCases :: [TestTree]
stuckCases =
  [ testCase "the item's own example" $ do
      gs <- loaded
      -- @( λ x )@ — the binder wants @: ι .@ before the body, so the @)@ is
      -- where the reading gives out.
      stuckAtSomething gs "( \955 x )" ""
  , testCase "and a closer with nothing open" $ do
      gs <- loaded
      stuckAtSomething gs ") " ""
  , testCase "a prefix that does read is not stuck" $ do
      gs <- loaded
      o <- offerOf gs "( " ""
      offeredStuck o @?= Nothing
  , testCase "and neither is an empty region" $ do
      gs <- loaded
      o <- offerOf gs "" ""
      offeredStuck o @?= Nothing
  , testCase "the column is the furthest reached, not the cursor's" $ do
      gs <- loaded
      o <- offerOf gs "( \955 x )" ""
      case offeredStuck o of
        Nothing -> assertFailure "expected a stuck offer"
        Just (StuckView at _) ->
          -- The cursor sits at the end of seven characters; the reading gave
          -- out earlier, which is the whole distinction the field draws.
          if at < 7 then pure ()
            else assertFailure ("stuck at " <> show at <> ", which is not short of the cursor")
  ]

offerOf :: [Grammar] -> String -> String -> IO OfferView
offerOf gs before after =
  case displayOffer gs "LC" Nothing [WrittenText before] [WrittenText after] of
    Right o -> pure o
    Left p  -> assertFailure ("displayOffer refused the fixture: " <> show p)

-- | Stuck, and therefore silent on everything else.
stuckAtSomething :: [Grammar] -> String -> String -> IO ()
stuckAtSomething gs before after = do
  o <- offerOf gs before after
  case offeredStuck o of
    Nothing -> assertFailure "expected a stuck offer, got none"
    Just (StuckView _ expected) -> do
      (offeredOptions o, offeredWanted o, offeredRest o, offeredProductions o)
        @?= ([], [], Nothing, [])
      if null expected
        then assertFailure "stuck, but with nothing to say was expected there"
        else pure ()

-- | @Ty@ and @LC@, exactly `ms6\/SPEC.md`'s canonical shape, unbracketed
-- application left out so nothing here is ambiguous — the point of these
-- cases is the crossing, not the parser, which 'Thena.EarleyTests' already
-- covers on its own small grammars.
source :: String
source =
  unlines
    [ "module Charting where"
    , ""
    , "w : Token String"
    , "w = /[a-z][a-zA-Z0-9']*/"
    , ""
    , "language Ty, T, S where"
    , "  base  -> \953"
    , "  arrow -> ( T -> S )"
    , ""
    , "language LC, M, N, E where"
    , "  var : w as occurrence -> w"
    , "  abs : w as binder     -> ( \955 w : T . E[w] )"
    , "  app                   -> ( M N )"
    ]

loaded :: IO [Grammar]
loaded = do
  (s0, _) <- startingSession
  case loadProofSource s0 source of
    (s1, ProofLoaded {}) -> pure (grammars (machineOf s1))
    (_, other) -> assertFailure (show other) >> pure []

-- ---------------------------------------------------------------------------
-- Is this text one term

parseCases :: [TestTree]
parseCases =
  [ agree "a complete term"
      "( \955 x : \953 . x )"
  , agree "a nested type"
      "( \955 x : ( \953 -> \953 ) . x )"
  , agree "stuck before the closing paren"
      "( \955 x : \953 . x"
  , agree "stuck right after the opening paren"
      "( "
  ]
  where
    agree name text = testCase name $ do
      gs <- loaded
      mismatchParse gs "LC" text

mismatchParse :: [Grammar] -> String -> String -> IO ()
mismatchParse gs lang text
  | shown == drawn = pure ()
  | otherwise = assertFailure ("printed: " <> shown <> "\n  drawn:   " <> drawn)
  where
    shown = case Earley.parse (earleyRules gs) (Earley.StartAt lang) (Earley.pieces text) of
      Left f  -> parseFailureReason text f
      Right t -> renderTree t
    drawn = case displayParse gs lang Nothing [WrittenText text] of
      Left f  -> redrawFailure text f
      Right t -> redrawTree t

-- | What an editor is, for a parse tree: a function from a 'TreeView' to
-- text, and nothing else — mirrors 'Thena.Render.renderTree', the seam under
-- test.
redrawTree :: TreeView -> String
redrawTree t = case t of
  ANode n []  -> n
  ANode n cs  -> n ++ "(" ++ intercalate ", " (map redrawTree cs) ++ ")"
  ATokenView x -> x
  APlaceholderAt _ -> [placeholderChar]
  ASpliceOf k  -> "${" ++ show k ++ "}"

-- | Mirrors 'Thena.Render.parseFailureReason'.
redrawFailure :: String -> FailureView -> String
redrawFailure text f = case f of
  AnAmbiguity a b ->
    "this term parses two ways, as " ++ redrawTree a ++ " and as " ++ redrawTree b
  ADisagreement r x a b ->
    r ++ "'s " ++ x ++ " is written more than once and must read the same each time, "
      ++ "but here it is " ++ redrawTree a ++ " and " ++ redrawTree b
  AnUnboundedRule h ->
    "this term parses without end, because " ++ h ++ " can derive itself from the same text"
  AStuck p expected
    | p >= length text -> "the term ends too soon" ++ expecting expected
    | otherwise ->
        "unexpected " ++ escapeChar (text !! p) ++ " at character " ++ show (p + 1)
          ++ expecting expected
  where
    expecting [] = ""
    expecting ss = ", expecting " ++ oneOf (map redrawSymbolText ss)
    oneOf ws = case reverse ws of
      [w] -> w
      w : rest -> intercalate ", " (reverse rest) ++ " or " ++ w
      [] -> ""

redrawSymbolText :: SymbolView -> String
redrawSymbolText s = case s of
  ALiteralSymbol x -> x
  AScanSymbol n -> n
  ANonterminalSymbol n -> n

-- ---------------------------------------------------------------------------
-- What may stand at the cursor

offerCases :: [TestTree]
offerCases =
  [ agree "after ( \955, the rest of abs is inserted, slots as ?"
      "( \955" ""
  , agree "after ( alone, abs and paren both fit: listed"
      "( " ""
  , agree "a slot of the production under the cursor is offered"
      "( \955 x : " " . x )"
  , agree "the text after the cursor filters the options"
      "( \955 x : \953 . x " ")"
  , -- Phase 120: the rest is fitted to what follows the cursor, and a
    -- position that can have nothing still says what it wants — both of
    -- which the view has to carry, the first as 'offeredRest' and the
    -- second as 'offeredWanted'.
    agree "the rest is cut short by the closer already written"
      "( \955" " )"
  , agree "a contradicted type slot still says it wants a T"
      "( \955 x : " "? . x )"
  ]
  where
    agree name before after = testCase name $ do
      gs <- loaded
      mismatchOffer gs "LC" before after

mismatchOffer :: [Grammar] -> String -> String -> String -> IO ()
mismatchOffer gs lang before after
  | shown == drawn = pure ()
  | otherwise = assertFailure ("tabComplete: " <> show shown <> "\n  drawn:      " <> show drawn)
  where
    shown = tabComplete (earleyRules gs) lang (reverse before, after)
    -- **A region, as of phase 125** — one run of written text on each side, no
    -- splices, which is exactly what a terminal line is. The 'Left' cannot
    -- happen here: every caller names a language the fixture loaded.
    drawn = case displayOffer gs lang Nothing [WrittenText before] [WrittenText after] of
      Right o -> redrawOffer before o
      Left p  -> error ("displayOffer refused the fixture: " <> show p)

-- | 'Thena.Repl.tabComplete's own decision (the @'?'@-adjacent case aside,
-- which is the REPL's own hole spelling and not this phase's concern),
-- replayed over an 'OfferView' rather than a raw 'Earley.Offer'.
redrawOffer :: String -> OfferView -> (String, [(String, String)])
redrawOffer before (OfferView options wanted _ rest _ _ _ stuck) =
  case (rest, options ++ wanted) of
    (Just pfx, _) -> single (unwords (map redrawWritten pfx))
    (_, [s]) | isLiteralView s -> single (redrawWritten s)
    -- MS7 phase 134: the prefix did not read, so there is nothing at the cursor
    -- and the terminal says where the reading gave out instead.
    (_, []) | Just (StuckView at expected) <- stuck ->
      (reverse before, [("", redrawStuck at expected)])
    (_, ss) -> (reverse before, [ ("", redrawSymbolText' s) | s <- ss ])
  where
    single t = (reverse before, [(spaced t, t)])
    spaced t = if null before || isSpace (last before) then t else ' ' : t

redrawStuck :: Int -> [SymbolView] -> String
redrawStuck at expected =
  "stopped at " ++ show at
    ++ (if null expected then "" else ", wanted " ++ unwords (map redrawSymbolText' expected))

isLiteralView :: SymbolView -> Bool
isLiteralView s = case s of
  ALiteralSymbol _ -> True
  _ -> False

redrawWritten :: SymbolView -> String
redrawWritten s = case s of
  ALiteralSymbol t -> t
  _ -> [placeholderChar]

redrawSymbolText' :: SymbolView -> String
redrawSymbolText' s = case s of
  ALiteralSymbol t -> t
  AScanSymbol n -> "\8249" ++ n ++ "\8250"
  ANonterminalSymbol n -> "\8249" ++ n ++ "\8250"

-- ---------------------------------------------------------------------------
-- A region, as an editor holds one
--
-- **Phase 125's own change.** 'displayOffer' took the two sides of the cursor as
-- 'String's until here, so a region with a splice in it could not be asked about
-- at all and a caller that needed one — his own TUI — went to 'Earley.offer'
-- directly and rebuilt the view by hand, the two refusals included. These are
-- the cases that signature makes possible.

regionCases :: [TestTree]
regionCases =
  [ testCase "a language nothing declared is refused, by name" $
      displayOffer [] "LC" Nothing [] [] @?= Left (NoSuchLanguage "LC")
  , testCase "so is a production the language does not have" $ do
      gs <- loaded
      displayOffer gs "LC" (Just "nope") [] [] @?= Left (NoSuchProduction "LC" "nope")
  , testCase "an explicit production starts there instead of at the language" $ do
      gs <- loaded
      -- At @app@ the region must open with @(@; at the language, @\955@ is
      -- reachable too, because @abs@ is a term as well.
      opts <- optionsOf gs "LC" (Just "app") [] []
      whole <- optionsOf gs "LC" Nothing [] []
      assertBool "app offers no more than LC does" (all (`elem` whole) opts)
      assertBool "and LC offers something app does not" (opts /= whole)
  , testCase "a placeholder as a run and as its character are the same thing" $ do
      gs <- loaded
      -- **The invariant phase 127 owes.** A frontend holding positions sends
      -- 'WrittenPlaceholder'; one holding only text puts 'placeholderChar' in.
      -- If those ever stopped agreeing, a region would read differently
      -- depending on which kind of frontend sent it.
      asRun <- optionsOf gs "LC" Nothing [WrittenText "( ", WrittenPlaceholder] []
      asChar <- optionsOf gs "LC" Nothing [WrittenText ("( " <> [placeholderChar])] []
      asRun @?= asChar
  , testCase "and that holds to the right of the cursor, where the flag is read" $ do
      gs <- loaded
      -- **The half the case above did not cover, and it was false.** The
      -- equivalence held on the left because 'piecesFrom' reads the character
      -- as a placeholder either way; on the right it did not, because
      -- 'offerAt' asks about the first /run/ there. So a frontend handing its
      -- line over as one 'WrittenText' was told the cursor was beside the box
      -- rather than in it, and was then answered about what may stand beside a
      -- box — nothing, wherever the production has no room for it.
      let after = " . " <> [placeholderChar] <> " )"
      asRun <- optionsOf gs "LC" Nothing [WrittenText "( \955 x : "] (WrittenPlaceholder : [WrittenText after])
      asChar <- optionsOf gs "LC" Nothing [WrittenText "( \955 x : "] [WrittenText ([placeholderChar] <> after)]
      asRun @?= asChar
      asRunFlag <- replacesAt gs [WrittenText "( \955 x : "] (WrittenPlaceholder : [WrittenText after])
      asCharFlag <- replacesAt gs [WrittenText "( \955 x : "] [WrittenText ([placeholderChar] <> after)]
      (asRunFlag, asCharFlag) @?= (True, True)
  , testCase "standing in the box, the offer says it replaces it" $ do
      gs <- loaded
      -- The cursor is in the box when the box is the first thing to its right.
      -- Phase 127: this is the case @tabComplete@ cannot express, because
      -- haskeline can only rewrite to the left of the cursor.
      inBox <- replacesAt gs [WrittenText "( "] [WrittenPlaceholder, WrittenText " )"]
      beside <- replacesAt gs [WrittenText "( "] [WrittenText " )"]
      (inBox, beside) @?= (True, False)
  , testCase "and what it offers there is what may stand in the box" $ do
      gs <- loaded
      -- Computed as though the placeholder were not there, so the box does not
      -- count as text already written.
      inBox <- optionsOf gs "LC" Nothing [WrittenText "( "] [WrittenPlaceholder, WrittenText " )"]
      without <- optionsOf gs "LC" Nothing [WrittenText "( "] [WrittenText " )"]
      inBox @?= without
  , testCase "and a splice stands where a placeholder does" $ do
      gs <- loaded
      -- A splice fills a slot exactly as a placeholder does, so what may follow
      -- it is what may follow a filled slot.
      spliced <- optionsOf gs "LC" Nothing [WrittenText "( ", WrittenSplice] []
      held <- optionsOf gs "LC" Nothing [WrittenText "( ", WrittenPlaceholder] []
      spliced @?= held
  , testCase "the splices of a region are numbered in order, from zero" $ do
      gs <- loaded
      -- **The numbering is only visible in a tree**, which is why this case
      -- reads rather than offers: an 'Earley.Offer' carries symbols, so a
      -- region numbered wrongly offers exactly what a region numbered rightly
      -- does. 'displayOffer' splits its region at the cursor and numbers the
      -- two halves as one; nothing about that is checkable there, and here it
      -- is.
      displayParse gs "LC" Nothing [WrittenText "( ", WrittenSplice, WrittenText " ", WrittenSplice, WrittenText " )"]
        @?= Right (ANode "app" [ASpliceOf 0, ASpliceOf 1])
  , testCase "and a written term beside a splice does not take a number" $ do
      gs <- loaded
      displayParse gs "LC" Nothing [WrittenText "( x ", WrittenSplice, WrittenText " )"]
        @?= Right (ANode "app" [ANode "var" [ATokenView "x"], ASpliceOf 0])
  , testCase "an explicit production reads at that production" $ do
      gs <- loaded
      -- @T@ is @Ty@'s own nonterminal, so @\953@ reads there and not at @LC@.
      displayParse gs "Ty" (Just "base") [WrittenText "\953"] @?= Right (ANode "base" [])
  ]

replacesAt :: [Grammar] -> [Written] -> [Written] -> IO Bool
replacesAt gs before after = case displayOffer gs "LC" Nothing before after of
  Left p  -> assertFailure ("displayOffer refused a fixture: " <> show p) >> pure False
  Right o -> pure (offeredReplaces o)

optionsOf :: [Grammar] -> String -> Maybe String -> [Written] -> [Written] -> IO [String]
optionsOf gs lang prod before after = case displayOffer gs lang prod before after of
  Left p  -> assertFailure ("displayOffer refused a fixture: " <> show p) >> pure []
  Right o -> pure (map redrawSymbolText (offeredOptions o ++ offeredWanted o))

-- ---------------------------------------------------------------------------
-- The productions offered whole
--
-- **His request of 2026-09-28**, and one of the features he named as mattering
-- most: the dropdown should list the productions that may stand here, with their
-- shapes, and inserting one should put its skeleton in the buffer with the parts
-- you still have to write left as boxes.
--
-- **The chart had this all along.** What these cases pin down is that the view
-- now carries it, that the label and the insertion are the same body rendered
-- two ways, and that a production which could not leave the line finishable is
-- not offered.

productionCases :: [TestTree]
productionCases =
  [ testCase "at the start of an LC, every LC production is offered" $ do
      gs <- loaded
      -- Declaration order, which is the order the author reads their own file
      -- in. This fixture's LC has exactly these three.
      named gs [] [] >>= (@?= ["var", "abs", "app"])
  , testCase "with their shapes, which is what a list shows" $ do
      gs <- loaded
      shapeOf gs [] [] "app" >>= (@?= Just ["(", "LC", "LC", ")"])
  , -- **His own example, exactly.** @app: ( LC LC )@ in the list, @( █ █ )@ in
    -- the buffer — and the boxes arrive as runs, so the editor knows where they
    -- are without scanning the text it just inserted.
    testCase "and inserting one writes its terminals and leaves boxes" $ do
      gs <- loaded
      insertOf gs [] [] "app"
        >>= (@?= Just
              [ WrittenText "( "
              , WrittenPlaceholder
              , WrittenText " "
              , WrittenPlaceholder
              , WrittenText " )"
              ])
  , testCase "a binding form's binder is a box too, being a slot" $ do
      gs <- loaded
      -- @abs@ is @( λ x : T . E[x] )@: three slots, one of them a token class.
      insertOf gs [] [] "abs"
        >>= (@?= Just
              [ WrittenText "( λ "
              , WrittenPlaceholder
              , WrittenText " : "
              , WrittenPlaceholder
              , WrittenText " . "
              , WrittenPlaceholder
              , WrittenText " )"
              ])
  , -- **The filter earns its place, and this is the case that shows it.**
    -- Inside a paren that is already closed, @var@ is dropped while @abs@ and
    -- @app@ survive: this fixture's grammar has no parenthesis production, so
    -- @( w )@ can never be finished, and the two that open with a @(@ of their
    -- own can.
    testCase "a production that could not be finished here is not offered" $ do
      gs <- loaded
      named gs [WrittenText "( "] [WrittenText " )"] >>= (@?= ["abs", "app"])
  , -- **The crossing, and it is the assertion worth having here.** A production
    -- may begin at the cursor only if its opening symbol may be written there,
    -- so every offered production's first symbol has to be among the options the
    -- same offer gives. The converse does not hold — an option may continue a
    -- production already open rather than start one — and that is exactly why
    -- this field is not derivable from 'offeredOptions'.
    testCase "every offered production opens with something the offer allows" $ do
      gs <- loaded
      let opening p = case productionShape p of
            s : _ -> redrawSymbolText s
            []    -> ""
          at (before, after) = do
            ps <- offered gs before after
            os <- optionsOf gs "LC" Nothing before after
            pure [ (productionName p, opening p) | p <- ps, opening p `notElem` os ]
      bad <- concat <$> mapM at
        [ ([], [])
        , ([WrittenText "( "], [WrittenText " )"])
        , ([WrittenText "( λ x : "], [WrittenText " . x )"])
        , ([WrittenText "( "], [])
        ]
      bad @?= []
  , testCase "and inside a Ty slot it is Ty's productions, not LC's" $ do
      gs <- loaded
      named gs [WrittenText "( λ x : "] [WrittenText " . x )"] >>= (@?= ["base", "arrow"])
  ]
  where
    offered gs before after = case displayOffer gs "LC" Nothing before after of
      Left p  -> assertFailure ("displayOffer refused a fixture: " <> show p) >> pure []
      Right o -> pure (offeredProductions o)
    named gs before after = map productionName <$> offered gs before after
    one gs before after n =
      (\ps -> listToMaybe [ p | p <- ps, productionName p == n ]) <$> offered gs before after
    shapeOf gs before after n = fmap (map redrawSymbolText . productionShape) <$> one gs before after n
    insertOf gs before after n = fmap productionInsert <$> one gs before after n
