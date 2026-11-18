-- | What a term reads as once it is drawn.
--
-- **Every test here is a 'Display' built by hand, drawn, and compared against
-- one line of screen text.** Nothing mocks a terminal: 'Brick.Main.renderWidget'
-- is pure, and 'Graphics.Vty.PictureToSpans.displayOpsForPic' turns the picture
-- it returns into spans whose text is the characters that would have been
-- written. So this is the real drawing path and not a policy function standing
-- in for it — which matters, because `~r3fp9` was not a wrong policy, it was a
-- right policy consulted at the wrong call site.
module DrawingTests (drawingTests) where

import Data.List (dropWhileEnd)
import qualified Data.Text.Lazy as TL
import Data.Char (isSpace)
import qualified Data.Vector as V

import Brick (Widget)
import Brick.AttrMap (AttrMap, attrMap)
import Brick.Main (renderWidget)
import qualified Graphics.Vty as Vty
import Graphics.Vty.PictureToSpans (displayOpsForPic)
import Graphics.Vty.Span (SpanOp (..))

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

import Thena.View.Address (Address (..), Move (GoAlong))
import Thena.View.Core (Binding (..), Display (..), ObjectItem (..), Shape (..))
import Thena.View.Instral (ValueView (..))
import Thena.View.Machine (MachineView (..))
import Tui.Panes
  ( FileKind (..)
  , ModuleEntry (..)
  , ModuleMark (..)
  , PaneRow (..)
  , foldMark
  , globalRows
  , markColumns
  , markGlyph
  , moduleRows
  , outputRows
  , paneBarWidget
  , paneRowWidget
  )
import Tui.Render (Fold (..), foldAttr, renderDisplay, renderMachineView)


-- * Drawing a widget without a terminal

-- | The region every test draws into. Wide enough that nothing here wraps —
-- a wrapped line would make the comparison about layout, which is the pty's
-- question and not this suite's.
region :: (Int, Int)
region = (200, 4)

-- | A widget's first line, as the characters that would reach the screen.
--
-- 'renderWidget' wants an 'Brick.AttrMap.AttrMap' only to resolve attribute
-- names; an empty one is enough, because nothing here asserts a colour.
drawLine :: Widget () -> String
drawLine w =
  case drawToLines w of
    (l : _) -> l
    []      -> ""

-- | Every line of it, trailing blanks trimmed.
drawToLines :: Widget () -> [String]
drawToLines = drawToLinesIn region

-- | The same, into a region of a stated size. **Narrow regions are the point
-- of it**: a pane is a quarter of the screen and a term is longer than that,
-- so where the drawing breaks a line is only decidable against a width.
drawToLinesIn :: (Int, Int) -> Widget () -> [String]
drawToLinesIn size w = map (trimEnd . concatMap fst) (drawToSpansIn (attrMap Vty.defAttr []) size w)
  where
    trimEnd = dropWhileEnd isSpace

-- | Every line as its spans, each with the attribute it would be written in.
-- **The attribute is the half a string cannot carry**, and it is the reason
-- 'Tui.Render' builds pieces rather than text: a folded literal is coloured
-- over exactly its own span, so a break inside one has to leave both halves
-- still coloured.
drawToSpansIn :: AttrMap -> (Int, Int) -> Widget () -> [[(String, Vty.Attr)]]
drawToSpansIn am size w =
  map (concatMap opSpans . V.toList) (V.toList (displayOpsForPic picture size))
  where
    picture = renderWidget (Just am) [w] size

    opSpans op = case op of
      TextSpan a _ _ t -> [(TL.unpack t, a)]
      Skip n           -> [(replicate n ' ', Vty.defAttr)]
      RowEnd n         -> [(replicate n ' ', Vty.defAttr)]


-- * Terms, built by hand

-- | Nothing in this suite asserts anything about addresses, so they are all
-- the root. The fold is off for the same reason — 'NoFold' draws everything
-- expanded, which is the case a bracket question is about.
at :: Shape -> Display
at = Display (Address [])

draw :: Shape -> String
draw = drawLine . renderDisplay NoFold . at

var :: String -> Display
var name = at (AVariable name Nothing)

global :: String -> Display
global name = at (AGlobal name [])

-- | @\\x : A . x@
lam :: Display
lam = at (AnAbstraction (Binding "x" (global "A")) (var "x"))

-- | @(y : A) -> B@
pity :: Display
pity = at (AFunction (Binding "y" (global "A")) (global "B"))

-- | @z = v : A . z@
lett :: Display
lett = at (ALet (Binding "z" (global "A")) (global "v") (var "z"))

-- | @cons n a as@ — a saturated former.
former :: Display
former = at (AFormer "cons" [] [var "n", var "a", var "as"])

-- | @elim Nat () P (step) () tgt@.
--
-- **'eliminatorName' is the datatype alone** — 'Thena.View.Core' builds it from
-- the bare 'Thena.Core.Term.GlobalName', so the word @elim@ is the drawer's to
-- write. An earlier version of this fixture spelled the name @"elim Nat"@ and
-- so proved the brackets while hiding the missing head (`~9wcpr`).
elimination :: Display
elimination =
  at
    AnElimination
      { eliminatorName = "Nat"
      , eliminatorLevels = []
      , eliminatorParameters = []
      , eliminatorMotive = global "P"
      , eliminatorMethods = [global "step"]
      , eliminatorIndices = []
      , eliminatorTarget = var "tgt"
      }

-- | @trusted T U e@
trusted :: Display
trusted = at (ATrusted (global "T") (global "U") (global "e"))

app :: Display -> Display -> Shape
app = AnApplication


-- * The tests

drawingTests :: TestTree
drawingTests =
  testGroup
    "drawing"
    [ testGroup "an argument is bracketed when it extends to the right" argumentCases
    , testGroup "so is a function position, which is `~r3fp9`" functionCases
    , testGroup "and a spine head is not" spineCases
    , testGroup "the engine's own lines, drawn" engineCases
    , testGroup "a value in an env pane" valueCases
    , testGroup "the second column's rows, decided" paneRowCases
    , testGroup "and drawn" paneDrawCases
    , testGroup "a term too wide for its pane breaks rather than clipping" wrapCases
    , testGroup "a production's words and slots are spaced, which is `~mxhfj`" spacingCases
    , testGroup "the bar that names every pane, `~7tfhd`" paneBarCases
    ]

-- | **`~7tfhd`, his instruction of 2026-11-13**: /"lists all the available
-- panes … opened ones are rendered a bit differently to closed ones, and they
-- show the position they are rendered at (the number)."/
--
-- **Each item is a filled chip as of his instruction of the same day**: /"Each
-- 'item' in the bar should be visually its own thing. I am proposing a pink
-- accent background around the text … and between the items there is the black
-- background space."/ So a chip is padded one column either side **inside** its
-- own background, and two unstyled columns separate one from the next — which
-- is why every expected string here is spaced the way it is.
--
-- **The colours are the other half and are not asserted here**, this suite's
-- rule being that nothing in it asserts one; the contrast figures are in
-- 'Tui.App''s attribute table and the fills were read off the pty.
paneBarCases :: [TestTree]
paneBarCases =
  [ testCase "an open pane carries its number and a closed one carries none" $
      assertEqual ""
        " globals 1    proofterm 2    proofs"
        (drawLine (paneBarWidget
                    [("globals", Just 1), ("proofterm", Just 2), ("proofs", Nothing)]))
  , -- The default screen, which is what he sees before he types anything.
    testCase "the default screen reads as the sketch he picked" $
      assertEqual ""
        " globals 1    proofterm 2    modules 3    goals 4    output 5    machine 6    proofs"
        (drawLine (paneBarWidget
                    [ ("globals", Just 1), ("proofterm", Just 2), ("modules", Just 3)
                    , ("goals", Just 4), ("output", Just 5), ("machine", Just 6)
                    , ("proofs", Nothing)
                    ]))
  , -- | **The case his own ruling made reachable** — every pane closed, so the
    -- bar is the only thing on screen that says a pane exists at all.
    testCase "a screen with no panes still names them, with no numbers" $
      assertEqual ""
        " globals    modules    output"
        (drawLine (paneBarWidget
                    [("globals", Nothing), ("modules", Nothing), ("output", Nothing)]))
  ]

-- | **HIS REPORT, 2026-11-12, and the suite could not have caught it** —
-- `~mxhfj`: /"The TUI renders the tagget term literals weird. There are no
-- spaces between the identifiers. Instead of @n value@ it's @nvalue@ and the
-- same is for lambda expressions like: @((λx.m)n)-->m[x->n]@."/
--
-- **Every object-term case in this suite before these had exactly one item**,
-- so there was no pair for a missing separator to fall between. That is why a
-- defect this visible survived a passing suite, and it is the reason these
-- cases are shaped as whole productions rather than as one slot.
--
-- **The expected strings are the prompt's, not taste.**
-- 'Thena.Language.Build.laid' joins a production's items with
-- @intercalate [Written " "] css@ over the same one-entry-per-grammar-item
-- list 'Thena.View.Core.objectItems' builds, so one space between consecutive
-- items is the engine's own rule and these pin the TUI to it.
spacingCases :: [TestTree]
spacingCases =
  [ -- His own first example. The @value@ judgment's production is @M value@ —
    -- one slot, one terminal — and it used to draw as @value`${n}value`@.
    testCase "a slot and a terminal are not run together" $
      assertEqual ""
        "value`${n} value`"
        (draw (AnObjectTerm "value" "V-num" [ObjectChild True (var "n"), ObjectText "value"]))
  , -- His second. Terminals and slots alternating, which is the shape every
    -- production in his demo's @step@ judgment has: @abs@ is
    -- @( λ x . E[x] )@, a binder slot in a token class and a nonterminal
    -- slot between four terminals.
    testCase "a production of alternating terminals and slots reads as written" $
      assertEqual ""
        "LC`( λ x . E )`"
        (draw (AnObjectTerm "LC" "abs"
                [ ObjectText "("
                , ObjectText "λ"
                , ObjectToken (at (AToken "x"))
                , ObjectText "."
                , ObjectChild False (var "E")
                , ObjectText ")"
                ]))
  , -- **An inline child is one item of its parent and spaced as one**, while
    -- its own items are spaced one level down — which is how 'laid' recurses.
    -- A child that lost its own spacing, or gained a space against its
    -- neighbours, would both show here.
    testCase "a nested production is spaced inside and spaced as one item" $
      assertEqual ""
        "LC`( λ x . x ) n`"
        (draw (AnObjectTerm "LC" "app"
                [ ObjectChild False
                    (at (AnObjectTerm "LC" "abs"
                          [ ObjectText "("
                          , ObjectText "λ"
                          , ObjectToken (at (AToken "x"))
                          , ObjectText "."
                          , ObjectChild False (var "x")
                          , ObjectText ")"
                          ]))
                , ObjectToken (at (AToken "n"))
                ]))
  , -- **A splice keeps its @${...}@ fences and is still one item.** His own
    -- report's spelling is a spliced variable, so this is the case that says
    -- the fences and the new space do not fight.
    testCase "a splice is fenced and spaced as one item" $
      assertEqual ""
        "step`${m} --> ${n}`"
        (draw (AnObjectTerm "step" "E-beta"
                [ ObjectChild True (var "m")
                , ObjectText "-->"
                , ObjectChild True (var "n")
                ]))
  , -- A one-item production has no pair to separate, so it must not gain a
    -- leading or trailing space. This is the shape every case in this suite
    -- had before `~mxhfj`, which is why it is worth pinning.
    testCase "a production of one item gains no space" $
      assertEqual ""
        "LC`x`"
        (draw (AnObjectTerm "LC" "var" [ObjectText "x"]))
  ]

-- | **His report, 2026-11-12**: /"Make sure that each smaller pane correctly
-- 'line-breaks'. Specifically the 'output' is clipping horizontally. Not
-- great, I can't read the message."/ The panes are a quarter of the screen,
-- a core term is longer than that, and what ran past the edge used to be
-- simply not drawn.
--
-- **This is the suite's own remit and not the pty's**: where a line breaks at
-- a given width is a function of the text, decidable with no terminal. How
-- wide a pane actually is stays the pty's question.
wrapCases :: [TestTree]
wrapCases =
  [ testCase "it breaks at a space, and the continuation is indented two" $
      assertEqual ""
        ["Eq {0} Nat", "  zero zero"]
        (wrapAt 12 eqNatZeroZero)
  , -- **The case that replaced the first implementation.** Pieces are emitted
    -- one per drawer step, so @"(snd A B s)"@ and the @")"@ closing the term
    -- around it are two of them with no space between — and a layout that
    -- broke between any two pieces put that @")"@ alone at the head of a
    -- line. A break may fall at whitespace and nowhere else.
    testCase "a bracket with no space before it stays with what it closes" $
      assertEqual ""
        ["f (cons n a", "  as)"]
        (wrapAt 12 (at (app (global "f") former)))
  , -- A name, a path and a level-decorated global are each one word, and are
    -- routinely longer than a pane. Refusing to cut them would be the clip
    -- this is here to replace.
    testCase "a word longer than the pane is cut, not dropped" $
      assertEqual ""
        ["Averyver", "  ylongn", "  ame"]
        (wrapAt 8 (global "Averyverylongname"))
  , -- The whole reason 'Tui.Render' works in pieces rather than in text.
    testCase "a folded literal is still coloured on both sides of a break" $
      assertEqual "" [True, True] (foldedSpanPerLine 14 foldedLiteral)
  ]

-- | A display's lines at a stated width, the fold off and the blank rows
-- below it dropped — the region has to be taller than the text to prove
-- nothing was lost off the bottom, which leaves empty rows to trim.
wrapAt :: Int -> Display -> [String]
wrapAt w = dropWhileEnd null . drawToLinesIn (w, 8) . renderDisplay NoFold

-- | For each drawn line that has any text on it, whether some span of it
-- carries the fold's own background. **Red, because the suite's own attribute
-- map is otherwise empty** — an unmapped name resolves to the default attr,
-- so a fold drawn through an empty map would be indistinguishable from
-- ordinary text and the test would pass without proving anything.
foldedSpanPerLine :: Int -> Display -> [Bool]
foldedSpanPerLine w d =
  [ any ((== Vty.SetTo Vty.red) . Vty.attrBackColor . snd) spans
  | spans <- drawToSpansIn folded (w, 8) (renderDisplay (Fold (Address [])) d)
  , any (not . all isSpace . fst) spans
  ]
  where
    folded = attrMap Vty.defAttr [(foldAttr, Vty.withBackColor Vty.defAttr Vty.red)]

-- | A tagged literal whose own address is not a prefix of the focus, so the
-- fold applies — @surface`one two three four`@, long enough to break at 14.
foldedLiteral :: Display
foldedLiteral =
  Display (Address [GoAlong]) $
    ARegion
      (Display (Address [GoAlong]) (AnObjectTerm "surface" "app" [ObjectText "one two three four"]))

-- | **What the three new panes say** — `~z5dmq`'s content, decided by
-- 'Tui.Panes' and therefore decidable here. The pty stays the authority on
-- where the panes are and how wide; this is the text in them.
-- | **Pins the row type where a row has no click name to infer one from.**
-- 'outputRows' is polymorphic in what a 'Tui.Panes.Tap' would be named by, and
-- never builds one, so an expected list of its rows has nothing to fix the
-- variable. **'globalRows' is no longer one of those** — `~6n5qb` made every
-- namespace heading a 'Tui.Panes.TapHeading' named by its label.
asRows :: [PaneRow String] -> [PaneRow String]
asRows = id

-- | An open namespace heading, as `~6n5qb` draws one — the label is the click
-- name, the text carries the symbol.
openGroup :: String -> Int -> PaneRow String
openGroup label n = TapHeading label (foldMark True <> " " <> label) (Just n)

-- | A module that came in whole, with the file it was read from — `~nf5tx`.
--
-- **At the root of the import tree**, depth 0; 'nested' is the one below.
whole :: String -> Maybe FilePath -> ModuleEntry
whole n f = ModuleEntry n f AllIn False [] 0

-- | One that came in partly, folded, with nothing recorded against it yet.
partial :: String -> ModuleEntry
partial n = ModuleEntry n Nothing SomeIn False [] 0

-- | The same module one step further down the import tree — `~84j24`.
nested :: Int -> ModuleEntry -> ModuleEntry
nested d me = me { meDepth = d }

paneRowCases :: [TestTree]
paneRowCases =
  [ testCase "an empty group is not drawn as a heading with nothing under it" $
      assertEqual ""
        (asRows [openGroup "Prelude" 2, Entry "And.both", Entry "Eq.refl"])
        (globalRows [] [("proved in this session", []), ("Prelude", ["Eq.refl", "And.both"])])
  , testCase "a name listed twice is listed once — a suspended proof is two runs" $
      assertEqual ""
        (asRows [openGroup "proved in this session" 1, Entry "subst"])
        (globalRows [] [("proved in this session", ["subst", "subst"])])
  , -- | **`~6n5qb`, his instruction of 2026-11-12.** The pane as it was before
    -- anyone clicked: nothing collapsed, so every group's names are drawn, and
    -- a heading is a click target whether it is open or shut.
    testCase "a collapsed namespace keeps its heading and its count, and drops its names" $
      assertEqual ""
        [ TapHeading "Prelude" "\x25b8 Prelude" (Just 2)
        , openGroup "examples.Lambda" 1
        , Entry "step.E-beta"
        ]
        (globalRows ["Prelude"]
          [ ("Prelude", ["Eq.refl", "And.both"])
          , ("examples.Lambda", ["step.E-beta"])
          ])
  , testCase "the symbol pair says which state a namespace is in, and only that" $
      assertEqual "" ("\x25be", "\x25b8") (foldMark True, foldMark False)
  , -- | **A label that is collapsed and no longer on screen changes nothing** —
    -- nothing prunes 'Tui.App.stGlobalsClosed', so the set outlives the group.
    testCase "a collapsed label for a group that is gone is ignored" $
      assertEqual ""
        (asRows [openGroup "Prelude" 1, Entry "Eq.refl"])
        (globalRows ["examples.Gone"] [("Prelude", ["Eq.refl"])])
  , -- | **Collapsing every group leaves the headings and nothing else**, which
    -- is his reason for asking: eight module groups fit where one module's
    -- thirty names did not.
    testCase "every namespace collapsed leaves one row each" $
      assertEqual ""
        [ TapHeading "a" "\x25b8 a" (Just 2)
        , TapHeading "b" "\x25b8 b" (Just 1)
        ]
        (globalRows ["a", "b"] [("a", ["a.one", "a.two"]), ("b", ["b.one"])])
  , testCase "a module carries its file, and the prelude has none" $
      assertEqual ""
        [ Heading "modules" (Just 2)
        , Entry "\x2705 examples.Stlc01Syntax"
        , Detail "examples/Stlc01Syntax.thena"
        , Entry "\x2705 Prelude"
        ]
        (moduleRows
          [ whole "examples.Stlc01Syntax" (Just "examples/Stlc01Syntax.thena")
          , whole "Prelude" Nothing
          ]
          [])
  , testCase "a consulted rule base is its own group, and ours is shown by its tail" $
      assertEqual ""
        [ Heading "rule bases" (Just 1)
        , Entry "examples/demo/Demo08Pausing.thena.rules"
        , Heading "shipped with thena" (Just 1)
        , Entry "rules/standard.thena.rules"
        ]
        (moduleRows []
          [ (ARuleBase, "examples/demo/Demo08Pausing.thena.rules")
          , (AShippedFile, "/Users/x/.cabal/share/aarch64-osx-ghc-9.12.4/thena-0.1.0.0/rules/standard.thena.rules")
          ])
  , testCase "a module's own file is not repeated outside its module" $
      assertEqual ""
        [Heading "modules" (Just 1), Entry "\x2705 m", Detail "m.thena"]
        (moduleRows [whole "m" (Just "m.thena")] [(AModuleFile, "m.thena")])
  , -- | **`~nf5tx`, his instruction of 2026-11-13.** A whole module is a plain
    -- entry; a module that came in partly is a 'Tap', because only it has
    -- something to unfold and a row that looks clickable and does nothing is
    -- worse than one that does not look it.
    testCase "only a module with something to unfold is clickable" $
      assertEqual ""
        [ Heading "modules" (Just 3)
        , Entry "\x2705 whole"
        , Tap "some" "\x26A0\xFE0F some"
        , Tap "none" "\x274C none"
        ]
        (moduleRows
          [ whole "whole" Nothing
          , (partial "some") { meUnfinished = [("b", ["why"])] }
          , (partial "none") { meMark = NoneIn, meUnfinished = [("b", ["why"])] }
          ]
          [])
  , -- | **The three marks, spelled out, and the spelling is the decision** —
    -- `~nf5tx`. ⚠ carries U+FE0F, the variation selector, because that is what
    -- asks for the coloured presentation: his instruction, /"I like the colored
    -- version. The glyph version is not visible enough."/
    testCase "the warning mark is the coloured spelling, selector and all" $
      assertEqual ""
        ["\x2705", "\x26A0\xFE0F", "\x274C"]
        (map markGlyph [AllIn, SomeIn, NoneIn])
  , -- | **The one his report of 2026-11-13 turned into a test**: /"the new
    -- symbol for ✅ next to the prelude moves the accent bar of the next pane
    -- to the right."/ vty budgets cells by width, so a mark it reads as one
    -- column where the terminal spends two shoves the rest of the row along and
    -- the row runs past its pane into the next one's bar. Every mark measuring
    -- two is what keeps it inside.
    --
    -- **'markColumns' and not 'safeWcwidth' on the glyphs**, because the latter
    -- answers for a vty with no table installed and would report one — the state
    -- no running TUI is in, 'Tui.App.declareWideGlyphs' having declared
    -- 'wideGlyphs' before it made a vty.
    testCase "every mark is two columns, so no row overruns its pane" $
      assertEqual "" [2, 2, 2] (map markColumns [AllIn, SomeIn, NoneIn])
  , -- | The engine's ruling of 2026-11-11, /"one failure and forty-seven
    -- pending, not forty-eight warnings"/: the first is the root and carries
    -- its reason, the rest are named and nothing is said about why — because
    -- nothing worked out why.
    testCase "unfolded, the first says why and the rest are only named" $
      assertEqual ""
        [ Heading "modules" (Just 1)
        , Tap "m" "\x26A0\xFE0F m"
        , Detail "broken did not go in:"
        , Detail "  stuck: not in scope: nonesuch"
        , Detail "after is pending"
        , Detail "last is pending"
        ]
        (moduleRows
          [ (partial "m")
              { meOpen = True
              , meUnfinished =
                  [ ("broken", ["stuck: not in scope: nonesuch"])
                  , ("after", ["never asked"])
                  , ("last", [])
                  ]
              }
          ]
          [])
  , -- | **`~84j24`, his request of 2026-11-11** — the pane is the import tree,
    -- /"rendered as the dependency tree and not a flat list"/, because
    -- leniency reaches all the way down and /"the module you typed may be ✅
    -- while something three levels beneath it is ⚠️"/. A child is indented two
    -- columns per step, **and the indent is in the row's own text** so that
    -- 'Tui.Panes.paneWrap' keeps a wrapped module path under its own step.
    testCase "a module's imports are indented two columns per step" $
      assertEqual ""
        [ Heading "modules" (Just 3)
        , Entry "\x2705 top"
        , Detail "top.thena"
        , Entry "  \x2705 middle"
        , Detail "  middle.thena"
        , Entry "    \x2705 bottom"
        ]
        (moduleRows
          [ whole "top" (Just "top.thena")
          , nested 1 (whole "middle" (Just "middle.thena"))
          , nested 2 (whole "bottom" Nothing)
          ]
          [])
  , -- | **HIS RULING OF 2026-11-18, and the two cheaper renderings it turned
    -- down.** A module two others import is a row under each of them, drawn
    -- the same both times: /"my reason for the pane was to see the dependency
    -- structure. That means only (a) is acceptable."/ The alternatives were a
    -- repeat reduced to a back-reference and each module drawn once, and the
    -- measurement put to him was that importing
    -- @examples.poplmark.Fsub06Transitivity@ is 6 distinct modules and 32 rows
    -- when every path is drawn, against 16 and 6. **So no row of this pane is
    -- a first-occurrence special case** — a repeat carries its mark, its file
    -- and its unfold like any other row.
    testCase "a module two others import is drawn under each, identically" $
      assertEqual ""
        [ Heading "modules" (Just 4)
        , Entry "\x2705 root"
        , Entry "  \x2705 left"
        , Entry "    \x2705 shared"
        , Detail "    shared.thena"
        , Entry "  \x2705 right"
        , Entry "    \x2705 shared"
        , Detail "    shared.thena"
        ]
        (moduleRows
          [ whole "root" Nothing
          , nested 1 (whole "left" Nothing)
          , nested 2 (whole "shared" (Just "shared.thena"))
          , nested 1 (whole "right" Nothing)
          , nested 2 (whole "shared" (Just "shared.thena"))
          ]
          [])
  , -- | **The count is what is loaded, not how many rows it took** — `~84j24`.
    -- A module imported by three others is three rows and one module, and the
    -- heading answers /what is in/.
    testCase "the heading counts distinct modules and not rows" $
      assertEqual ""
        [ Heading "modules" (Just 2)
        , Entry "\x2705 root"
        , Entry "  \x2705 shared"
        , Entry "  \x2705 shared"
        ]
        (moduleRows
          [ whole "root" Nothing
          , nested 1 (whole "shared" Nothing)
          , nested 1 (whole "shared" Nothing)
          ]
          [])
  , -- | **A deep ⚠️ is the whole motive for the tree** — `~84j24`, his own
    -- case: the module he typed is ✅ and something three levels beneath it is
    -- not. What it unfolds keeps the row's indent, so the small print stays
    -- under the module it is about rather than reading as the root's.
    testCase "a nested module's unfolded reasons keep its indent" $
      assertEqual ""
        [ Heading "modules" (Just 2)
        , Entry "\x2705 top"
        , Tap "deep" "    \x26A0\xFE0F deep"
        , Detail "    broken did not go in:"
        , Detail "      stuck: not in scope: nonesuch"
        , Detail "    after is pending"
        ]
        (moduleRows
          [ whole "top" Nothing
          , nested 2 (partial "deep")
              { meOpen = True
              , meUnfinished =
                  [ ("broken", ["stuck: not in scope: nonesuch"])
                  , ("after", ["never asked"])
                  ]
              }
          ]
          [])
  , testCase "folded, a module is its row and its file and nothing else" $
      assertEqual ""
        [Heading "modules" (Just 1), Tap "m" "\x26A0\xFE0F m", Detail "m.thena"]
        (moduleRows
          [ (partial "m")
              { meFile = Just "m.thena"
              , meUnfinished = [("broken", ["stuck"])]
              }
          ]
          [])
  , testCase "no line in focus is no rows at all" $
      assertEqual "" (asRows []) (outputRows Nothing ["something"])
  , testCase "a line that answered nothing is its heading and nothing else" $
      assertEqual "" (asRows [Heading ":theorem t : Nat" Nothing]) (outputRows (Just ":theorem t : Nat") [])
  , testCase "and nothing is capped, which is the point of the move off the foot" $
      assertEqual "" 21
        (length (outputRows (Just ":show subst") [show n | n <- [1 .. 20 :: Int]]))
  ]

-- | The three row kinds, drawn. **The indents are the structure**, so they
-- are worth a test: a detail that lined up with an entry would read as a
-- second entry.
paneDrawCases :: [TestTree]
paneDrawCases =
  [ testCase "a heading carries its count" $
      assertEqual "" "Prelude  115" (drawLine (paneRowWidget (Heading "Prelude" (Just 115))))
  , testCase "a heading with nothing to count carries no number" $
      assertEqual "" ":show o" (drawLine (paneRowWidget (Heading ":show o" Nothing)))
  , testCase "an entry is one step in" $
      assertEqual "" "  And.both" (drawLine (paneRowWidget (Entry "And.both")))
  , testCase "a detail is two" $
      assertEqual "" "    examples/Stlc01Syntax.thena"
        (drawLine (paneRowWidget (Detail "examples/Stlc01Syntax.thena")))
  ]

-- | The argument side is the rung every drawer gets right, so these are the
-- control: if one of them fails the ladder is upside down.
argumentCases :: [TestTree]
argumentCases =
  [ eq "a lambda" "f (\\x : A . x)" (app (global "f") lam)
  , eq "a function type" "f ((y : A) -> B)" (app (global "f") pity)
  , eq "a let" "f (z = v : A . z)" (app (global "f") lett)
  , eq "a saturated former" "f (cons n a as)" (app (global "f") former)
  , eq "an elimination" "f (elim Nat () P (step) () tgt)" (app (global "f") elimination)
  , eq "a trusted term" "f (trusted T U e)" (app (global "f") trusted)
  ]

-- | **`~r3fp9` itself.** The function side was drawn with no brackets at any
-- shape, so an elimination standing here came out as @elim Nat P step tgt a@ —
-- and the core grammar refuses that outright, because an elimination's last
-- slot is its target, written bare, so it swallows the argument after it.
--
-- A lambda, a function type and a let are the same failure one rung down: each
-- extends to the right and so eats what follows it.
functionCases :: [TestTree]
functionCases =
  [ eq "an elimination" "(elim Nat () P (step) () tgt) a" (app elimination (var "a"))
  , eq "a lambda" "(\\x : A . x) a" (app lam (var "a"))
  , eq "a function type" "((y : A) -> B) a" (app pity (var "a"))
  , eq "a let" "(z = v : A . z) a" (app lett (var "a"))
  ]

-- | Application is left associative and a former application is a spine, so
-- neither needs brackets on a function side. **A trusted term does not either**
-- — 'Thena.Render' brackets it at the argument rung only, and this suite
-- follows that printer rather than guessing.
spineCases :: [TestTree]
spineCases =
  [ eq "an application" "f a b" (app (at (app (global "f") (var "a"))) (var "b"))
  , eq "a saturated former" "cons n a as b" (app former (var "b"))
  , eq "a trusted term" "trusted T U e a" (app trusted (var "a"))
  , eq "an unsaturated former" "nil" (AFormer "nil" [] [])
  ]

-- | **Two drawers, one reading — his ruling, 2026-10-20:** /"We print exactly
-- what engine gives us… TUI literally follows what engine gives and doesn't
-- invent lies in the frontend layer."/
--
-- **Each expected string below is a real line of engine output**, lifted from
-- `test\/golden` and not composed here, with only the two differences the
-- drawers are allowed: a λ is drawn @\\x : A . b@ rather than
-- @λ (x : A) -> b@, and a level atom that the terminal writes @ℓ₁@ arrives
-- pre-rendered. **A group is parenthesised even when it is empty** — that is
-- what keeps the slots positional, and whether @()@ is the right thing for the
-- engine to say is `~2jjqc`, which is his.
engineCases :: [TestTree]
engineCases =
  [ -- plusZero's body. Engine:
    --   elim Nat () (λ (target : Nat) -> Eq {0} Nat (plus target zero) target)
    --     (zeroMethod succMethod) () n
    eq
      "an elimination with two methods and no parameters or indices"
      "elim Nat () (\\target : Nat . Eq {0} Nat (plus target zero) target) \
      \(zeroMethod succMethod) () n"
      (displayShape plusZeroBody)
  , -- A level argument on a global is written, because without it the text
    -- does not re-read: `Eq A a b` is an arity error (`~mtnxt`).
    eq "a global's level arguments" "Eq {0} Nat zero zero" (displayShape eqNatZeroZero)
  , -- And on a saturated former.
    eq "a former's level arguments" "f (refl {0} Nat zero)"
      (app (global "f") (at (AFormer "refl" ["0"] [global "Nat", global "zero"])))
  , -- An elimination over a parameterised datatype carries both: a non-empty
    -- parameter group and a level. Engine: elim Id {0} (A) (λ …) ((λ …)) (a b) q
    eq
      "an elimination with levels, a parameter group and an index group"
      "elim Id {0} (A) (\\x : A . P) ((rfl {0} A c)) (a b) q"
      (displayShape idElimination)
  ]

-- | @elim Nat () (\\target : Nat . Eq {0} Nat (plus target zero) target)
-- (zeroMethod succMethod) () n@
plusZeroBody :: Display
plusZeroBody =
  at
    AnElimination
      { eliminatorName = "Nat"
      , eliminatorLevels = []
      , eliminatorParameters = []
      , eliminatorMotive =
          at
            (AnAbstraction
              (Binding "target" (global "Nat"))
              (at (app (at (app eqNatTy plusTargetZero)) (var "target"))))
      , eliminatorMethods = [global "zeroMethod", global "succMethod"]
      , eliminatorIndices = []
      , eliminatorTarget = var "n"
      }
  where
    -- @Eq {0} Nat@, the head the two arguments above are applied to.
    eqNatTy = at (app (at (AGlobal "Eq" ["0"])) (global "Nat"))

    -- @plus target zero@ — an application, so it brackets as an argument.
    plusTargetZero = at (app (at (app (global "plus") (var "target"))) (global "zero"))

-- | @Eq {0} Nat zero zero@
eqNatZeroZero :: Display
eqNatZeroZero =
  at (app (at (app (at (app (at (AGlobal "Eq" ["0"])) (global "Nat"))) (global "zero"))) (global "zero"))

-- | @elim Id {0} (A) (\\x : A . P) ((rfl {0} A c)) (a b) q@
idElimination :: Display
idElimination =
  at
    AnElimination
      { eliminatorName = "Id"
      , eliminatorLevels = ["0"]
      , eliminatorParameters = [global "A"]
      , eliminatorMotive = at (AnAbstraction (Binding "x" (global "A")) (global "P"))
      , eliminatorMethods = [at (AFormer "rfl" ["0"] [global "A", global "c"])]
      , eliminatorIndices = [var "a", var "b"]
      , eliminatorTarget = var "q"
      }

-- | The one contrast 'Tui.Render.renderValue' exists to draw — `~g482j`, the
-- entry the engine track left open against this file. A name value used to
-- fall off the end of that @case@ and be drawn by whatever arm followed.
--
-- **The quoting is the whole of it**: @instral@ has a type for text and a type
-- for names, and a pane that draws both quoted says the name is a string.
valueCases :: [TestTree]
valueCases =
  [ testCase "a name is drawn bare" $
      assertEqual "" ["env:", "w = Nat.zero"] (envLines [("w", ValName "Nat.zero")])
  , testCase "and text beside it is drawn quoted" $
      assertEqual "" ["env:", "w = \"zero\""] (envLines [("w", ValText "zero")])
  , testCase "a name at the root has no path and is still bare" $
      assertEqual "" ["env:", "n = refl"] (envLines [("n", ValName "refl")])
  ]

-- | A machine view that is nothing but an @env@, and the @env@ lines of what it
-- draws. 'renderMachineView' is the exported door; 'renderValue' is not.
envLines :: [(String, ValueView)] -> [String]
envLines env =
  takeWhile (/= "stack:") (dropWhile (/= "env:") (renderMachineView (MachineView [] env [])))

eq :: String -> String -> Shape -> TestTree
eq name expected shape =
  testCase name (assertEqual "" expected (draw shape))
