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
import Brick.AttrMap (attrMap)
import Brick.Main (renderWidget)
import qualified Graphics.Vty as Vty
import Graphics.Vty.PictureToSpans (displayOpsForPic)
import Graphics.Vty.Span (SpanOp (..))

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertEqual, testCase)

import Thena.View.Address (Address (..))
import Thena.View.Core (Binding (..), Display (..), Shape (..))
import Thena.View.Instral (ValueView (..))
import Thena.View.Machine (MachineView (..))
import Tui.Panes
  ( FileKind (..)
  , PaneRow (..)
  , globalRows
  , moduleRows
  , outputRows
  , paneRowWidget
  )
import Tui.Render (Fold (..), renderDisplay, renderMachineView)


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
drawToLines w =
  map rowText (V.toList (displayOpsForPic picture region))
  where
    picture = renderWidget (Just (attrMap Vty.defAttr [])) [w] region

    rowText = trimEnd . concatMap opText . V.toList

    opText op = case op of
      TextSpan _ _ _ t -> TL.unpack t
      Skip n           -> replicate n ' '
      RowEnd n         -> replicate n ' '

    trimEnd = dropWhileEnd isSpace


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
    ]

-- | **What the three new panes say** — `~z5dmq`'s content, decided by
-- 'Tui.Panes' and therefore decidable here. The pty stays the authority on
-- where the panes are and how wide; this is the text in them.
paneRowCases :: [TestTree]
paneRowCases =
  [ testCase "an empty group is not drawn as a heading with nothing under it" $
      assertEqual ""
        [Heading "Prelude" (Just 2), Entry "And.both", Entry "Eq.refl"]
        (globalRows [("proved in this session", []), ("Prelude", ["Eq.refl", "And.both"])])
  , testCase "a name listed twice is listed once — a suspended proof is two runs" $
      assertEqual ""
        [Heading "proved in this session" (Just 1), Entry "subst"]
        (globalRows [("proved in this session", ["subst", "subst"])])
  , testCase "a module carries its file, and the prelude has none" $
      assertEqual ""
        [ Heading "modules" (Just 2)
        , Entry "examples.Stlc01Syntax"
        , Detail "examples/Stlc01Syntax.thena"
        , Entry "Prelude"
        ]
        (moduleRows
          [ ("examples.Stlc01Syntax", Just "examples/Stlc01Syntax.thena")
          , ("Prelude", Nothing)
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
        [Heading "modules" (Just 1), Entry "m", Detail "m.thena"]
        (moduleRows [("m", Just "m.thena")] [(AModuleFile, "m.thena")])
  , testCase "no line in focus is no rows at all" $
      assertEqual "" [] (outputRows Nothing ["something"])
  , testCase "a line that answered nothing is its heading and nothing else" $
      assertEqual "" [Heading ":theorem t : Nat" Nothing] (outputRows (Just ":theorem t : Nat") [])
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
