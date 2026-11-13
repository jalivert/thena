-- | Turning 'Thena.View.*' values into brick 'Widget's.
--
-- **Per-span attributes, not flat text.** A folded literal wants "a
-- different background and typeface" (his words) applied to exactly its own
-- span, not the whole line — a 'String' cannot carry that. The machine pane
-- stays plain text for this pass — it rarely holds literals worth folding,
-- and doing it there too is more of the same pattern, not a new design
-- question; noted, not a `CLOSEOUT.md` item.
--
-- **A term is built as 'Piece's and laid out by 'flow', not glued together
-- with '<+>'** — `~r4gvd`, his report of 2026-11-12: /"make sure that each smaller pane
-- correctly line-breaks."/ An '<+>' of 'str's is one unbreakable row as wide
-- as the term is long, so in a pane a quarter of the screen wide everything
-- past the edge was simply not drawn: measured under a pty, the proof-term
-- pane showed @> guess eta : (A : Type₀) -@ and stopped there. A 'Piece'
-- carries its own attribute, so the fold's per-span colouring survives being
-- broken across lines, which is the thing a 'String' could not do and the
-- reason this module existed in the first place.
module Tui.Render
  ( Fold (..)
  , isUnderneath
  , foldAttr
  , spliceAttr
  , renderDisplay
  , renderDevelopment
  , renderGoals
  , renderMachineView
  ) where

import Data.Char (isSpace)
import Data.Function (on)
import Data.List (groupBy, intercalate, intersperse, isPrefixOf)

import Brick
  ( Size (Fixed, Greedy)
  , Widget (Widget, render)
  , availWidthL
  , getContext
  , hBox
  , padLeft
  , str
  , vBox
  , withAttr
  , (<+>)
  )
import Brick.AttrMap (AttrName, attrName)
import Brick.Widgets.Core (Padding (Pad))
import Lens.Micro ((^.))

import Thena.View.Address (Address (..))
import Thena.View.Core (Binding (..), Display (..), ObjectItem (..), Shape (..))
import Thena.View.Development (ConstraintView (..), LinkShape (..), LinkView (..))
import Thena.View.Instral
  ( OperandView (..)
  , SkeletonView (..)
  , StatementDetail (..)
  , StatementView (..)
  , ValueView (..)
  )
import Thena.View.Machine (FrameView (..), MachineView (..))

-- | Whether the reading-flow fold is on, and if so, where the cursor is —
-- an 'ARegion' folds unless the cursor stands at or beneath its own
-- address. 'NoFold' prints everything expanded, everywhere, unconditionally
-- — the toggle's off state.
data Fold = NoFold | Fold Address

-- | TAGGED-LITERALS.md's own words: "a prefix test on displayAt against
-- your focus address." Both are move-lists in the order the cursor
-- descended, so a literal's address is a prefix of the focus exactly when
-- the cursor stands inside it (or on it).
isUnderneath :: Address -> Address -> Bool
isUnderneath (Address at) (Address focus) = at `isPrefixOf` focus

foldAttr, spliceAttr :: AttrName
foldAttr = attrName "fold.literal"
spliceAttr = attrName "fold.splice"

expandedAt :: Fold -> Address -> Bool
expandedAt NoFold _ = True
expandedAt (Fold focus) at = at `isUnderneath` focus

-- * Pieces, and how a line of them breaks

-- | **A run of characters and the attribute it is drawn in.** The unit the
-- term drawers below build, in place of a 'Widget' each: a list of these is
-- a line of text that still knows which parts of itself are a folded literal
-- or a splice, and a list of them can be measured and broken, which a
-- 'Widget' cannot.
data Piece = Piece
  { pieceText :: String
  , pieceAttr :: Maybe AttrName
    -- ^ 'Nothing' is the ambient attribute. **Set, not stacked** — brick's
    -- own 'withAttr' is a field assignment rather than a stack (it is why
    -- @placeholder.recovered@ exists as a named combination), so a piece
    -- carrying one name is exactly as expressive as the nesting it replaces.
  }

plain :: String -> [Piece]
plain t = [Piece t Nothing]

inAttr :: AttrName -> [Piece] -> [Piece]
inAttr an = map (\p -> p { pieceAttr = Just an })

-- | **Pieces, laid out across however many columns there turn out to be.**
-- Greedy fill: as many pieces as fit, break at a space, and a continuation
-- line is indented by 'hangIndent' so it reads as the same line carried over
-- rather than as a new one.
--
-- **The width is the terminal's own**, read from the render context — the
-- pane widths are percentages of a screen nobody knows the size of until it
-- is drawn, so a constant here would be wrong on every screen but one. The
-- widget is horizontally 'Greedy' on purpose: it is drawn after a fixed
-- marker (@"> "@, @"? name : "@) in an 'hBox', and greedy is what makes
-- brick hand it the columns that are left rather than the whole row.
flow :: [Piece] -> Widget n
flow pieces = Widget Greedy Fixed $ do
  ctx <- getContext
  render (vBox (map lineWidget (fill (max 1 (ctx ^. availWidthL)) (atomsOf pieces))))
  where
    lineWidget as = case concatMap atomRuns as of
      [] -> str " "
      ps -> hBox (map runWidget ps)
    runWidget p = case pieceAttr p of
      Nothing -> str (pieceText p)
      Just an -> withAttr an (str (pieceText p))

-- | How far a broken line's continuation is indented. **Two columns, the
-- same step a pane row's own wrap takes** ('Tui.Panes.paneWrap'), so a term
-- that breaks in the proof-term pane and a line that breaks in the output
-- pane look like the same thing happening.
hangIndent :: Int
hangIndent = 2

-- | One word, or one run of spaces. **A line may break between atoms and
-- nowhere else**, which is what makes an atom the unit rather than a 'Piece':
--
--   * a drawer emits @"(A : "@ as one piece, and a layout that could only
--     break between pieces would not break at the space inside it;
--   * @"… (snd A B s)"@ and the @")"@ that closes the term around it are two
--     pieces with no space between them, and a layout that broke between any
--     two pieces put that @")"@ alone at the start of a line — measured under
--     a pty, which is how this model replaced the first one.
--
-- So an atom is cut out of the pieces' concatenated text at whitespace, and
-- **it keeps the attribute runs it spans** — a word that is half ordinary
-- term and half folded literal is one atom of two runs, not two atoms.
data Atom = Atom
  { atomRuns  :: [Piece]
  , atomSpace :: Bool
  }

atomLength :: Atom -> Int
atomLength = sum . map (length . pieceText) . atomRuns

-- | Cut an atom after @n@ columns, for the one case that has to cut: a word
-- longer than the whole width.
splitAtom :: Int -> Atom -> (Atom, Atom)
splitAtom n a = (a { atomRuns = runs before }, a { atomRuns = runs after })
  where
    (before, after) = splitAt n (chars (atomRuns a))

atomsOf :: [Piece] -> [Atom]
atomsOf pieces =
  [ Atom (runs group) (all (isSpace . fst) group)
  | group <- groupBy ((==) `on` (isSpace . fst)) (chars pieces)
  , not (null group)
  ]

-- | A piece list as characters, each carrying the attribute it is drawn in,
-- and back again — the one place the piece boundaries are deliberately
-- forgotten, so that only whitespace decides where a line may break.
chars :: [Piece] -> [(Char, Maybe AttrName)]
chars = concatMap (\p -> [(c, pieceAttr p) | c <- pieceText p])

runs :: [(Char, Maybe AttrName)] -> [Piece]
runs cs =
  [ Piece (map fst (c : more)) (snd c)
  | (c : more) <- groupBy ((==) `on` snd) cs
  ]

-- | Greedy fill into lines of at most @w@ columns.
--
-- **Three rules and the third is the one that matters here.** A space at the
-- start of a line is dropped, because a break happens *at* the space and
-- keeping it would indent the continuation by one more column than asked. A
-- word that does not fit on a partly-filled line is tried on a fresh one. And
-- **a word that does not fit on a fresh line either is cut** — a core term's
-- name, a module path and a level-decorated global are each one unbreakable
-- word and are routinely longer than a quarter of the screen, so refusing to
-- cut them would be the clip this function exists to replace. It consumes at
-- least one column per step, so it terminates at any width.
fill :: Int -> [Atom] -> [[Atom]]
fill w = line 0 [] 0
  where
    line base cur n as = case as of
      [] -> [reverse cur | not (null cur)]
      (a : rest)
        | atomSpace a, n == base -> line base cur n rest
        | n + len <= w -> line base (a : cur) (n + len) rest
        | n > base -> reverse cur : continue as
        | otherwise ->
            let (here, over) = splitAtom (max 1 (w - n)) a
             in reverse (here : cur) : continue (over : rest)
        where
          len = atomLength a
    continue = line hangIndent [indent] hangIndent
    indent = Atom [Piece (replicate hangIndent ' ') Nothing] True

-- | Where a 'Display' is being drawn, which decides whether it needs
-- parentheses. **The three rungs are 'Thena.Render'\'s own @Prec@ and the
-- ladder is deliberately the same one** — @Shape@ carries no brackets, so
-- every drawer supplies its own, and two drawers that disagree about where
-- mean the same term reads as two different terms depending on the pane it
-- is in. `~kq45n`: the engine's printer is the reference.
data Prec
  = AtTop   -- ^ a λ, a ∀, an arrow and a let are all fine unparenthesised here
  | AtApp   -- ^ the function side of an application
  | AtAtom  -- ^ the argument side of an application
  deriving (Eq, Ord)

-- | A term as a widget: its pieces, flowed. **The one entry point that is
-- still a 'Widget'**, because a pane draws one term per line and the break
-- decisions belong to the line as a whole — see 'flow'.
renderDisplay :: Fold -> Display -> Widget n
renderDisplay fold = flow . displayPieces fold

displayPieces :: Fold -> Display -> [Piece]
displayPieces fold = renderAt fold AtTop

renderAt :: Fold -> Prec -> Display -> [Piece]
renderAt fold prec (Display _at shape) = renderShape fold prec shape

renderShape :: Fold -> Prec -> Shape -> [Piece]
renderShape fold prec shape = case shape of
  AVariable name _ -> plain name
  AGlobal name levels -> plain (name <> levelArgs levels)
  AUniverse lvl -> plain lvl
  ALiteral text -> plain text
  -- Application is left associative, so the function side needs no brackets
  -- for another application -- but it does for everything that extends to
  -- the right, which is what `~r3fp9` was: an 'AnElimination' standing here
  -- drew as @elim … tgt arg@ and the core grammar refuses that outright.
  AnApplication f a ->
    parensIf (prec > AtApp) (renderAt fold AtApp f <> plain " " <> renderAt fold AtAtom a)
  AFunction b body ->
    parensIf (prec > AtTop) $
      plain ("(" <> bindingName b <> " : ") <> renderAt fold AtTop (bindingType b)
        <> plain ") -> " <> renderAt fold AtTop body
  AnAbstraction b body ->
    parensIf (prec > AtTop) $
      plain ("\\" <> bindingName b <> " : ") <> renderAt fold AtTop (bindingType b)
        <> plain " . " <> renderAt fold AtTop body
  ALet b val body ->
    parensIf (prec > AtTop) $
      plain (bindingName b <> " = ") <> renderAt fold AtTop val
        <> plain " : " <> renderAt fold AtTop (bindingType b)
        <> plain " . " <> renderAt fold AtTop body
  -- A saturated former is a spine and brackets like one: bare on a function
  -- side, bracketed as an argument. An unsaturated one is a bare name.
  AFormer name levels args
    | null args -> plain (name <> levelArgs levels)
    | otherwise ->
        parensIf (prec > AtApp)
          (concat
            (plain (name <> levelArgs levels)
              : map (\a -> plain " " <> renderAt fold AtAtom a) args))
  -- **The keyword, the levels and a parenthesis per group — his ruling,
  -- 2026-10-20 (`~23wfh`, `~9wcpr`):** /"We print exactly what engine gives
  -- us… TUI literally follows what engine gives and doesn't invent lies in
  -- the frontend layer."/ So the groups are drawn group by group **including
  -- the empty ones**, which is what keeps the slots positional — a reader
  -- cannot otherwise tell the methods from the indices. That the empty ones
  -- read as @()@ is the engine's question and he has taken it (`~2jjqc`).
  AnElimination eliminator levels params motive methods indices target ->
    parensIf (prec > AtTop) $
      concat
        [ plain ("elim " <> eliminator <> levelArgs levels)
        , plain " " <> group params
        , plain " " <> renderAt fold AtAtom motive
        , plain " " <> group methods
        , plain " " <> group indices
        , plain " " <> renderAt fold AtAtom target
        ]
    where
      -- A group is always parenthesised and never elided, so a slot's position
      -- is readable off the text. 'Thena.Render'\'s @atoms@, exactly.
      group ds =
        plain "("
          <> concat (intersperse (plain " ") (map (renderAt fold AtAtom) ds))
          <> plain ")"
  -- MS8 phase 149 added the node; **this is a placeholder the engine track
  -- wrote to keep the tree compiling, and how a trusted term should look is
  -- yours** -- see `.jalivert/NOTES.md`. The two types are both here on purpose:
  -- the pair is the obligation, and `actual` is what says whether the trust is
  -- still load-bearing.
  ATrusted claimed actual body ->
    parensIf (prec > AtApp) $
      concat
        (plain "trusted"
          : map (\a -> plain " " <> renderAt fold AtAtom a) [claimed, actual, body])
  ADangling n -> plain ("#" <> show n)
  AnElision -> plain "…"
  ARegion inner -> renderRegion fold inner
  AnObjectTerm lang _prod items ->
    plain (lang <> "`") <> objectBody fold True items <> plain "`"
  AToken text -> plain text

parensIf :: Bool -> [Piece] -> [Piece]
parensIf False ps = ps
parensIf True ps = plain "(" <> ps <> plain ")"

-- | A name's level arguments, written the way 'Thena.Syntax.Print.levelArgs'
-- writes them.
--
-- **The atoms are already rendered** — 'Thena.View.Core' normalises them,
-- because level normalisation is system work and a frontend must never do it.
-- All that is left is the punctuation. **Empty means nothing is written**, so
-- everything monomorphic looks exactly as it did.
levelArgs :: [String] -> String
levelArgs [] = ""
levelArgs ls = " {" <> unwords ls <> "}"

-- | 'ARegion' always wraps an 'AnObjectTerm' — the fold decision is made
-- once, here, and handed down to every item inside as the `expanded` flag,
-- so a nested inline child never re-derives it.
renderRegion :: Fold -> Display -> [Piece]
renderRegion fold (Display at shape) = case shape of
  AnObjectTerm lang _prod items
    | expanded  -> plain (lang <> "`") <> body <> plain "`"
    | otherwise -> inAttr foldAttr body
    where body = objectBody fold expanded items
  other -> renderShape fold AtTop other
  where
    expanded = expandedAt fold at

-- | **A production's items, with ONE SPACE between consecutive ones** —
-- `~mxhfj`, his report of 2026-11-12: /"There are no spaces between the
-- identifiers. Instead of @n value@ it's @nvalue@."/
--
-- **The separator is the frontend's to supply and the engine has already
-- chosen it.** 'Thena.View.Core.objectItems' hands over a production's
-- terminals and slots in written order and deliberately joins them with
-- nothing — deciding that is a frontend's business. The engine's own printer
-- decides it in 'Thena.Language.Build.laid', with
-- @intercalate [Written " "] css@ over exactly the same one-entry-per-grammar-item
-- list. **So this is not a spacing rule of ours; it is the prompt's rule,
-- matched.** The test is that @:infer@ and the pane now agree about one term.
--
-- **Uniform, with no exceptions, because `laid` has none.** A grammar's
-- terminals are single tokens and never carry spaces of their own, so there is
-- no pair this doubles.
--
-- **Nesting needs nothing extra.** An inline child ('ObjectChild' 'False') is
-- one item of its parent and is spaced as one, while its own items are spaced
-- by this same function one level down — which is exactly how 'laid' recurses
-- through 'go'.
objectBody :: Fold -> Bool -> [ObjectItem] -> [Piece]
objectBody fold expanded = intercalate (plain " ") . map (renderObjectItem fold expanded)

renderObjectItem :: Fold -> Bool -> ObjectItem -> [Piece]
renderObjectItem fold expanded item = case item of
  ObjectText t -> plain t
  ObjectToken d -> displayPieces fold d
  ObjectChild True d
    | expanded  -> plain "${" <> displayPieces fold d <> plain "}"
    | otherwise -> inAttr spliceAttr (displayPieces fold d)
  ObjectChild False d -> renderInline fold expanded d

-- | More of the same literal, inline — no tag of its own (`ARegion` never
-- wraps this case), so the enclosing region's `expanded` flag just carries
-- through unchanged.
renderInline :: Fold -> Bool -> Display -> [Piece]
renderInline fold expanded (Display _ (AnObjectTerm _ _ items)) =
  objectBody fold expanded items
renderInline fold _ d = displayPieces fold d

-- | The development's chain, one line per link, a guess's own body indented
-- beneath it. '>' marks the focused link — 'linkFocus', not a computed
-- comparison.
renderDevelopment :: Fold -> [LinkView] -> Widget n
renderDevelopment fold = vBox . map (renderLink fold 0)

renderLink :: Fold -> Int -> LinkView -> Widget n
renderLink fold depth (LinkView _at focus shape) =
  case nested of
    [] -> line
    _  -> vBox (line : nested)
  where
    marker = if focus then "> " else "  "
    -- | **The marker is a fixed column beside the flow, not a piece inside
    -- it** — so the term's continuation lines align under the term rather
    -- than under the marker, and an unfocused link keeps its indent. Putting
    -- it inside was tried and measured: an unfocused marker is two spaces,
    -- 'fill' drops a leading space at a line start (a break happens *at* the
    -- space), and every unfocused link lost its step and lined up with the
    -- focused one.
    line = padLeft (Pad (2 * depth)) (str marker <+> flow (linkPieces fold shape))
    nested = case shape of
      AGuessLink {guessBody = body} -> map (renderLink fold (depth + 1)) body
      _ -> []

linkPieces :: Fold -> LinkShape -> [Piece]
linkPieces fold shape = case shape of
  AnAssumption name ty -> plain ("assume " <> name <> " : ") <> displayPieces fold ty
  ADefinition name ty val ->
    plain ("let " <> name <> " : ") <> displayPieces fold ty <> plain " = " <> displayPieces fold val
  AClaimLink name ty blocked ->
    plain ("? " <> name <> " : ") <> displayPieces fold ty <> plain (blockedSuffix blocked)
  AGuessLink name ty pure' blocked _body ->
    plain ("guess " <> name <> " : ") <> displayPieces fold ty
      <> plain (impureSuffix pure' <> blockedSuffix blocked)
  AQuantifier name ty -> plain ("forall " <> name <> " : ") <> displayPieces fold ty
  APending c -> constraintPieces fold c
  AResult d -> displayPieces fold d
  where
    blockedSuffix b = if b then " (blocked)" else ""
    impureSuffix p = if p then "" else " (impure)"

constraintPieces :: Fold -> ConstraintView -> [Piece]
constraintPieces fold (ConstraintView _xi lhs rhs ty) =
  displayPieces fold lhs
    <> plain " =?= "
    <> displayPieces fold rhs
    <> plain " : "
    <> displayPieces fold ty

-- | "Goal" means an open claim in the development, nothing more — no kernel
-- metas view exists to ask instead. Guesses branch, so this recurses into
-- their own bodies the same way 'renderDevelopment' does.
renderGoals :: Fold -> [LinkView] -> Widget n
renderGoals fold links = case goalsOf links of
  [] -> str " "
  gs -> vBox gs
  where
    goalsOf = concatMap goalOf
    goalOf (LinkView _at _focus shape) = case shape of
      AClaimLink {} -> [flow (linkPieces fold shape)]
      AGuessLink {guessBody = body} -> goalsOf body
      _ -> []

renderMachineView :: MachineView -> [String]
renderMachineView (MachineView pc env stack) =
  ("pc:" : map renderStatement pc)
    <> ("env:" : map renderBinding env)
    <> ("stack:" : map renderFrame stack)
  where
    renderBinding (name, v) = name <> " = " <> renderValue v
    renderFrame (FrameView n returned) =
      show n <> " instruction(s) to resume" <> (if returned then " (returned)" else "")

renderStatement :: StatementView -> String
renderStatement sv =
  marker <> bind <> statementWord sv
    <> (if null ops then "" else " " <> unwords ops)
    <> detail
  where
    marker = if statementNext sv then "> " else "  "
    ops = map renderOperand (statementOperands sv)
    bind = case statementBind sv of
      Nothing -> ""
      Just b -> b <> maybe "" (" : " <>) (statementAnnotation sv) <> " = "
    detail = case statementDetail sv of
      Nothing -> ""
      Just (AsksFor k) -> " (asks " <> k <> ")"
      Just (Declares n) -> " (declares " <> n <> ")"
      Just (Calls n) -> " (calls " <> n <> ")"
      Just (Crosses k) -> " (cross " <> k <> ")"

renderOperand :: OperandView -> String
renderOperand op = case op of
  OpndRef name -> name
  OpndLiteral v -> renderValue v
  OpndList xs -> "[" <> intercalate ", " (map renderOperand xs) <> "]"
  OpndPair a b -> "(" <> renderOperand a <> ", " <> renderOperand b <> ")"
  OpndObject skel -> renderSkeleton skel

renderSkeleton :: SkeletonView OperandView -> String
renderSkeleton skel = case skel of
  SkelNode name args -> name <> "(" <> intercalate ", " (map renderSkeleton args) <> ")"
  SkelLiteral t -> t
  SkelHole op -> renderOperand op

-- | 'ValSurface' is rendered as a placeholder for now — a real surface
-- printer ('Thena.View.Surface' has the structure) is its own piece of
-- work, not needed to get panes on screen.
renderValue :: ValueView -> String
renderValue v = case v of
  ValText t -> show t
  -- A name prints bare where 'ValText' prints quoted, and that contrast is
  -- the whole of the case: in an @env@ pane @w = "zero"@ is a piece of text
  -- and @w = Nat.zero@ is a name. 'Thena.Render.renderValue' makes the same
  -- distinction, and `~g482j` is the entry that asked for it — a name value
  -- used to fall off the end of this @case@ and draw as an @Int@.
  --
  -- **Drawn as it arrives, which is dotted and whole** ('nameDotted'). The
  -- shortest-ending policy is over terms, and a bare name value has no term
  -- around it to be standing in, so there is no scope to shorten against.
  ValName s -> s
  ValInt n -> show n
  ValChar c -> c
  ValBool b -> if b then "true" else "false"
  ValList xs -> "[" <> intercalate ", " (map renderValue xs) <> "]"
  ValNone -> "none"
  ValSome x -> "some(" <> renderValue x <> ")"
  ValPair a b -> "(" <> renderValue a <> ", " <> renderValue b <> ")"
  ValLevel l -> l
  ValTerm d -> renderPlain d
  ValSurface _ -> "<surface>"
  ValOpaque name -> "<" <> name <> ">"

-- | A last resort for the one place a 'Display' still needs to become a
-- 'String' — inside a machine value, which this pass keeps as plain text
-- (see the module header). Always expanded; the machine pane doesn't fold.
renderPlain :: Display -> String
renderPlain (Display _ shape) = case shape of
  AVariable name _ -> name
  AGlobal name _ -> name
  AUniverse lvl -> lvl
  ALiteral text -> text
  AnApplication f a -> renderPlain f <> " " <> renderPlain a
  ARegion (Display _ (AnObjectTerm lang _ items)) ->
    lang <> "`" <> plainBody items <> "`"
  AnObjectTerm lang _ items -> lang <> "`" <> plainBody items <> "`"
  AToken text -> text
  AnElision -> "…"
  ADangling n -> "#" <> show n
  _ -> "…"
  where
    -- | The same one space 'objectBody' puts between items, for the machine
    -- pane's plain text — `~mxhfj`. **Both paths or neither**: a term that
    -- reads correctly in the proof-term pane and runs together in the machine
    -- pane is the same defect, half fixed.
    plainBody = intercalate " " . map plainItem
    plainItem it = case it of
      ObjectText t -> t
      ObjectToken d -> renderPlain d
      ObjectChild True d -> "${" <> renderPlain d <> "}"
      ObjectChild False (Display _ (AnObjectTerm _ _ items)) -> plainBody items
      ObjectChild False d -> renderPlain d
