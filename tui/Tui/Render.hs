-- | Turning 'Thena.View.*' values into brick 'Widget's.
--
-- **Per-span attributes, not flat text.** A folded literal wants "a
-- different background and typeface" (his words) applied to exactly its own
-- span, not the whole line — a 'String' cannot carry that, so the
-- development/proof-term rendering below builds 'Widget's directly and
-- composes them with '<+>'/'vBox', the same way brick composes anything
-- else. The machine pane stays plain text for this pass — it rarely holds
-- literals worth folding, and doing it there too is more of the same
-- pattern, not a new design question; noted, not a `CLOSEOUT.md` item.
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

import Data.List (intercalate, isPrefixOf)

import Brick
  ( Widget
  , hBox
  , padLeft
  , str
  , vBox
  , withAttr
  , (<+>)
  )
import Brick.AttrMap (AttrName, attrName)
import Brick.Widgets.Core (Padding (Pad))

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

renderDisplay :: Fold -> Display -> Widget n
renderDisplay fold (Display _at shape) = renderShape fold shape

renderShape :: Fold -> Shape -> Widget n
renderShape fold shape = case shape of
  AVariable name _ -> str name
  AGlobal name _ -> str name
  AUniverse lvl -> str lvl
  ALiteral text -> str text
  AnApplication f a -> renderDisplay fold f <+> str " " <+> atomW fold a
  AFunction b body ->
    str ("(" <> bindingName b <> " : ") <+> renderDisplay fold (bindingType b)
      <+> str ") -> " <+> renderDisplay fold body
  AnAbstraction b body ->
    str ("\\" <> bindingName b <> " : ") <+> renderDisplay fold (bindingType b)
      <+> str " . " <+> renderDisplay fold body
  ALet b val body ->
    str (bindingName b <> " = ") <+> renderDisplay fold val
      <+> str " : " <+> renderDisplay fold (bindingType b)
      <+> str " . " <+> renderDisplay fold body
  AFormer name _levels args -> hBox (str name : map (\a -> str " " <+> atomW fold a) args)
  AnElimination eliminator _levels params motive methods indices target ->
    hBox
      (str eliminator
        : map (\a -> str " " <+> atomW fold a) (params <> [motive] <> methods <> indices <> [target]))
  ADangling n -> str ("#" <> show n)
  AnElision -> str "…"
  ARegion inner -> renderRegion fold inner
  AnObjectTerm lang _prod items ->
    str (lang <> "`") <+> hBox (map (renderObjectItem fold True) items) <+> str "`"
  AToken text -> str text

atomW :: Fold -> Display -> Widget n
atomW fold d@(Display _ sh) = case sh of
  AnApplication {} -> bracket
  AFunction {}     -> bracket
  AnAbstraction {} -> bracket
  ALet {}          -> bracket
  AnElimination {} -> bracket
  _                -> renderDisplay fold d
  where
    bracket = str "(" <+> renderDisplay fold d <+> str ")"

-- | 'ARegion' always wraps an 'AnObjectTerm' — the fold decision is made
-- once, here, and handed down to every item inside as the `expanded` flag,
-- so a nested inline child never re-derives it.
renderRegion :: Fold -> Display -> Widget n
renderRegion fold (Display at shape) = case shape of
  AnObjectTerm lang _prod items
    | expanded  -> str (lang <> "`") <+> body <+> str "`"
    | otherwise -> withAttr foldAttr body
    where body = hBox (map (renderObjectItem fold expanded) items)
  other -> renderShape fold other
  where
    expanded = expandedAt fold at

renderObjectItem :: Fold -> Bool -> ObjectItem -> Widget n
renderObjectItem fold expanded item = case item of
  ObjectText t -> str t
  ObjectToken d -> renderDisplay fold d
  ObjectChild True d
    | expanded  -> str "${" <+> renderDisplay fold d <+> str "}"
    | otherwise -> withAttr spliceAttr (renderDisplay fold d)
  ObjectChild False d -> renderInline fold expanded d

-- | More of the same literal, inline — no tag of its own (`ARegion` never
-- wraps this case), so the enclosing region's `expanded` flag just carries
-- through unchanged.
renderInline :: Fold -> Bool -> Display -> Widget n
renderInline fold expanded (Display _ (AnObjectTerm _ _ items)) =
  hBox (map (renderObjectItem fold expanded) items)
renderInline fold _ d = renderDisplay fold d

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
    line = padLeft (Pad (2 * depth)) (str marker <+> renderLinkShape fold shape)
    nested = case shape of
      AGuessLink {guessBody = body} -> map (renderLink fold (depth + 1)) body
      _ -> []

renderLinkShape :: Fold -> LinkShape -> Widget n
renderLinkShape fold shape = case shape of
  AnAssumption name ty -> str ("assume " <> name <> " : ") <+> renderDisplay fold ty
  ADefinition name ty val ->
    str ("let " <> name <> " : ") <+> renderDisplay fold ty <+> str " = " <+> renderDisplay fold val
  AClaimLink name ty blocked ->
    str ("? " <> name <> " : ") <+> renderDisplay fold ty <+> str (blockedSuffix blocked)
  AGuessLink name ty pure' blocked _body ->
    str ("guess " <> name <> " : ") <+> renderDisplay fold ty
      <+> str (impureSuffix pure' <> blockedSuffix blocked)
  AQuantifier name ty -> str ("forall " <> name <> " : ") <+> renderDisplay fold ty
  APending c -> renderConstraint fold c
  AResult d -> renderDisplay fold d
  where
    blockedSuffix b = if b then " (blocked)" else ""
    impureSuffix p = if p then "" else " (impure)"

renderConstraint :: Fold -> ConstraintView -> Widget n
renderConstraint fold (ConstraintView _xi lhs rhs ty) =
  renderDisplay fold lhs <+> str " =?= " <+> renderDisplay fold rhs <+> str " : " <+> renderDisplay fold ty

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
      AClaimLink {} -> [renderLinkShape fold shape]
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
    lang <> "`" <> concatMap plainItem items <> "`"
  AnObjectTerm lang _ items -> lang <> "`" <> concatMap plainItem items <> "`"
  AToken text -> text
  AnElision -> "…"
  ADangling n -> "#" <> show n
  _ -> "…"
  where
    plainItem it = case it of
      ObjectText t -> t
      ObjectToken d -> renderPlain d
      ObjectChild True d -> "${" <> renderPlain d <> "}"
      ObjectChild False (Display _ (AnObjectTerm _ _ items)) -> concatMap plainItem items
      ObjectChild False d -> renderPlain d
