-- | Turning 'Thena.View.*' values into plain text lines — a first pass.
--
-- **Always the expanded form.** The "reading flow" fold ('Thena.View.Core.ARegion'
-- drawn as nothing, a splice styled instead of fenced) is real and designed but
-- needs cursor/mouse-proximity tracking this module doesn't have yet — every
-- 'ARegion' here prints its tag and backticks. No parentheses or layout choice
-- is asked of the engine (`Thena.View.Core`'s own doc: "no text in here except
-- where the text /is/ the answer"), so the minimal bracketing below is this
-- module's own, not the view's.
module Tui.Render
  ( renderDisplay
  , renderLinkViews
  , goalLines
  , renderMachineView
  ) where

import Data.List (intercalate)

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

renderDisplay :: Display -> String
renderDisplay (Display _ shape) = renderShape shape

renderShape :: Shape -> String
renderShape shape = case shape of
  AVariable name _ -> name
  AGlobal name _ -> name
  AUniverse lvl -> lvl
  ALiteral text -> text
  AnApplication f a -> renderDisplay f <> " " <> atom a
  AFunction b body -> "(" <> bindingName b <> " : " <> renderDisplay (bindingType b) <> ") -> " <> renderDisplay body
  AnAbstraction b body -> "\\" <> bindingName b <> " : " <> renderDisplay (bindingType b) <> " . " <> renderDisplay body
  ALet b val body -> bindingName b <> " = " <> renderDisplay val <> " : " <> renderDisplay (bindingType b) <> " . " <> renderDisplay body
  AFormer name _ args -> unwords (name : map atom args)
  AnElimination eliminator _levels params motive methods indices target ->
    unwords (eliminator : map atom (params <> [motive] <> methods <> indices <> [target]))
  ADangling n -> "#" <> show n
  AnElision -> "…"
  ARegion inner -> renderRegion inner
  AnObjectTerm lang _prod items -> lang <> "`" <> concatMap renderObjectItem items <> "`"
  AToken text -> text
  where
    atom d@(Display _ sh) = case sh of
      AnApplication {}   -> "(" <> renderDisplay d <> ")"
      AFunction {}       -> "(" <> renderDisplay d <> ")"
      AnAbstraction {}   -> "(" <> renderDisplay d <> ")"
      ALet {}            -> "(" <> renderDisplay d <> ")"
      AnElimination {}   -> "(" <> renderDisplay d <> ")"
      _                  -> renderDisplay d

-- | An 'ARegion' always wraps an 'AnObjectTerm' (`Thena.View.Core`'s own
-- invariant); the other-shape branch is unreachable in practice, kept only
-- so this stays total.
renderRegion :: Display -> String
renderRegion (Display _ shape) = case shape of
  AnObjectTerm lang _prod items -> lang <> "`" <> concatMap renderObjectItem items <> "`"
  other -> renderShape other

renderObjectItem :: ObjectItem -> String
renderObjectItem item = case item of
  ObjectText t -> t
  ObjectToken d -> renderDisplay d
  ObjectChild True d -> "${" <> renderDisplay d <> "}"
  ObjectChild False d -> renderInline d
  where
    renderInline (Display _ (AnObjectTerm _ _ items)) = concatMap renderObjectItem items
    renderInline d = renderDisplay d

-- | The development's chain, one line per link, a guess's own body indented
-- beneath it. '>' marks the focused link — 'linkFocus', not a computed
-- comparison.
renderLinkViews :: [LinkView] -> [String]
renderLinkViews = concatMap (renderLink 0)

renderLink :: Int -> LinkView -> [String]
renderLink depth (LinkView _at focus shape) =
  (marker <> indent <> renderLinkShape shape) : nested
  where
    marker = if focus then "> " else "  "
    indent = concat (replicate depth "  ")
    nested = case shape of
      AGuessLink {guessBody = body} -> concatMap (renderLink (depth + 1)) body
      _ -> []

renderLinkShape :: LinkShape -> String
renderLinkShape shape = case shape of
  AnAssumption name ty -> "assume " <> name <> " : " <> renderDisplay ty
  ADefinition name ty val -> "let " <> name <> " : " <> renderDisplay ty <> " = " <> renderDisplay val
  AClaimLink name ty blocked ->
    "? " <> name <> " : " <> renderDisplay ty <> blockedSuffix blocked
  AGuessLink name ty pure' blocked _body ->
    "guess " <> name <> " : " <> renderDisplay ty <> impureSuffix pure' <> blockedSuffix blocked
  AQuantifier name ty -> "forall " <> name <> " : " <> renderDisplay ty
  APending c -> renderConstraint c
  AResult d -> renderDisplay d
  where
    blockedSuffix b = if b then " (blocked)" else ""
    impureSuffix p = if p then "" else " (impure)"

renderConstraint :: ConstraintView -> String
renderConstraint (ConstraintView _xi lhs rhs ty) =
  renderDisplay lhs <> " =?= " <> renderDisplay rhs <> " : " <> renderDisplay ty

-- | "Goal" means an open claim in the development, nothing more — no kernel
-- metas view exists to ask instead. Guesses branch, so this recurses into
-- their own bodies the same way 'renderLinkViews' does.
goalLines :: [LinkView] -> [String]
goalLines = concatMap goalsOf
  where
    goalsOf (LinkView _at _focus shape) = case shape of
      AClaimLink name ty blocked -> [renderLinkShape (AClaimLink name ty blocked)]
      AGuessLink {guessBody = body} -> goalLines body
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
-- printer ('Thena.View.Surface' has the structure) is its own piece of work,
-- not needed to get the machine pane on screen.
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
  ValTerm d -> renderDisplay d
  ValSurface _ -> "<surface>"
  ValOpaque name -> "<" <> name <> ">"
