-- | What an @instral@ statement looks like to the editor (MS7 phase 115d;
-- @discussion\/editor-display.md@ §7, first half).
--
-- **A statement carries its word and its operands, generically.** 'Op' has
-- more than sixty constructors and 'Thena.Repl.renderOp' already found the
-- shape that does not need one case per constructor — the word from
-- 'Thena.Instral.Ops.opKeyword', the operands from
-- 'Thena.Instral.Ops.operandsOf' — and drifted the one time a second table of
-- the same thing was kept beside it (phase 23b, fixed 25c). This reuses that
-- table rather than writing a third one.
--
-- **Addressing does not reach here yet.** 'Thena.Protocol.Address.Move' is
-- exactly the development cursor's own descents, and there is no cursor over
-- an instral block to extend it with — 'Thena.Protocol.Address.follow' would
-- have nothing to call. A 'StatementView' carries its plain position in the
-- block it came from instead of a real 'Thena.Protocol.Address.Address'; see
-- the phase's own plan for the judgement call.
module Thena.Protocol.Instral
  ( StatementView (..)
  , StatementDetail (..)
  , OperandView (..)
  , ValueView (..)
  , SkeletonView (..)
  , displayBlock
  , displayValue
  , patternText
  ) where

import Data.List (intercalate)

import Thena.Core.Term (GlobalName (..), Literal (..))
import Thena.Global.Env (inductiveName)
import Thena.Instral.Ops
  ( AnswerKind (..)
  , Instr (..)
  , Op (..)
  , Operand (..)
  , Skeleton (..)
  , Value (..)
  , opKeyword
  , operandsOf
  )
import Thena.Instral.Pattern (Pattern (..))
import Thena.Instral.Type (renderTy)
import Thena.Language.Grammar (Grammar)
import Thena.Protocol.Address (Address)
import Thena.Protocol.Display (Budget, Display, displayCore)
import Thena.Syntax.Print (Env, escapeChar, escapeString, renderLevel)
import Thena.Core.Term (Var)

-- | One instruction, positioned.
data StatementView = StatementView
  { statementIndex :: Int
  , statementNext  :: Bool
    -- ^ is this the head of a **live** @pc@ — the instruction that runs next.
    -- Always 'False' for a rule's own body, which has no @pc@ of its own.
  , statementBind  :: Maybe String
    -- ^ the pattern a 'Bind' assigns to, spelled as written. Plain text and
    -- not a structured view: a pattern has no reader here to keep faith with
    -- (@Thena.Repl@'s own line for its display renderers) and nothing in it
    -- is session state — a name it introduces, not one it resolves.
  , statementAnnotation :: Maybe String
    -- ^ the author's own type annotation on a 'Bind', spelled as written —
    -- 'Thena.Instral.Type.renderTy' is already pure and shared, so this is
    -- not a second copy of anything. **Read only by inference** (his ruling,
    -- MS5 phase 77); 'Thena.Engine' never looks at it, and neither does
    -- anything downstream of this field.
  , statementWord     :: String
  , statementOperands :: [OperandView]
  , statementDetail   :: Maybe StatementDetail
  }
  deriving (Eq, Show)

-- | What 'Thena.Instral.Ops.operandsOf' does not carry, for the four ops
-- that are not simply "the word, then its operands" —
-- 'Thena.Repl.renderOp's own list, minus 'Unify' (infix is presentation, not
-- structure).
data StatementDetail
  = AsksFor String
    -- ^ 'Thena.Instral.Ops.Ask's 'AnswerKind' — what the frontend should
    -- offer, exactly as the terminal spells it (@:text@, @:name@, @:term@,
    -- @:rule@).
  | Declares String
    -- ^ 'Thena.Instral.Ops.DefineData's name. The declaration itself is not
    -- displayed — a datatype's own display is not this phase's.
  | Calls String
    -- ^ 'Thena.Instral.Ops.Call's target, as written. **Which rule it would
    -- dispatch to is deliberately not resolved here** — it depends on the
    -- local environment a static body does not have, and it is the one fact
    -- §7 names that this phase leaves for the next: see the plan's closing
    -- section.
  | Crosses String
    -- ^ 'Thena.Instral.Ops.CrossType' and 'Thena.Instral.Ops.CrossValue'
    -- share one word, @cross@ — @"type"@ or @"val"@ is the only thing that
    -- tells the two apart, in the terminal and here alike.
  deriving (Eq, Show)

-- | One operand, generically — 'Thena.Instral.Ops.Operand's own five shapes.
data OperandView
  = OpndRef String
    -- ^ a bound name, as written. **Not resolved to its current value** —
    -- Core's own 'Thena.Protocol.Display.AVariable' does not carry one either
    -- until asked; this is the same restraint.
  | OpndLiteral ValueView
  | OpndList [OperandView]
  | OpndPair OperandView OperandView
  | OpndObject (SkeletonView OperandView)
  deriving (Eq, Show)

-- | An object term built inside a body (MS6 phase 104c) — a production and
-- its slots, or a literal, or a hole still to be filled.
--
-- **Not 'Thena.Protocol.Display.AnObjectTerm'.** That shape is a *term*,
-- addressed and read against a grammar; this is the *skeleton* a rule body
-- builds one from, with no grammar and no address — 'Thena.Repl.renderSkeleton'
-- draws the same distinction in text, writing @app(var("f"), x)@ rather than
-- notation because "the region's own notation needs the grammar and this
-- printer has none".
data SkeletonView a
  = SkelNode String [SkeletonView a]
  | SkelLiteral String
  | SkelHole a
  deriving (Eq, Show)

-- | A runtime value, generically — 'Thena.Instral.Ops.Value's own shapes.
--
-- **A closure, a surface focus and an unresolved core region show their
-- shape and not their contents** — 'Thena.Repl.renderValue's own choice, for
-- its own reason: a closure's body and captured environment "would say more
-- than a reader wants and less than they could use", a surface printer does
-- not exist, and neither does one for 'Thena.Syntax.Concrete.Raw'. 'ValOpaque'
-- is that shape, named, until each has a display of its own.
data ValueView
  = ValText String
  | ValInt Int
  | ValChar String
    -- ^ escaped as the lexer reads it back, like 'ValText' — not a bare
    -- 'Char', for the same reason 'Thena.Protocol.Display.ALiteral' stores
    -- its own literals escaped rather than raw.
  | ValBool Bool
  | ValList [ValueView]
  | ValNone
  | ValSome ValueView
  | ValPair ValueView ValueView
  | ValLevel String
  | ValTerm Display
  | ValOpaque String
  deriving (Eq, Show)

-- | A block of instructions, positioned — a rule's own body, a closure's, or
-- a live @pc@.
--
-- @next@ names which position (if any) is the head of a **live** @pc@;
-- 'Nothing' for a body that is not currently running.
--
-- @at@ is where an embedded 'Thena.Instral.Ops.VTerm' is displayed from —
-- there is no address of its own for a value inside an instral statement
-- (see the module header), so it is built at the block's own position, the
-- same "no finer position yet" choice phase 115c made for a constraint's
-- fields.
displayBlock
  :: [Grammar]
  -> Budget
  -> Env
  -> [(Var, Address)]
  -> Int
  -> Address
  -> Maybe Int
  -> [Instr]
  -> [StatementView]
displayBlock gs budget env bs n at next instrs =
  [ statement k instr | (k, instr) <- zip [0 ..] instrs ]
  where
    statement k instr =
      StatementView
        { statementIndex = k
        , statementNext = Just k == next
        , statementBind = bindOf instr
        , statementAnnotation = annotationOf instr
        , statementWord = opKeyword (opOf instr)
        , statementOperands = map operand (operandsOf (opOf instr))
        , statementDetail = detailOf (opOf instr)
        }

    bindOf i = case i of
      Bind p _ _ -> Just (patternText p)
      Do _       -> Nothing

    annotationOf i = case i of
      Bind _ (Just t) _ -> Just (renderTy t)
      _                 -> Nothing

    opOf i = case i of
      Bind _ _ o -> o
      Do o       -> o

    detailOf o = case o of
      Ask _ k'     -> Just (AsksFor (answerKindText k'))
      DefineData d -> Just (Declares (let GlobalName g = inductiveName d in g))
      Call nm _    -> Just (Calls nm)
      CrossType    -> Just (Crosses "type")
      CrossValue   -> Just (Crosses "val")
      _            -> Nothing

    operand o = case o of
      Ref x -> OpndRef x
      Lit v -> OpndLiteral (displayValue gs budget env bs n at v)
      ListOf os -> OpndList (map operand os)
      PairOf a b -> OpndPair (operand a) (operand b)
      ObjectOf sk -> OpndObject (skeleton sk)

    skeleton sk = case sk of
      SNode (GlobalName nm) kids -> SkelNode nm (map skeleton kids)
      SLit l -> SkelLiteral (literalText l)
      SHole _ o -> SkelHole (operand o)

-- | A runtime value, generically — shared with 'Thena.Protocol.Machine',
-- whose @env@ pane is values with no operand around them at all.
displayValue :: [Grammar] -> Budget -> Env -> [(Var, Address)] -> Int -> Address -> Value -> ValueView
displayValue gs budget env bs n at v = case v of
  VText s -> ValText (escapeString s)
  VInt k -> ValInt k
  VChar c -> ValChar (escapeChar c)
  VBool b -> ValBool b
  VList vs -> ValList (map go vs)
  VOption Nothing -> ValNone
  VOption (Just v') -> ValSome (go v')
  VPair a b -> ValPair (go a) (go b)
  VLevel l -> ValLevel (renderLevel l)
  VTerm t -> ValTerm (displayCore gs budget env bs n at t)
  VClosure {} -> ValOpaque "closure"
  VRaw _ -> ValOpaque "core-region"
  VSurface _ -> ValOpaque "surface"
  where
    go = displayValue gs budget env bs n at

literalText :: Literal -> String
literalText l = case l of
  LString s -> escapeString s
  LChar c   -> escapeChar c
  LInt k    -> show k
  LRegex r  -> "/" ++ r ++ "/"

answerKindText :: AnswerKind -> String
answerKindText k = case k of
  AText -> ":text"
  AName -> ":name"
  ATerm -> ":term"
  ARule -> ":rule"

-- | A pattern, spelled as written. **Duplicated from
-- 'Thena.Repl.renderPattern' rather than shared**: that function's own module
-- keeps every display renderer, on the stated ground that their output "has
-- no reader" and so is not the kind of thing 'Thena.Syntax.Print' collects —
-- moving it would cross that line for the sake of one caller here. A pattern
-- is small and self-contained (no session state, no address), which is what
-- makes the second copy cheap rather than a second table of the same
-- disagreement 'opKeyword'\/'operandsOf' already had.
patternText :: Pattern -> String
patternText pt = case pt of
  PVar x      -> x
  PWild       -> "_"
  PInt k      -> show k
  PChar c     -> show c
  PBool True  -> "true"
  PBool False -> "false"
  PText t     -> show t
  PPair a b   -> "(" ++ patternText a ++ ", " ++ patternText b ++ ")"
  PSome a     -> "(some " ++ patternText a ++ ")"
  PNone       -> "none"
  PObject sk  -> skeletonText sk
  PList ps mt ->
    "[" ++ intercalate ", " (map patternText ps ++ tl) ++ "]"
    where
      tl = case mt of
        Nothing -> []
        Just t  -> ["..." ++ patternText t]

skeletonText :: Skeleton Pattern -> String
skeletonText sk = case sk of
  SNode (GlobalName nm) [] -> nm
  SNode (GlobalName nm) kids -> nm ++ "(" ++ commas (map skeletonText kids) ++ ")"
  SLit l -> case l of
    LString s -> escapeString s
    LChar c   -> escapeChar c
    LInt k    -> show k
    LRegex r  -> "/" ++ r ++ "/"
  SHole _ p -> "$" ++ "{" ++ patternText p ++ "}"
  where
    commas = intercalate ", "
