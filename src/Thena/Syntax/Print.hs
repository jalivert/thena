-- | The as-written trees, printed back as text (MS7 phase 112c).
--
-- **The inverse of "Thena.Syntax.Parser", and it sits beside it for that
-- reason.** `PLAN-interface.md` §2.5 said rendering *"lives in "Thena.Repl" for
-- now"*, and this is the half of it that stops being provisional: printing a
-- tree the way it was written is not a frontend's concern, it is the other
-- direction of reading one, and the storage format needs it as much as the
-- prompt does.
--
-- **The display renderers stay where they are.** `Core` with its levels, a
-- cursor with its path, a machine with its frames, every error — those are
-- written for someone looking at a terminal and have no reader, so they remain
-- "Thena.Repl"'s. The line is whether the output is meant to be read back.
--
-- **What is here round-trips**, and that is the whole point of the module:
-- 'Thena.Syntax.Parser' on this output gives the same tree. It is not a claim,
-- it is checked over every file the project ships
-- ("Thena.Protocol.TextTests").
module Thena.Syntax.Print
  ( renderSurface
    -- * The written pieces, for printers built on this one
  , rawInstruction
  , rawOperation
  , rawOperand
  , rawRhs
  , rawFunBody
  , rawPattern
  , rawTy
    -- * Declarations, blocks and whole files
  , rawDecl
  , printRuleFile
  , printBlock
    -- * Shared with the display renderers
  , subscript
  , tick
  , escapeString
  , escapeChar
  ) where

import Data.List (intercalate)
import qualified Data.List.NonEmpty as NE

import Thena.Core.Term (Literal (..))
import Thena.Instral.Concrete
  ( RawDecl (..)
  , RawFunction (..)
  , RawRule (..)
  , RawSignature (..)
  , RawTest (..)
  , RawTy (..)
  , RawBody (..)
  , RawInstr (..)
  , RawOp (..)
  , RawOperand (..)
  , RawPattern (..)
  , RawRhs (..)
  )
-- The reader's own @RawRule@ is a record and its accessors are imported
-- without the type, which is already taken here by @instral@'s rule.
import Thena.Language.Reader
  ( Block (..)
  , Metadata (..)
  , Production (..)
  , RawItem (..)
  , ruleConclusion
  , ruleName
  , rulePremises
  , ruleQuantifier
  )
import Thena.Syntax.Lexer (BlockKind (..))
import Thena.Surface.Concrete
  ( ObjectPiece (..)
  , Plicity (..)
  , Surface (..)
  , SurfaceArg (..)
  , SurfaceBinder (..)
  )

-- | A surface term, as written (MS4 phase 39).
--
-- **Its own function, not a case of the development printer.** The two
-- languages print
-- differently — a surface lambda's binder may have no type, its arguments carry
-- braces, and it has @_@ and @?foo@ where the development calculus has neither.
-- Sharing one printer would mean a printer that has to ask which language it is
-- in, which is the special case the first design principle refuses.
--
-- Parenthesised by precedence, and it round-trips: 'Thena.Surface.Parser.parseSurface'
-- on this output gives the same tree back.
renderSurface :: Surface -> String
renderSurface = surf Loose

rawInstruction :: RawInstr -> String
rawInstruction i = case i of
  RawBind x r  -> rawPattern x ++ " = " ++ rawRhs r
  RawDo     o  -> rawOperation o
  -- **A surface @do@ block cannot contain one** (MS5 phase 77): the surface
  -- grammar has no type notation, and a block in a surface term is not
  -- type-checked anyway (@ms5\/CLOSEOUT.md@ 20), so an annotation there
  -- would be decoration. This printer never meets one; it answers rather
  -- than leaving the case open.
  RawAnnot x _ -> x

rawRhs :: RawRhs -> String
rawRhs r = case r of
  RhsOp o    -> rawOperation o
  RhsValue a -> rawOperand a

-- **A block body prints explicitly** (MS5 phase 75b). This printer is
-- crossed against its reader, and layout is a pass the reader runs before
-- the grammar sees anything — so printing an indented block would be
-- printing something this module cannot claim reads back. Braces do.
rawFunBody :: RawBody -> String
rawFunBody b = case b of
  BodyRhs r      -> rawRhs r
  BodyBlock is   -> "do { " ++ intercalate " ; " (map rawInstruction is) ++ " }"

-- | A pattern, as written.
--
-- **Text and characters go through 'escapeString' and 'escapeChar', not
-- @show@** — that was @ms6\/CLOSEOUT.md@ 2, and it is the bug that stopped a
-- printed rule file reading back: @show@ renders @∀@ as @\\8704@, which the
-- lexer does not accept. The surface case a few lines below always used the
-- right pair; these did not, and nothing exercised them until a whole rule file
-- had to be printed and re-read (MS7 phase 112c).
rawPattern :: RawPattern -> String
rawPattern rp = case rp of
  RawPWord w   -> w
  RawPInt k    -> show k
  RawPChar c   -> escapeChar c
  RawPText t   -> escapeString t
  RawPApp w as -> "(" ++ unwords (w : map rawPattern as) ++ ")"
  RawPPair a b -> "(" ++ rawPattern a ++ ", " ++ rawPattern b ++ ")"
  -- Exact, because a region keeps its source text (MS6 phase 104c).
  RawPObject tag prod src ->
    tag ++ maybe "" (\w -> "[" ++ w ++ "]") prod ++ [tick] ++ src ++ [tick]
  RawPList ps mt ->
    "[" ++ intercalate ", " (map rawPattern ps ++ tl) ++ "]"
    where tl = case mt of
                 Nothing -> []
                 Just t  -> ["..." ++ rawPattern t]

rawOperation :: RawOp -> String
rawOperation (RawOp w as) = unwords (w : map rawOperand as)

rawOperand :: RawOperand -> String
rawOperand a = case a of
  RawLambda ps b -> "\\ " ++ unwords (map rawPattern ps) ++ " -> " ++ rawFunBody b
  RawRef x  -> x
  RawPos k  -> show k
  RawText t -> escapeString t
  RawChar c -> escapeChar c
  RawList os    -> "[" ++ intercalate ", " (map rawOperand os) ++ "]"
  RawPairOf x y -> "(" ++ rawOperand x ++ ", " ++ rawOperand y ++ ")"
  -- Exact, because the region kept its source text: a rule listing shows
  -- the embedded term as the author wrote it.
  RawRegion tag prod src ->
    tag ++ maybe "" (\w -> "[" ++ w ++ "]") prod ++ [tick] ++ src ++ [tick]
  -- The same gap 'renderValue' has for a 'Thena.Instral.Ops.VRaw': there is no
  -- printer for written syntax, so this says what it is rather than what it
  -- contains (§7b's register).
  RawQuoted _       -> "⌜…⌝"
  -- A nested call, written back as it was written (MS5 phase 63). This is
  -- the one place a rule listing shows the /written/ form rather than the
  -- resolved one — resolution lifts it into a binding of its own.
  RawNested w as    -> "(" ++ unwords (w : map rawOperand as) ++ ")"

surf :: SurfacePrec -> Surface -> String
surf _ (SurfaceName x)      = x
surf _ (SurfaceUniverse l)  = "Type" ++ subscript l
surf _ (SurfaceLiteral l)   = case l of
  LString s -> escapeString s
  LChar c   -> escapeChar c
  LInt k    -> show k
  LRegex r  -> "/" ++ r ++ "/"
-- **A tagged term literal prints as it was written** (MS6 phase 104): its
-- text is kept, and only the three characters the region scanner reads
-- specially are put back behind a backslash. A splice prints as a term,
-- because that is what it holds.
surf _ (SurfaceObject lang prod ps) =
  lang ++ maybe "" (\p -> "[" ++ p ++ "]") prod
    ++ [tick] ++ concatMap objectPiece ps ++ [tick]
surf _ SurfaceUniverseOpen  = "Type"
surf _ SurfacePlaceholder   = "_"
surf _ (SurfaceHole h)      = "?" ++ h
-- **Printed with explicit braces and semicolons**, never re-laid-out: the
-- grammar accepts both spellings and this is the one that is unambiguous on
-- one line, which is what every other case here produces too.
surf _ (SurfaceDo b)        =
  "do { " ++ intercalate " ; " (map rawInstruction b) ++ " }" 
surf p (SurfaceApp f as)    =
  paren (p >= Tight) (surf Spine f ++ concatMap arg (NE.toList as))
-- **The body of each of these four is @Arrowed@ and not @Term@**, which is
-- what the grammar says and what an ascription inside one turns on. A
-- binder's own type and a @let@'s annotation and value are @Term@, so they
-- stay @Loose@.
surf p (SurfaceLam bs b)    =
  paren (p >= Spine) ("λ" ++ concatMap binder (NE.toList bs) ++ " -> " ++ surf Arrowed b)
surf p (SurfacePi bs b)     =
  paren (p >= Spine) ("∀" ++ concatMap binder (NE.toList bs) ++ " -> " ++ surf Arrowed b)
surf p (SurfaceArrow a b)   =
  paren (p >= Spine) (surf Tight a ++ " -> " ++ surf Arrowed b)
surf p (SurfaceLet x ty v b) =
  paren (p >= Spine)
    ("let " ++ x ++ maybe "" (\t -> " : " ++ surf Loose t) ty
       ++ " = " ++ surf Loose v ++ " in " ++ surf Arrowed b)
-- @Term : Arrowed ':' Arrowed@ — both sides, and it needs its own
-- parentheses anywhere an @Arrowed@ is wanted.
surf p (SurfaceAnnot e ty)  =
  paren (p >= Arrowed) (surf Arrowed e ++ " : " ++ surf Arrowed ty)
surf p (SurfaceElim d ps mot ms is tgt) =
  paren (p >= Tight)
    ("elim " ++ d ++ " " ++ list ps ++ " " ++ surf Tight mot ++ " " ++ list ms
       ++ " " ++ list is ++ " " ++ surf Tight tgt)

objectPiece :: ObjectPiece -> String
objectPiece pc = case pc of
  ObjectText txt -> concatMap escapeRaw txt
  ObjectSplice e -> "$" ++ ['{'] ++ surf Loose e ++ ['}']

-- The region scanner reads a backslash before any of these as the
-- character itself, so writing them this way is what makes the printer's
-- output readable again.
escapeRaw :: Char -> String
escapeRaw c
  | c `elem` [tick, '\\', '$'] = ['\\', c]
  | otherwise                  = [c]

arg :: SurfaceArg -> String
arg (SurfaceArg Explicit t) = " " ++ surf Tight t
arg (SurfaceArg Implicit t) = " {" ++ surf Loose t ++ "}"

binder :: SurfaceBinder -> String
binder (SurfaceBinder Explicit x Nothing)   = " " ++ x
binder (SurfaceBinder Explicit x (Just ty)) = " (" ++ x ++ " : " ++ surf Loose ty ++ ")"
binder (SurfaceBinder Implicit x Nothing)   = " {" ++ x ++ "}"
binder (SurfaceBinder Implicit x (Just ty)) = " {" ++ x ++ " : " ++ surf Loose ty ++ "}"

list :: [Surface] -> String
list ts = "(" ++ unwords (map (surf Tight) ts) ++ ")"

paren :: Bool -> String -> String
paren True t  = "(" ++ t ++ ")"
paren False t = t

-- | Where a surface term is being printed, and therefore what has to be
-- parenthesised.
--
-- **One level per non-terminal of @Surface.Parser@, and they are listed in that
-- grammar's order** — @Loose@ is @Term@, @Arrowed@ is @Arrowed@, @Spine@ is
-- @App@, @Tight@ is @Atom@. Anything else is a guess about what nests inside
-- what.
--
-- @Arrowed@ arrived 2026-09-12, and its absence was a real defect: with three
-- levels against the grammar's four, the body of a λ, a @∀@, an arrow and a
-- @let@ were all printed at @Term@, which admits an ascription that the body
-- position does not. So @λ x -> (x : y)@ printed as @λ x -> x : y@ and read back
-- as @(λ x -> x) : y@ — a different term, silently — and @a : (b : c)@ printed
-- as @a : b : c@, which does not parse at all.
data SurfacePrec = Loose | Arrowed | Spine | Tight
  deriving (Eq, Ord)

-- | A universe's level, as the digits the lexer reads: @Type₀@.
--
-- Here rather than in "Thena.Repl" because both printers need it and this is
-- the lower module.
subscript :: Int -> String
subscript = map sub . show
  where
    sub c = toEnum (fromEnum '₀' + (fromEnum c - fromEnum '0'))

-- | The backtick, written by its code point so the source of this module is not
-- fighting Haskell's own quoting.
tick :: Char
tick = toEnum 96

-- | A string literal as the lexer reads it back: @\"@, @\\@ and @\n@ are the
-- three escapes @\@escape@ accepts, and every other character stands for
-- itself — a tab included, which is why this is not @show@.
escapeString :: String -> String
escapeString s = "\"" ++ concatMap esc s ++ "\""
  where
    esc c = case c of
      '"'  -> "\\\""
      '\\' -> "\\\\"
      '\n' -> "\\n"
      _    -> [c]

-- | A character literal, escaped as @\@chresc@ reads it.
escapeChar :: Char -> String
escapeChar c = "'" ++ esc ++ "'"
  where
    esc = case c of
      '\'' -> "\\'"
      '\\' -> "\\\\"
      '\n' -> "\\n"
      _    -> [c]

-- --------------------------------------------------------------------------
-- Declarations, blocks and whole files
-- --------------------------------------------------------------------------

-- | An @instral@ type, as written.
rawTy :: RawTy -> String
rawTy t = case t of
  RawTyVar a       -> a
  RawTyUnit        -> "()"
  RawTyCon c []    -> c
  RawTyCon c as    -> c ++ " " ++ unwords (map rawTyAtom as)
  RawTyPair a b    -> "(" ++ rawTy a ++ ", " ++ rawTy b ++ ")"
  RawTyArrow a b   -> rawTyAtom a ++ " -> " ++ rawTy b
  RawTyGroup a     -> "(" ++ rawTy a ++ ")"

rawTyAtom :: RawTy -> String
rawTyAtom t = case t of
  RawTyVar a    -> a
  RawTyUnit     -> "()"
  RawTyCon c [] -> c
  RawTyPair {}  -> rawTy t
  RawTyGroup {} -> rawTy t
  _             -> "(" ++ rawTy t ++ ")"

-- | A rule-file declaration.
--
-- **A body is always written as a @do@ block**, whatever it was written as: a
-- one-line right-hand side and a block mean the same thing to the reader, and
-- picking one shape is what makes this a canonical printer rather than a
-- reconstruction of the original file.
rawDecl :: RawDecl -> [String]
rawDecl d = case d of
  DeclSignature (RawSignature n t) -> [n ++ " : " ++ rawTy t]
  DeclFunction (RawFunction n ps b) ->
    header (n ++ concatMap ((" " ++) . rawPattern) ps) b
  DeclRule (RawRule n ps ts is) ->
    ("rule " ++ n ++ concatMap ((" " ++) . rawPattern) ps ++ " :-" ++ whens ts ++ " do")
      : map (("  " ++) . rawInstruction) is
  where
    header lhs b = case b of
      BodyRhs r    -> [lhs ++ " = " ++ rawRhs r]
      BodyBlock is -> (lhs ++ " = do") : map (("  " ++) . rawInstruction) is

    -- @Rule@ is @rule ident Params ':-' Tests do Block@ and @Tests@ is one
    -- @when@ followed by however many tests, so the keyword is written once and
    -- the tests are juxtaposed after it.
    whens [] = ""
    whens ts = " when " ++ unwords (map test ts)

    -- A test with operands is parenthesised; a bare one is not. That is the
    -- grammar's own distinction (@Test@), not a choice about spacing.
    test (RawTest w []) = w
    test (RawTest w as) = "(" ++ w ++ " " ++ unwords (map rawOperand as) ++ ")"

-- | A whole rule file: its docstring, its header, and its declarations.
printRuleFile :: String -> Maybe String -> [RawDecl] -> String
printRuleFile nm desc ds =
  unlines (docstring ++ ["rule base " ++ nm ++ " where", ""] ++ body)
  where
    docstring = maybe [] (\d -> ["\"\"\"" ++ d ++ "\"\"\"", ""]) desc
    body = intercalate [""] (map rawDecl ds)

-- --------------------------------------------------------------------------
-- Object-language blocks
-- --------------------------------------------------------------------------

-- | A @language@, @context@ or @judgment@ block, as written.
--
-- **The dashed line is syntax, not decoration** — the reader takes the premises
-- above it and the conclusion below — so it is printed, and **it is as long as
-- the longest premise or conclusion** (his instruction, 2026-09-24).
--
-- **Each premise goes on its own line**, whatever the original did. That is his
-- instruction and it is also exactly faithful: a line break ends a premise
-- (@Thena.Language.Reader@), so an element of 'rulePremises' /is/ a line, and
-- several premises written on one line are one element and stay one line.
printBlock :: Block -> String
printBlock b =
  unlines (headerLine : productions ++ concatMap judgmentRule (blockRules b))
  where
    -- **The two header shapes are the reader's, not a choice made here.** A
    -- judgment is @‹name› = ‹notation› where@ and carries its notation's words
    -- where the other kinds carry their metavariables; a language or a context
    -- is @‹name›, ‹metavars› where@. 'readJudgmentHeader' is the other half of
    -- this and it branches the same way.
    headerLine = case blockKind b of
      JudgmentBlock ->
        "judgment " ++ blockName b ++ " = " ++ unwords (map item notation) ++ " where"
      k ->
        kindWord k ++ " " ++ intercalate ", " (blockName b : blockMetavars b) ++ " where"

    -- **A judgment's notation is stored as its one production** — 'readBlock'
    -- builds @Block kind n [] [Production l0 n Nothing items] rules@ — so it is
    -- printed in the header and not again below it. A language or a context has
    -- no notation in its header and all its productions underneath.
    notation = concatMap productionItems (blockProductions b)

    productions = case blockKind b of
      JudgmentBlock -> []
      _             -> map production (blockProductions b)

    production p =
      "  "
        ++ productionName p
        ++ maybe "" ((" : " ++) . metadata) (productionMetadata p)
        ++ " -> "
        ++ unwords (map item (productionItems p))

    metadata m = case m of
      AsOccurrence x -> x ++ " as occurrence"
      AsBinders [x]  -> x ++ " as binder"
      AsBinders xs   -> "{ " ++ intercalate ", " xs ++ " } as binders"

    item i = case i of
      Word w       -> w
      Binding w xs -> w ++ "[" ++ intercalate ", " xs ++ "]"

    -- **Two rule headers, and they are the reader's two tiers** (§6.1, §6.4):
    -- a plain rule is @‹name›:@, and one that quantifies is
    -- @rule ‹name› where ∀ … ->@. 'readRule' accepts exactly these, so a
    -- quantified rule printed in the plain form does not read back — which is
    -- how this was found.
    judgmentRule r =
      ""
        : ("  " ++ maybe (ruleName r ++ ":") quantified (ruleQuantifier r))
        : map ("    " ++) (rulePremises r)
          ++ ["    " ++ replicate width dash, "    " ++ ruleConclusion r]
      where
        width = maximum (map length (ruleConclusion r : rulePremises r))
        quantified q = "rule " ++ ruleName r ++ " where " ++ q ++ " ->"

-- | The character a rule line is drawn with.
dash :: Char
dash = '-'

kindWord :: BlockKind -> String
kindWord k = case k of
  LanguageBlock -> "language"
  ContextBlock  -> "context"
  JudgmentBlock -> "judgment"
