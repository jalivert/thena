{
-- | The Happy grammar for the **surface language** (MS4 phase 39).
--
-- **A second grammar, over the same lexer.** "Thena.Syntax.Lexer" is shared —
-- the identifier rule, the reserved set and the unicode spellings are decided
-- once for the whole project (@PLAN-interface.md@ §2.6) and must not fork, and
-- phase 40's layout is a pass over that one token stream. The /grammars/ are
-- separate because the two languages disagree about the same syntax: a
-- development-calculus lambda must annotate its binder and a surface one need
-- not, so one @Binder@ nonterminal would either conflict or let each language
-- write the other's.
--
-- One start symbol, 'parseSurface'. Declarations and modules are phase 42;
-- layout is phase 40; @do@ blocks are phase 45.
--
-- Shallow, exactly as "Thena.Syntax.Parser" is: it produces names, and what a
-- name denotes is elaboration's answer.
module Thena.Surface.Parser
  ( SurfaceParseError (..)
  , parseSurface
  , parseSurfaceDecls
  , parseSurfaceModule
  ) where

import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NE

import Thena.Surface.Concrete
  ( Plicity (..)
  , Surface (..)
  , SurfaceDecl (..)
  , SurfaceModule (..)
  , SurfaceData (..)
  , SurfaceConstructor (..)
  , SurfaceArg (..)
  , SurfaceBinder (..)
  )
import Thena.Instral.Concrete (RawInstr (..), RawOp (..), RawOperand (..), RawRhs (..), RawBody (..), RawPattern (..))
import Thena.Syntax.Lexer (Located (..), Pos, Token (..))
}

%name parseSurface Term
%name parseSurfaceDecls Decls
%name parseSurfaceModule Module
%tokentype { Located Token }
%monad { Either SurfaceParseError }
%error { parseError }

%token
  'λ'     { Located _ TLambda }
  '∀'     { Located _ TForall }
  '->'    { Located _ TArrow }
  '('     { Located _ TLParen }
  ')'     { Located _ TRParen }
  '{'     { Located _ TLBrace }
  '}'     { Located _ TRBrace }
  ':'     { Located _ TColon }
  ';'     { Located _ TSemi }
  '?'     { Located _ TQuery }
  '='     { Located _ TEquals }
  let     { Located _ TLet }
  in      { Located _ TIn }
  elim    { Located _ TElim }
  where   { Located _ TWhere }
  data    { Located _ TData }
  module  { Located _ TModule }
  do      { Located _ TDo }
  num     { Located _ (TNumber $$) }
  str     { Located _ (TString $$) }
  chr     { Located _ (TChar $$) }
  '...'   { Located _ TSpread }
  '['     { Located _ TLBracket }
  ']'     { Located _ TRBracket }
  ','     { Located _ TComma }
  univ    { Located _ (TUniverse $$) }
  tagopen  { Located _ (TTagOpen $$) }
  raw      { Located _ (TRaw $$) }
  tagclose { Located _ TTagClose }
  Type    { Located _ TUniverseOpen }
  ident   { Located _ (TIdent $$) }

%right '->'

%%

-- | A run of signatures and equations — a surface module (MS4 phase 42).
--
-- **Separated the way layout separates anything else**, so the same text works
-- with the braces and semicolons written out, which is how a declaration is
-- typed at the REPL until files arrive (phase 43).
--
-- Accumulated reversed and turned round by the caller, which is what every
-- other list in this grammar does.
-- | A proof module (MS4 phase 43): a header, then the declarations.
--
-- **The braces and semicolons are the layout pass's**, exactly as they are for
-- @data … where@ — @where@ became a layout keyword in the same phase, so a file
-- written with indentation and one written with explicit braces reach this
-- production as the same token stream.
Module :: { SurfaceModule }
  : module ident where '{' Decls '}'       { SurfaceModule $2 (reverse $5) }

-- | A block of the **instruction** language (MS4 phase 45).
--
-- **These five productions mirror "Thena.Syntax.Parser"\'s, and that is the
-- phase\'s one judgement call.** Happy has no way to share productions between
-- two grammars, and the alternatives were worse: merging the two parsers would
-- put the surface language and the development calculus in one file, which
-- phase 39 deliberately separated, and lifting the block out as raw tokens
-- before parsing would leave an unparsed hole in a parsed file.
--
-- **What makes the duplication safe is that it is crossed by a test**, not that
-- it is small: @SurfaceTests@ parses the same block text through this grammar
-- and through @parseRule@\'s and asserts the two @[RawInstr]@ are equal. Same
-- arrangement as @commandSummary@ against @dispatch@, and the same admitted
-- cost.
--
-- **The instruction language is term-free**, which is why it can be mirrored at
-- all: an operand is an identifier, a number or a string, so neither copy
-- mentions a term grammar and neither can drift towards one.
Block :: { [RawInstr] }
  : Instr                                  { [$1] }
  | Block ';' Instr                        { $3 : $1 }

-- **A binding's left is a pattern** (MS5 phase 84) — @Thena.Syntax.Parser@'s
-- @Instr@, one grammar over, and §7b's registered duplication for the fourth
-- time. There is no annotation case here, so an @ident@ parts on @=@ alone.
Instr :: { RawInstr }
  : ident '=' InstrRhs                     { RawBind (RawPWord $1) $3 }
  | InstrCompoundPat '=' InstrRhs          { RawBind $1 $3 }
  | InstrOp                                { RawDo $1 }

-- **The same two cases the rule-file grammar has** (MS5 phase 68a) — kept level
-- with @Thena.Syntax.Parser@\'s @Rhs@ by hand, which is §7b's registered
-- duplication: a @do@ block is embedded in a surface term, so Happy cannot share
-- the non-terminal.
InstrRhs :: { RawRhs }
  : InstrOp                                { RhsOp $1 }
  | InstrValueOperand                      { RhsValue $1 }
  | InstrLambda                            { RhsValue $1 }

-- **A lambda inside a @do@ block** (MS5 phase 73) — @Thena.Syntax.Parser@\'s
-- @Lambda@, one grammar over. It was missing until here, which is §7b's
-- registered duplication doing exactly what it was registered to do: phase 68b
-- added lambdas to the rule-file grammar and not to this one, so
-- @do { f = \\ z -> … }@ did not parse.
InstrLambda :: { RawOperand }
  : 'λ' InstrParams '->' InstrFunBody      { RawLambda (reverse $2) $4 }

-- **Level with @Thena.Syntax.Parser@\'s @FunBody@** (MS5 phase 75b) — §7b's
-- registered duplication again, and added here in the same phase this time
-- rather than two phases later.
InstrFunBody :: { RawBody }
  : InstrRhs                               { BodyRhs $1 }
  | do '{' Block '}'                       { BodyBlock (reverse $3) }

-- **Level with @Thena.Syntax.Parser@\'s @Params@ and @PatAtom@** (MS5 phase
-- 82) — §7b's registered duplication a third time, and added in the same phase
-- again. A lambda written inside a @do@ block in a surface term takes the same
-- patterns one written in a rule file does.
InstrParams :: { [RawPattern] }
  :                                        { [] }
  | InstrParams InstrPatAtom               { $2 : $1 }

InstrPatAtom :: { RawPattern }
  : ident                                  { RawPWord $1 }
  | InstrCompoundPat                       { $1 }

InstrCompoundPat :: { RawPattern }
  : num                                    { RawPInt $1 }
  | str                                    { RawPText $1 }
  | chr                                    { RawPChar $1 }
  | '[' ']'                                { RawPList [] Nothing }
  | '[' InstrPatItems ']'                  { RawPList (reverse $2) Nothing }
  | '[' InstrPatItems ',' '...' InstrPatAtom ']' { RawPList (reverse $2) (Just $5) }
  | '[' '...' InstrPatAtom ']'             { RawPList [] (Just $3) }
  | '(' ident InstrPatAtoms ')'            { RawPApp $2 (reverse $3) }
  | '(' InstrPatAtom ',' InstrPatAtom ')'  { RawPPair $2 $4 }

InstrPatAtoms :: { [RawPattern] }
  :                                        { [] }
  | InstrPatAtoms InstrPatAtom             { $2 : $1 }

InstrPatItems :: { [RawPattern] }
  : InstrPatAtom                           { [$1] }
  | InstrPatItems ',' InstrPatAtom         { $3 : $1 }

InstrOp :: { RawOp }
  : ident InstrOperands                    { RawOp $1 (reverse $2) }

InstrOperands :: { [RawOperand] }
  :                                        { [] }
  | InstrOperands InstrOperand             { $2 : $1 }

-- | **The same operands a rule body writes**, and they have to be written out
-- again here because Happy cannot share a non-terminal between two grammars
-- (MS5 phase 65; @discussion\/the-five-languages.md@ §7b records the
-- duplication).
--
-- They were not the same until this phase: a @do@ block could write a name, a
-- number or a string and nothing else, so the character literal of phase 64, the
-- nested call of phase 63 and the literals below were all unwritable in one of
-- @instral@'s three places.
InstrOperand :: { RawOperand }
  : ident                                  { RawRef $1 }
  | InstrValueOperand                      { $1 }

-- Every operand but a bare name — @Thena.Syntax.Parser@\'s @ValueOperand@, one
-- grammar over.
InstrValueOperand :: { RawOperand }
  : '(' InstrLambda ')'                    { $2 }
  | num                                    { RawPos $1 }
  | str                                    { RawText $1 }
  | chr                                    { RawChar $1 }
  | '[' ']'                                { RawList [] }
  | '[' InstrElements ']'                  { RawList (reverse $2) }
  | '(' InstrOperand ',' InstrOperand ')'  { RawPairOf $2 $4 }
  | '(' ident InstrOperands ')'            { RawNested $2 (reverse $3) }
  -- **A tagged region** (MS5 phase 69) — @Thena.Syntax.Parser@\'s two
  -- productions, one grammar over. They were missing until 2026-09-12, so
  -- @do { f surface\`x\` }@ did not parse while the same body in a rule file
  -- did: §7b's registered duplication drifting for the second time, and the
  -- second time it was found by enumerating the forms rather than by reading.
  | tagopen raw tagclose                   { RawRegion $1 $2 }
  | tagopen tagclose                       { RawRegion $1 "" }

InstrElements :: { [RawOperand] }
  : InstrOperand                           { [$1] }
  | InstrElements ',' InstrOperand         { $3 : $1 }

Decls :: { [SurfaceDecl] }
  : Decl                                   { [$1] }
  | Decls ';' Decl                         { $3 : $1 }

-- | **Agda\/Haskell-style: a declaration is two of these.**
-- 'Thena.Surface.Concrete.paired' puts a signature together with the equation
-- that follows it.
Decl :: { SurfaceDecl }
  : ident ':' Term                         { SurfaceSignature $1 $3 }
  | ident '=' Term                         { SurfaceEquation $1 $3 }
  | Datatype                               { SurfaceDatatype $1 }
  -- **A top-level block is an item, not an expression** — his, 2026-09-03.
  -- Same syntax, different role: at the top of a module it plays where the
  -- other items declare.
  | do '{' Block '}'                       { SurfaceBlock (reverse $3) }

-- | **The same shape "Thena.Syntax.Parser"'s @Data@ has**, because §3.7's split
-- between parameters and indices is syntactic in both: the parameters are the
-- binder groups left of the @:@, the indices the arrow prefix of what is right
-- of it.
Datatype :: { SurfaceData }
  : data ident DataParams ':' Term where '{' Constructors '}'
      { SurfaceData $2 (reverse $3) $5 (reverse $8) }

DataParams :: { [(String, Surface)] }
  :                                        { [] }
  | DataParams '(' ident ':' Term ')'      { ($3, $5) : $1 }

-- A datatype with no constructors is legal and useful: @Empty@ (§3.7).
Constructors :: { [SurfaceConstructor] }
  :                                        { [] }
  | SomeConstructors                       { $1 }

SomeConstructors :: { [SurfaceConstructor] }
  : Constructor                            { [$1] }
  | SomeConstructors ';' Constructor       { $3 : $1 }

Constructor :: { SurfaceConstructor }
  : ident ':' Term                         { SurfaceConstructor $1 $3 }

-- | A whole surface term.
--
-- **Ascription binds loosest**, so @\\ x -> x : A -> A@ ascribes the lambda and
-- not its body — the reading Agda and Haskell both give it.
Term :: { Surface }
  : Arrowed ':' Arrowed                    { SurfaceAnnot $1 $3 }
  | Arrowed                                { $1 }

Arrowed :: { Surface }
  : 'λ' LamBinders '->' Arrowed            { SurfaceLam (NE.fromList (reverse $2)) $4 }
  | '∀' PiBinders '->' Arrowed             { SurfacePi (NE.fromList (reverse $2)) $4 }
  | let '{' Bindings '}' in Arrowed        { lets (reverse $3) $6 }
  | App '->' Arrowed                       { SurfaceArrow $1 $3 }
  | App                                    { $1 }

-- **The spine is built here and nowhere else.** A head with no arguments is
-- the head itself, so 'SurfaceApp' can never hold an empty list, and a spine
-- whose head is itself a spine is flattened — see 'spine'.
App :: { Surface }
  : Atom                                   { $1 }
  | Atom Args                              { spine $1 (NE.fromList (reverse $2)) }

Args :: { [SurfaceArg] }
  : Arg                                    { [$1] }
  | Args Arg                               { $2 : $1 }

Arg :: { SurfaceArg }
  : Atom                                   { SurfaceArg Explicit $1 }
  | '{' Term '}'                           { SurfaceArg Implicit $2 }

Atom :: { Surface }
  : ident                                  { name $1 }
  -- **@?foo@ is two tokens, not one.** @?@ cannot start an identifier —
  -- @PLAN-interface.md@ §2.6's @$idstart@ is a letter, @_@, or a character
  -- above ASCII — so the lexer hands over @TQuery@ and then the name. Writing
  -- it as a grammar rule rather than a lexer one keeps @?@ available inside a
  -- name, where it already is.
  | '?' ident                              { SurfaceHole $2 }
  | univ                                   { SurfaceUniverse $1 }
  | Type                                   { SurfaceUniverseOpen }
  | '(' Term ')'                           { $2 }
  -- **An atom, so it needs no parentheses in an argument run** — @try (do { … })@
  -- and @try do { … }@ both read, the same way a parenthesised term does.
  | do '{' Block '}'                       { SurfaceDo (reverse $3) }
  | elim ident '(' Terms ')' Atom '(' Terms ')' '(' Terms ')' Atom
      { SurfaceElim $2 (reverse $4) $6 (reverse $8) (reverse $11) $13 }

Terms :: { [Surface] }
  :                                        { [] }
  | Terms Atom                             { $2 : $1 }

-- A lambda's binder may be a bare name; a @∀@'s may not. The user, 2026-09-01:
-- /"only lambdas with no type annotation? let bindings and global
-- functions\/theorems should have annotation and foralls always have
-- annotations too."/
-- Accumulated in reverse, group by group, and put back in order by the
-- productions above — the same shape "Thena.Syntax.Parser" uses. A group's own
-- names are reversed on the way in so that @(x y : A)@ stays @x@ then @y@.
LamBinders :: { [SurfaceBinder] }
  : LamBinder                              { reverse $1 }
  | LamBinders LamBinder                   { reverse $2 ++ $1 }

LamBinder :: { [SurfaceBinder] }
  : ident                                  { [SurfaceBinder Explicit $1 Nothing] }
  | '(' Names ':' Term ')'                 { group Explicit (reverse $2) (Just $4) }
  | '{' Names ':' Term '}'                 { group Implicit (reverse $2) (Just $4) }
  | '{' Names '}'                          { group Implicit (reverse $2) Nothing }

PiBinders :: { [SurfaceBinder] }
  : PiBinder                               { reverse $1 }
  | PiBinders PiBinder                     { reverse $2 ++ $1 }

PiBinder :: { [SurfaceBinder] }
  : '(' Names ':' Term ')'                 { group Explicit (reverse $2) (Just $4) }
  | '{' Names ':' Term '}'                 { group Implicit (reverse $2) (Just $4) }

-- **The grammar only ever sees explicit braces and semicolons.**
-- "Thena.Surface.Layout" inserts them where the offside rule says they belong,
-- and a program that writes them itself reaches here unchanged — which is what
-- makes the two spellings one language.
Bindings :: { [(String, Maybe Surface, Surface)] }
  : Binding                                { [$1] }
  | Bindings ';' Binding                   { $3 : $1 }

Binding :: { (String, Maybe Surface, Surface) }
  : ident '=' Term                         { ($1, Nothing, $3) }
  | ident ':' Term '=' Term                { ($1, Just $3, $5) }

Names :: { [String] }
  : ident                                  { [$1] }
  | Names ident                            { $2 : $1 }

{

-- | Structured, per §12 invariant 2.
--
-- Its own type rather than "Thena.Syntax.Parser"'s 'ParseError': the two
-- grammars fail at different tokens for different reasons, and one type shared
-- between them would be the first place the two languages got confused for each
-- other.
data SurfaceParseError
  = SurfaceUnexpectedToken Pos Token
  | SurfaceUnexpectedEndOfInput
  deriving (Eq, Show)

parseError :: [Located Token] -> Either SurfaceParseError a
parseError ts = Left $ case ts of
  []                -> SurfaceUnexpectedEndOfInput
  Located p t : _   -> SurfaceUnexpectedToken p t

-- | @_@ is a placeholder and @?foo@ is a named hole; everything else is a name.
--
-- **Neither is a lexer rule**, and that is deliberate. @_@ and @?@ are both
-- legal inside an identifier (@PLAN-interface.md@ §2.6 reserves neither), so
-- the lexer hands over @TIdent "_"@ and @TIdent "?foo"@ and the /surface/
-- grammar decides they mean something here. Making them tokens would take
-- @_@ and a leading @?@ away from names in the development calculus too, for
-- a distinction only this language draws.
name :: String -> Surface
name x = case x of
  "_"      -> SurfacePlaceholder
  '?' : h  -> SurfaceHole h
  _        -> SurfaceName x

-- | Build an application, **flattening a head that is already one**.
--
-- @(f a) b@ and @f a b@ are the same term, and without this they are two
-- different trees — which is exactly the confusion that having a single
-- application constructor was meant to avoid. Parentheses are not represented,
-- so they must not survive as structure.
--
-- **Documented, not enforced.** @SurfaceApp (SurfaceApp …) …@ is still a
-- constructible value; nothing the parser produces is one, and no type stops a
-- hand-written test from building one (@PLAN-representation.md@ §3.4's line).
-- | Flatten a spine as it is parsed, so that @f a b@ and @(f a) b@ are the same
-- tree and a 'SurfaceApp' never has a 'SurfaceApp' for a head.
--
-- **The whole design rests on this staying true of every producer of a
-- 'Surface'**, and there is more than one — @Engine@'s @elim-spine@ assembles a
-- 'SurfaceApp' by hand rather than through this function. The reason a clause
-- needs the flat form is that elaborating @x ⃗a@ wants the head **and the whole
-- argument list at once**: to expand implicits, to walk the head's real
-- telescope, and to claim the domains in telescope order.
--
-- **IF THAT EVER STOPS HOLDING, DO NOT REDESIGN FROM SCRATCH.** Two ways of
-- elaborating a nested application were worked out in 2026-09-09 and written
-- up as @application-representation.md@ in the project's design notes —
-- inside-out (climb back up with the zipper) and outside-in (match the outer
-- application, ask whether its head is one too, and accumulate). The second is
-- the one to try: it needs one new head test and one accumulating instruction,
-- both of a kind the rule language already has. **Check first whether a
-- producer has simply stopped flattening** — that is likelier than the design
-- being wrong, and it is one assertion to test.
spine :: Surface -> NonEmpty SurfaceArg -> Surface
spine (SurfaceApp f as) bs = SurfaceApp f (as <> bs)
spine f                 bs = SurfaceApp f bs

-- | @let { x = a ; y = b } in c@ nests, one 'SurfaceLet' per binding.
--
-- **The bindings are sequential and cannot be mutually recursive**, and that is
-- not a preference: a development is a /chain/ of components, so @y@ is in
-- scope after @x@ and nothing in the development calculus can express two
-- bindings that refer to each other. Recursion comes from eliminators.
--
-- So @let { x = a ; y = b } in c@ and @let x = a in let y = b in c@ are the
-- same tree. Two spellings of one term is what sugar is; what would be wrong is
-- one term with two representations.
lets :: [(String, Maybe Surface, Surface)] -> Surface -> Surface
lets bs body = foldr (\(x, ty, v) b -> SurfaceLet x ty v b) body bs

-- | @(x y : A)@ binds two names at one type. Grouping is a spelling and not a
-- structure: it is expanded here so that nothing downstream can ask how many
-- names shared a pair of parentheses.
group :: Plicity -> [String] -> Maybe Surface -> [SurfaceBinder]
group p xs ty = [ SurfaceBinder p x ty | x <- xs ]
}