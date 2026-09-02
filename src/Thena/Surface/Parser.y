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
  univ    { Located _ (TUniverse $$) }
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
