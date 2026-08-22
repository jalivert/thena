{
module Thena.Syntax.Parser
  ( ParseError (..)
  , parseTerm
  , parseNameAndType
  , parseData
  ) where

import Thena.Syntax.Concrete
  ( Raw (..)
  , RawBinder (..)
  , RawConstraint (..)
  , RawConstructor (..)
  , RawData (..)
  )
import Thena.Syntax.Lexer (Located (..), Pos, Token (..))
}

%name parseTerm Term
%name parseNameAndType NameAndType
%name parseData Data
%tokentype { Located Token }
%monad { Either ParseError }
%error { parseError }

%token
  'λ'     { Located _ TLambda }
  '∀'     { Located _ TForall }
  '->'    { Located _ TArrow }
  '('     { Located _ TLParen }
  ')'     { Located _ TRParen }
  '{'     { Located _ TLBrace }
  '}'     { Located _ TRBrace }
  ';'     { Located _ TSemi }
  ':'     { Located _ TColon }
  '='     { Located _ TEquals }
  '?'     { Located _ TQuery }
  '≐'     { Located _ TGuessed }
  '▸'     { Located _ TThen }
  '⊢'     { Located _ TTurnstile }
  '≟'     { Located _ TEquate }
  '[|'    { Located _ TOpenQuote }
  '|]'    { Located _ TCloseQuote }
  let     { Located _ TLet }
  in      { Located _ TIn }
  elim    { Located _ TElim }
  univ    { Located _ (TUniverse $$) }
  ident   { Located _ (TIdent $$) }

%right '->'

%%

Term :: { Raw }
  : 'λ' Binders '->' Term                          { RawLam (reverse $2) $4 }
  | '∀' Binders '->' Term                          { RawPi (reverse $2) $4 }
  | let ident '=' Term ':' Term in Term            { RawLet $2 $4 $6 $8 }
  | let '?' ident ':' Term in Term                 { RawClaim $3 $5 $7 }
  | let '?' ident ':' Term '≐' '(' Term ')' in Term
                                                   { RawGuess $3 $5 $8 $11 }
  | Constraint '▸' Term                            { RawPending $1 $3 }
  | '[|' Term '|]'                                 { RawQuote $2 }
  | elim ident '(' Atoms ')' Atom '(' Atoms ')' '(' Atoms ')' Atom
      { RawElim $2 (reverse $4) $6 (reverse $8) (reverse $11) $13 }
  | App '->' Term                                  { RawArrow $1 $3 }
  | App                                            { $1 }

-- The argument of @assume@ and @claim@ (§2.4's "commands are the op vocabulary
-- spelled out"). The nameless form is the one that makes the op ask (§7.5).
NameAndType :: { (Maybe String, Raw) }
  : ident ':' Term                         { (Just $1, $3) }
  | ':' Term                               { (Nothing, $2) }

-- The argument of @data@ (§2.7's grammar, extended; decided by the user
-- planning phase 6). @data@ itself is not a token: the driver splits the first
-- word off the line before the lexer sees anything, which is what keeps @data@
-- a perfectly good identifier (§2.4).
--
-- Parameters are the binder groups left of the @:@; indices are the arrow
-- prefix of the type right of it, which must end in a universe. That is the
-- split §3.7 requires disambiguated, made syntactic.
Data :: { RawData }
  : ident MaybeBinders ':' Term '{' Constructors '}'
                                           { RawData $1 (reverse $2) $4 (reverse $6) }

MaybeBinders :: { [RawBinder] }
  :                                        { [] }
  | Binders                                { $1 }

-- A datatype with no constructors is legal and useful: @Empty@ (§3.7).
Constructors :: { [RawConstructor] }
  :                                        { [] }
  | SomeConstructors                       { $1 }

SomeConstructors :: { [RawConstructor] }
  : Constructor                            { [$1] }
  | SomeConstructors ';' Constructor       { $3 : $1 }

Constructor :: { RawConstructor }
  : ident ':' Term                         { RawConstructor $1 $3 }

Constraint :: { RawConstraint }
  : Binders '⊢' Term '≟' Term ':' Term   { RawConstraint (reverse $1) $3 $5 $7 }
  | '⊢' Term '≟' Term ':' Term           { RawConstraint [] $2 $4 $6 }

App :: { Raw }
  : App Atom                               { RawApp $1 $2 }
  | Atom                                   { $1 }

Atom :: { Raw }
  : ident                                  { RawName $1 }
  | univ                                   { RawUniverse $1 }
  | '(' Term ')'                           { $2 }

-- A possibly-empty run of atoms, accumulated in reverse like 'Binders'. An
-- 'elim''s three list-valued fields (§2.6, phase 7): each is parenthesized so
-- that a fixed field count and a fixed field order are the whole grammar, with
-- nothing left for a motive or a target to swallow by extending rightward the
-- way a λ or ∀ body does.
Atoms :: { [Raw] }
  :                                        { [] }
  | Atoms Atom                             { $2 : $1 }

-- Accumulated in reverse; the productions above put them back in order.
Binders :: { [RawBinder] }
  : Binder                                 { [$1] }
  | Binders Binder                         { $2 : $1 }

Binder :: { RawBinder }
  : '(' ident ':' Term ')'                 { RawBinder $2 $4 }

{

-- | Structured, per §12 invariant 2.
data ParseError
  = UnexpectedToken Pos Token
  | UnexpectedEndOfInput
  deriving (Eq, Show)

parseError :: [Located Token] -> Either ParseError a
parseError ts = Left $ case ts of
  Located p t : _ -> UnexpectedToken p t
  []              -> UnexpectedEndOfInput
}
