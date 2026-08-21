{
module Thena.Syntax.Parser
  ( ParseError (..)
  , parseTerm
  ) where

import Thena.Syntax.Concrete (Raw (..), RawBinder (..), RawConstraint (..))
import Thena.Syntax.Lexer (Located (..), Pos, Token (..))
}

%name parseTerm Term
%tokentype { Located Token }
%monad { Either ParseError }
%error { parseError }

%token
  'λ'     { Located _ TLambda }
  '∀'     { Located _ TForall }
  '->'    { Located _ TArrow }
  '('     { Located _ TLParen }
  ')'     { Located _ TRParen }
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
  | App '->' Term                                  { RawArrow $1 $3 }
  | App                                            { $1 }

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
