{
module Parser where

import Grammar
import Lexer
}

%name      parseExpr
%tokentype { Token }
%error     { parseError }
%monad     { Either String }{ >>= }{ return }

%token IDENT  { Ident $$ }
%token IMPL   { ImplT }
%token OR     { OrT }
%token AND    { AndT }
%token NOT    { NotT }
%token LEFTP  { LeftP }
%token RIGHTP { RightP }

%%

Expr
  : Disj               { $1 }
  | Disj IMPL Expr     { Impl $1 $3 }

Disj
  : Conj               { $1 }
  | Disj OR Conj       { Or $1 $3 }

Conj
  : Term               { $1 }
  | Conj AND Term      { And $1 $3 }

Term
  : NOT Term           { Neg $2 }
  | LEFTP Expr RIGHTP  { $2 }
  | IDENT              { Var $1 }

{
parseError = fail "Parse error"
}
