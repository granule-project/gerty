{
{-# LANGUAGE FlexibleContexts #-}

module Language.Dlam.Syntax.Parser
  ( parseProgram
  ) where

import Numeric
import System.Exit
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class (lift)

import Language.Dlam.Syntax.Lexer
import Language.Dlam.Syntax.PrettyPrint (pprint)
import Language.Dlam.Syntax.Syntax

}

%name program Program
%name expr Expr
%tokentype { Token }
%error { parseError }
%monad { ReaderT String (Either String) }

%token
    nl      { TokenNL _ }
    let     { TokenLet _ }
    rewrite { TokenRewrite _ }
    '_'     { TokenImplicit _ }
    case    { TokenCase _ }
    inl     { TokenInl _ }
    inr     { TokenInr _ }
    zero    { TokenZero _ }
    succ    { TokenSucc _ }
    of      { TokenOf _ }
    in      { TokenIn  _  }
    VAR     { TokenSym _ _ }
    LANG    { TokenLang _ _ }
    NAT     { TokenNat _ _ }
    '\\'    { TokenLambda _ }
    '->'    { TokenArrow _ }
    '*'     { TokenProd _ }
    '+'     { TokenPlus _ }
    '='     { TokenEq _ }
    '('     { TokenLParen _ }
    ')'     { TokenRParen _ }
    ':'     { TokenSig _ }
    ','     { TokenComma _ }
    '.'     { TokenDot _ }
    ';'     { TokenSemiColon _ }
    '@'     { TokenAt _ }

%right in
%right '->'
%left ':'
%right '*'
%left '+' '-'
%%

Program :: { ParseAST }
  : Declarations  { AST $1 }

Declarations :: { [ParseDeclaration] }
  : Declaration NL Declarations { $1 : $3 }
  | Declaration          { pure $1 }

NL :: { () }
  : nl NL                     { }
  | nl                        { }

----------------------
---- Declarations ----
----------------------

-- Left-hand side of a function clause
FLHS :: { FLHS }
  -- we only support names for the moment
  : Ident { FLHSName $1 }
  -- TODO: add support for parsing patterns on the LHS (2020-02-29)

Declaration :: { Declaration }
  : FunctionDeclaration { $1 }

FunctionDeclaration :: { Declaration }
  : FLHS FRHS { funAssignOrTypeSig $1 $2 }

-- Right-hand side of a function clause
FRHS :: { FRHSOrTypeSig }
  -- Assignment
  : '=' Expr { IsRHS (FRHSAssign $2) }
  -- Type signature
  | ':' Expr { IsTypeSig $2 }

Ident :: { Identifier }
  : VAR { mkIdentFromSym $1 }

Expr :: { ParseExpr }
  : Expr '->' Expr   { FunTy (mkAbs ignoreVar $1 $3) }
  | TyBindings '->' Expr { foldr (\(n, ty) fty -> FunTy (mkAbs n ty fty)) $3 $1 }

  | '\\' LambdaArgs '->' Expr
    { foldr (\(n, ty) rty -> Abs (mkAbs n ty rty)) $4 $2 }


  | Expr '*' Expr   { ProductTy (mkAbs ignoreVar $1 $3) }

  | '(' Ident ':' Expr ')' '*' Expr { ProductTy (mkAbs $2 $4 $7) }

  | Expr '+' Expr   { Coproduct $1 $3 }

  | let Ident '@' '(' Ident ',' Ident ')' '=' Expr in '(' Expr ':' Expr ')' { PairElim ($2, $15) ($5, $7, $13) $10 }

  | let '(' Ident ',' Ident ')' '=' Expr in Expr { PairElim (ignoreVar, mkImplicit) ($3, $5, $10) $8 }

  | rewrite '(' Ident '.' Ident '.' Ident '.' Expr ',' Ident '.' Expr ',' Expr ',' Expr ',' Expr ')' { RewriteExpr $3 $5 $7 $9 $11 $13 $15 $17 $19 }

  | case Ident '@' Expr of '(' inl Ident '->' Expr ';' inr Ident '->' Expr ')' ':' Expr
    { CoproductCase ($2, $18) ($8, $10) ($13, $15) $4 }

  | case Ident '@' Expr of '(' zero '->' Expr ';' succ Ident '@' Ident '->' Expr ')' ':' Expr
    { NatCase ($2, $19) $9 ($12, $14, $16) $4 }

  -- TODO: this might cause issues with binders in dependent function types? (2020-02-22)
  | Expr ':' Expr  { Sig $1 $3 }

  | Juxt
    { $1 }


Juxt :: { ParseExpr }
  : Juxt Atom                 { App $1 $2 }
  | Atom                      { $1 }

Atom :: { ParseExpr }
  : '(' Expr ')'              { $2 }
  | Ident                       { Var $1 }
  | '_'                       { mkImplicit }
  | NAT                       { LitLevel (natTokenToInt $1) }
  | '(' Expr ',' Expr ')'     { Pair $2 $4 }

  -- For later
  -- | '?' { Hole }

-- List of space-separated identifiers.
VarsSpaced :: { [Identifier] }
  : Ident            { [$1] }
  | Ident VarsSpaced { $1 : $2 }

-- Arguments for a lambda term.
LambdaArg :: { [(Identifier, ParseExpr)] }
  : Ident       { [($1, mkImplicit)] }
  | TyBinding { $1 }

LambdaArgs :: { [(Identifier, ParseExpr)] }
  : LambdaArg { $1 }
  | LambdaArg LambdaArgs { $1 <> $2 }

-- syntax for bindings in a type
TyBinding :: { [(Identifier, ParseExpr)] }
  : '(' Ident VarsSpaced ':' Expr ')'
    { let ty = $5 in fmap (\n -> (n, ty)) ($2 : $3) }
  | '(' Ident ':' Expr ')'        { [($2, $4)] }

TyBindings :: { [(Identifier, ParseExpr)] }
  : TyBinding            { $1 }
  | TyBinding TyBindings { $1 <> $2 }

{

type ParseExpr = Expr
type ParseAST = AST
type ParseDeclaration = Declaration

parseError :: [Token] -> ReaderT String (Either String) a
parseError [] = lift . Left $ "Premature end of file"
parseError t  =  do
    file <- ask
    lift . Left $ file <> ":" <> show l <> ":" <> show c
                        <> ": parse error"
  where (l, c) = getPos (head t)

parseProgram :: FilePath -> String -> Either String ParseAST
parseProgram file input = runReaderT (program $ scanTokens input) file

natTokenToInt :: Token -> Int
natTokenToInt (TokenNat _ x) = x

mkIdentFromSym :: Token -> Identifier
mkIdentFromSym = mkIdent . symString

data FRHSOrTypeSig = IsRHS FRHS | IsTypeSig Expr

funAssignOrTypeSig :: FLHS -> FRHSOrTypeSig -> Declaration
funAssignOrTypeSig n (IsRHS e) = FunEqn n e
funAssignOrTypeSig (FLHSName n) (IsTypeSig t) = TypeSig n t
-- TODO: improve error system in parser here to use a monad (2020-03-01)
funAssignOrTypeSig lhs (IsTypeSig _) = error $ "'" <> pprint lhs <> "' is not allowed a type signature"

}
