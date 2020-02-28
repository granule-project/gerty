{
{-# LANGUAGE FlexibleContexts #-}

module Language.Dlam.Syntax.Parser
  ( parseProgram
  ) where

import Numeric
import System.Exit
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class (lift)

import Language.Dlam.Options
import Language.Dlam.Syntax.Lexer
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
    if { TokenIf _ }
    then { TokenThen _ }
    else { TokenElse _ }
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

Program :: { (ParseAST, [Option]) }
  : LangOpts Stmts  { (AST ($2 $1), $1) }

LangOpts :: { [Option] }
  : LANG NL LangOpts    {% (readOption $1) >>= (\opt -> addOption opt $3) }
  | LANG                {% readOption $1 >>= (return . (:[])) }
  | {- empty -}         { [] }

Stmts :: { [Option] -> [ParseStmt] }
  : Stmt NL Stmts { \opts -> ($1 opts) : ($3 opts) }
  | Stmt          { \opts -> pure ($1 opts) }

Stmt :: { [Option] -> ParseStmt }
  : VAR ':' Expr { \opts -> StmtType (symString $1) ($3 opts) }
  | VAR '=' Expr { \opts -> StmtAssign (symString $1) ($3 opts) }

NL :: { () }
  : nl NL                     { }
  | nl                        { }

Ident :: { Identifier }
  : VAR { mkIdentFromSym $1 }

Expr :: { [Option] -> ParseExpr }
  : Expr '->' Expr   { \opts -> FunTy (mkAbs ignoreVar ($1 opts) ($3 opts)) }
  | TyBindings '->' Expr { \opts -> foldr (\(n, ty) fty -> FunTy (mkAbs n ty fty)) ($3 opts) ($1 opts) }

  | '\\' LambdaArgs '->' Expr
    { \opts -> foldr (\(n, ty) rty -> Abs (mkAbs n ty rty)) ($4 opts) ($2 opts) }


  | Expr '*' Expr   { \opts -> ProductTy (mkAbs ignoreVar ($1 opts) ($3 opts)) }

  | '(' Ident ':' Expr ')' '*' Expr { \opts -> ProductTy (mkAbs $2 ($4 opts) ($7 opts)) }

  | Expr '+' Expr   { \opts -> Coproduct ($1 opts) ($3 opts) }

  | let Ident '@' '(' Ident ',' Ident ')' '=' Expr in '(' Expr ':' Expr ')' { \opts -> PairElim ($2, $15 opts) ($5, $7, $13 opts) ($10 opts) }

  | let '(' Ident ',' Ident ')' '=' Expr in Expr { \opts -> PairElim (ignoreVar, mkImplicit) ($3, $5, $10 opts) ($8 opts) }

  | rewrite '(' Ident '.' Ident '.' Ident '.' Expr ',' Ident '.' Expr ',' Expr ',' Expr ',' Expr ')' { \opts -> RewriteExpr $3 $5 $7 ($9 opts) $11 ($13 opts) ($15 opts) ($17 opts) ($19 opts) }

  | case Ident '=' Expr of '(' inl Ident '->' Expr ';' inr Ident '->' Expr ')' ':' Expr
    { \opts -> CoproductCase ($2, $18 opts) ($8, $10 opts) ($13, $15 opts) ($4 opts) }

  | case Ident '@' Expr of '(' zero '->' Expr ';' succ Ident '@' Ident '->' Expr ')' ':' Expr
    { \opts -> NatCase ($2, $19 opts) ($9 opts) ($12, $14, $16 opts) ($4 opts) }

  | if Expr then Expr else Expr { \opts -> IfExpr ($2 opts) ($4 opts) ($6 opts) }

  -- TODO: this might cause issues with binders in dependent function types? (2020-02-22)
  | Expr ':' Expr  { \opts -> Sig ($1 opts) ($3 opts) }

  | Juxt
    { $1 }


Juxt :: { [Option] -> ParseExpr }
  : Juxt Atom                 { \opts -> App ($1 opts) ($2 opts) }
  | Atom                      { $1 }

Atom :: { [Option] -> ParseExpr }
  : '(' Expr ')'              { $2 }
  | Ident                       { \opts -> Var $1 }
  | '_'                       { \opts -> mkImplicit }
  | NAT                       { \opts -> LitLevel (natTokenToInt $1) }
  | '(' Expr ',' Expr ')'     { \opts -> Pair ($2 opts) ($4 opts) }

  -- For later
  -- | '?' { Hole }

-- List of space-separated identifiers.
VarsSpaced :: { [Identifier] }
  : Ident            { [$1] }
  | Ident VarsSpaced { $1 : $2 }

-- Arguments for a lambda term.
LambdaArg :: { [Option] -> [(Identifier, ParseExpr)] }
  : Ident       { \opts -> [($1, mkImplicit)] }
  | TyBinding { \opts -> $1 opts }

LambdaArgs :: { [Option] -> [(Identifier, ParseExpr)] }
  : LambdaArg { \opts -> $1 opts }
  | LambdaArg LambdaArgs { \opts -> $1 opts <> $2 opts }

-- syntax for bindings in a type
TyBinding :: { [Option] -> [(Identifier, ParseExpr)] }
  : '(' Ident VarsSpaced ':' Expr ')'
    { \opts -> let ty = $5 opts in fmap (\n -> (n, ty)) ($2 : $3) }
  | '(' Ident ':' Expr ')'        { \opts -> [($2, $4 opts)] }

TyBindings :: { [Option] -> [(Identifier, ParseExpr)] }
  : TyBinding            { \opts -> $1 opts }
  | TyBinding TyBindings { \opts -> $1 opts <> $2 opts }

{

type ParseExpr = Expr
type ParseAST = AST
type ParseStmt = Stmt

readOption :: Token -> ReaderT String (Either String) Option
readOption (TokenLang _ x) = lift . Left $ "Unknown language option: " <> x
readOption _ = lift . Left $ "Wrong token for language"

parseError :: [Token] -> ReaderT String (Either String) a
parseError [] = lift . Left $ "Premature end of file"
parseError t  =  do
    file <- ask
    lift . Left $ file <> ":" <> show l <> ":" <> show c
                        <> ": parse error"
  where (l, c) = getPos (head t)

parseProgram :: FilePath -> String -> Either String (ParseAST, [Option])
parseProgram file input = runReaderT (program $ scanTokens input) file

natTokenToInt :: Token -> Int
natTokenToInt (TokenNat _ x) = x

mkIdentFromSym :: Token -> Identifier
mkIdentFromSym = mkIdent . symString

}
