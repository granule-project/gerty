{
{-# LANGUAGE FlexibleContexts #-}

module Dlam.Parser where

import Numeric
import System.Exit
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class (lift)

import Dlam.Lexer
import Dlam.Syntax
import Dlam.Options

}

%name program Program
%name expr Expr
%tokentype { Token }
%error { parseError }
%monad { ReaderT String (Either String) }

%token
    nl      { TokenNL _ }
    let     { TokenLet _ }
    '_'     { TokenWild _ }
    in      { TokenIn  _  }
    VAR     { TokenSym _ _ }
    LANG    { TokenLang _ _ }
    NAT     { TokenNat _ _ }
    '\\'    { TokenLambda _ }
    '->'    { TokenArrow _ }
    '*'     { TokenProd _ }
    '='     { TokenEq _ }
    '('     { TokenLParen _ }
    ')'     { TokenRParen _ }
    ':'     { TokenSig _ }
    ','     { TokenComma _ }

%right in
%right '->'
%left ':'
%right '*'
%left '+' '-'
%%

Program :: { (AST NoExt, [Option]) }
  : LangOpts Stmts  { (AST ($2 $1), $1) }

LangOpts :: { [Option] }
  : LANG NL LangOpts    {% (readOption $1) >>= (\opt -> addOption opt $3) }
  | LANG                {% readOption $1 >>= (return . (:[])) }
  | {- empty -}         { [] }

Stmts :: { [Option] -> [Stmt NoExt] }
  : Stmt NL Stmts { \opts -> ($1 opts) : ($3 opts) }
  | Stmt          { \opts -> pure ($1 opts) }

Stmt :: { [Option] -> Stmt NoExt }
  : VAR ':' Expr { \opts -> StmtType (symString $1) ($3 opts) }
  | VAR '=' Expr { \opts -> StmtAssign (symString $1) ($3 opts) }

NL :: { () }
  : nl NL                     { }
  | nl                        { }

Expr :: { [Option] -> Expr NoExt }
  : let VAR '=' Expr in Expr
    { \opts ->
      if isML opts
       then GenLet (mkIdentFromSym $2) ($4 opts) ($6 opts)
       else App (Abs (mkAbs (mkIdentFromSym $2) Wild ($6 opts))) ($4 opts) }

  | Expr '->' Expr   { \opts -> FunTy (mkAbs ignoreVar ($1 opts) ($3 opts)) }
  | TyBindings '->' Expr { \opts -> foldr (\(n, ty) fty -> FunTy (mkAbs n ty fty)) ($3 opts) ($1 opts) }

  | '\\' LambdaArgs '->' Expr
    { \opts -> foldr (\(n, ty) rty -> Abs (mkAbs n ty rty)) ($4 opts) ($2 opts) }


  | Expr '*' Expr   { \opts -> ProductTy (mkAbs ignoreVar ($1 opts) ($3 opts)) }

  | '(' VAR ':' Expr ')' '*' Expr { \opts -> ProductTy (mkAbs (mkIdentFromSym $2) ($4 opts) ($7 opts)) }

  | let '(' VAR ',' VAR ')' '=' Expr in Expr { \opts -> PairElim (mkIdentFromSym $3) (mkIdentFromSym $5) ($8 opts) ($10 opts) }

  | Expr ':' Expr  { \opts -> Sig ($1 opts) ($3 opts) }

  | Juxt
    { $1 }


Juxt :: { [Option] -> Expr NoExt }
  : Juxt Atom                 { \opts -> App ($1 opts) ($2 opts) }
  | Atom                      { $1 }

Atom :: { [Option] -> Expr NoExt }
  : '(' Expr ')'              { $2 }
  | VAR                       { \opts -> Var $ mkIdentFromSym $1 }
  | '_'                       { \opts -> Wild }
  | NAT                       { \opts -> LitLevel (natTokenToInt $1) }
  | '(' Expr ',' Expr ')'     { \opts -> Pair ($2 opts) ($4 opts) }

  -- For later
  -- | '?' { Hole }

-- List of space-separated identifiers.
VarsSpaced :: { [Identifier] }
  : VAR            { [mkIdentFromSym $1] }
  | VAR VarsSpaced { mkIdentFromSym $1 : $2 }

-- Arguments for a lambda term.
LambdaArg :: { [Option] -> [(Identifier, Expr NoExt)] }
  : VAR       { \opts -> [(mkIdentFromSym $1, Wild)] }
  | TyBinding { \opts -> $1 opts }

LambdaArgs :: { [Option] -> [(Identifier, Expr NoExt)] }
  : LambdaArg { \opts -> $1 opts }
  | LambdaArg LambdaArgs { \opts -> $1 opts <> $2 opts }

-- syntax for bindings in a type
TyBinding :: { [Option] -> [(Identifier, Expr NoExt)] }
  : '(' VAR VarsSpaced ':' Expr ')'
    { \opts -> let ty = $5 opts in fmap (\n -> (n, ty)) (mkIdentFromSym $2 : $3) }
  | '(' VAR ':' Expr ')'        { \opts -> [((mkIdentFromSym $2), $4 opts)] }

TyBindings :: { [Option] -> [(Identifier, Expr NoExt)] }
  : TyBinding            { \opts -> $1 opts }
  | TyBinding TyBindings { \opts -> $1 opts <> $2 opts }

{

readOption :: Token -> ReaderT String (Either String) Option
readOption (TokenLang _ x) | x == "lang.ml"    = return ML
readOption (TokenLang _ x) = lift . Left $ "Unknown language option: " <> x
readOption _ = lift . Left $ "Wrong token for language"

parseError :: [Token] -> ReaderT String (Either String) a
parseError [] = lift . Left $ "Premature end of file"
parseError t  =  do
    file <- ask
    lift . Left $ file <> ":" <> show l <> ":" <> show c
                        <> ": parse error"
  where (l, c) = getPos (head t)

parseProgram :: FilePath -> String -> Either String (AST NoExt, [Option])
parseProgram file input = runReaderT (program $ scanTokens input) file

natTokenToInt :: Token -> Int
natTokenToInt (TokenNat _ x) = x

mkIdentFromSym :: Token -> Identifier
mkIdentFromSym = mkIdent . symString

}
