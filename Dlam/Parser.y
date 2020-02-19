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
    '|'     { TokenSep _ }
    in      { TokenIn  _  }
    type    { TokenType _ }
    VAR     { TokenSym _ _ }
    LANG    { TokenLang _ _ }
    CONSTR  { TokenConstr _ _ }
    forall  { TokenForall _ }
    '\\'    { TokenLambda _ }
    Lam     { TokenTyLambda _ }
    '->'    { TokenArrow _ }
    '='     { TokenEq _ }
    '('     { TokenLParen _ }
    ')'     { TokenRParen _ }
    ':'     { TokenSig _ }
    '?'     { TokenHole _ }
    '.'     { TokenDot _ }
    '@'     { TokenAt _ }

%right in
%right '->'
%left ':'
%left '+' '-'
%left '*'
%%

Program :: { (Expr NoExt, [Option]) }
  : LangOpts Defs  { ($2 $1, $1) }

LangOpts :: { [Option] }
  : LANG NL LangOpts    {% (readOption $1) >>= (\opt -> addOption opt $3) }
  | LANG                {% readOption $1 >>= (return . (:[])) }
  | {- empty -}         { [] }

Defs :: { [Option] -> Expr NoExt }
  : Def NL Defs           { \opts -> ($1 opts) ($3 opts) }
  | Expr                  { \opts -> $1 opts }

NL :: { () }
  : nl NL                     { }
  | nl                        { }

Def :: { [Option] -> Expr NoExt -> Expr NoExt }
  : VAR '=' Expr { \opts -> \program -> App (Abs (symString $1) Nothing program) ($3 opts) }

Expr :: { [Option] -> Expr NoExt }
  : let VAR '=' Expr in Expr
    { \opts ->
      if isML opts
       then GenLet (symString $2) ($4 opts) ($6 opts)
       else App (Abs (symString $2) Nothing ($6 opts)) ($4 opts) }

  | Expr '->' Expr   { \opts -> FunTy (mkAbs "_" ($1 opts) ($3 opts)) }
  | '(' VAR ':' Expr ')' '->' Expr { \opts -> FunTy (mkAbs (symString $2) ($4 opts) ($7 opts)) }

  | type { \opts -> TypeTy 0 }

  | '\\' '(' VAR ':' Expr ')' '->' Expr
    { \opts -> Abs (symString $3) (Just ($5 opts)) ($8 opts) }

  | '\\' VAR '->' Expr
    { \opts -> Abs (symString $2) Nothing ($4 opts) }

  | Expr ':' Expr  { \opts -> Sig ($1 opts) ($3 opts) }

  | Juxt
    { $1 }


Juxt :: { [Option] -> Expr NoExt }
  : Juxt Atom                 { \opts -> App ($1 opts) ($2 opts) }
  | Atom                      { $1 }

Atom :: { [Option] -> Expr NoExt }
  : '(' Expr ')'              { $2 }
  | VAR                       { \opts -> Var $ symString $1 }

  -- For later
  -- | '?' { Hole }

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

parseProgram :: FilePath -> String -> Either String (Expr NoExt, [Option])
parseProgram file input = runReaderT (program $ scanTokens input) file

}
