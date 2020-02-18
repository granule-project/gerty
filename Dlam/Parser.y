{
{-# LANGUAGE FlexibleContexts #-}

module Lam.Parser where

import Numeric
import System.Exit
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class (lift)

import Lam.Lexer
import Lam.Syntax
import Lam.Options

}

%name program Program
%name expr Expr
%tokentype { Token }
%error { parseError }
%monad { ReaderT String (Either String) }

%token
    nl      { TokenNL _ }
    let     { TokenLet _ }
    case    { TokenCase _ }
    natcase { TokenNatCase _ }
    of      { TokenOf _ }
    '|'     { TokenSep _ }
    fix     { TokenFix _ }
    fst     { TokenFst _ }
    snd     { TokenSnd _ }
    inl     { TokenInl _ }
    inr     { TokenInr _ }
    in      { TokenIn  _  }
    zero    { TokenZero _ }
    succ    { TokenSucc _ }
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
    '*'     { TokenProd _ }
    '+'     { TokenSum _ }
    '<'     { TokenLPair _ }
    '>'     { TokenRPair _ }
    ', '    { TokenMPair _ }
    '.'     { TokenDot _ }
    '@'     { TokenAt _ }

%right in
%right '->'
%left ':'
%left '+' '-'
%left '*'
%%

Program :: { (Expr PCF, [Option]) }
  : LangOpts Defs  { ($2 $1, $1) }

LangOpts :: { [Option] }
  : LANG NL LangOpts    {% (readOption $1) >>= (\opt -> addOption opt $3) }
  | LANG                {% readOption $1 >>= (return . (:[])) }
  | {- empty -}         { [] }

Defs :: { [Option] -> Expr PCF }
  : Def NL Defs           { \opts -> ($1 opts) ($3 opts) }
  | Expr                  { \opts -> $1 opts }

NL :: { () }
  : nl NL                     { }
  | nl                        { }

Def :: { [Option] -> Expr PCF -> Expr PCF }
  : VAR '=' Expr { \opts -> \program -> App (Abs (symString $1) Nothing program) ($3 opts) }
  | zero '=' Expr { \opts ->
        if isPCF opts || isML opts
          then error "Cannot use 'zero' as a variable name"
          else \program -> App (Abs "zero" Nothing program) ($3 opts) }
  | succ '=' Expr { \opts ->
        if isPCF opts || isML opts
          then error "Cannot use 'succ' as a variable name"
          else  \program -> App (Abs "succ" Nothing program) ($3 opts) }

Expr :: { [Option] -> Expr PCF }
  : let VAR '=' Expr in Expr
    { \opts ->
      if isML opts
       then GenLet (symString $2) ($4 opts) ($6 opts)
       else App (Abs (symString $2) Nothing ($6 opts)) ($4 opts) }

  | '\\' '(' VAR ':' Type ')' '->' Expr
    { \opts -> Abs (symString $3) (Just ($5 opts)) ($8 opts) }

  | '\\' VAR '->' Expr
    { \opts -> Abs (symString $2) Nothing ($4 opts) }

  | Lam VAR '->' Expr
    { \opts -> TyAbs (symString $2) ($4 opts) }

  | Expr ':' Type  { \opts -> Sig ($1 opts) ($3 opts) }

  | Juxt
    { $1 }

  | fix '(' Expr ')'
     { \opts ->
      if isPCF opts || isML opts
        then Ext (Fix ($3 opts))
        else error "`fix` doesn't exists in the lambda calculus" }

  | natcase Expr of zero '->' Expr '|' succ VAR '->' Expr
     { \opts ->
          if isPCF opts || isML opts
            then Ext (NatCase ($2 opts) ($6 opts) (symString $9, ($11 opts)))
            else error "`natcase` doesn't exist in the lambda calculus" }

  | fst '(' Expr ')'
     { \opts ->
      if isPCF opts || isML opts
        then Ext (Fst ($3 opts))
        else error "`fst` doesn't exists in the lambda calculus" }

  | snd '(' Expr ')'
     { \opts ->
      if isPCF opts || isML opts
        then Ext (Snd ($3 opts))
        else error "`snd` doesn't exists in the lambda calculus" }

  | inl '(' Expr ')'
     { \opts ->
      if isPCF opts || isML opts
        then Ext (Inl ($3 opts))
        else error "`inl` doesn't exists in the lambda calculus" }

  | inr '(' Expr ')'
     { \opts ->
      if isPCF opts || isML opts
        then Ext (Inr ($3 opts))
        else error "`inr` doesn't exists in the lambda calculus" }

 | case Expr of inl VAR '->' Expr '|' inr VAR '->' Expr
     { \opts ->
          if isPCF opts || isML opts
            then Ext (Case ($2 opts) (symString $5, $7 opts) (symString $10, ($12 opts)))
            else error "`case` doesn't exist in the lambda calculus" }


Type :: { [Option] -> Type }
Type
  : TypeAtom         { $1 }
  | Type '->' Type   { \opts -> FunTy ($1 opts) ($3 opts) }
  | Type '*' Type    { \opts -> ProdTy ($1 opts) ($3 opts) }
  | Type '+' Type    { \opts -> SumTy ($1 opts) ($3 opts) }
  | forall VAR '.' Type { \opts ->
                            if isPoly opts
                              then Forall (symString $2) ($4 opts)
                              else error "Type quantification not supported in simple types; try lang.poly. " }

TypeAtom :: { [Option] -> Type }
TypeAtom
  : CONSTR           { \opts -> if constrString $1 == "Nat" then NatTy else error $ "Unknown type constructor " ++ constrString $1 }
  | VAR              { \opts ->
                          if isPoly opts
                            then TyVar (symString $1)
                            else error "Type variables not supported in simple types; try lang.poly." }
  | '(' Type ')'     { \opts -> $2 opts }

Juxt :: { [Option] -> Expr PCF }
  : Juxt Atom                 { \opts -> App ($1 opts) ($2 opts) }
  | Atom                      { $1 }

Atom :: { [Option] -> Expr PCF }
  : '(' Expr ')'              { $2 }
  | VAR                       { \opts -> Var $ symString $1 }
  | zero
    { \opts ->
        if isPCF opts || isML opts
          then Ext Zero
          else Var "zero" }
  | succ
    { \opts ->
        if isPCF opts || isML opts
          then Ext Succ
          else Var "succ" }

  | '@' TypeAtom
    { \opts ->
        if isPoly opts
          then TyEmbed ($2 opts)
          else error "Cannot embed a type as a term; try lang.poly" }

  | '<' Expr ', ' Expr '>'
     { \opts ->
          if isPCF opts || isML opts
            then Ext (Pair ($2 opts) ($4 opts))
            else error "pairs don't exists in the lambda calculus"}



  -- For later
  -- | '?' { Hole }

{

readOption :: Token -> ReaderT String (Either String) Option
readOption (TokenLang _ x) | x == "lang.pcf"   = return PCF
readOption (TokenLang _ x) | x == "lang.ml"    = return ML
readOption (TokenLang _ x) | x == "lang.typed" = return Typed
readOption (TokenLang _ x) | x == "lang.poly"  = return Poly
readOption (TokenLang _ x) | x == "lang.cbv"   = return CBV
readOption (TokenLang _ x) | x == "lang.cbn"   = return CBN
readOption (TokenLang _ x) = lift . Left $ "Unknown language option: " <> x
readOption _ = lift . Left $ "Wrong token for language"

parseError :: [Token] -> ReaderT String (Either String) a
parseError [] = lift . Left $ "Premature end of file"
parseError t  =  do
    file <- ask
    lift . Left $ file <> ":" <> show l <> ":" <> show c
                        <> ": parse error"
  where (l, c) = getPos (head t)

parseProgram :: FilePath -> String -> Either String (Expr PCF, [Option])
parseProgram file input = runReaderT (program $ scanTokens input) file

}
