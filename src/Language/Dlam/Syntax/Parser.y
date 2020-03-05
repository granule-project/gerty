{
{-# LANGUAGE FlexibleContexts #-}

module Language.Dlam.Syntax.Parser
  ( parseProgram
  ) where

import Numeric
import System.Exit
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class (lift)

import Language.Dlam.Syntax.Concrete
import Language.Dlam.Syntax.Lexer
import Language.Dlam.Util.Pretty (pprintShow)

}

%name program Program
%name expr Expr
%tokentype { Token }
%error { parseError }
%monad { ReaderT String (Either String) }

%token
    nl      { TokenNL _ }
    let     { TokenLet _ }
    record  { TokenRecord _ }
    where   { TokenWhere _ }
    rewrite { TokenRewrite _ }
    constructor { TokenConstructor _ }
    field   { TokenField _ }
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
    absurd  { TokenAbsurd _ }
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
  : Declaration NL Declarations { $1 <> $3 }
  | Declaration          { $1 }
  | {- empty -}         { [] }

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

Declaration :: { [Declaration] }
  : FunctionDeclaration { [$1] }
  | RecordDef { [$1] }
  | Field { $1 }

FunctionDeclaration :: { Declaration }
  : FLHS FRHS { funAssignOrTypeSig $1 $2 }

-- Right-hand side of a function clause
FRHS :: { FRHSOrTypeSig }
  -- Assignment
  : '=' Expr { IsRHS (FRHSAssign $2) }
  -- Type signature
  | ':' Expr { IsTypeSig $2 }


-----------------------
-- Record definition --
-----------------------

RecordDef :: { Declaration }
  : record Ident LambdaBindingsOrEmpty ':' Expr where constructor Ident Declarations
      { RecordDef $2 (Just $8) $3 $5 $9 }
  | record Ident LambdaBindingsOrEmpty ':' Expr where Declarations
      { RecordDef $2 Nothing $3 $5 $7 }

TypedBinding :: { TypedBinding }
  : '(' Ident VarsSpaced ':' Expr ')' { TypedBinding ($2 : $3) $5 }
  | '(' Ident ':' Expr ')'            { TypedBinding [$2] $4 }

LambdaBinding :: { LambdaBinding }
  : TypedBinding { NamedBinding $1 }
  -- TODO: add support for simple names/expressions, currently not
  -- working because of parsing precedence (2020-03-05)
  -- | Expr         { UnnamedBinding $1 }

LambdaBindingsOrEmpty :: { [LambdaBinding] }
  : LambdaBinding                       { [$1] }
  | LambdaBinding LambdaBindingsOrEmpty { $1 : $2 }
  | {- empty -}                         { [] }


Field :: { [Declaration] }
  : field EmptyOrTypeSigs { fmap (uncurry Field) $2 }


EmptyOrTypeSigs :: { [(Name, Expr)] }
  : TypeSig { [$1] }
  | TypeSig NL EmptyOrTypeSigs { $1 : $3 }
  | {- empty -}                { [] }


TypeSig :: { (Name, Expr) }
  : Ident ':' Expr { ($1, $3) }


Ident :: { Name }
  : VAR { mkIdentFromSym $1 }

Expr :: { ParseExpr }
  : Expr '->' Expr   { FunTy (mkAbs ignoreVar $1 $3) }
  | TyBindings '->' Expr { foldr (\(n, ty) fty -> FunTy (mkAbs n ty fty)) $3 $1 }

  | '\\' LambdaArgs '->' Expr
    { foldr (\(n, ty) rty -> Abs (mkAbs n ty rty)) $4 $2 }


  | Expr '*' Expr   { ProductTy (mkAbs ignoreVar $1 $3) }

  | '(' Ident ':' Expr ')' '*' Expr { ProductTy (mkAbs $2 $4 $7) }

  | Expr '+' Expr   { Coproduct $1 $3 }

  | let LetBinding in Expr { Let $2 $4 }

  | let Ident '@' absurd '=' Expr ':' Expr { EmptyElim ($2, $8) $6 }

  | rewrite '(' Ident '.' Ident '.' Ident '.' Expr ',' Ident '.' Expr ',' Expr ',' Expr ',' Expr ')' { RewriteExpr ($3, $5, $7, $9) ($11, $13) $15 $17 $19 }

  | case Ident '@' Expr of '(' inl Ident '->' Expr ';' inr Ident '->' Expr ')' ':' Expr
    { CoproductCase ($2, $18) ($8, $10) ($13, $15) $4 }

  | case Expr of inl Ident '->' Expr ';' inr Ident '->' Expr
    { CoproductCase (ignoreVar, mkImplicit) ($5, $7) ($10, $12) $2 }

  | case Ident '@' Expr of '(' zero '->' Expr ';' succ Ident '@' Ident '->' Expr ')' ':' Expr
    { NatCase ($2, $19) $9 ($12, $14, $16) $4 }

  -- TODO: this might cause issues with binders in dependent function types? (2020-02-22)
  | Expr ':' Expr  { Sig $1 $3 }

  | Juxt
    { $1 }


LetBinding :: { LetBinding }
  : Pattern '=' Expr { LetPatBound $1 $3 }


Pattern :: { Pattern }
  : Ident '@' Pattern { PAt $1 $3 }
  | Ident { PIdent $1 }
  | '(' Pattern ',' Pattern ')' { PPair $2 $4 }
  | '*' { PUnit }


Juxt :: { ParseExpr }
  : Juxt Atom                 { App $1 $2 }
  | Atom                      { $1 }

Atom :: { ParseExpr }
  : '(' Expr ')'              { $2 }
  | Ident                       { Ident $1 }
  | '_'                       { mkImplicit }
  | NAT                       { LitLevel (natTokenToInt $1) }
  | '(' Expr ',' Expr ')'     { Pair $2 $4 }

  -- For later
  -- | '?' { Hole }

-- List of space-separated identifiers.
VarsSpaced :: { [Name] }
  : Ident            { [$1] }
  | Ident VarsSpaced { $1 : $2 }

-- Arguments for a lambda term.
LambdaArg :: { [(Name, ParseExpr)] }
  : Ident       { [($1, mkImplicit)] }
  | TyBinding { $1 }

LambdaArgs :: { [(Name, ParseExpr)] }
  : LambdaArg { $1 }
  | LambdaArg LambdaArgs { $1 <> $2 }

-- syntax for bindings in a type
TyBinding :: { [(Name, ParseExpr)] }
  : '(' Ident VarsSpaced ':' Expr ')'
    { let ty = $5 in fmap (\n -> (n, ty)) ($2 : $3) }
  | '(' Ident ':' Expr ')'        { [($2, $4)] }

TyBindings :: { [(Name, ParseExpr)] }
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

mkIdentFromSym :: Token -> Name
mkIdentFromSym = mkIdent . symString

data FRHSOrTypeSig = IsRHS FRHS | IsTypeSig Expr

funAssignOrTypeSig :: FLHS -> FRHSOrTypeSig -> Declaration
funAssignOrTypeSig n (IsRHS e) = FunEqn n e
funAssignOrTypeSig (FLHSName n) (IsTypeSig t) = TypeSig n t
-- TODO: improve error system in parser here to use a monad (2020-03-01)
funAssignOrTypeSig lhs (IsTypeSig _) = error $ "'" <> pprintShow lhs <> "' is not allowed a type signature"

}
