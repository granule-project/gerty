{
{-# LANGUAGE FlexibleContexts #-}

module Language.Dlam.Syntax.Parser
  ( parseProgram
  ) where

import Numeric
import System.Exit
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class (lift)
import Data.List.NonEmpty ((<|))

import Language.Dlam.Syntax.Common
import Language.Dlam.Syntax.Concrete
import Language.Dlam.Syntax.Lexer
import Language.Dlam.Util.Pretty (pprintShow)

}

%name program Program
%name expr Expr
%tokentype { Token }
%error { parseError }
%monad { ReaderT String (Either String) }

%nonassoc LOWEST
%nonassoc '->'

%token
    nl      { TokenNL _ }
    QID     { TokenQid _ _ }
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
    NAT     { TokenNat _ _ }
    absurd  { TokenAbsurd _ }
    '\\'    { TokenLambda _ }
    '->'    { TokenArrow _ }
    '*'     { TokenProd _ }
    '+'     { TokenPlus _ }
    '='     { TokenEq _ }
    '('     { TokenLParen _ }
    ')'     { TokenRParen _ }
    '{'     { TokenLBrace _ }
    '}'     { TokenRBrace _ }
    ':'     { TokenSig _ }
    ','     { TokenComma _ }
    '.'     { TokenDot _ }
    ';'     { TokenSemiColon _ }
    '@'     { TokenAt _ }
    '|'     { TokenPipe _ }
    -- temporary tokens until we can parse mixfix names
    '::'    { TokenDoubleColon _ }

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


---------------------------------
----- Names and identifiers -----
---------------------------------


Ident :: { Name }
  : VAR { mkIdentFromSym $1 }


QId :: { QName }
  : QID { mkQualFromSym $1 }
  | Ident { Unqualified $1 }


BoundName :: { BoundName }
  : Ident { BoundName $1 }


BoundNames :: { OneOrMoreBoundNames }
  : BoundName { pure $1 }
  | BoundName BoundNames { $1 <| $2 }


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

Field :: { [Declaration] }
  : field EmptyOrTypeSigs { fmap (uncurry Field) $2 }


EmptyOrTypeSigs :: { [(Name, Expr)] }
  : TypeSig { [$1] }
  | TypeSig NL EmptyOrTypeSigs { $1 : $3 }
  | {- empty -}                { [] }


TypeSig :: { (Name, Expr) }
  : Ident ':' Expr { ($1, $3) }


-------------------
----- Binders -----
-------------------


TypedBinding :: { TypedBinding }
  : '(' BoundNames ':' Expr ')' { mkTypedBinding NotHidden $2 $4 }
  | '{' BoundNames ':' Expr '}' { mkTypedBinding IsHidden $2 $4 }


TypedBindings :: { [TypedBinding] }
  : TypedBinding { pure $1 }
  | TypedBinding TypedBindings { $1 : $2 }


LambdaBinding :: { LambdaBinding }
  : TypedBinding { lambdaBindingFromTyped $1 }
  -- TODO: add support for simple names/expressions, currently not
  -- working because of parsing precedence (2020-03-05)
  -- | Expr         { UnnamedBinding $1 }


LambdaBindingsOrEmpty :: { [LambdaBinding] }
  : LambdaBinding LambdaBindingsOrEmpty { $1 : $2 }
  | {- empty -}                         { [] }


PiBindings :: { PiBindings }
  : TypedBindings { PiBindings $1 }


-----------------------
----- Expressions -----
-----------------------


Expr :: { Expr }
  : Expr0 { $1 }


-- function types
Expr0 :: { Expr }
  : Expr1 '->' Expr   { Fun $1 $3 }
  | PiBindings '->' Expr { Pi $1 $3 }
  | Expr1 %prec LOWEST { $1 }


-- applications
Expr1 :: { Expr }
  : Application { mkAppFromExprs $1 }
  | Expr1 '*' Expr1   { ProductTy (mkAbs ignoreVar $1 $3) }
  | Ident '::' Expr1 '*' Expr1 { ProductTy (mkAbs $1 $3 $5) }
  | Expr1 '+' Expr1   { Coproduct $1 $3 }
  | Expr1 ',' Expr1 { Pair $1 $3 }

Application :: { [Expr] }
  : Expr2 { [$1] }
  | Expr3 Application { $1 : $2 }


ExprOrSig :: { Expr }
  : Expr { $1 }
  | Expr ':' Expr { Sig $1 $3 }


-- lambdas, lets, cases
Expr2 :: { ParseExpr }
  : '\\' LambdaArgs '->' Expr { Lam $2 $4 }

  | let LetBinding in ExprOrSig { Let $2 $4 }

  | let Ident '@' absurd '=' Expr ':' Expr { EmptyElim ($2, $8) $6 }

  | rewrite '(' '\\' Ident Ident Ident '->' Expr '|' '\\' Ident '->' Expr '|' Expr '|' Expr '|' Expr ')' { RewriteExpr ($4, $5, $6, $8) ($11, $13) $15 $17 $19 }

  | case Ident '@' Expr of '(' inl Ident '->' Expr ';' inr Ident '->' Expr ')' ':' Expr
    { CoproductCase ($2, $18) ($8, $10) ($13, $15) $4 }

  | case Expr of inl Ident '->' Expr ';' inr Ident '->' Expr
    { CoproductCase (ignoreVar, mkImplicit) ($5, $7) ($10, $12) $2 }

  | case Ident '@' Expr of '(' zero '->' Expr ';' succ Ident '@' Ident '->' Expr ')' ':' Expr
    { NatCase ($2, $19) $9 ($12, $14, $16) $4 }

  | Expr3 { $1 }


Expr3Braces :: { Expr }
  : Ident '=' Expr { BraceArg (Named $1 $3) }
  | Expr           { BraceArg (Unnamed $1) }


-- atomic values
Expr3 :: { Expr }
  : '{' Expr3Braces '}' { $2 }
  | Atom { $1 }


Atom :: { ParseExpr }
  : '(' Expr ')'              { Parens $2 }
  | QId                       { Ident $1 }
  | '_'                       { mkImplicit }
  | NAT                       { LitLevel (natTokenToInt $1) }

  -- For later
  -- | '?' { Hole }


LetBinding :: { LetBinding }
  : Pattern '=' Expr { LetPatBound $1 $3 }


Pattern :: { Pattern }
  : QId SomeAtomicPatterns     { PApp $1 $2 }
  | Pattern ',' Pattern { PPair $1 $3 }
  | PatternAtomic %prec LOWEST { $1 }


SomeAtomicPatterns :: { [Pattern] }
  : PatternAtomic AtomicPatternsOrEmpty { $1 : $2 }


AtomicPatternsOrEmpty :: { [Pattern] }
  : PatternAtomic AtomicPatternsOrEmpty { $1 : $2 }
  | {- empty -}                         { [] }


PatternAtomic :: { Pattern }
  : '(' Pattern ')' { PParens $2 }
  -- if the name is in scope, then try and treat it as a constructor, otherwise
  -- we will bind it as a new name
  | QId             { PIdent $1 }
  | '*'             { PUnit }
  | Ident '@' PatternAtomic { PAt $1 $3 }


-- Arguments for a lambda term.
LambdaArg :: { LambdaArg }
  : BoundName            { mkArg NotHidden $ itIsNot (pure $1) }
  | '{' BoundNames '}'   { mkArg IsHidden  $ itIsNot $2 }
  | TypedBinding         { lambdaArgFromTypedBinding $1 }

LambdaArgsOrEmpty :: { LambdaArgs }
  : LambdaArg LambdaArgsOrEmpty { $1 : $2 }
  | {- empty -}                 { [] }

LambdaArgs :: { LambdaArgs }
  : LambdaArg LambdaArgsOrEmpty { $1 : $2 }

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

mkQualFromSym :: Token -> QName
mkQualFromSym t = mkQualFromString (symString t)
  where mkQualFromString st =
          case break (=='.') st of
            (s, []) -> Unqualified (Name s)
            (s, '.':q)  -> Qualified (Name s) (mkQualFromString q)


mkAppFromExprs :: [Expr] -> Expr
mkAppFromExprs = foldl1 App


data FRHSOrTypeSig = IsRHS FRHS | IsTypeSig Expr

funAssignOrTypeSig :: FLHS -> FRHSOrTypeSig -> Declaration
funAssignOrTypeSig n (IsRHS e) = FunEqn n e
funAssignOrTypeSig (FLHSName n) (IsTypeSig t) = TypeSig n t
-- TODO: improve error system in parser here to use a monad (2020-03-01)
funAssignOrTypeSig lhs (IsTypeSig _) = error $ "'" <> pprintShow lhs <> "' is not allowed a type signature"

}
