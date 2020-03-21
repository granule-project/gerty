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
import Language.Dlam.Syntax.Literal
import Language.Dlam.Syntax.Parser.Monad
import Language.Dlam.Syntax.Parser.Tokens
import Language.Dlam.Syntax.Position
import Language.Dlam.Util.Pretty (pprintShow)

}

%name program File
%name expr Expr
%tokentype { Token }
-- %error { parseError }
-- %monad { ReaderT String (Either String) }
%monad { Parser }
%lexer { lexer } { TokEOF{} }

%nonassoc LOWEST
%nonassoc '->'

%token
    QID     { TokQId $$ }
    let     { TokKeyword KwLet $$ }
    record  { TokKeyword KwRecord $$ }
    where   { TokKeyword KwWhere $$ }
    rewrite { TokKeyword KwRewrite $$ }
    constructor { TokKeyword KwConstructor $$ }
    field   { TokKeyword KwField $$ }
    '_'     { TokSymbol SymUnderscore $$ }
    case    { TokKeyword KwCase $$ }
    inl     { TokKeyword KwInl $$ }
    inr     { TokKeyword KwInr $$ }
    zero    { TokKeyword KwZero $$ }
    succ    { TokKeyword KwSucc $$ }
    of      { TokKeyword KwOf $$ }
    in      { TokKeyword KwIn  $$  }
    VAR     { TokId $$ }
    literal { TokLiteral $$ }
    absurd  { TokSymbol SymAbsurd $$ }
    '\\'    { TokSymbol SymLambda $$ }
    '->'    { TokSymbol SymArrow $$ }
    '*'     { TokSymbol SymStar $$ }
    '+'     { TokSymbol SymPlus $$ }
    '='     { TokSymbol SymEqual $$ }
    '('     { TokSymbol SymOpenParen $$ }
    ')'     { TokSymbol SymCloseParen $$ }
    '{'     { TokSymbol SymOpenBrace $$ }
    '}'     { TokSymbol SymCloseBrace $$ }
    '['     { TokSymbol SymOpenBracket $$ }
    ']'     { TokSymbol SymCloseBracket $$ }
    ':'     { TokSymbol SymColon $$ }
    ','     { TokSymbol SymComma $$ }
    '.'     { TokSymbol SymDot $$ }
    ';'     { TokSymbol SymSemi $$ }
    '@'     { TokSymbol SymAt $$ }
    '|'     { TokSymbol SymBar $$ }
    -- temporary tokens until we can parse mixfix names
    '::'    { TokSymbol SymDoubleColon _ }
    vopen   { TokSymbol SymOpenVirtualBrace $$ }
    vclose  { TokSymbol SymCloseVirtualBrace $$ }
    vsemi   { TokSymbol SymVirtualSemi $$ }

%%

File :: { ParseAST }
  : TopLevel { AST $1 }
  -- : vopen TopLevel maybe_vclose { AST $2 }

TopLevel :: { [Declaration] }
  : TopDeclarations { $1 }

maybe_vclose :: { () }
maybe_vclose : {- empty -} { () }
             | vclose      { () }


TopDeclarations :: { [Declaration] }
TopDeclarations
  : {- empty -}   { [] }
  | Declarations0 { $1 }


-- Arbitrary declarations
Declarations :: { [Declaration] }
Declarations
    : vopen Declarations1 close { $2 }

-- Arbitrary declarations (possibly empty)
Declarations0 :: { [Declaration] }
Declarations0
    : vopen close  { [] }
    | Declarations { $1 }

Declarations1 :: { [Declaration] }
Declarations1
    : Declaration semi Declarations1 { $1 <> $3 }
    | Declaration vsemi              { $1 }
    | Declaration                    { $1 }


---------------------------------
----- Names and identifiers -----
---------------------------------


Ident :: { CName }
  : VAR {% mkName $1 }


QId :: { QName }
  : QID { % mkQName $1 }
  | Ident { Unqualified $1 }


BoundName :: { BoundName }
  : Ident { bindName $1 }


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
  : record Ident LambdaBindingsOrEmpty ':' Expr where RecordDeclBody
      { let (con, bod) = $7 in RecordDef $2 con $3 $5 bod }

RecordDeclBody :: { (Maybe CName, [Declaration]) }
  : vopen close { (Nothing, []) }
  | vopen RecordDirective close { (Just $2, []) }
  | Declarations { (Nothing, $1) }

RecordDirective :: { CName }
  : constructor RecordConstructorName { $2 }

RecordConstructorName :: { CName }
  : Ident { $1 }

Field :: { [Declaration] }
  : field EmptyOrTypeSigs { fmap (uncurry Field) $2 }


EmptyOrTypeSigs :: { [(CName, Expr)] }
  : vopen TypeSigs0 close { reverse $2 }


TypeSigs0 :: { [(CName, Expr)] }
  : TypeSigs0 semi TypeSig { $3 : $1 }
  | TypeSig                { pure $1 }
  | {- empty -}            { [] }


TypeSig :: { (CName, Expr) }
  : Ident ':' Expr { ($1, $3) }


-------------------
----- Binders -----
-------------------


-- grades are just expressions
Grade :: { Grade }
  : Application { mkAppFromExprs $1 }


MaybeBinderGrading :: { Maybe Grading }
  : '[' Grade ',' Grade ']' { Just (mkGrading $2 $4) }
  | {- empty -} { Nothing }


TypedBinding :: { TypedBinding }
  : '(' BoundNames ':' MaybeBinderGrading Expr ')' { mkTypedBinding NotHidden $2 $4 $5 }
  | '{' BoundNames ':' MaybeBinderGrading Expr '}' { mkTypedBinding IsHidden  $2 $4 $5 }


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
  | literal                   { LitLevel (natTokenToInt $1) }

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


{--------------------------------------------------------------------------
    Meta rules (from Agda)
 --------------------------------------------------------------------------}

-- The first token in a file decides the indentation of the top-level layout
-- block. Or not. It will if we allow the top-level module to be omitted.
-- topen :      {- empty -}     {% pushCurrentContext }


{-  A layout block might have to be closed by a parse error. Example:
        let x = e in e'
    Here the 'let' starts a layout block which should end before the 'in'.  The
    problem is that the lexer doesn't know this, so there is no virtual close
    brace. However when the parser sees the 'in' there will be a parse error.
    This is our cue to close the layout block.
-}
close :: { () }
close : vclose  { () }
      | error   {% popContext }


-- You can use concrete semi colons in a layout block started with a virtual
-- brace, so we don't have to distinguish between the two semi colons. You can't
-- use a virtual semi colon in a block started by a concrete brace, but this is
-- simply because the lexer will not generate virtual semis in this case.
semi :: { Interval }
semi : ';'    { $1 }
     | vsemi  { $1 }


-- Enter the 'imp_dir' lex state, where we can parse the keyword 'to'.
beginImpDir :: { () }
beginImpDir : {- empty -}   {% pushLexState imp_dir }

{

type ParseExpr = Expr
type ParseAST = AST


-- TODO: once we support parsing modules, remove the 'layout' fragment here, as
-- this should be handled by the fact that 'where' is a layout keyword (2020-03-10)
parseProgram :: FilePath -> String -> ParseResult ParseAST
parseProgram file = parseFromSrc defaultParseFlags [layout, normal] program (Just file)

natTokenToInt :: Literal -> Integer
natTokenToInt (LitNat _ x) = x

mkAppFromExprs :: [Expr] -> Expr
mkAppFromExprs = foldl1 App


data FRHSOrTypeSig = IsRHS FRHS | IsTypeSig Expr

funAssignOrTypeSig :: FLHS -> FRHSOrTypeSig -> Declaration
funAssignOrTypeSig n (IsRHS e) = FunEqn n e
funAssignOrTypeSig (FLHSName n) (IsTypeSig t) = TypeSig n t
-- TODO: improve error system in parser here to use a monad (2020-03-01)
funAssignOrTypeSig lhs (IsTypeSig _) = error $ "'" <> pprintShow lhs <> "' is not allowed a type signature"


-- | Create a name from a string.
mkName :: (Interval, String) -> Parser CName
mkName (_i, s) = pure $ CName s


-- | Create a qualified name from a list of strings
mkQName :: [(Interval, String)] -> Parser QName
mkQName ss = do
  xs <- mapM mkName ss
  pure $ foldr Qualified (Unqualified $ last xs) (init xs)


-- | Required by Happy.
happyError :: Parser a
happyError = parseError "Parse error"

}
