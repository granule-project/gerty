module Language.Dlam.Interpreter
  ( runParser
  , runScoper
  , runTypeChecker
  , InterpreterError
  , InterpreterResult
  , formatError
  , formatErrorDefault
  ) where

import qualified Language.Dlam.Scoping.Monad as SC
import Language.Dlam.Syntax.Abstract
import qualified Language.Dlam.Syntax.Concrete as C
import Language.Dlam.Syntax.Parser      (parseProgram)
import Language.Dlam.Syntax.Parser.Monad (ParseResult(..))
import Language.Dlam.Syntax.Translation.ConcreteToAbstract (toAbstract)
import Language.Dlam.Types
import Language.Dlam.TypeChecking.Monad
import Language.Dlam.Util.Pretty hiding ((<>))

type InterpreterError = TCErr
type InterpreterResult = AST


formatError :: InterpreterError -> Doc
formatError = pprint


formatErrorDefault :: InterpreterError -> String
formatErrorDefault = pprintShow


scopeAnalyseCST :: C.AST -> CM AST
scopeAnalyseCST cst =
  let res = SC.runNewScoper (toAbstract cst)
  in case SC.scrRes res of
       Left err -> scoperError err
       Right ast -> pure ast


runParser :: FilePath -> String -> CM C.AST
runParser fname input =
  case parseProgram fname input of
    ParseOk _ r -> pure r
    ParseFailed err -> parseError err


runScoper :: FilePath -> String -> CM AST
runScoper fname input = do
  cst <- runParser fname input

  -- Pretty print CST
  info $ (bold "Pretty CST:") $$ pprint cst

  ast <- scopeAnalyseCST cst

  -- Pretty print AST
  info $ (bold "Pretty AST:") $$ pprint ast

  pure ast


runTypeChecker :: FilePath -> String -> CM AST
runTypeChecker fname input = do
  ast <- runScoper fname input

  -- Typing
  doASTInference ast
