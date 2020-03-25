module Language.Dlam.Interpreter
  ( runParser
  , runScoper
  , runTypeChecker
  , InterpreterError
  , InterpreterResult
  , formatError
  ) where

import Control.Exception (displayException)

import qualified Language.Dlam.Scoping.Monad as SC
import Language.Dlam.Syntax.Abstract
import qualified Language.Dlam.Syntax.Concrete as C
import Language.Dlam.Syntax.Parser      (parseProgram)
import Language.Dlam.Syntax.Parser.Monad (ParseResult(..))
import Language.Dlam.Syntax.Translation.ConcreteToAbstract (toAbstract)
import Language.Dlam.TypeChecking (checkAST)
import Language.Dlam.TypeChecking.Monad
import Language.Dlam.Util.Pretty (pprintShow)

type InterpreterError = TCErr
type InterpreterResult = AST

formatError :: InterpreterError -> String
formatError = displayException


scopeAnalyseCST :: C.AST -> CM AST
scopeAnalyseCST cst =
  let res = SC.runNewScoper (toAbstract cst)
  in case SC.scrRes res of
       Left err -> scoperError err
       Right ast -> updateWithScopeInfo res >> pure ast


runParser :: FilePath -> String -> CM C.AST
runParser fname input =
  case parseProgram fname input of
    ParseOk _ r -> pure r
    ParseFailed err -> parseError err


runScoper :: FilePath -> String -> CM AST
runScoper fname input = do
  cst <- runParser fname input

  -- Show CST
  info $ ansi_bold <> "CST: " <> ansi_reset <> show cst

  -- Pretty print CST
  info $ ansi_bold <> "Pretty CST:\n" <> ansi_reset <> pprintShow cst

  ast <- scopeAnalyseCST cst

  -- Pretty print AST
  info $ ansi_bold <> "Pretty AST:\n" <> ansi_reset <> pprintShow ast

  pure ast


runTypeChecker :: FilePath -> String -> CM ()
runTypeChecker fname input = do
  ast <- runScoper fname input

  -- Typing
  checkAST ast
  -- TODO: add a warning for any unsolved metas at the top level (2020-03-25)
  -- TODO: add a check to make sure there are no unsolved implicits (2020-03-25)
  metas <- getMetas
  info $ "I was able to produce the following information about metas\n" <> pprintShow metas


ansi_reset, ansi_bold :: String
ansi_reset = "\ESC[0m"
ansi_bold  = "\ESC[1m"
