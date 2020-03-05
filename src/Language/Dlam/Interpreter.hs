module Language.Dlam.Interpreter
  ( run
  , InterpreterError
  , InterpreterResult
  , formatError
  ) where

import Control.Exception (displayException)
import Control.Monad.Writer (tell)

import qualified Language.Dlam.Scoping.Monad as SC
import Language.Dlam.Syntax.Abstract
import qualified Language.Dlam.Syntax.Concrete as C
import Language.Dlam.Syntax.Parser      (parseProgram)
import Language.Dlam.Syntax.Translation.ConcreteToAbstract (toAbstract)
import Language.Dlam.Types
import Language.Dlam.TypeChecking.Monad
import Language.Dlam.Util.Pretty (pprintShow)

type InterpreterError = TCError
type InterpreterResult = AST

formatError :: InterpreterError -> String
formatError = displayException


scopeAnalyseCST :: C.AST -> CM AST
scopeAnalyseCST cst =
  let res = SC.runNewScoper (toAbstract cst)
  in case SC.scrRes res of
       Left err -> scoperError err
       Right ast -> pure ast


run :: FilePath -> String -> CM AST
run fname input =
  case parseProgram fname input of
    Right cst -> do
      -- Show CST
      tell $ "\n " <> ansi_bold <> "CST: " <> ansi_reset <> show cst

      -- Pretty print CST
      tell $ "\n " <> ansi_bold <> "Pretty CST:\n" <> ansi_reset <> pprintShow cst

      ast <- scopeAnalyseCST cst

      -- Pretty print AST
      tell $ "\n " <> ansi_bold <> "Pretty AST:\n" <> ansi_reset <> pprintShow ast

      -- Typing
      doASTInference ast

    Left msg -> parseError msg


ansi_reset, ansi_bold :: String
ansi_reset = "\ESC[0m"
ansi_bold  = "\ESC[1m"
