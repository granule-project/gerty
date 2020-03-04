module Language.Dlam.Interpreter
  ( run
  , InterpreterError
  , InterpreterResult
  , formatError
  ) where

import Control.Exception (displayException)
import Control.Monad.Writer (tell)

import Language.Dlam.Syntax.Abstract
import Language.Dlam.Syntax.Parser      (parseProgram)
import Language.Dlam.Syntax.Translation.ConcreteToAbstract (toAbstract)
import Language.Dlam.Types
import Language.Dlam.TypeChecking.Monad
import Language.Dlam.Util.Pretty (pprintShow)

type InterpreterError = TCError
type InterpreterResult = AST

formatError :: InterpreterError -> String
formatError = displayException

run :: FilePath -> String -> CM AST
run fname input =
  case parseProgram fname input of
    Right cst -> do
      -- Show CST
      tell $ "\n " <> ansi_bold <> "CST: " <> ansi_reset <> show cst

      -- Pretty print
      tell $ "\n " <> ansi_bold <> "Pretty:\n" <> ansi_reset <> pprintShow cst

      ast <- toAbstract cst

      -- Typing
      doASTInference ast

    Left msg -> parseError msg


ansi_reset, ansi_bold :: String
ansi_reset = "\ESC[0m"
ansi_bold  = "\ESC[1m"
