module Language.Dlam.Interpreter
  ( run
  , InterpreterError
  , InterpreterResult
  , formatError
  ) where

import Control.Exception (displayException)
import Control.Monad.Writer (tell)

import Language.Dlam.Syntax.Parser      (parseProgram)
import Language.Dlam.Syntax.PrettyPrint (PrettyPrint(pprint))
import Language.Dlam.Syntax.Syntax
import Language.Dlam.Types
import Language.Dlam.TypeChecking.Monad

type InterpreterError = TCError
type InterpreterResult = AST

formatError :: InterpreterError -> String
formatError = displayException

run :: FilePath -> String -> CM AST
run fname input =
  case parseProgram fname input of
    Right ast -> do
      -- Show AST
      tell $ "\n " <> ansi_bold <> "AST: " <> ansi_reset <> show ast

      -- Pretty print
      tell $ "\n " <> ansi_bold <> "Pretty:\n" <> ansi_reset <> pprint ast

      -- Typing
      doASTInference ast

    Left msg -> parseError msg


ansi_reset, ansi_bold :: String
ansi_reset = "\ESC[0m"
ansi_bold  = "\ESC[1m"
