{-# LANGUAGE FlexibleContexts #-}
module Language.Dlam.Interpreter
  ( run
  , InterpreterError
  , InterpreterResult(..)
  , formatError
  ) where

import Control.Exception (Exception)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Writer (MonadWriter, tell)

import Language.Dlam.Binders
  ( HasNamedMap(..)
  , BinderMap
  , NormalFormMap
  , HasTyVal(..)
  )
import Language.Dlam.Parser      (parseProgram)
import Language.Dlam.PrettyPrint (pprint)
import Language.Dlam.Substitution (Substitutable(..))
import Language.Dlam.Syntax
import Language.Dlam.Types

newtype InterpreterError = InterpreterError String

newtype InterpreterResult = InterpreterResult (NAST NoExt)

instance Show InterpreterResult where
  show (InterpreterResult nast) = pprint nast


throwInterpreterError :: (MonadError InterpreterError m) => String -> m a
throwInterpreterError = throwError . InterpreterError

formatError :: InterpreterError -> String
formatError (InterpreterError e) = e

instance Show InterpreterError where
  show (InterpreterError e) = e

instance Exception InterpreterError

run :: (Substitutable m Identifier (Expr NoExt), HasNamedMap m BinderMap Identifier v, HasNamedMap m NormalFormMap (Expr NoExt) (Expr NoExt), HasTyVal v (Maybe (Expr NoExt)) (Expr NoExt), MonadError InterpreterError m, MonadWriter String m) => FilePath -> String -> m InterpreterResult
run fname input =
  case parseProgram fname input of
    Right (ast, _options) -> do
      -- Show AST
      tell $ "\n " <> ansi_bold <> "AST: " <> ansi_reset <> show ast
      let nast = normaliseAST ast
      tell $ "\n " <> ansi_bold <> "NAST: " <> ansi_reset <> show nast

      -- Pretty print
      tell $ "\n " <> ansi_bold <> "Pretty:\n" <> ansi_reset <> pprint nast

      -- Typing
      fmap InterpreterResult $ doNASTInference nast

    Left msg -> throwInterpreterError $ ansi_red ++ "Error: " ++ ansi_reset ++ msg


ansi_red, ansi_reset, ansi_bold :: String
ansi_red   = "\ESC[31;1m"
ansi_reset = "\ESC[0m"
ansi_bold  = "\ESC[1m"
