{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Dlam.Interpreter
  ( run
  , InterpreterError
  , InterpreterResult(..)
  , formatError
  ) where

import Control.Exception (Exception, displayException)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Writer (MonadWriter, tell)

import Language.Dlam.Exception
import Language.Dlam.Syntax.Parser      (parseProgram)
import Language.Dlam.Syntax.PrettyPrint (PrettyPrint(pprint))
import Language.Dlam.Syntax.Syntax
import Language.Dlam.Types

data InterpreterError ann e =
    ISynthError (SynthError ann e)
  | IImplementationError ImplementationError
  | IScopeError ScopeError
  | ITypeError (TypeError ann e)
  | IGenericError String

instance InjErr (SynthError ann e) (InterpreterError ann e) where injErr = ISynthError
instance InjErr ScopeError (InterpreterError ann e) where injErr = IScopeError
instance InjErr ImplementationError (InterpreterError ann e) where
  injErr = IImplementationError
instance InjErr (TypeError ann e) (InterpreterError ann e) where injErr = ITypeError

newtype InterpreterResult = InterpreterResult (NAST NoAnn NoExt)

instance Show InterpreterResult where
  show (InterpreterResult nast) = pprint nast


throwGenericError :: (MonadError (InterpreterError ann e) m) => String -> m a
throwGenericError = throwError . IGenericError

formatError :: (ExceptionCompat ann e) => InterpreterError ann e -> String
formatError (ISynthError e) = displayException e
formatError (ITypeError e) = displayException e
formatError (IImplementationError e) = displayException e
formatError (IScopeError e) = displayException e
formatError (IGenericError s) = s

instance (PrettyPrint e) => Show (InterpreterError ann e) where
  show (ISynthError e) = show e
  show (ITypeError e) = show e
  show (IScopeError e) = show e
  show (IImplementationError e) = show e
  show (IGenericError e) = e

instance (ExceptionCompat ann e) => Exception (InterpreterError ann e)

run :: (Checkable m (InterpreterError NoAnn NoExt) NoAnn NoExt v, MonadWriter String m) => FilePath -> String -> m InterpreterResult
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

    Left msg -> throwGenericError $ ansi_red ++ "Error: " ++ ansi_reset ++ msg


ansi_red, ansi_reset, ansi_bold :: String
ansi_red   = "\ESC[31;1m"
ansi_reset = "\ESC[0m"
ansi_bold  = "\ESC[1m"
