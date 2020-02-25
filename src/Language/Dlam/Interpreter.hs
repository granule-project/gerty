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
import Language.Dlam.Parser      (parseProgram)
import Language.Dlam.PrettyPrint (PrettyPrint(pprint))
import Language.Dlam.Syntax
import Language.Dlam.Types

data InterpreterError e =
    ISynthError (SynthError e)
  | IImplementationError ImplementationError
  | IScopeError ScopeError
  | ITypeError (TypeError e)
  | IGenericError String

instance InjErr (SynthError e) (InterpreterError e) where injErr = ISynthError
instance InjErr ScopeError (InterpreterError e) where injErr = IScopeError
instance InjErr ImplementationError (InterpreterError e) where
  injErr = IImplementationError
instance InjErr (TypeError e) (InterpreterError e) where injErr = ITypeError

newtype InterpreterResult = InterpreterResult (NAST NoExt)

instance Show InterpreterResult where
  show (InterpreterResult nast) = pprint nast


throwGenericError :: (MonadError (InterpreterError e) m) => String -> m a
throwGenericError = throwError . IGenericError

formatError :: (ExceptionCompat e) => InterpreterError e -> String
formatError (ISynthError e) = displayException e
formatError (ITypeError e) = displayException e
formatError (IImplementationError e) = displayException e
formatError (IScopeError e) = displayException e
formatError (IGenericError s) = s

instance (PrettyPrint e) => Show (InterpreterError e) where
  show (ISynthError e) = show e
  show (ITypeError e) = show e
  show (IScopeError e) = show e
  show (IImplementationError e) = show e
  show (IGenericError e) = e

instance (ExceptionCompat e) => Exception (InterpreterError e)

run :: (Checkable m (InterpreterError NoExt) NoExt v, MonadWriter String m) => FilePath -> String -> m InterpreterResult
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
