{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Dlam.Exception
  ( InjErr(..)
  -- ** Implementation errors
  , ImplementationError
  , notImplemented
  -- ** Scope errors
  , ScopeError
  , unknownNameErr
  -- ** Synthesis errors
  , SynthError
  , cannotSynthTypeForExpr
  , cannotSynthExprForType
  -- ** Type errors
  , TypeError
  , tyMismatch
  , expectedInferredTypeForm
  ) where

import Control.Exception (Exception)
import Control.Monad.Except (MonadError, throwError)

import Language.Dlam.Syntax.Syntax
import Language.Dlam.Syntax.PrettyPrint (PrettyPrint(pprint))


class InjErr a b where
  injErr :: a -> b


type CanThrow m err errSpec = (MonadError err m, InjErr errSpec err)


---------------------------
-- Implementation Errors --
---------------------------


data ImplementationError =
  NotImplemented String


instance Show ImplementationError where
  show (NotImplemented e) = e


instance Exception ImplementationError


notImplemented :: (CanThrow m err ImplementationError) => String -> m a
notImplemented descr = throwError (injErr (NotImplemented descr))


------------------
-- Scope Errors --
------------------


data ScopeError =
  NotInScope Name


instance Show ScopeError where
  show (NotInScope n) = "Unknown identifier '" <> pprint n <> "'"


instance Exception ScopeError


-- | Indicate that an identifier is not known to be defined.
unknownNameErr :: (CanThrow m err ScopeError) => Name -> m a
unknownNameErr n = throwError (injErr (NotInScope n))


------------------
-- Synth Errors --
------------------


data SynthError =
    CannotSynthTypeForExpr Expr
  | CannotSynthExprForType Expr


instance Show SynthError where
  show (CannotSynthTypeForExpr expr) =
    "I was asked to try and synthesise a type for '" <> pprint expr <> "' but I wasn't able to do so."
  show (CannotSynthExprForType t) =
    "I was asked to try and synthesise a term of type '" <> pprint t <> "' but I wasn't able to do so."


instance Exception SynthError


cannotSynthTypeForExpr :: (MonadError err m, InjErr SynthError err) => Expr -> m a
cannotSynthTypeForExpr expr = throwError (injErr (CannotSynthTypeForExpr expr))


cannotSynthExprForType :: (MonadError err m, InjErr SynthError err) => Expr -> m a
cannotSynthExprForType t = throwError (injErr (CannotSynthExprForType t))


-----------------
-- Type Errors --
-----------------


data TypeError =
    TypeMismatch Expr Expr Expr
  | ExpectedInferredTypeForm String Expr Expr

instance Show TypeError where
  show (TypeMismatch expr tyExpected tyActual) =
    "Error when checking the type of '" <> pprint expr <>
    "', expected '" <> pprint tyExpected <> "' but got '" <> pprint tyActual <> "'"
  show (ExpectedInferredTypeForm descr expr t) =
    "I was expecting the expression '" <> pprint expr
    <> "' to have a " <> descr <> " type, but instead I found its type to be '"
    <> pprint t <> "'"


instance Exception TypeError


-- | 'tyMismatch expr tyExpected tyActual' indicates that an expression
-- | was found to have a type that differs from expected.
tyMismatch :: (MonadError err m, InjErr TypeError err) => Expr -> Expr -> Expr -> m a
tyMismatch expr tyExpected tyActual =
  throwError (injErr (TypeMismatch expr tyExpected tyActual))


expectedInferredTypeForm :: (MonadError err m, InjErr TypeError err) => String -> Expr -> Expr -> m a
expectedInferredTypeForm descr expr t =
  throwError (injErr (ExpectedInferredTypeForm descr expr t))
