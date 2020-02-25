{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Dlam.Exception
  ( InjErr(..)
  , ExceptionCompat
  -- ** Implementation errors
  , ImplementationError
  , notImplemented
  -- ** Scope errors
  , ScopeError
  , unknownIdentifierErr
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
import Type.Reflection (Typeable)

import Language.Dlam.Syntax
import Language.Dlam.PrettyPrint (PrettyPrint(pprint))


class InjErr a b where
  injErr :: a -> b


-- | Type for types that can be embedded in lamb exceptions.
type ExceptionCompat e = (Typeable e, PrettyPrint e)


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
  NotInScope Identifier


instance Show ScopeError where
  show (NotInScope n) = "Unknown identifier '" <> pprint n <> "'"


instance Exception ScopeError


-- | Indicate that an identifier is not known to be defined.
unknownIdentifierErr :: (CanThrow m err ScopeError) => Identifier -> m a
unknownIdentifierErr n = throwError (injErr (NotInScope n))


------------------
-- Synth Errors --
------------------


data SynthError e =
    CannotSynthTypeForExpr (Expr e)
  | CannotSynthExprForType (Expr e)


instance (PrettyPrint e) => Show (SynthError e) where
  show (CannotSynthTypeForExpr expr) =
    "I was asked to try and synthesise a type for '" <> pprint expr <> "' but I wasn't able to do so."
  show (CannotSynthExprForType t) =
    "I was asked to try and synthesise a term of type '" <> pprint t <> "' but I wasn't able to do so."


instance (ExceptionCompat e) => Exception (SynthError e)


cannotSynthTypeForExpr :: (MonadError err m, InjErr (SynthError e) err) => Expr e -> m a
cannotSynthTypeForExpr expr = throwError (injErr (CannotSynthTypeForExpr expr))


cannotSynthExprForType :: (MonadError err m, InjErr (SynthError e) err) => Expr e -> m a
cannotSynthExprForType t = throwError (injErr (CannotSynthExprForType t))


-----------------
-- Type Errors --
-----------------


data TypeError e =
    TypeMismatch (Expr e) (Expr e) (Expr e)
  | ExpectedInferredTypeForm String (Expr e) (Expr e)

instance (PrettyPrint e) => Show (TypeError e) where
  show (TypeMismatch expr tyExpected tyActual) =
    "Error when checking the type of '" <> pprint expr <>
    "', expected '" <> pprint tyExpected <> "' but got '" <> pprint tyActual <> "'"
  show (ExpectedInferredTypeForm descr expr t) =
    "I was expecting the expression '" <> pprint expr
    <> "' to have a " <> descr <> " type, but instead I found its type to be '"
    <> pprint t <> "'"


instance (ExceptionCompat e) => Exception (TypeError e)


-- | 'tyMismatch expr tyExpected tyActual' indicates that an expression
-- | was found to have a type that differs from expected.
tyMismatch :: (MonadError err m, InjErr (TypeError e) err) => Expr e -> Expr e -> Expr e -> m a
tyMismatch expr tyExpected tyActual =
  throwError (injErr (TypeMismatch expr tyExpected tyActual))


expectedInferredTypeForm :: (MonadError err m, InjErr (TypeError e) err) => String -> Expr e -> Expr e -> m a
expectedInferredTypeForm descr expr t =
  throwError (injErr (ExpectedInferredTypeForm descr expr t))
