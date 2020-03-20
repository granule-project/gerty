{-# LANGUAGE FlexibleContexts #-}
module Language.Dlam.Scoping.Monad.Exception
  (
  -- * Exceptions and error handling
    SCError

  -- ** Implementation errors
  , notImplemented

  -- ** Scope errors
  , unknownNameErr
  , nameClash

  -- ** Pattern errors
  , notAValidPattern
  , nonConstructorInPattern
  ) where

import Control.Exception (Exception)

import qualified Language.Dlam.Syntax.Concrete as C
import Language.Dlam.Util.Pretty (pprintShow)


-----------------------------------------
----- Exceptions and error handling -----
-----------------------------------------


data SCError
  ---------------------------
  -- Implementation Errors --
  ---------------------------

  = NotImplemented String

  ------------------
  -- Scope Errors --
  ------------------

  | NotInScope C.QName

  | NameClash C.CName

  --------------------
  -- Pattern Errors --
  --------------------

  | NotAValidPattern C.Pattern

  | NonConstructorInPattern C.QName


instance Show SCError where
  show (NotImplemented e) = e
  show (NotInScope n) = "Unknown identifier '" <> pprintShow n <> "'"
  show (NameClash n) = "Already defined '" <> pprintShow n <> "'"
  show (NotAValidPattern p) =
    "'" <> pprintShow p <> "' is not a valid pattern"
  show (NonConstructorInPattern n) =
    "Cannot use non-constructor '" <> pprintShow n <> "' in pattern"


instance Exception SCError


notImplemented :: String -> SCError
notImplemented = NotImplemented


-- | Indicate that an identifier is not known to be defined.
unknownNameErr :: C.QName -> SCError
unknownNameErr = NotInScope


nameClash :: C.CName -> SCError
nameClash = NameClash


notAValidPattern  :: C.Pattern -> SCError
notAValidPattern = NotAValidPattern


nonConstructorInPattern  :: C.QName -> SCError
nonConstructorInPattern = NonConstructorInPattern
