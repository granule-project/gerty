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

  | NameClash C.Name


instance Show SCError where
  show (NotImplemented e) = e
  show (NotInScope n) = "Unknown identifier '" <> pprintShow n <> "'"
  show (NameClash n) = "Already defined '" <> pprintShow n <> "'"


instance Exception SCError


notImplemented :: String -> SCError
notImplemented = NotImplemented


-- | Indicate that an identifier is not known to be defined.
unknownNameErr :: C.QName -> SCError
unknownNameErr = NotInScope


nameClash :: C.Name -> SCError
nameClash = NameClash
