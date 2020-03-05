{-# LANGUAGE FlexibleContexts #-}
module Language.Dlam.Scoping.Monad.Exception
  (
  -- * Exceptions and error handling
    SCError

  -- ** Implementation errors
  , notImplemented

  -- ** Scope errors
  , unknownNameErr
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

  | NotInScope C.Name


instance Show SCError where
  show (NotImplemented e) = e
  show (NotInScope n) = "Unknown identifier '" <> pprintShow n <> "'"


instance Exception SCError


notImplemented :: String -> SCError
notImplemented = NotImplemented


-- | Indicate that an identifier is not known to be defined.
unknownNameErr :: C.Name -> SCError
unknownNameErr = NotInScope