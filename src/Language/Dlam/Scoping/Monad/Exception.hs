{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
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

import qualified Language.Dlam.Syntax.Concrete as C
import Language.Dlam.Util.Pretty hiding ((<>))

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

  --------------------
  -- Pattern Errors --
  --------------------

  | NotAValidPattern C.Pattern

  | NonConstructorInPattern C.QName


instance Pretty SCError where
  pprint (NotImplemented e) = text e
  pprint (NotInScope n) = "Unknown identifier" <+> quoted n
  pprint (NameClash n) = "Already defined" <+> quoted n
  pprint (NotAValidPattern p) = quoted p <+> "is not a valid pattern"
  pprint (NonConstructorInPattern n) =
    "Cannot use non-constructor" <+> quoted n <+> "in pattern"


notImplemented :: String -> SCError
notImplemented = NotImplemented


-- | Indicate that an identifier is not known to be defined.
unknownNameErr :: C.QName -> SCError
unknownNameErr = NotInScope


nameClash :: C.Name -> SCError
nameClash = NameClash


notAValidPattern  :: C.Pattern -> SCError
notAValidPattern = NotAValidPattern


nonConstructorInPattern  :: C.QName -> SCError
nonConstructorInPattern = NonConstructorInPattern
