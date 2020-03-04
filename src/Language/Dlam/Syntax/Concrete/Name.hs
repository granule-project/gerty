module Language.Dlam.Syntax.Concrete.Name
  ( Name(..)
  , mkIdent
  , ignoreVar
  ) where


import Prelude hiding ((<>))

import Language.Dlam.Util.Pretty


data Name = Ident String | GenIdent (String, Int) | Ignore
  deriving (Show, Eq, Ord)


-- | Create a new identifier from a (syntactic) string.
mkIdent :: String -> Name
mkIdent = Ident


-- | Name for use when the value is unused.
ignoreVar :: Name
ignoreVar = Ignore


instance Pretty Name where
  pprint (Ident v) = text v
  pprint (GenIdent (v, i)) = text v <> char '_' <> int i
  pprint Ignore = char '_'
