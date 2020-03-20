module Language.Dlam.Syntax.Concrete.Name
  ( CName(..)
  , QName(..)
  , mkIdent
  , ignoreVar
  ) where


import Prelude hiding ((<>))

import Language.Dlam.Syntax.Common (NameId(..))
import Language.Dlam.Util.Pretty


data CName
  = CName String
  -- ^ Concrete name.
  | NoName NameId
  -- ^ Unused/generated name.
  deriving (Show, Eq, Ord)


-- | A name can be qualified or unqualified.
data QName = Qualified CName QName | Unqualified CName
  deriving (Show, Eq, Ord)


-- | Create a new identifier from a (syntactic) string.
mkIdent :: String -> CName
mkIdent = CName


-- | Name for use when the value is unused.
ignoreVar :: CName
ignoreVar = NoName (NameId 0)


instance Pretty CName where
  isLexicallyAtomic _ = True

  pprint (CName v) = text v
  pprint NoName{} = char '_'


instance Pretty QName where
  isLexicallyAtomic _ = True

  pprint (Qualified n qs) = pprint n <> char '.' <> pprint qs
  pprint (Unqualified n)  = pprint n
