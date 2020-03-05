module Language.Dlam.Scoping.Scope
  ( Scope(..)
  , InScopeName(..)
  , lookupInScope
  , addNameToScope
  ) where


import qualified Data.Map as M

import qualified Language.Dlam.Syntax.Abstract as A
import qualified Language.Dlam.Syntax.Concrete as C


data Scope = Scope
  { scopeNameSpace :: NameSpace }


type NameSpace = M.Map C.Name InScopeName


data InScopeName
  -- | Definition name.
  = InScopeDefName A.Name



lookupInNameSpace :: C.Name -> NameSpace -> Maybe InScopeName
lookupInNameSpace = M.lookup


lookupInScope :: C.Name -> Scope -> Maybe InScopeName
lookupInScope n = lookupInNameSpace n . scopeNameSpace


addNameToNameSpace :: C.Name -> A.Name -> NameSpace -> NameSpace
addNameToNameSpace cn an = M.insert cn (InScopeDefName an)


addNameToScope :: C.Name -> A.Name -> Scope -> Scope
addNameToScope cn an s = let sn = scopeNameSpace s in s { scopeNameSpace = addNameToNameSpace cn an sn }
