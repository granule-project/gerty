module Language.Dlam.Scoping.Scope
  ( Scope(..)
  , InScopeName(..)
  , InScopeType(..)
  , lookupInScope
  , addNameToScope
  ) where


import qualified Data.List as L
import qualified Data.Map as M

import qualified Language.Dlam.Syntax.Abstract as A
import qualified Language.Dlam.Syntax.Concrete as C


data Scope = Scope
  { scopeNameSpace :: NameSpace }


type NameSpace = M.Map C.Name InScopeName


data InScopeName
  -- | A name in scope, with an explanation as to why it is in scope.
  = InScopeName { howBound :: [InScopeType], isnName :: A.Name }


-- | Different types of things we can have in scope.
data InScopeType
  -- | A signature for a definition.
  = ISSig
  -- | A definition.
  | ISDef
  deriving (Eq)



lookupInNameSpace :: C.Name -> NameSpace -> Maybe InScopeName
lookupInNameSpace = M.lookup


lookupInScope :: C.Name -> Scope -> Maybe InScopeName
lookupInScope n = lookupInNameSpace n . scopeNameSpace


addNameToNameSpace :: InScopeType -> C.Name -> A.Name -> NameSpace -> NameSpace
addNameToNameSpace st cn an =
  M.insertWith mergeInScope cn (InScopeName [st] an)
  where mergeInScope (InScopeName st1 an1) (InScopeName st2 _)
          = InScopeName (L.union st1 st2) an1


addNameToScope :: InScopeType -> C.Name -> A.Name -> Scope -> Scope
addNameToScope st cn an s
  = let sn = scopeNameSpace s in s { scopeNameSpace = addNameToNameSpace st cn an sn }
