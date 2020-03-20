module Language.Dlam.Scoping.Scope
  ( Scope(..)
  , InScopeName(..)
  , InScopeType(..)
  , lookupInScope
  , addNameToScope
  , ResolvedName(..)
  , nameOf
  ) where


import qualified Data.List as L
import qualified Data.Map as M

import qualified Language.Dlam.Syntax.Abstract as A
import qualified Language.Dlam.Syntax.Concrete as C
import Language.Dlam.Util.Pretty (Pretty(..), text)


data Scope = Scope
  { scopeNameSpace :: NameSpace }


type NameSpace = M.Map C.CName InScopeName


data InScopeName
  -- | A name in scope, with an explanation as to why it is in scope.
  = InScopeName { howBound :: [InScopeType], isnName :: A.AName }
  deriving (Show)


-- | Different types of things we can have in scope.
data InScopeType
  -- | A signature for a definition.
  = ISSig
  -- | A definition.
  | ISDef
  -- | A constructor.
  | ISCon
  deriving (Show, Eq)


-- | A name that has been resolved in scope.
data ResolvedName
  -- | A local variable.
  = ResolvedVar A.AName
  -- | A definition name.
  | ResolvedDef A.AName
  -- | A resolved constructor.
  | ResolvedCon A.AName
  -- | An associated type signature.
  | ResolvedSig A.AName


-- | The associated name.
nameOf :: ResolvedName -> A.AName
nameOf (ResolvedVar n) = n
nameOf (ResolvedDef n) = n
nameOf (ResolvedCon n) = n
nameOf (ResolvedSig n) = n


lookupInNameSpace :: C.CName -> NameSpace -> Maybe InScopeName
lookupInNameSpace = M.lookup


lookupInScope :: C.QName -> Scope -> Maybe InScopeName
lookupInScope (C.Unqualified n) = lookupInNameSpace n . scopeNameSpace
lookupInScope (C.Qualified _n _q) = error "qualified lookups not yet supported"


addNameToNameSpace :: InScopeType -> C.CName -> A.AName -> NameSpace -> NameSpace
addNameToNameSpace st cn an =
  M.insertWith mergeInScope cn (InScopeName [st] an)
  where mergeInScope (InScopeName st1 an1) (InScopeName st2 _)
          = InScopeName (L.union st1 st2) an1


addNameToScope :: InScopeType -> C.CName -> A.AName -> Scope -> Scope
addNameToScope st cn an s
  = let sn = scopeNameSpace s in s { scopeNameSpace = addNameToNameSpace st cn an sn }


--------------------------
----- Prettification -----
--------------------------


instance Pretty InScopeType where
  pprint ISCon = text "constructor"
  pprint ISDef = text "definition"
  pprint ISSig = text "signature"
