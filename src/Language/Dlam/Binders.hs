{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
module Language.Dlam.Binders
  ( HasTyVal(..)
  , IsTag(..)
  , getBinder
  , getBinderType
  , getBinderValue
  , withBinding
  , HasNamedMap(..)
  , BinderMap
  , HasBinderMap
  , NormalFormMap
  , HasNormalFormMap
  ) where

import qualified Data.Map as M

class IsTag a where
  mkTag   :: a

class (IsTag t) => HasNamedMap m t k v | m t -> k,  m t -> v where
  -- | Get the bindings as a map.
  getBindings :: t -> m (M.Map k v)
  -- | Set the value and type for a given binder.
  setBinder :: t -> k -> v -> m ()
  -- | Execute the action, restoring bindings to their original value afterwards.
  preservingBindings :: t -> m a -> m a


class HasTyVal v e t | v -> e, v -> t where
  toVal :: v -> e
  toTy  :: v -> t
  fromTyVal :: (e, t) -> v


-- | Get the value at a given binder, if it exists.
getBinder :: (Ord n, HasNamedMap m t n v, Functor m) => t -> n -> m (Maybe v)
getBinder t n = M.lookup n <$> getBindings t

-- | Get the type of the given binder, where types are of type 't'.
getBinderType :: (Ord n, Functor m, HasNamedMap m p n v, HasTyVal v e t) => p -> n -> m (Maybe t)
getBinderType p = (fmap . fmap) toTy . getBinder p

-- | Get the value of the given binder, where values are of type 'e'.
getBinderValue :: (Ord n, Functor m, HasNamedMap m p n v, HasTyVal v e t) => p -> n -> m (Maybe e)
getBinderValue p = (fmap . fmap) toVal . getBinder p

-- | Execute the given action with a given binding active,
-- | and restore the binding afterwards.
withBinding :: (Applicative m, HasNamedMap m t n v) => t -> (n, v) -> m a -> m a
withBinding p (n, v) m = preservingBindings p $ setBinder p n v *> m


newtype BinderMap = BinderMap ()

instance IsTag BinderMap where
  mkTag = BinderMap ()

class (HasNamedMap m BinderMap k v) => HasBinderMap m k v


newtype NormalFormMap = NormalFormMap ()

instance IsTag NormalFormMap where
  mkTag = NormalFormMap ()

class (HasNamedMap m NormalFormMap k v) => HasNormalFormMap m k v
