{-# LANGUAGE FunctionalDependencies #-}
module Dlam.Binders
  ( HasBinders(..)
  , HasTyVal(..)
  , getBinderType
  , getBinderValue
  , withBinding
  ) where

import qualified Data.Map as M

class HasBinders m n v | m -> n, m -> v where
  -- | Get the bindings as a map.
  getBindings :: m (M.Map n v)
  -- | Set the value and type for a given binder.
  setBinder :: n -> v -> m ()
  -- | Execute the action, restoring bindings to their original value afterwards.
  preservingBindings :: m a -> m a


class HasTyVal v e t | v -> e, v -> t where
  toVal :: v -> e
  toTy  :: v -> t
  fromTyVal :: (e, t) -> v


-- | Get the value at a given binder, if it exists.
getBinder :: (Ord n, HasBinders m n v, Functor m) => n -> m (Maybe v)
getBinder n = M.lookup n <$> getBindings

-- | Get the type of the given binder, where types are of type 't'.
getBinderType :: (Ord n, Functor m, HasBinders m n v, HasTyVal v e t) => n -> m (Maybe t)
getBinderType = (fmap . fmap) toTy . getBinder

-- | Get the value of the given binder, where values are of type 'e'.
getBinderValue :: (Ord n, Functor m, HasBinders m n v, HasTyVal v e t) => n -> m (Maybe e)
getBinderValue = (fmap . fmap) toVal . getBinder

-- | Execute the given action with a given binding active,
-- | and restore the binding afterwards.
withBinding :: (Monad m, HasBinders m n v) => (n, v) -> m a -> m a
withBinding (n, v) m = preservingBindings $ setBinder n v >> m
