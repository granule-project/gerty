{-# LANGUAGE FunctionalDependencies #-}
module Dlam.Binders
  ( HasBinders(..)
  , HasTyVal(..)
  , getBinderType
  , getBinderValue
  ) where

class HasBinders m n v | m -> n, m -> v where
  -- | Get the value at a given binder, if it exists.
  getBinder :: n -> m (Maybe v)
  -- | Set the value and type for a given binder.
  setBinder :: n -> v -> m ()


class HasTyVal v e t | v -> e, v -> t where
  toVal :: v -> e
  toTy  :: v -> t
  fromTyVal :: (e, t) -> v

-- | Get the type of the given binder, where types are of type 't'.
getBinderType :: (Functor m, HasBinders m n v, HasTyVal v e t) => n -> m (Maybe t)
getBinderType = (fmap . fmap) toTy . getBinder

-- | Get the value of the given binder, where values are of type 'e'.
getBinderValue :: (Functor m, HasBinders m n v, HasTyVal v e t) => n -> m (Maybe e)
getBinderValue = (fmap . fmap) toVal . getBinder
