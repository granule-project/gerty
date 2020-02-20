{-# LANGUAGE FunctionalDependencies #-}
module Dlam.Binders
  ( HasBinders(..)
  ) where

class HasBinders m n e t | m -> n, m -> e, m -> t where
  -- | Get the type of the given binder, where types are of type 't'.
  getBinderType :: n -> m (Maybe t)
  -- | Get the value of the given binder, where values are of type 'e'.
  getBinderValue :: n -> m (Maybe e)
  -- | Set the value and type for a given binder.
  setBinder :: n -> (e, t) -> m ()
