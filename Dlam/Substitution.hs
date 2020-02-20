{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Dlam.Substitution
  ( Substitutable(..)
  , substAbs
  , Freshenable(..)
  ) where

import Dlam.Binders (HasBinders(..), HasTyVal(fromTyVal))
import Dlam.Syntax

class Freshenable m n | m -> n where
  freshen :: n -> m n

class Substitutable m n e | m -> n, m -> e where
  substitute :: (n, e) -> e -> m e

substAbs :: (Monad m, HasTyVal v (Maybe a) (Expr e), HasBinders m Identifier v, Freshenable m Identifier, Substitutable m Identifier (Expr e)) => (Identifier, Expr e) -> Abstraction e -> m (Abstraction e)
substAbs s ab = do
  v <- freshen (absVar ab)
  t <- substitute s (absTy ab)
  setBinder v (fromTyVal (Nothing, t))
  e <- substitute (absVar ab, Var v) (absExpr ab) >>= substitute s
  pure $ mkAbs v t e
