{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Dlam.Substitution
  ( Substitutable(..)
  , substAbs
  , Freshenable(..)
  ) where

import Language.Dlam.Binders
  ( IsTag(mkTag)
  , HasTyVal(fromTyVal)
  , withBinding
  , BinderMap
  , HasBinderMap
  )
import Language.Dlam.Syntax

class Freshenable m n | m -> n where
  freshen :: n -> m n

class Substitutable m n e | m -> n, m -> e where
  substitute :: (n, e) -> e -> m e

substAbs :: (Monad m, HasTyVal v (Maybe a) (Expr ann e), HasBinderMap m Identifier v, Freshenable m Identifier, Substitutable m Identifier (Expr ann e)) => (Identifier, Expr ann e) -> Abstraction ann e -> m (Abstraction ann e)
substAbs s ab = do
  let v = absVar ab
  v' <- freshen v
  t <- substitute s (absTy ab)
  withBinding (mkTag :: BinderMap) (v', fromTyVal (Nothing, t)) $ do
    e <- substitute (v, Var v') (absExpr ab) >>= substitute s
    pure $ mkAbs v' t e
