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
import Language.Dlam.Syntax.Syntax

class Freshenable m n | m -> n where
  freshen :: n -> m n

class Substitutable m n e | m -> n, m -> e where
  substitute :: (n, e) -> e -> m e

substAbs :: (Monad m, HasTyVal v (Maybe a) Expr, HasBinderMap m Name v, Freshenable m Name, Substitutable m Name Expr) => (Name, Expr) -> Abstraction -> m Abstraction
substAbs s ab = do
  let v = absVar ab
  v' <- freshen v
  t <- substitute s (absTy ab)
  withBinding (mkTag :: BinderMap) (v', fromTyVal (Nothing, t)) $ do
    e <- substitute (v, Var v') (absExpr ab) >>= substitute s
    pure $ mkAbs v' t e
