{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.Dlam.Substitution
  ( Substitutable(..)
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


type SubstConstr m v =
  ( Monad m, HasTyVal v (Maybe Expr) Expr
  , HasBinderMap m Name v, Freshenable m Name
  , Substitutable m Name Expr)

substAbs :: (SubstConstr m v) => (Name, Expr) -> Abstraction -> m Abstraction
substAbs s ab = do
  let v = absVar ab
  v' <- freshen v
  t <- substitute s (absTy ab)
  withBinding (mkTag :: BinderMap) (v', fromTyVal (Nothing, t)) $ do
    e <- substitute (v, Var v') (absExpr ab) >>= substitute s
    pure $ mkAbs v' t e


instance (SubstConstr m v) => Substitutable m Name Expr where
  substitute (v, e) (Var x)
    | v == x    = pure e
    | otherwise = pure (Var x)
  substitute s (FunTy abs) = FunTy <$> substAbs s abs
  substitute s (Abs   abs) = Abs   <$> substAbs s abs
  substitute s (ProductTy abs) = ProductTy <$> substAbs s abs
  substitute s (Pair e1 e2) = Pair <$> substitute s e1 <*> substitute s e2
  substitute s@(v, _) (PairElim (z, tC) (x, y, g) p) = do
    p' <- substitute s p
    g' <- if v == x || v == y then pure g else substitute s g
    tC' <- if v == z then pure tC else substitute s tC
    pure $ PairElim (z, tC') (x, y, g') p'
  substitute s (App e1 e2) = do
    e1' <- substitute s e1
    e2' <- substitute s e2
    pure (App e1' e2')
  substitute s (Coproduct e1 e2) = Coproduct <$> substitute s e1 <*> substitute s e2
  substitute s@(v, _) (CoproductCase (z, tC) (x, c) (y, d) e) = do
    e' <- substitute s e
    tC' <- if v == z then pure tC else substitute s tC
    c'  <- if v == x then pure c else substitute s c
    d'  <- if v == y then pure d else substitute s d
    pure $ CoproductCase (z, tC') (x, c') (y, d') e'
  substitute s@(v, _) (NatCase (x, tC) cz (w, y, cs) n) = do
    tC' <- if v == x then pure tC else substitute s tC
    cz' <- substitute s cz
    cs' <- if v == y || v == w then pure cs else substitute s cs
    n'  <- substitute s n
    pure $ NatCase (x, tC') cz' (w, y, cs') n'
  substitute _ e@LitLevel{} = pure e
  substitute _ e@Hole{} = pure e
  substitute _ e@Implicit = pure e
  substitute s (Sig e t) = Sig <$> substitute s e <*> substitute s t
  substitute s@(v, _) (RewriteExpr (x, y, pv, tC) (z, c) a b pe) = do
    tC' <- if v `elem` [x, y, pv] then pure tC else substitute s tC
    c' <- if v == z then pure c else substitute s c
    a' <- substitute s a
    b' <- substitute s b
    pe' <- substitute s pe
    pure $ RewriteExpr (x, y, pv, tC') (z, c') a' b' pe'
  substitute s@(v, _) (UnitElim (x, tC) c a) = do
    tC' <- if v == x then pure tC else substitute s tC
    c' <- substitute s c
    a' <- substitute s a
    pure $ UnitElim (x, tC') c' a'
  substitute s@(v, _) (EmptyElim (x, tC) a) = do
    tC' <- if v == x then pure tC else substitute s tC
    a' <- substitute s a
    pure $ EmptyElim (x, tC') a'
  substitute _ e@Builtin{} = pure e
