{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Dlam.Syntax.Translation.ConcreteToAbstract
  ( ToAbstract(..)
  ) where


import qualified Language.Dlam.Syntax.Abstract as A
import qualified Language.Dlam.Syntax.Concrete as C
import Language.Dlam.TypeChecking.Monad


-- Scope checking monad (Checker monad alias).
type SM = CM


class ToAbstract c a where
  toAbstract :: c -> SM a


instance ToAbstract C.AST A.AST where
  toAbstract (C.AST ds) = A.AST <$> mapM toAbstract ds


instance ToAbstract C.Declaration A.Declaration where
  toAbstract (C.FunEqn l r) = A.FunEqn <$> toAbstract l <*> toAbstract r
  toAbstract (C.TypeSig n e) = A.TypeSig <$> pure n <*> toAbstract e


instance ToAbstract C.FLHS A.FLHS where
  toAbstract (C.FLHSName n) = pure $ A.FLHSName n


instance ToAbstract C.FRHS A.FRHS where
  toAbstract (C.FRHSAssign e) = A.FRHSAssign <$> toAbstract e


instance ToAbstract C.Expr A.Expr where
  toAbstract (C.Var v) = pure $ A.Var v
  toAbstract (C.LitLevel n) = pure $ A.LitLevel n
  toAbstract (C.FunTy ab) = A.FunTy <$> toAbstract ab
  toAbstract (C.Abs ab) = A.Abs <$> toAbstract ab
  toAbstract (C.ProductTy ab) = A.ProductTy <$> toAbstract ab
  toAbstract (C.Pair l r) = A.Pair <$> toAbstract l <*> toAbstract r
  toAbstract (C.PairElim (z, tC) (x, y, c) p) = do
    tC' <- toAbstract tC
    c'  <- toAbstract c
    p'  <- toAbstract p
    pure $ A.PairElim (z, tC') (x, y, c') p'
  toAbstract (C.Coproduct t1 t2) = A.Coproduct <$> toAbstract t1 <*> toAbstract t2
  toAbstract (C.CoproductCase (z, tC) (x, c) (y, d) p) = do
    tC' <- toAbstract tC
    c' <- toAbstract c
    d' <- toAbstract d
    p' <- toAbstract p
    pure $ A.CoproductCase (z, tC') (x, c') (y, d') p'
  toAbstract (C.NatCase (x, tC) cz (w, y, cs) n) = do
    tC' <- toAbstract tC
    cz' <- toAbstract cz
    cs' <- toAbstract cs
    n' <- toAbstract n
    pure $ A.NatCase (x, tC') cz' (w, y, cs') n'
  toAbstract (C.RewriteExpr (x, y, p, tC) (z, c) a b e) = do
    tC' <- toAbstract tC
    c' <- toAbstract c
    a' <- toAbstract a
    b' <- toAbstract b
    e' <- toAbstract e
    pure $ A.RewriteExpr (x, y, p, tC') (z, c') a' b' e'
  toAbstract (C.UnitElim (x, tC) c a) = do
    tC' <- toAbstract tC
    c' <- toAbstract c
    a' <- toAbstract a
    pure $ A.UnitElim (x, tC') c' a'
  toAbstract (C.EmptyElim (x, tC) a) = do
    tC' <- toAbstract tC
    a' <- toAbstract a
    pure $ A.EmptyElim (x, tC') a'
  toAbstract (C.App f e) = A.App <$> toAbstract f <*> toAbstract e
  toAbstract (C.Sig e t) = A.Sig <$> toAbstract e <*> toAbstract t
  toAbstract C.Hole = pure A.Hole
  toAbstract C.Implicit = pure A.Implicit
  toAbstract (C.Builtin b) = A.Builtin <$> toAbstract b


instance ToAbstract C.BuiltinTerm A.BuiltinTerm where
  toAbstract C.LevelTy = pure A.LevelTy
  toAbstract C.LZero = pure A.LZero
  toAbstract C.LSuc = pure A.LSuc
  toAbstract C.LMax = pure A.LMax
  toAbstract C.TypeTy = pure A.TypeTy
  toAbstract C.Inl = pure A.Inl
  toAbstract C.Inr = pure A.Inr
  toAbstract C.DUnitTerm = pure A.DUnitTerm
  toAbstract C.DUnitTy = pure A.DUnitTy
  toAbstract C.IdTy = pure A.IdTy
  toAbstract C.DRefl = pure A.DRefl
  toAbstract C.DNat = pure A.DNat
  toAbstract C.DNZero = pure A.DNZero
  toAbstract C.DNSucc = pure A.DNSucc
  toAbstract C.DEmptyTy = pure A.DEmptyTy


instance ToAbstract C.Abstraction A.Abstraction where
  toAbstract ab =
    A.mkAbs (C.absVar ab) <$> toAbstract (C.absTy ab) <*> toAbstract (C.absExpr ab)
