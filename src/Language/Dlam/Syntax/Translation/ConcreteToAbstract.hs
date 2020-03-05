{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Dlam.Syntax.Translation.ConcreteToAbstract
  ( ToAbstract(..)
  ) where


import Control.Monad.Except (throwError)


import Language.Dlam.Substitution (fresh)
import qualified Language.Dlam.Syntax.Abstract as A
import qualified Language.Dlam.Syntax.Concrete as C
import Language.Dlam.Scoping.Monad


class ToAbstract c a where
  toAbstract :: c -> SM a


type Locals = [(C.Name, A.Name)]


instance ToAbstract C.AST A.AST where
  toAbstract (C.AST []) = pure $ A.AST []
  toAbstract (C.AST ((C.TypeSig n e):ds)) = do
    -- TODO: make sure name isn't already defined here (2020-03-05)
    n' <- toAbstract n
    bindNameCurrentScope n n'
    e' <- toAbstract e
    (A.AST ds') <- withLocals [(n, n')] $ toAbstract (C.AST ds)
    pure . A.AST $ (A.TypeSig n' e'):ds'
  toAbstract (C.AST ((C.FunEqn (C.FLHSName n) r):ds)) = do
    n' <- toAbstract (MaybeOldName n)
    r' <- toAbstract r
    (A.AST ds') <- withLocals [(n, n')] $ toAbstract (C.AST ds)
    pure . A.AST $ (A.FunEqn (A.FLHSName n') r'):ds'


instance ToAbstract C.Declaration A.Declaration where
  toAbstract (C.FunEqn l r) = A.FunEqn <$> toAbstract l <*> toAbstract r
  toAbstract (C.TypeSig n e) = A.TypeSig <$> toAbstract n <*> toAbstract e


instance ToAbstract C.FLHS A.FLHS where
  toAbstract (C.FLHSName n) = A.FLHSName <$> toAbstract n


instance ToAbstract C.FRHS A.FRHS where
  toAbstract (C.FRHSAssign e) = A.FRHSAssign <$> toAbstract e


instance ToAbstract C.Name A.Name where
  toAbstract n = do
    i <- fresh
    pure $ A.Name { A.nameId = i, A.nameConcrete = n }


newtype MaybeOldName = MaybeOldName C.Name

instance ToAbstract MaybeOldName A.Name where
  -- we try to find an existing instance of the name, but if the name
  -- isn't in scope, then we initialise it here.
  toAbstract (MaybeOldName n) = do
    rn <- lookupLocalVar n
    case rn of
      Just v -> pure v
      Nothing -> toAbstract n


newtype OldName = OldName C.Name

instance ToAbstract OldName A.Name where
  toAbstract (OldName n) = do
    rn <- lookupLocalVar n
    case rn of
      Just v -> pure v
      Nothing -> throwError $ unknownNameErr n


instance ToAbstract C.Expr A.Expr where
  toAbstract (C.Var v) = A.Var <$> toAbstract (OldName v)
  toAbstract (C.LitLevel n) = pure $ A.LitLevel n
  toAbstract (C.FunTy ab) = A.FunTy <$> toAbstract ab
  toAbstract (C.Abs ab) = A.Abs <$> toAbstract ab
  toAbstract (C.ProductTy ab) = A.ProductTy <$> toAbstract ab
  toAbstract (C.Pair l r) = A.Pair <$> toAbstract l <*> toAbstract r
  toAbstract (C.Coproduct t1 t2) = A.Coproduct <$> toAbstract t1 <*> toAbstract t2
  toAbstract (C.CoproductCase (z, tC) (x, c) (y, d) p) = do
    z' <- toAbstract z
    x' <- toAbstract x
    y' <- toAbstract y
    tC' <- withLocals [(z, z')] $ toAbstract tC
    p' <- toAbstract p
    c' <- withLocals [(x, x')] $ toAbstract c
    d' <- withLocals [(y, y')] $ toAbstract d
    pure $ A.CoproductCase (z', tC') (x', c') (y', d') p'
  toAbstract (C.NatCase (x, tC) cz (w, y, cs) n) = do
    x' <- toAbstract x
    w' <- toAbstract w
    y' <- toAbstract y
    tC' <- withLocals [(x, x')] $ toAbstract tC
    cz' <- toAbstract cz
    cs' <- withLocals [(w, w'), (y, y')] $ toAbstract cs
    n' <- toAbstract n
    pure $ A.NatCase (x', tC') cz' (w', y', cs') n'
  toAbstract (C.RewriteExpr (x, y, p, tC) (z, c) a b e) = do
    x' <- toAbstract x
    y' <- toAbstract y
    p' <- toAbstract p
    z' <- toAbstract z
    tC' <- withLocals [(x, x'), (y, y'), (p, p')] $ toAbstract tC
    c' <- withLocals [(z, z')] $ toAbstract c
    a' <- toAbstract a
    b' <- toAbstract b
    e' <- toAbstract e
    pure $ A.RewriteExpr (x', y', p', tC') (z', c') a' b' e'
  toAbstract (C.EmptyElim (x, tC) a) = do
    x' <- toAbstract x
    tC' <- withLocals [(x, x')] $ toAbstract tC
    a' <- toAbstract a
    pure $ A.EmptyElim (x', tC') a'
  toAbstract (C.App f e) = A.App <$> toAbstract f <*> toAbstract e
  toAbstract (C.Sig e t) = A.Sig <$> toAbstract e <*> toAbstract t
  toAbstract C.Hole = pure A.Hole
  toAbstract C.Implicit = pure A.Implicit
  toAbstract (C.Let (C.LetPatBound p e1) e2) = do
    (p', names) <- toAbstract p
    e1' <- toAbstract e1
    e2' <- withLocals names $ toAbstract e2
    pure $ A.Let (A.LetPatBound p' e1') e2'


instance ToAbstract C.Pattern (A.Pattern, Locals) where
  -- TODO: make sure we don't allow repeated names in patterns (2020-03-05)
  -- TODO: add support for binding the vars for the type (2020-03-05)
  toAbstract (C.PIdent n) = do
    n' <- toAbstract n
    pure (A.PVar (A.BindName n'), [(n, n')])
  toAbstract (C.PPair p1 p2) = do
    (p1', p1vs) <- toAbstract p1
    (p2', p2vs) <- toAbstract p2
    pure $ (A.PPair p1' p2', p1vs <> p2vs)
  toAbstract (C.PAt n p) = do
    n' <- toAbstract n
    (p', pvs) <- toAbstract p
    pure $ (A.PAt (A.BindName n') p', (n, n') : pvs)
  toAbstract C.PUnit = pure (A.PUnit, [])


instance ToAbstract C.Abstraction A.Abstraction where
  toAbstract ab = do
    v <- toAbstract (C.absVar ab)
    t <- toAbstract (C.absTy ab)
    e <- withLocals [(C.absVar ab, v)] $ toAbstract (C.absExpr ab)
    pure $ A.mkAbs v t e
