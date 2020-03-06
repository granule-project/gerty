{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Dlam.Syntax.Translation.ConcreteToAbstract
  ( ToAbstract(..)
  ) where


import Control.Monad.Except (throwError)


import Language.Dlam.Substitution (fresh)
import qualified Language.Dlam.Syntax.Abstract as A
import qualified Language.Dlam.Syntax.Concrete as C
import Language.Dlam.Scoping.Monad
import Language.Dlam.Scoping.Scope


class ToAbstract c a where
  toAbstract :: c -> SM a


type Locals = [(C.Name, A.Name)]


-- | Generate a new, ignored name.
newIgnoredName :: SM A.Name
newIgnoredName = toAbstract C.ignoreVar


instance ToAbstract C.AST A.AST where
  toAbstract (C.AST []) = pure $ A.AST []
  toAbstract (C.AST ((C.TypeSig n e):ds)) = do
    n' <- toAbstract (mustBeNew n ISSig)
    e' <- toAbstract e
    (A.AST ds') <- toAbstract (C.AST ds)
    pure . A.AST $ (A.TypeSig n' e'):ds'
  toAbstract (C.AST ((C.FunEqn (C.FLHSName n) r):ds)) = do
    n' <- toAbstract (fdefLookingForSignature n)
    r' <- toAbstract r
    (A.AST ds') <- toAbstract (C.AST ds)
    pure . A.AST $ (A.FunEqn (A.FLHSName n') r'):ds'
  -- currently just ignoring records pending implementation (2020-03-05, GD)
  toAbstract (C.AST ((C.RecordDef _n _con _p _e _decls):ds)) = toAbstract (C.AST ds)
  toAbstract (C.AST ((C.Field _n _t):ds)) = toAbstract (C.AST ds)


instance ToAbstract C.FLHS A.FLHS where
  toAbstract (C.FLHSName n) = A.FLHSName <$> toAbstract n


instance ToAbstract C.FRHS A.FRHS where
  toAbstract (C.FRHSAssign e) = A.FRHSAssign <$> toAbstract e


instance ToAbstract C.Name A.Name where
  toAbstract n = do
    i <- fresh
    pure $ A.Name { A.nameId = i, A.nameConcrete = n }


mkMaybeOldName :: C.Name -> InScopeType -> NameClassifier -> MaybeOldName
mkMaybeOldName n c nc =
  MaybeOldName { monName = n, monHowBind = HowBind { hbBindsAs = c, hbClashesWith = nc } }


mustBeNew :: C.Name -> InScopeType -> MaybeOldName
mustBeNew n c = mkMaybeOldName n c NCAll


fdefLookingForSignature :: C.Name -> MaybeOldName
fdefLookingForSignature n = mkMaybeOldName n ISDef (AllExcept [NCT ISSig])


data MaybeOldName = MaybeOldName
  { monName :: C.Name
  , monHowBind :: HowBind
  }

instance ToAbstract MaybeOldName A.Name where
  -- we try to find an existing instance of the name, but if the name
  -- isn't in scope, then we initialise it here.
  toAbstract mon = do
    let n = monName mon
    rn <- lookupLocalVar n
    case rn of
      -- currently we should always clash with locals, as
      -- this is treated as a 'top-level' definitions check
      Just _ -> throwError $ nameClash n
      Nothing -> do
        res <- maybeResolveNameCurrentScope n
        case res of
          Nothing -> do
            n' <- toAbstract n
            bindNameCurrentScope (monHowBind mon) n n'
            pure n'
          Just (InScopeName _ n') -> do
            bindNameCurrentScope (monHowBind mon) n n'
            pure n'


newtype OldName = OldName C.Name

instance ToAbstract OldName A.Name where
  toAbstract (OldName n) = do
    rn <- lookupLocalVar n
    case rn of
      -- locals always override
      Just v -> pure v
      -- if there's no matching locals, try and resolve the name in
      -- the definitions scope
      Nothing -> do
        res <- maybeResolveNameCurrentScope n
        case res of
          Nothing -> throwError $ unknownNameErr n
          Just inScope -> pure (isnName inScope)


instance ToAbstract C.PiBindings ([(A.Name, A.Expr)], Locals) where
  toAbstract (C.PiBindings []) = pure ([], [])
  toAbstract (C.PiBindings ((C.TypedBinding ns s):bs)) = do
    ns' <- mapM toAbstract ns
    s' <- toAbstract s
    let nsLocs = zip ns ns'
    (piBinds, locals) <- withLocals nsLocs $ toAbstract (C.PiBindings bs)
    pure $ (zip ns' (repeat s') <> piBinds, nsLocs <> locals)


instance ToAbstract C.LambdaArgs ([(A.Name, A.Expr)], Locals) where
  toAbstract [] = pure ([], [])
  toAbstract ((C.LamArgTyped (C.TypedBinding ns s)):bs) = do
    ns' <- mapM toAbstract ns
    s' <- toAbstract s
    let nsLocs = zip ns ns'
    (args, locals) <- withLocals nsLocs $ toAbstract bs
    pure $ (zip ns' (repeat s') <> args, nsLocs <> locals)
  toAbstract ((C.LamArgUntyped (C.BoundName n)):bs) = do
    n' <- toAbstract n
    let nTy = A.Implicit
        nsBind = [(n, n')]
    (args, locals) <- withLocals nsBind $ toAbstract bs
    pure $ ([(n', nTy)] <> args, nsBind <> locals)


instance ToAbstract C.Expr A.Expr where
  toAbstract (C.Ident v) = A.Var <$> toAbstract (OldName v)
  toAbstract (C.LitLevel n) = pure $ A.LitLevel n
  toAbstract (C.Fun e1 e2) = do
    name <- newIgnoredName
    e1' <- toAbstract e1
    e2' <- toAbstract e2
    pure $ A.FunTy (A.mkAbs name e1' e2')
  toAbstract (C.Pi piBinds expr) = do
    (piBinds' :: [(A.Name, A.Expr)], mySpace) <- toAbstract piBinds
    expr' <- withLocals mySpace $ toAbstract expr
    pure $ foldr (\(arg, space) f -> A.FunTy (A.mkAbs arg space f)) expr' piBinds'
  toAbstract (C.Abs args expr) = do
    (args' :: [(A.Name, A.Expr)], mySpace) <- toAbstract args
    expr' <- withLocals mySpace $ toAbstract expr
    pure $ foldr (\(arg, space) f -> A.Abs (A.mkAbs arg space f)) expr' args'
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
