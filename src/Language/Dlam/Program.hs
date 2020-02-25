{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Dlam.Program
  ( runProgFull
  ) where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Map as M

import Language.Dlam.Binders
  ( HasNamedMap(..)
  , BinderMap
  , NormalFormMap
  , HasTyVal(..)
  )
import Language.Dlam.Syntax.PrettyPrint (pprint)
import Language.Dlam.Substitution (Substitutable(..), substAbs, Freshenable(..))
import Language.Dlam.Syntax.Syntax

newtype BindV ann e = BindV { getBindV :: (Maybe (Expr ann e), Expr ann e) }

type BindV' = BindV NoAnn NoExt
type Expr' = Expr NoAnn NoExt

instance (Show e) => Show (BindV ann e) where
  show = show . getBindV

type Context = M.Map Identifier BindV'
type NormalFormContext = M.Map Expr' Expr'

type ProgMaps = (Context, NormalFormContext)

builtins :: Context
builtins = M.fromList
           [ (mkIdent "Type",  BindV (Just typeTy, typeTyTY))
           , (mkIdent "Level", BindV (Just levelTy, levelTyTY))
           , (mkIdent "lzero", BindV (Just lzero, lzeroTY))
           , (mkIdent "lsuc", BindV (Just lsuc, lsucTY))
           , (mkIdent "lmax", BindV (Just lmax, lmaxTY))
           , (mkIdent "Bool", BindV (Just dBool, dBoolTY))
           , (mkIdent "true", BindV (Just dtrue, dtrueTY))
           , (mkIdent "false", BindV (Just dfalse, dfalseTY))
           , (mkIdent "unit", BindV (Just unitTerm, unitTermTY))
           , (mkIdent "Unit", BindV (Just unitTy, unitTyTY))
           ]

type ProgState = (Int, ProgMaps)

newtype Prog err a =
  Prog { runProg :: ExceptT err (WriterT String (State ProgState)) a }
  deriving ( Applicative, Functor, Monad
           , MonadState ProgState
           , MonadWriter String
           , MonadError err)

-- Example instance where identifiers are mapped to types
-- and (optional) definitions via a list.
instance HasNamedMap (Prog err) BinderMap Identifier BindV' where
  getBindings _ = fst . snd <$> get
  setBinder _ x e = do
    (count, (ctx, nfs)) <- get
    put (count, (M.insert x e ctx, nfs))
  preservingBindings _ m = get >>= \(_, (old, _)) -> m <* (get >>= \(c, (_, n)) -> put (c, (old, n)))

instance HasNamedMap (Prog err) NormalFormMap Expr' Expr' where
  getBindings _ = snd . snd <$> get
  setBinder _ x e = do
    (count, (ctx, nfs)) <- get
    put (count, (ctx, M.insert x e nfs))
  preservingBindings _ m = get >>= \(_, (_, old)) -> m <* (get >>= \(c, (v, _)) -> put (c, (v, old)))

instance HasTyVal (BindV ann e) (Maybe (Expr ann e)) (Expr ann e) where
  toVal = fst . getBindV
  toTy  = snd . getBindV
  fromTyVal = BindV


instance Freshenable (Prog err) Identifier where
  -- TODO: update this to actually do freshening (2020-02-20)
  freshen v = do
    (count, ctx) <- get
    put (count + 1, ctx)
    pure $ case v of
      Ignore -> GenIdent ("_", count)
      Ident v -> GenIdent (v, count)
      GenIdent (v, _) -> GenIdent (v, count)


instance Substitutable (Prog err) Identifier Expr' where
  substitute (v, e) (Var x)
    | v == x    = pure e
    | otherwise = pure (Var x)
  substitute s (FunTy abs) = FunTy <$> substAbs s abs
  substitute s (Abs   abs) = Abs   <$> substAbs s abs
  substitute s (ProductTy abs) = ProductTy <$> substAbs s abs
  substitute s (Pair e1 e2) = Pair <$> substitute s e1 <*> substitute s e2
  substitute s@(v, _) (PairElim v0 v1 v2 e1 e2 e3) = do
    e1' <- substitute s e1
    e2' <- if v == v1 || v == v2 then pure e2 else substitute s e2
    e3' <- if v == v0 then pure e3 else substitute s e3
    pure $ PairElim v0 v1 v2 e1' e2' e3'
  substitute s (IfExpr e1 e2 e3) = IfExpr <$> substitute s e1 <*> substitute s e2 <*> substitute s e3
  substitute s (App e1 e2) = do
    e1' <- substitute s e1
    e2' <- substitute s e2
    pure (App e1' e2')
  substitute _ e@Builtin{} = pure e
  substitute _ e@LitLevel{} = pure e
  substitute _ e@Hole{} = pure e
  substitute _ e@Implicit = pure e
  substitute _ e = error $ "substitution not yet defined for '" <> pprint e <> "'"


runProgFull :: Prog err a -> (Either err a, String)
runProgFull prog =
  evalState (runWriterT $ (runExceptT (runProg prog))) (0, (builtins, M.empty))
