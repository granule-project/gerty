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

newtype BindV = BindV { getBindV :: (Maybe Expr, Expr) }

instance Show BindV where
  show = show . getBindV

type Context = M.Map Name BindV
type NormalFormContext = M.Map Expr Expr

type ProgMaps = (Context, NormalFormContext)

builtins :: Context
builtins = M.fromList
  (fmap (\bin -> (builtinName bin, BindV (Just $ builtinBody bin, builtinType bin)))
   [ typeTy
   , levelTy, lzero, lsuc, lmax
   , inlTerm, inrTerm
   , natTy, dnzero, dnsucc
   , unitTerm, unitTy
   , idTy, reflTerm
   , emptyTy
   ])

type ProgState = (Int, ProgMaps)

newtype Prog err a =
  Prog { runProg :: ExceptT err (WriterT String (State ProgState)) a }
  deriving ( Applicative, Functor, Monad
           , MonadState ProgState
           , MonadWriter String
           , MonadError err)

-- Example instance where identifiers are mapped to types
-- and (optional) definitions via a list.
instance HasNamedMap (Prog err) BinderMap Name BindV where
  getBindings _ = fst . snd <$> get
  setBinder _ x e = do
    (count, (ctx, nfs)) <- get
    put (count, (M.insert x e ctx, nfs))
  preservingBindings _ m = get >>= \(_, (old, _)) -> m <* (get >>= \(c, (_, n)) -> put (c, (old, n)))

instance HasNamedMap (Prog err) NormalFormMap Expr Expr where
  getBindings _ = snd . snd <$> get
  setBinder _ x e = do
    (count, (ctx, nfs)) <- get
    put (count, (ctx, M.insert x e nfs))
  preservingBindings _ m = get >>= \(_, (_, old)) -> m <* (get >>= \(c, (v, _)) -> put (c, (v, old)))

instance HasTyVal BindV (Maybe Expr) Expr where
  toVal = fst . getBindV
  toTy  = snd . getBindV
  fromTyVal = BindV


instance Freshenable (Prog err) Name where
  -- TODO: update this to actually do freshening (2020-02-20)
  freshen v = do
    (count, ctx) <- get
    put (count + 1, ctx)
    pure $ case v of
      Ignore -> GenIdent ("_", count)
      Ident v -> GenIdent (v, count)
      GenIdent (v, _) -> GenIdent (v, count)


instance Substitutable (Prog err) Name Expr where
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
  substitute _ e@Builtin{} = pure e
  substitute _ e@LitLevel{} = pure e
  substitute _ e@Hole{} = pure e
  substitute _ e@Implicit = pure e
  substitute _ e = error $ "substitution not yet defined for '" <> pprint e <> "'"


runProgFull :: Prog err a -> (Either err a, String)
runProgFull prog =
  evalState (runWriterT $ (runExceptT (runProg prog))) (0, (builtins, M.empty))
