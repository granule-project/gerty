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
import Language.Dlam.Syntax.Syntax
import Language.Dlam.Substitution (Freshenable(..))

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


runProgFull :: Prog err a -> (Either err a, String)
runProgFull prog =
  evalState (runWriterT $ (runExceptT (runProg prog))) (0, (builtins, M.empty))
