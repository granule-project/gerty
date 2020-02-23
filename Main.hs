{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Dlam where

import Control.Monad.State
import Control.Monad.Trans.Maybe
import qualified Data.Map as M

import Language.Dlam.Binders
  ( HasNamedMap(..)
  , HasBinderMap
  , BinderMap
  , NormalFormMap
  , HasNormalFormMap
  , HasTyVal(..)
  )
import Language.Dlam.Parser      (parseProgram)
import Language.Dlam.PrettyPrint (pprint)
import Language.Dlam.Substitution (Substitutable(..), substAbs, Freshenable(..))
import Language.Dlam.Syntax
import Language.Dlam.Types

import System.Directory   (doesPathExist)
import System.Environment (getArgs)
import System.Exit

newtype BindV e = BindV { getBindV :: (Maybe (Expr e), Expr e) }

instance (Show e) => Show (BindV e) where
  show = show . getBindV

data MapTypes = VarBindings | NormalForms

type Context = M.Map Identifier (BindV NoExt)
type NormalFormContext = M.Map (Expr NoExt) (Expr NoExt)

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
           ]

type ProgState = (Int, ProgMaps)

newtype Prog a =
  Prog { runProg :: MaybeT (State ProgState) a }
  deriving ( Applicative, Functor, Monad
           , MonadState ProgState)

-- Example instance where identifiers are mapped to types
-- and (optional) definitions via a list.
instance HasNamedMap Prog BinderMap Identifier (BindV NoExt) where
  getBindings _ = fst . snd <$> get
  setBinder _ x e = do
    (count, (ctx, nfs)) <- get
    put (count, (M.insert x e ctx, nfs))
  preservingBindings _ m = get >>= \(_, (old, _)) -> m <* (get >>= \(c, (_, n)) -> put (c, (old, n)))

instance HasBinderMap Prog Identifier (BindV NoExt)

instance HasNamedMap Prog NormalFormMap (Expr NoExt) (Expr NoExt) where
  getBindings _ = snd . snd <$> get
  setBinder _ x e = do
    (count, (ctx, nfs)) <- get
    put (count, (ctx, M.insert x e nfs))
  preservingBindings _ m = get >>= \(_, (_, old)) -> m <* (get >>= \(c, (v, _)) -> put (c, (v, old)))

instance HasNormalFormMap Prog (Expr NoExt) (Expr NoExt)

instance HasTyVal (BindV e) (Maybe (Expr e)) (Expr e) where
  toVal = fst . getBindV
  toTy  = snd . getBindV
  fromTyVal = BindV


instance Freshenable Prog Identifier where
  -- TODO: update this to actually do freshening (2020-02-20)
  freshen v = do
    (count, ctx) <- get
    put (count + 1, ctx)
    pure $ case v of
      Ignore -> GenIdent ("_", count)
      Ident v -> GenIdent (v, count)
      GenIdent (v, _) -> GenIdent (v, count)


instance Substitutable Prog Identifier (Expr NoExt) where
  substitute (v, e) (Var x)
    | v == x    = pure e
    | otherwise = pure (Var x)
  substitute s (FunTy abs) = FunTy <$> substAbs s abs
  substitute s (Abs   abs) = Abs   <$> substAbs s abs
  substitute s (ProductTy abs) = ProductTy <$> substAbs s abs
  substitute s (Pair e1 e2) = Pair <$> substitute s e1 <*> substitute s e2
  substitute s@(v, _) (PairElim v1 v2 e1 e2) = do
    e1' <- substitute s e1
    e2' <- if v == v1 || v == v2 then pure e2 else substitute s e2
    pure $ PairElim v1 v2 e1' e2'
  substitute s (IfExpr e1 e2 e3) = IfExpr <$> substitute s e1 <*> substitute s e2 <*> substitute s e3
  substitute s (App e1 e2) = do
    e1' <- substitute s e1
    e2' <- substitute s e2
    pure (App e1' e2')
  substitute _ e@Builtin{} = pure e
  substitute _ e@LitLevel{} = pure e
  substitute _ e@Wild{} = pure e
  substitute _ e = error $ "substitution not yet defined for '" <> pprint e <> "'"

main :: IO ()
main = do
  args <- getArgs
  -- Get command line args
  case args of
    [] -> putStrLn "Please supply a filename as a command line argument"
    -- If we have at least one
    (fname:_) -> do
      -- Check if this is a file
      exists <- doesPathExist fname
      if not exists
        then putStrLn $ "File `" <> fname <> "` cannot be found."
        else do
          -- Read the file, parse, and do something...
          input <- readFile fname
          case parseProgram fname input of
            Right (ast, _options) -> do
              -- Show AST
              putStrLn $ "\n " <> ansi_bold <> "AST: " <> ansi_reset <> show ast
              let nast = normaliseAST ast
              putStrLn $ "\n " <> ansi_bold <> "NAST: " <> ansi_reset <> show nast

              -- Pretty print
              putStrLn $ "\n " <> ansi_bold <> "Pretty:\n" <> ansi_reset <> pprint nast

              -- Typing
              case evalState (runMaybeT (runProg (doNASTInference nast))) (0, (builtins, M.empty)) of

                 Nothing -> putStrLn "could not infer type"
                 Just nastInfed  ->
                   putStrLn $ "\n " <> ansi_bold <> "NAST after inference:\n" <> ansi_reset <> pprint nastInfed

            Left msg -> do
              putStrLn $ ansi_red ++ "Error: " ++ ansi_reset ++ msg
              exitFailure

ansi_red, ansi_green, ansi_reset, ansi_bold :: String
ansi_red   = "\ESC[31;1m"
ansi_green = "\ESC[32;1m"
ansi_reset = "\ESC[0m"
ansi_bold  = "\ESC[1m"
