{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Dlam where

import Control.Monad.State
import Control.Monad.Trans.Maybe
import qualified Data.Map as M

import Dlam.Binders (HasBinders(..), HasTyVal(..))
import Dlam.Parser      (parseProgram)
import Dlam.PrettyPrint (pprint)
import Dlam.Substitution (Substitutable(..), substAbs, Freshenable(..))
import Dlam.Syntax
import Dlam.Types

import System.Directory   (doesPathExist)
import System.Environment (getArgs)
import System.Exit

newtype BindV e = BindV { getBindV :: (Maybe (Expr e), Expr e) }

instance (Show e) => Show (BindV e) where
  show = show . getBindV

type Context = [(Identifier, BindV NoExt)]

builtins :: Context
builtins = [ ("Type",  BindV (Just typeTy, FunTy (mkAbs "_" levelTy (mkUnivTy (LitLevel 0)))))
           , ("Level", BindV (Just levelTy, (mkUnivTy (LitLevel 0))))
           , ("lzero", BindV (Just lzero, levelTy))
           ]

newtype Prog a =
  Prog { runProg :: MaybeT (State Context) a }
  deriving ( Applicative, Functor, Monad
           , MonadState [(Identifier, BindV NoExt)])

-- Example instance where identifiers are mapped to types
-- and (optional) definitions via a list.
instance HasBinders Prog Identifier (BindV NoExt) where
  getBindings = M.fromList <$> get
  setBinder x e = do
    st <- get
    put ((x, e) : st)
  preservingBindings m = get >>= \old -> m <* put old

instance HasTyVal (BindV e) (Maybe (Expr e)) (Expr e) where
  toVal = fst . getBindV
  toTy  = snd . getBindV
  fromTyVal = BindV


instance Freshenable Prog Identifier where
  -- TODO: update this to actually do freshening (2020-02-20)
  freshen v = pure v


instance Substitutable Prog Identifier (Expr NoExt) where
  substitute (v, e) (Var x)
    | v == x    = pure e
    | otherwise = pure (Var x)
  substitute s (FunTy abs) = FunTy <$> substAbs s abs
  substitute s@(v,_) (Abs x (Just t) e) = do
    t' <- substitute s t
    e' <- if v == x then pure e else substitute s e
    pure (Abs x (Just t') e')
  substitute s@(v,_) (Abs x Nothing e) = do
    e' <- if v == x then pure e else substitute s e
    pure (Abs x Nothing e')
  substitute s (App e1 e2) = do
    e1' <- substitute s e1
    e2' <- substitute s e2
    pure (App e1' e2')
  substitute _ e@Builtin{} = pure e
  substitute _ e@LitLevel{} = pure e
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
              case evalState (runMaybeT (runProg (doNASTInference nast))) builtins of

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
