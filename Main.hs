{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Dlam where

import Control.Monad.State
import Control.Monad.Trans.Maybe

import Dlam.Binders (HasBinders(..))
import Dlam.Options
import Dlam.Parser      (parseProgram)
import Dlam.PrettyPrint (pprint)
import Dlam.Syntax
import Dlam.Types

import System.Directory   (doesPathExist)
import System.Environment (getArgs)
import System.Exit

newtype Prog a =
  Prog { runProg :: MaybeT (State [(Identifier, (Maybe (Expr NoExt), Expr NoExt))]) a }
  deriving ( Applicative, Functor, Monad
           , MonadState [(Identifier, (Maybe (Expr NoExt), Expr NoExt))])

-- Example instance where identifiers are mapped to types
-- and (optional) definitions via a list.
instance HasBinders Prog Identifier (Maybe (Expr NoExt)) (Expr NoExt) where
  getBinderType x = do
    st <- get
    pure $ snd <$> lookup x st
  getBinderValue x = do
    st <- get
    pure $ fst <$> lookup x st
  setBinder x e = do
    st <- get
    put ((x, e) : st)

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
            Right (ast, options) -> do
              -- Show AST
              putStrLn $ "\n " <> ansi_bold <> "AST: " <> ansi_reset <> show ast
              let nast = normaliseAST ast
              putStrLn $ "\n " <> ansi_bold <> "NAST: " <> ansi_reset <> show nast

              -- Pretty print
              putStrLn $ "\n " <> ansi_bold <> "Pretty:\n" <> ansi_reset <> pprint nast

              -- Typing
              case evalState (runMaybeT (runProg (doNASTInference nast))) [] of

                 Nothing -> putStrLn "could not infer type"
                 Just nastInfed  ->
                   putStrLn $ "\n " <> ansi_bold <> "NAST after inference:\n" <> ansi_reset <> pprint nastInfed

{-
              case typeInference options ast of
                 Nothing -> putStrLn $ "\n " <> ansi_bold <> ansi_red
                                             <> "Not well-typed.\n" <> ansi_reset
                 Just ty -> putStrLn $ "\n " <> ansi_bold <> ansi_green
                                             <> "Well-typed " <> ansi_reset
                                             <> ansi_bold <> "as " <> ansi_reset <>pprint ty
 -}
            Left msg -> do
              putStrLn $ ansi_red ++ "Error: " ++ ansi_reset ++ msg
              exitFailure

typeInference :: [Option] -> Expr NoExt -> Maybe (Expr NoExt)
typeInference _ = synth []

ansi_red, ansi_green, ansi_reset, ansi_bold :: String
ansi_red   = "\ESC[31;1m"
ansi_green = "\ESC[32;1m"
ansi_reset = "\ESC[0m"
ansi_bold  = "\ESC[1m"
