module Dlam where

import Dlam.Options
import Dlam.Parser      (parseProgram)
import Dlam.PrettyPrint (pprint)
import Dlam.Syntax
import Dlam.Types

import System.Directory   (doesPathExist)
import System.Environment (getArgs)
import System.Exit

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

              -- Pretty print
              putStrLn $ "\n " <> ansi_bold <> "Pretty:\n" <> ansi_reset <> pprint ast

              let nast = normaliseAST ast
              putStrLn $ "\n " <> ansi_bold <> "NAST: " <> ansi_reset <> show nast

              -- Pretty print
              putStrLn $ "\n " <> ansi_bold <> "Pretty (NAST):\n" <> ansi_reset <> pprint nast

              -- Typing
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
