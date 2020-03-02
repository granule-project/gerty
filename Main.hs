module Dlam (main) where

import Language.Dlam.Interpreter (formatError)
import Language.Dlam.TypeChecking.Monad (runNewChecker, tcrLog, tcrRes)
import qualified Language.Dlam.Interpreter as Interpreter

import System.Directory   (doesPathExist)
import System.Environment (getArgs)
import System.Exit


main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> putStrLn "Please supply a filename as a command line argument"
    (fname:_) -> do
      exists <- doesPathExist fname
      if not exists
        then putStrLn $ "File `" <> fname <> "` cannot be found."
        else do
          input <- readFile fname
          let res = runNewChecker (Interpreter.run fname input)
          putStrLn (tcrLog res)
          case tcrRes res of
            Left err -> putStrLn (formatError err) >> exitFailure
            Right _ -> exitSuccess
