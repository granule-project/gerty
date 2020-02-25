module Dlam (main) where

import Language.Dlam.Interpreter (formatError)
import Language.Dlam.Program (runProgFull)
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
          let (res, log) = runProgFull (Interpreter.run fname input)
          putStrLn log
          case res of
            Left err -> putStrLn (formatError err) >> exitFailure
            Right _ -> exitSuccess
