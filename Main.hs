module Dlam (main) where

import Language.Dlam.Interpreter (formatError)
import Language.Dlam.TypeChecking.Monad
  ( runNewChecker
  , tcrLog
  , tcrRes
  , Verbosity
  , verbositySilent
  , verbosityDebug
  , verbosityInfo
  , TCLog
  , formatLog
  )
import qualified Language.Dlam.Interpreter as Interpreter

import Data.List (isPrefixOf, partition)
import System.Directory   (doesPathExist)
import System.Environment (getArgs)
import System.Exit


data Options = Options { verbosity :: Verbosity }


defaultOptions :: Options
defaultOptions = Options { verbosity = verbosityInfo }


printLog :: Verbosity -> TCLog -> IO ()
printLog v l = putStr (formatLog v l)


parseArgs :: [String] -> IO (Options, [String])
parseArgs args = do
  let (optionArgs, nonOptionArgs) = partition ("--" `isPrefixOf`) args
  opts <- parseArgsWithDefaults defaultOptions optionArgs
  pure (opts, nonOptionArgs)
  where parseArgsWithDefaults opts [] = pure opts
        parseArgsWithDefaults opts ("--silent":xs) =
          parseArgsWithDefaults (opts { verbosity = verbositySilent }) xs
        parseArgsWithDefaults opts ("--info":xs) =
          parseArgsWithDefaults (opts { verbosity = verbosityInfo }) xs
        parseArgsWithDefaults opts ("--debug":xs) =
          parseArgsWithDefaults (opts { verbosity = verbosityDebug }) xs
        parseArgsWithDefaults _ (x:_) = do
          putStrLn $ "unknown option: " <> x
          exitFailure


main :: IO ()
main = do
  (opts, args) <- parseArgs =<< getArgs
  case args of
    [] -> putStrLn "Please supply a filename as a command line argument"
    (fname:_) -> do
      exists <- doesPathExist fname
      if not exists
        then putStrLn $ "File `" <> fname <> "` cannot be found."
        else do
          input <- readFile fname
          let res = runNewChecker (Interpreter.runTypeChecker fname input)
          printLog (verbosity opts) (tcrLog res)
          case tcrRes res of
            Left err -> do
              putStrLn $ "\x1b[31m" ++ "Ill-typed." ++ "\x1b[0m"
              putStrLn (formatError err) >> exitFailure
            Right _ -> do
              putStrLn $ "\x1b[32m" ++ "Well typed." ++ "\x1b[0m"
              exitSuccess
