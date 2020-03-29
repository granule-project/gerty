module Dlam (main) where

import Language.Dlam.TypeChecking.Monad
import qualified Language.Dlam.Interpreter as Interpreter

import Data.Either (partitionEithers)
import Data.List (isPrefixOf, partition)
import System.Directory   (doesPathExist)
import System.Environment (getArgs)
import System.Exit


data Options = Options { verbosity :: Verbosity, verboseErrors :: ErrorVerbosity }


defaultOptions :: Options
defaultOptions = Options { verbosity = verbosityInfo, verboseErrors = errVerbosityNone }


printLog :: Verbosity -> TCLog -> IO ()
printLog v l = putStr (formatLog v l)


parseArgs :: [String] -> IO (Options, [String])
parseArgs args = do
  let (valuedArgs, optionArgs, nonOptionArgs) =
        let (allOptArgs, nonOptArgs) = partition ("--" `isPrefixOf`) args
            (vArgs, optArgs) =
              partitionEithers $ fmap (\a -> case break (=='=') a of
                                               (wVal, '=':v) -> Left (wVal, v)
                                               (x, _) -> Right x) allOptArgs
        in (vArgs, optArgs, nonOptArgs)
  opts <- flip parseValArgsWithDefaults valuedArgs
       =<< parseArgsWithDefaults defaultOptions optionArgs
  pure (opts, nonOptionArgs)
  where parseArgsWithDefaults opts [] = pure opts
        parseArgsWithDefaults opts ("--silent":xs) =
          parseArgsWithDefaults (opts { verbosity = verbositySilent }) xs
        parseArgsWithDefaults opts ("--info":xs) =
          parseArgsWithDefaults (opts { verbosity = verbosityInfo }) xs
        parseArgsWithDefaults opts ("--debug":xs) =
          parseArgsWithDefaults (opts { verbosity = verbosityDebug }) xs
        parseArgsWithDefaults opts ("--verbose-errors":xs) =
          parseArgsWithDefaults (opts { verboseErrors = errVerbosityPartial }) xs
        parseArgsWithDefaults _ (x:_) = do
          putStrLn $ "unknown option: " <> x
          exitFailure
        parseValArgsWithDefaults opts [] = pure opts
        parseValArgsWithDefaults opts (("--verbose-errors", v):xs) = do
          verb <- case v of
                    "none" -> pure errVerbosityNone
                    "partial" -> pure errVerbosityPartial
                    "full-no-builtins" -> pure errVerbosityFullNoBuiltins
                    "full" -> pure errVerbosityFull
                    _ -> putStrLn ("bad value for option '--verbose-errors': " <> v) >> exitFailure
          parseValArgsWithDefaults (opts { verboseErrors = verb }) xs
        parseValArgsWithDefaults _ ((x, _):_) = do
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
            Left err -> putStrLn (displayError (verboseErrors opts) err) >> exitFailure
            Right _ -> exitSuccess
