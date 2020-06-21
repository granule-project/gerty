{-# LANGUAGE OverloadedStrings #-}
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
import Language.Dlam.Util.Pretty
  ( RenderOptions(..)
  , defaultRenderOptions
  , pprintShowWithOpts
  , green, red
  )

import Data.List (isPrefixOf, partition)
import System.Directory   (doesPathExist)
import System.Environment (getArgs)
import System.Exit


data Options = Options { verbosity :: Verbosity
                       , renderOpts :: RenderOptions
                       }


defaultOptions :: Options
defaultOptions = Options { verbosity = verbosityInfo, renderOpts = defaultRenderOptions }


printLog :: RenderOptions -> Verbosity -> TCLog -> IO ()
printLog ro v l = putStrLn $ pprintShowWithOpts ro (formatLog v l)


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
          parseArgsWithDefaults (opts { verbosity = verbosityDebug, renderOpts = (renderOpts opts) { showIdentNumbers = True } }) xs
        parseArgsWithDefaults _ (x:_) = do
          putStrLn $ "unknown option: " <> x
          exitFailure


main :: IO ()
main = do
  (opts, args) <- parseArgs =<< getArgs
  let rOpts   = renderOpts opts
      printLn = putStrLn . pprintShowWithOpts rOpts
  case args of
    [] -> putStrLn "Please supply a filename as a command line argument"
    (fname:_) -> do
      exists <- doesPathExist fname
      if not exists
        then putStrLn $ "File `" <> fname <> "` cannot be found."
        else do
          input <- readFile fname
          let res = runNewChecker (Interpreter.runTypeChecker fname input)
          printLog (renderOpts opts) (verbosity opts) (tcrLog res)
          case tcrRes res of
            Left err -> do
              printLn $ red "Ill-typed."
              printLn (formatError err) >> exitFailure
            Right _ -> do
              printLn $ green "Well typed."
              exitSuccess
