module Gerty (main) where

import Language.Gerty.Interpreter (formatError, InterpreterResult)
import Language.Gerty.TypeChecking.Monad
  ( runNewCheckerWithOpts
  , tcrLog
  , tcrRes
  , TCErr
  , Verbosity
  , verbositySilent
  , verbosityDebug
  , verbosityInfo
  , TCLog
  , formatLog
  , TCOpts
  , defaultTCOpts
  )
import qualified Language.Gerty.TypeChecking.Monad as TM
import qualified Language.Gerty.Interpreter as Interpreter
import Language.Gerty.Util.Pretty
  ( RenderOptions(..)
  , defaultRenderOptions
  , pprintShowWithOpts
  , Doc
  , green, red
  )

import Control.Monad      (unless, when)
import Data.List          (isPrefixOf, partition, intercalate)
import System.Directory   (doesPathExist)
import System.Environment (getArgs)
import System.Exit
import qualified System.Clock as Clock
import Text.Printf

import qualified Data.Version as Version
import Paths_gerty_main (version)

data Options = Options
  { verbosity :: Verbosity
  , renderOpts :: RenderOptions
  , tycOptimise :: Bool
  , benchmark   :: Bool
  , trials      :: Int
  , smtSimplify :: Bool
  , useSMT      :: Bool
  , showHelp    :: Bool
  , showVersion :: Bool
  }


defaultOptions :: Options
defaultOptions = Options
  { verbosity = verbositySilent
  , renderOpts = defaultRenderOptions
  , tycOptimise = False
  , benchmark   = False
  , trials      = 1
  , smtSimplify = False
  , useSMT      = True
  , showHelp    = False
  , showVersion = False
  }


extractTCOpts :: Options -> TCOpts
extractTCOpts opts = defaultTCOpts { TM.benchmark = benchmark opts
                                   , TM.tycOptimise = tycOptimise opts
                                   , TM.smtSimplify = smtSimplify opts
                                   , TM.useSMT      = useSMT opts
                                   }


printLog :: RenderOptions -> Verbosity -> TCLog -> IO ()
printLog ro v l = putStrLn $ pprintShowWithOpts ro (formatLog v l)

outputHelp :: IO ()
outputHelp = do
  putStrLn "----------------------------------------------------------------"
  outputVersion
  putStrLn "----------------------------------------------------------------\n"
  flip mapM_ options
    (\(opt, (desc, _))
        -> putStrLn $ "  --" ++ opt ++ (replicate (40 - (length opt)) ' ') ++ desc)
  putStrLn ""
  return ()


outputVersion :: IO ()
outputVersion = putStrLn $ "Gerty v" <> Version.showVersion version ++ " - graded modal dependent type theory"

options :: [(String, (String, String -> Options -> Either String Options))]
options = [
   ("help",            ("Show information on flags"
                        , \_ o -> Right (o { showHelp = True })))

  ,("version",         ("Show version"
                        , \_ o -> Right (o { showVersion = True })))

  ,("tyc-optimise",    ("Apply grade-directed optimisation to type checking"
                        , \_ o -> Right (o { tycOptimise = True })))

  ,("benchmark",       ("Benchmarking: Timing on"
                        , \_ o -> Right (o { benchmark = True })))

  ,("trials",          ("Benchmarking: Number of times to repeat type checking"
                        , \x o -> Right (o { trials = read (drop 9 x) })))

  ,("silent",          ("Run in silent mode"
                        , \_ o -> Right (o { verbosity = verbositySilent })))

  ,("info",            ("Run in more verbose mode"
                        , \_ o -> Right (o { verbosity = verbosityInfo })))

  ,("no-simplify-smt", ("Don't simplify the SMT theorems"
                        , \_ o -> Right (o { smtSimplify = False })))

  ,("simplify-smt",    ("Simplify the SMT theorems"
                        , \_ o -> Right (o { smtSimplify = True })))

  ,("no-smt",          ("Turn off SMT for type checking; use normalisation only"
                        , \_ o -> Right (o { useSMT = False })))

  ,("use-smt",         ("Turn on SMT for type checking"
                        , \_ o -> Right (o { useSMT = True })))

  ,("debug",           ("Run in debugging mode (mostly for devs)"
                        , \_ o -> Right (o { verbosity = verbosityDebug
                                           , renderOpts = (renderOpts o) { showIdentNumbers = True }})))
 ]

parseArgs :: [String] -> IO (Options, [String])
parseArgs args = do
  let (optionArgs, nonOptionArgs) = partition ("--" `isPrefixOf`) args
  opts <- parseArgsWithDefaults defaultOptions optionArgs
  pure (opts, nonOptionArgs)
  where
    parseArgsWithDefaults opts (('-':'-':optionText):rest) =
      -- Parsed an options, check the available options
      case lookup optionText options of
        Nothing -> do
          putStrLn $ "unknown option: " <> optionText
          exitFailure
        Just (_, optionFun)  ->
          case optionFun optionText opts of
            -- Didn't provide the option properly
            Left msg -> do
              putStrLn msg
              exitFailure
            -- Success
            Right opts' ->
              parseArgsWithDefaults opts' rest

    parseArgsWithDefaults opts [] =
      pure opts

    parseArgsWithDefaults _ (opt:_) = do
      putStrLn $ "unknown option: " <> opt
      exitFailure

main :: IO ()
main = do
  (opts, args) <- parseArgs =<< getArgs
  let printLn = putStrLn . pprintShowWithOpts (renderOpts opts)
  handleMode printLn opts args

-- | Dispatch on help / version / file argument, one level of nesting.
handleMode :: (Doc -> IO ()) -> Options -> [String] -> IO ()
handleMode printLn opts args
  | showHelp opts    = outputHelp
  | showVersion opts = outputVersion
  | otherwise        = case args of
      []          -> putStrLn "Please supply a filename as a command line argument OR --help to see options"
      (fname : _) -> typeCheckFile printLn opts fname

-- | Check a single file: validate existence, then run the checker.
typeCheckFile :: (Doc -> IO ()) -> Options -> FilePath -> IO ()
typeCheckFile printLn opts fname = do
  exists <- doesPathExist fname
  unless exists $ do
    putStrLn $ "File `" <> fname <> "` cannot be found."
    exitFailure
  input <- readFile fname
  status <- typeCheckInput printLn opts fname input
  handleResult printLn status

-- | Type-check the input, reporting per-run status. Returns an error
-- if any run failed to type-check, otherwise the AST.
typeCheckInput :: (Doc -> IO ())
               -> Options -> FilePath -> String
               -> IO (Either TCErr InterpreterResult)
typeCheckInput printLn opts fname input =
  benchmarkTime (benchmark opts) (trials opts) $ \isLast -> do
    res <- runNewCheckerWithOpts (extractTCOpts opts)
                                   (Interpreter.runTypeChecker fname input)
    when isLast $ printLog (renderOpts opts) (verbosity opts) (tcrLog res)
    reportResult printLn isLast (tcrRes res)

-- | Report the result of a single checker run and pass it through.
reportResult :: (Doc -> IO ()) -> Bool -> Either TCErr InterpreterResult -> IO (Either TCErr InterpreterResult)
reportResult printLn isLast res = case res of
  Left _    -> do printLn (red "Ill-typed."); pure res
  Right ast -> do
    when isLast $ printLn (green "Well typed.")
    pure (Right ast)

-- | Map the overall check result to a process exit status.
handleResult :: (Doc -> IO ()) -> Either TCErr InterpreterResult -> IO ()
handleResult printLn res = case res of
  Left err -> printLn (formatError err) >> exitFailure
  Right _  -> exitSuccess

-- Benchmarking helpers follow

benchmarkTime :: Bool -> Int -> (Bool -> IO a) -> IO a
benchmarkTime False _ m = m True
benchmarkTime True  trials m = runBenchmark trials m

runBenchmark :: Int -> (Bool -> IO a) -> IO a
runBenchmark trials m = do
  measurements <- mapM (timedRun m) [0..trials]
  let result = head (map snd measurements)
      runs   = map fst measurements
      totalTime = sum runs
      meanTime = totalTime / fromIntegral trials
      stdErr   = stdError runs
  -- Output
  putStrLn $ "Timing for each run   = " <> intercalate ", " (map show runs)
  printf "Mean time of %d trials = %6.2f (%6.2f) ms\n" trials meanTime stdErr
  pure result

timedRun :: (Bool -> IO a) -> Int -> IO (Double, a)
timedRun m n = do
  start  <- Clock.getTime Clock.Monotonic
  -- Run the computation
  result <- m (n == 0)
  -- Force the result (to WHNF)
  _ <- pure $ result `seq` result
  end    <- Clock.getTime Clock.Monotonic
  let time = fromIntegral (Clock.toNanoSecs (Clock.diffTimeSpec end start)) / (10^(6 :: Integer)::Double)
  pure (time, result)

-- Sample standard deviation
stdDeviation :: [Double] -> Double
stdDeviation xs = sqrt (divisor * (sum . map (\x -> (x - mean)**2) $ xs))
  where
   divisor = 1 / ((cast n) - 1)
   n = length xs
   mean = sum xs / (cast n)

cast :: Int -> Double
cast = fromInteger . toInteger

-- Sample standard error
stdError :: [Double] -> Double
stdError []  = 0
stdError [_] = 0
stdError xs  = (stdDeviation xs) / sqrt (cast n)
  where
    n = length xs
