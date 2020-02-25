{-# LANGUAGE ScopedTypeVariables #-}
import Control.Exception (catch, throwIO)
import Control.Monad.Except
import Data.Algorithm.Diff (getGroupedDiff)
import Data.Algorithm.DiffOutput (ppDiff)
import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden (findByExtension)
import Test.Tasty.Golden.Advanced (goldenTest)
import System.Directory (removeFile)
import qualified System.IO.Strict as Strict


import Language.Dlam.Interpreter
  ( InterpreterResult(..)
  , InterpreterError
  , formatError
  )
import Language.Dlam.PrettyPrint (pprint)
import Language.Dlam.Program (runProgFull)
import Language.Dlam.Syntax (NoAnn, NoExt)
import qualified Language.Dlam.Interpreter as Interpreter


main :: IO ()
main = do
  negative <- goldenTestsNegative
  positive <- goldenTestsPositive
  runTestsAndCleanUp $ testGroup "Golden tests" [negative, positive]


type InterpreterError' = InterpreterError NoAnn NoExt

positiveTestCasesDir :: FilePath
positiveTestCasesDir = "tests/cases/positive"

negativeTestCasesDir :: FilePath
negativeTestCasesDir = "tests/cases/negative"

examplesDir :: FilePath
examplesDir = "examples"

dlamFileExtensions :: [String]
dlamFileExtensions = [".lam"]

findDlamFilesInDir :: FilePath -> IO [FilePath]
findDlamFilesInDir = findByExtension dlamFileExtensions

outputFileExtension :: String
outputFileExtension = ".output"

findOutputFilesInDir :: FilePath -> IO [FilePath]
findOutputFilesInDir = findByExtension [outputFileExtension]


-- | The collection of negative tests (i.e., those that should not type check).
goldenTestsNegative :: IO TestTree
goldenTestsNegative = do
  files <- findByExtension dlamFileExtensions negativeTestCasesDir

  pure $ testGroup "negative cases" (map (dlamGolden formatResult) files)

  where
    formatResult :: Either InterpreterError' InterpreterResult -> String
    formatResult res = case res of
                         Left err -> formatError err
                         Right x -> error $ "Negative test passed!\n" <> show x


-- | The collection of positive tests (i.e., those that should type check).
goldenTestsPositive :: IO TestTree
goldenTestsPositive = do
  exampleFiles  <- findDlamFilesInDir examplesDir
  positiveFiles <- findDlamFilesInDir positiveTestCasesDir
  let files = exampleFiles <> positiveFiles

  pure $ testGroup "positive cases and examples" (map (dlamGolden formatResult) files)

  where
    formatResult :: Either InterpreterError' InterpreterResult -> String
    formatResult res = case res of
                         Right (InterpreterResult val) -> pprint val
                         Left err -> error $ formatError err


dlamGolden
  :: (Either InterpreterError' InterpreterResult -> String)
  -> FilePath
  -> TestTree
dlamGolden formatResult file = goldenTest
    file
    (Strict.readFile outfile)
    (formatResult <$> runDlam file)
    checkDifference
    (\actual -> unless (null actual) (writeFile outfile actual))
  where
    outfile = file <> outputFileExtension
    checkDifference :: String -> String -> IO (Maybe String)
    checkDifference exp act = pure $ if exp == act
      then Nothing
      else Just $ unlines
        [ "Contents of " <> outfile <> " (<) and actual output (>) differ:"
        , ppDiff $ getGroupedDiff (lines exp) (lines act)
        ]

    runDlam :: FilePath -> IO (Either InterpreterError' InterpreterResult)
    runDlam fp = do
      src <- readFile fp
      -- Typing
      let (res, _log) = runProgFull (Interpreter.run fp src)
      pure res


-- | Run tests and remove all output files.
runTestsAndCleanUp :: TestTree -> IO ()
runTestsAndCleanUp tests = do
  defaultMain tests `catch` (\(e :: InterpreterError') -> do
    outfiles <- findOutputFilesInDir "."
    forM_ outfiles removeFile
    throwIO e)
