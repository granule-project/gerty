module Main (main) where

import Data.Either (isLeft)
import qualified System.IO.Strict as Strict

import Test.Tasty.HUnit (testCase, assertFailure, assertBool)
import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden (findByExtension)

import Language.Dlam.Interpreter (formatError)
import Language.Dlam.Program (runProgFull)

import qualified Language.Dlam.Interpreter as Interpreter


main :: IO ()
main = do
  negativeFiles <- findNegativeFiles
  positiveFiles <- findPositiveFiles
  defaultMain $
    testGroup "Tests"
      [ testGroup "File tests"
          [ fileTestsPositive positiveFiles, fileTestsNegative negativeFiles ]
      ]


-- | The collection of positive tests (i.e., those that should type check).
fileTestsPositive :: [FilePath] -> TestTree
fileTestsPositive = testGroup "positive cases and examples" .
  fmap (\file -> testCase ("checking " <> file <> " type checks") $ do
                   src <- Strict.readFile file
                   let (res, _log) = runProgFull (Interpreter.run file src)
                   case res of
                     Right _ -> pure ()
                     Left err -> assertFailure
                       ("Expected file to type check, but got: " <> formatError err))


-- | The collection of negative tests (i.e., those that should not type check).
fileTestsNegative :: [FilePath] -> TestTree
fileTestsNegative = testGroup "negative file cases" .
  fmap (\file -> testCase ("checking " <> file <> " doesn't type check") $ do
                   src <- Strict.readFile file
                   let (res, _log) = runProgFull (Interpreter.run file src)
                   assertBool "Expected file not to type check, but it did."
                                (isLeft res))


positiveTestCasesDir :: FilePath
positiveTestCasesDir = "tests/cases/positive"


negativeTestCasesDir :: FilePath
negativeTestCasesDir = "tests/cases/negative"


examplesDir :: FilePath
examplesDir = "examples"


dlamFileExtensions :: [String]
dlamFileExtensions = [".lam"]


findNegativeFiles, findPositiveFiles :: IO [FilePath]
findNegativeFiles = findDlamFilesInDir negativeTestCasesDir
findPositiveFiles =
  (<>) <$> findDlamFilesInDir examplesDir <*> findDlamFilesInDir positiveTestCasesDir


findDlamFilesInDir :: FilePath -> IO [FilePath]
findDlamFilesInDir = findByExtension dlamFileExtensions
