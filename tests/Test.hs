module Main (main) where

import System.Directory (doesDirectoryExist)
import qualified System.IO.Strict as Strict

import Test.Tasty.HUnit (testCase, assertFailure, assertBool)
import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden (findByExtension)

import Language.Dlam.Interpreter (formatError)
import Language.Dlam.TypeChecking.Monad
  ( CM
  , TCErr, isSyntaxErr, isScopingErr, isTypingErr
  , runNewChecker
  , tcrRes)

import qualified Language.Dlam.Interpreter as Interpreter


main :: IO ()
main = do
  negativeSyntaxFiles <- findNegativeFiles syntaxDirName
  negativeScopeFiles <- findNegativeFiles scopeDirName
  negativeTypingFiles <- findNegativeFiles typingDirName
  positiveSyntaxFiles <- findPositiveFiles syntaxDirName
  positiveScopeFiles <- findPositiveFiles scopeDirName
  positiveTypingFiles <- findPositiveFiles typingDirName
  exampleFiles <- findExampleFiles
  defaultMain $
    testGroup "Tests"
      [ testGroup "File tests"
          [ testGroup "Positive cases"
            [ fileTestsPositiveSyntax positiveSyntaxFiles
            , fileTestsPositiveScope positiveScopeFiles
            , fileTestsPositiveTyping positiveTypingFiles
            , fileTestsPositiveExamples exampleFiles
            ]
          , testGroup "Negative cases"
            [ fileTestsNegativeSyntax negativeSyntaxFiles
            , fileTestsNegativeScope negativeScopeFiles
            , fileTestsNegativeTyping negativeTypingFiles
            ]
          ]
      ]


--------------------------
----- Positive tests -----
--------------------------


fileTestsPositiveGen :: String -> String -> (FilePath -> String -> CM a) -> [FilePath] -> TestTree
fileTestsPositiveGen groupName desc phase = testGroup groupName .
  fmap (\file -> testCase ("checking " <> file <> " " <> desc <> "s") $ do
                   src <- Strict.readFile file
                   let res = tcrRes $ runNewChecker (phase file src)
                   case res of
                     Right _ -> pure ()
                     Left err -> assertFailure
                       ("Expected file to " <> desc <> ", but got: " <> formatError err))


-- | The collection of positive syntax tests (i.e., those that should parse).
fileTestsPositiveSyntax :: [FilePath] -> TestTree
fileTestsPositiveSyntax = fileTestsPositiveGen "well-formed syntax" "parse" Interpreter.runParser


-- | The collection of positive scope tests (i.e., those that should scope check).
fileTestsPositiveScope :: [FilePath] -> TestTree
fileTestsPositiveScope = fileTestsPositiveGen "scope checking" "scope check" Interpreter.runScoper


-- | The collection of positive typing tests (i.e., those that should type check).
fileTestsPositiveTyping :: [FilePath] -> TestTree
fileTestsPositiveTyping = fileTestsPositiveGen "type-checking" "type check" Interpreter.runTypeChecker


-- | The collection of positive examples (should type check)
fileTestsPositiveExamples :: [FilePath] -> TestTree
fileTestsPositiveExamples = fileTestsPositiveGen "type-checking examples" "type check" Interpreter.runTypeChecker


--------------------------
----- Negative tests -----
--------------------------


fileTestsNegativeGen :: String -> String -> (FilePath -> String -> CM a) -> (TCErr -> Bool) -> [FilePath] -> TestTree
fileTestsNegativeGen groupName desc phase isErrGood = testGroup groupName .
  fmap (\file -> testCase ("checking " <> file <> " doesn't " <> desc) $ do
                   src <- Strict.readFile file
                   let res = tcrRes $ runNewChecker (phase file src)
                       (didErrOK, phaseMsg) =
                         either (\err ->
                           if isErrGood err
                           then (True, "")
                           else (False, "gave the following undesired error: " <> formatError err))
                                  (const (False, "did.")) res
                   assertBool ("Expected file not to " <> desc <> ", but it " <> phaseMsg) didErrOK)


-- | The collection of negative syntax tests (i.e., those that should not parse).
fileTestsNegativeSyntax :: [FilePath] -> TestTree
fileTestsNegativeSyntax = fileTestsNegativeGen "bad syntax" "parse" Interpreter.runParser isSyntaxErr


-- | The collection of negative scope tests (i.e., those that should not scope check).
fileTestsNegativeScope :: [FilePath] -> TestTree
fileTestsNegativeScope = fileTestsNegativeGen "ill-scoped" "scope check" Interpreter.runScoper isScopingErr


-- | The collection of negative typing tests (i.e., those that should not type check).
fileTestsNegativeTyping :: [FilePath] -> TestTree
fileTestsNegativeTyping = fileTestsNegativeGen "ill-typed" "type check" Interpreter.runTypeChecker isTypingErr


-------------------
----- Helpers -----
-------------------


positiveTestCasesDir :: FilePath
positiveTestCasesDir = "tests/cases/positive"


negativeTestCasesDir :: FilePath
negativeTestCasesDir = "tests/cases/negative"


examplesDir, syntaxDirName, scopeDirName, typingDirName :: FilePath
examplesDir = "examples"
syntaxDirName = "syntax"
scopeDirName = "scope"
typingDirName = "typing"


dlamFileExtensions :: [String]
dlamFileExtensions = [".lam"]


findNegativeFiles, findPositiveFiles :: FilePath -> IO [FilePath]
findNegativeFiles dir = findDlamFilesInDir (negativeTestCasesDir <> "/" <> dir)
findPositiveFiles dir = findDlamFilesInDir (positiveTestCasesDir <> "/" <> dir)

findExampleFiles :: IO [FilePath]
findExampleFiles = findDlamFilesInDir examplesDir


-- | Find DLAM files in the directory. If the directory does not
-- | exist, then returns an empty list.
findDlamFilesInDir :: FilePath -> IO [FilePath]
findDlamFilesInDir dir = do
  exists <- doesDirectoryExist dir
  if exists then findByExtension dlamFileExtensions dir else pure []
