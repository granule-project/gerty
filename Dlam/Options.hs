module Dlam.Options where

import Control.Monad.Trans.Reader

------------------------------
-- Language options that `lcore` accepts in files

data Option = ML
  deriving (Eq, Show)

-- Some helpers
isFullBeta :: [Option] -> Bool
isFullBeta options = True

isML :: [Option] -> Bool
isML options = elem ML options

language :: [Option] -> String
language options = if isML options then "ML" else "lambda"

-- Builds up a the language option list and checks for conflicting options
addOption :: Option -> [Option] -> ReaderT String (Either String) [Option]
addOption opt opts = pure $ opt : opts

showReducer :: [Option] -> String
showReducer opts | isFullBeta opts = "Determinised full beta"
showReducer _ = "no reducer statisfied the options"
