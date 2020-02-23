module Language.Dlam.Options
  ( Option(..)
  , isML
  , addOption
  ) where

import Control.Monad.Trans.Reader

------------------------------
-- Language options that `lcore` accepts in files

data Option = ML
  deriving (Eq, Show)

isML :: [Option] -> Bool
isML options = elem ML options

-- Builds up a the language option list and checks for conflicting options
addOption :: Option -> [Option] -> ReaderT String (Either String) [Option]
addOption opt opts = pure $ opt : opts