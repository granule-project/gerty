{-# LANGUAGE EmptyDataDeriving #-}
module Language.Dlam.Options
  ( Option
  , addOption
  ) where

import Control.Monad.Trans.Reader

------------------------------
-- Language options that `dlam` accepts in files

data Option
  deriving (Eq, Show)


-- Builds up a the language option list and checks for conflicting options
addOption :: Option -> [Option] -> ReaderT String (Either String) [Option]
addOption opt opts = pure $ opt : opts
