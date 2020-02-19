module Dlam.Options where

import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class (lift)

------------------------------
-- Language options that `lcore` accepts in files

data Option = CBV | CBN | Poly | ML
  deriving (Eq, Show)

-- Some helpers
isCBV :: [Option] -> Bool
isCBV options = elem CBV options

isCBN :: [Option] -> Bool
isCBN options = elem CBN options

isFullBeta :: [Option] -> Bool
isFullBeta options = not (isCBV options) && not (isCBN options)

isPoly :: [Option] -> Bool
isPoly options = elem Poly options

isML :: [Option] -> Bool
isML options = elem ML options

language :: [Option] -> String
language options = if isML options then "ML" else "lambda"

-- Builds up a the language option list and checks for conflicting options
addOption :: Option -> [Option] -> ReaderT String (Either String) [Option]
addOption opt opts =
  case opt of
    CBV | isCBN opts -> lift $ Left "Cannot choose both CBV and CBN."
    CBN | isCBV opts -> lift $ Left "Cannot choose both CBN and CBV."
    _ -> return $ opt : opts

showReducer :: [Option] -> String
showReducer opts | isCBV opts      = "Call-By-Value"
showReducer opts | isCBN opts      = "Call-By-Name"
showReducer opts | isFullBeta opts = "Determinised full beta"
showReducer _ = "no reducer statisfied the options"
