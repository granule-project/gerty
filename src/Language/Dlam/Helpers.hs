module Language.Dlam.Helpers
  ( todo
  ) where

-- A helper for showing which bits are not done yet
todo :: String -> a
todo msg = error $ "TODO: Implement `" ++ msg ++ "`"
