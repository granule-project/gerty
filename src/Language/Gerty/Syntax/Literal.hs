{-# LANGUAGE DeriveDataTypeable #-}

module Language.Gerty.Syntax.Literal
  ( Literal(..)
  ) where

import Data.Data (Data)

import Language.Gerty.Syntax.Position
import Language.Gerty.Util.Pretty

data Literal = LitNat    Range !Integer
  deriving Data

instance Show Literal where
  showsPrec p l = showParen (p > 9) $ case l of
    LitNat _ n    -> sh "LitNat _" n
    where
      sh :: Show a => String -> a -> ShowS
      sh c x = showString (c ++ " ") . shows x

instance Pretty Literal where
    pprint (LitNat _ n)     = text $ show n

instance Eq Literal where
  LitNat _ n    == LitNat _ m    = n == m

instance Ord Literal where
  LitNat _ n    `compare` LitNat _ m    = n `compare` m

instance HasRange Literal where
  getRange (LitNat    r _) = r

instance SetRange Literal where
  setRange r (LitNat    _ x) = LitNat    r x

instance KillRange Literal where
  killRange (LitNat    r x) = LitNat    (killRange r) x
