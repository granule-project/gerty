{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-| Common syntax declarations. -}
module Language.Dlam.Syntax.Common
  (
  -- * NameId
    NameId(..)

  -- * Un
  , Un(..)

  -- * Typing
  , Typed
  , unTyped
  , IsTyped(..)
  , typeWith

  -- * Implicity
  , HasImplicity(..)
  , Implicity(..)
  ) where


import Data.Int (Int64)


import Language.Dlam.Util.Pretty (Pretty(..), (<+>), colon)


-----------
-- * NameId
-----------


-- I think Int64 is more efficient than using an Integer here (see
-- https://stackoverflow.com/questions/8873000/integer-vs-int64-vs-word64).
-- Agda uses !Word64, but I'm not sure what the advantage of that over
-- Int64 would be. (2020-03-05, GD)
newtype NameId = NameId Int64
  deriving (Show, Eq, Ord, Num, Enum)


-------
-- * Un
-------


class Un a e | a -> e where
  un :: a -> e


----------
-- * Typed
----------


-- | A thing with a type.
data Typed t a = Typed { unTyped :: a, typedTy :: t }
  deriving (Show, Eq, Ord)


-- | Annotate the value with the given type.
typeWith :: e -> t -> Typed t e
typeWith = Typed


class IsTyped a t where
  typeOf :: a -> t


instance IsTyped (Typed t a) t where
  typeOf = typedTy


instance Un (Typed t a) a where
  un = unTyped


instance (Pretty t, Pretty a) => Pretty (Typed t a) where
  pprint e = pprint (un e) <+> colon <+> pprint (unTyped e)


--------------
-- * Implicity
--------------


data Implicity = IsImplicit | IsExplicit
  deriving (Show, Eq, Ord)


class HasImplicity a where
  relOf :: a -> Implicity


instance (HasImplicity a) => HasImplicity (Typed t a) where
  relOf = relOf . unTyped
