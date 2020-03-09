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

  -- * Hiding
  , IsHiddenOrNot(..)
  , CanHide(..)
  , MightHide
  , Hiding
  , isHidden
  , hide
  , notHidden
  , unHide
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


-----------
-- * Hiding
-----------


data IsHiddenOrNot = IsHidden | NotHidden
  deriving (Show, Eq, Ord)


newtype MightHide a = MightHide (IsHiddenOrNot, a)
  deriving (Show, Eq, Ord)


unHide :: MightHide a -> a
unHide (MightHide (_, x)) = x


instance Un (MightHide a) a where
  un = unHide


instance (IsTyped a t) => IsTyped (MightHide a) t where
  typeOf = typeOf . un


-- | 'CanHide a e' means that 'a' contains possibly hidden values
-- | of type 'e'.
class (Hiding (a e)) => CanHide a e where
  makeWithHiding :: IsHiddenOrNot -> e -> a e


-- | Hide a value.
hide :: (CanHide a e) => e -> a e
hide = makeWithHiding IsHidden


-- | A value that isn't hidden.
notHidden :: (CanHide a e) => e -> a e
notHidden = makeWithHiding NotHidden


class Hiding a where
  -- | Is the value hidden or not?
  isHidden :: a -> IsHiddenOrNot


instance Hiding (MightHide a) where
  isHidden (MightHide (h, _)) = h


instance CanHide MightHide a where
  makeWithHiding = curry MightHide
