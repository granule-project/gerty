{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-| Common syntax declarations. -}
module Language.Dlam.Syntax.Common
  (
  -- * NameId
    NameId(..)

  -- * MightBe
  , CouldBe(..)
  , MightBe
  , isIt
  , tryIt

  -- * ThenCouldBe
  , ThenCouldBe(..)
  , ThenMightBe

  -- * Un
  , Un(..)

  -- * Typing
  , Typed
  , unTyped
  , IsTyped(..)
  , typedWith

  -- * Hiding
  , IsHiddenOrNot(..)
  , CanHide(..)
  , MightHide
  , Hiding
  , isHidden
  , isHidden'
  , hide
  , notHidden
  , unHide

  -- * Arguments
  , Arg
  , mkArg
  ) where


import Data.Int (Int64)


import Language.Dlam.Util.Pretty (Pretty(..), (<+>), braces, colon, parens)


-----------
-- * NameId
-----------


-- I think Int64 is more efficient than using an Integer here (see
-- https://stackoverflow.com/questions/8873000/integer-vs-int64-vs-word64).
-- Agda uses !Word64, but I'm not sure what the advantage of that over
-- Int64 would be. (2020-03-05, GD)
newtype NameId = NameId Int64
  deriving (Show, Eq, Ord, Num, Enum)


data MightBe a e = ItIs (a e) | ItIsNot e
  deriving (Show, Eq, Ord)


class CouldBe t a e where
  -- | It most certainly is!
  itIs :: (forall b. b -> a b) -> e -> t a e

  -- | It most certainly is not!
  itIsNot :: e -> t a e

  -- | Deal with it.
  idc :: (a e -> b) -> (e -> b) -> t a e -> b


-- | Was it?
isIt :: (CouldBe t a e) => t a e -> Bool
isIt = idc (const True) (const False)


-- | Have a go.
tryIt :: (CouldBe t a e) => (a e -> b) -> t a e -> Maybe b
tryIt f = idc (Just . f) (const Nothing)


instance CouldBe MightBe a e where
  itIs f = ItIs . f

  itIsNot = ItIsNot

  idc f _ (ItIs x) = f x
  idc _ g (ItIsNot x) = g x


instance (Un (t e) e) => Un (MightBe t e) e where
  un (ItIs x) = un x
  un (ItIsNot x) = x


instance (Pretty (t e), Pretty e) => Pretty (MightBe t e) where
  pprint = idc pprint pprint


instance (IsTyped (m e) t, IsTyped e t) => IsTyped (MightBe m e) t where
  typeOf = idc typeOf typeOf


----------------
-- * ThenCouldBe
----------------


-- | @A `ThenMightBe` B@ could be @A@, or both @A@ and @B@.
newtype ThenMightBe t1 t2 a = TMB { unTMB :: (MightBe t2 (t1 a)) }


class ThenCouldBe t t1 t2 a where
  onlyFirst :: (a -> t1 a) -> a -> t t1 t2 a
  wasBoth   :: (forall b. b -> t1 b) -> (forall b. b -> t2 b) -> a -> t t1 t2 a

  idrc :: (t1 a -> b) -> (t2 (t1 a) -> b) -> t t1 t2 a -> b


instance ThenCouldBe ThenMightBe t1 t2 a where
  onlyFirst f = TMB . itIsNot . f
  wasBoth f g x = TMB (itIs g (f x))
  idrc f g (TMB x) = idc g f x


deriving instance (Show (t1 a), Show (t2 (t1 a))) => Show (ThenMightBe t1 t2 a)
deriving instance (Eq (t1 a), Eq (t2 (t1 a))) => Eq (ThenMightBe t1 t2 a)
deriving instance (Ord (t1 a), Ord (t2 (t1 a))) => Ord (ThenMightBe t1 t2 a)
deriving instance (Pretty (t2 (t1 e)), Pretty (t1 e)) => Pretty (ThenMightBe t1 t2 e)

instance (IsTyped (t1 a) ty, IsTyped (t2 (t1 a)) ty) => IsTyped (ThenMightBe t1 t2 a) ty where
  typeOf = idrc typeOf typeOf


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
typedWith :: e -> t -> Typed t e
typedWith = Typed


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


newtype Hidden e = Hidden e
  deriving (Show, Eq, Ord)


unHide :: Hidden a -> a
unHide (Hidden a) = a


instance Un (Hidden a) a where
  un = unHide


type MightHide = MightBe Hidden


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


isHidden' :: (Hiding a) => a -> Bool
isHidden' x = case isHidden x of IsHidden -> True; NotHidden -> False


instance Hiding (MightHide a) where
  isHidden h = if isIt h then IsHidden else NotHidden


instance CanHide MightHide a where
  makeWithHiding IsHidden = itIs Hidden
  makeWithHiding NotHidden = itIsNot


--------------
-- * Arguments
--------------


-- | Arguments can be hidden.
newtype Arg a = Arg { unArg :: MightHide a }
  deriving (Show, Eq, Ord)


instance Hiding (Arg e) where
  isHidden (Arg e) = isHidden e


instance CanHide Arg a where
  makeWithHiding h = Arg . makeWithHiding h


instance (IsTyped a t) => IsTyped (Arg a) t where
  typeOf = typeOf . un


instance Un (Arg a) a where
  un = un . unArg


mkArg :: IsHiddenOrNot -> a -> Arg a
mkArg = makeWithHiding


instance (Pretty e) => Pretty (Arg e) where
  pprint h =
    let e = un h
    in case isHidden h of
         IsHidden -> braces (pprint e)
         NotHidden -> (if isLexicallyAtomic e then id else parens) $ pprint e
