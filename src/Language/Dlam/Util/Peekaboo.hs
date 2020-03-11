{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
module Language.Dlam.Util.Peekaboo
  (
  -- * CouldBe
    CouldBe(..)
  , MightBe
  , isIt
  , tryIt

  -- * ThenCouldBe
  , ThenCouldBe(..)
  , ThenMightBe

  -- * Wrappers
  , Un(..)
  , Tag(..)
  , untag
  , Annotation(..)
  , annotatedWith
  ) where


import Language.Dlam.Util.Pretty (Pretty(pprint))


------------
-- * CouldBe
------------


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


instance (Un t) => Un (MightBe t) where
  un (ItIs x) = un x
  un (ItIsNot x) = x


instance (Pretty (t e), Pretty e) => Pretty (MightBe t e) where
  pprint = idc pprint pprint


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


-------------
-- * Wrappers
-------------


-- | Things that can be unwrapped.
class Un a where
  un :: a e -> e


-- | Types that tag other types.
class (Un a) => Tag a where
  tag :: e -> a e


-- | The thing that was tagged.
untag :: (Tag a) => a e -> e
untag = un


-- | Types that annotate other types with more data.
class Annotation t ann where
  annot :: ann -> e -> t e


-- | Annotate a value.
annotatedWith :: (Annotation t a) => e -> a -> t e
annotatedWith = flip annot
