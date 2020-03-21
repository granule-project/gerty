{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
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
  , tryMight

  -- * Wrappers
  , Un(..)
  , Tag(..)
  , untag
  , Annotation(..)
  , annotatedWith
  ) where


import Unbound.LocallyNameless

import Language.Dlam.Util.Pretty (Pretty(..))


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
  isLexicallyAtomic = idc isLexicallyAtomic isLexicallyAtomic
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


-- | Have a go.
tryMight :: (ThenCouldBe t t1 t2 a) => (t2 (t1 a) -> b) -> t t1 t2 a -> Maybe b
tryMight f = idrc (const Nothing) (Just . f)


instance ThenCouldBe ThenMightBe t1 t2 a where
  onlyFirst f = TMB . itIsNot . f
  wasBoth f g x = TMB (itIs g (f x))
  idrc f g (TMB x) = idc g f x


deriving instance (Show (t1 a), Show (t2 (t1 a))) => Show (ThenMightBe t1 t2 a)
deriving instance (Eq (t1 a), Eq (t2 (t1 a))) => Eq (ThenMightBe t1 t2 a)
deriving instance (Ord (t1 a), Ord (t2 (t1 a))) => Ord (ThenMightBe t1 t2 a)


instance (Pretty (t2 (t1 e)), Pretty (t1 e)) => Pretty (ThenMightBe t1 t2 e) where
  isLexicallyAtomic = idrc isLexicallyAtomic isLexicallyAtomic
  pprint = idrc pprint pprint


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


-----------------------
----- For Unbound -----
-----------------------


rMightBe :: forall a e. (Rep (a e), Rep e) => R (MightBe a e)
rMightBe =
  Data (DT "MightBe" ((rep :: R (a e)) :+: (rep :: R e) :+: MNil))
    [ Con rItIsEmb    ((rep :: R (a e)) :+: MNil)
    , Con rItIsNotEmb ((rep :: R e)     :+: MNil)]


rMightBe1 :: forall a e ctx. (Rep (a e), Rep e) => ctx (a e) -> ctx e -> R1 ctx (MightBe a e)
rMightBe1 ctxae ctxe =
  Data1 (DT "MightBe" ((rep :: R (a e)) :+: (rep :: R e) :+: MNil))
    [ Con rItIsEmb    (ctxae :+: MNil)
    , Con rItIsNotEmb (ctxe  :+: MNil) ]


rItIsEmb :: Emb (a e :*: Nil) (MightBe a e)
rItIsEmb =
   Emb {
            to   = (\ (v :*: Nil) -> (ItIs v)),
            from  = \x -> case x of
                    ItIs v    -> Just (v :*: Nil)
                    ItIsNot{} -> Nothing,
            labels = Nothing,
            name = "ItIs",
            fixity = Nonfix
          }


rItIsNotEmb :: Emb (e :*: Nil) (MightBe a e)
rItIsNotEmb =
   Emb {
            to   = (\ (v :*: Nil) -> (ItIsNot v)),
            from  = \x -> case x of
                    ItIsNot v -> Just (v :*: Nil)
                    ItIs{}    -> Nothing,
            labels = Nothing,
            name = "ItIsNot",
            fixity = Nonfix
          }


instance (Rep (a e), Rep e) => Rep (MightBe a e) where
  rep = rMightBe


instance (Rep (a e), Rep e, Sat (ctx (a e)), Sat (ctx e)) => Rep1 ctx (MightBe a e) where
  rep1 = rMightBe1 dict dict


instance (Alpha (a e), Alpha e) => Alpha (MightBe a e)
