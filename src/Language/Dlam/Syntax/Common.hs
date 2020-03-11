{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-| Common syntax declarations. -}
module Language.Dlam.Syntax.Common
  (
  -- * NameId
    NameId(..)

  , module Language.Dlam.Util.Peekaboo

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

import Language.Dlam.Syntax.Common.Language
import Language.Dlam.Util.Peekaboo
import Language.Dlam.Util.Pretty (Pretty(..), braces, parens)


-----------
-- * NameId
-----------


-- I think Int64 is more efficient than using an Integer here (see
-- https://stackoverflow.com/questions/8873000/integer-vs-int64-vs-word64).
-- Agda uses !Word64, but I'm not sure what the advantage of that over
-- Int64 would be. (2020-03-05, GD)
newtype NameId = NameId Int64
  deriving (Show, Eq, Ord, Num, Enum)


-----------
-- * Hiding
-----------


data IsHiddenOrNot = IsHidden | NotHidden
  deriving (Show, Eq, Ord)


newtype Hidden e = Hidden e
  deriving (Show, Eq, Ord)


unHide :: Hidden a -> a
unHide (Hidden a) = a


instance Un Hidden where
  un = unHide


type MightHide = MightBe Hidden


instance (IsTyped a t) => IsTyped (MightHide a) t where
  typeOf = typeOf . un


instance (Binds a n) => Binds (MightHide a) n where
  bindsWhat = bindsWhat . un


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


instance Un Arg where
  un = un . unArg


mkArg :: IsHiddenOrNot -> a -> Arg a
mkArg = makeWithHiding


instance (Pretty e) => Pretty (Arg e) where
  pprint h =
    let e = un h
    in case isHidden h of
         IsHidden -> braces (pprint e)
         NotHidden -> (if isLexicallyAtomic e then id else parens) $ pprint e


instance (Binds a n) => Binds (Arg a) n where
  bindsWhat = bindsWhat . un
