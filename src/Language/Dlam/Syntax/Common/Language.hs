{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-| You'll probably want to import this qualified, and re-export. |-}
module Language.Dlam.Syntax.Common.Language
  (
  -- * Typing
    Typed
  , unTyped
  , IsTyped(..)
  , typedWith

  -- * Grading
  , IsGraded(..)
  , Grading
  , Graded
  , subjectGrade
  , subjectTypeGrade
  , gradedWith
  , mkGrading
  ) where


import Language.Dlam.Util.Peekaboo
import Language.Dlam.Util.Pretty (Pretty(..), (<+>), colon)


----------
-- * Typed
----------


-- | A thing with a type.
data Typed t a = Typed { unTyped :: a, typedTy :: t }
  deriving (Show, Eq, Ord)


-- | Annotate the value with the given type.
typedWith :: e -> t -> Typed t e
typedWith = annotatedWith


instance Annotation (Typed t) t where
  annot = flip Typed


class IsTyped a t where
  typeOf :: a -> t


instance (IsTyped (t1 a) ty, IsTyped (t2 (t1 a)) ty) => IsTyped (ThenMightBe t1 t2 a) ty where
  typeOf = idrc typeOf typeOf


instance (IsTyped (m e) t, IsTyped e t) => IsTyped (MightBe m e) t where
  typeOf = idc typeOf typeOf


instance IsTyped (Typed t a) t where
  typeOf = typedTy


instance Un (Typed t) where
  un = unTyped


instance (Pretty t, Pretty a) => Pretty (Typed t a) where
  pprint e = pprint (un e) <+> colon <+> pprint (unTyped e)


------------------------------
----- Language Specifics -----
------------------------------


-- | Things that are graded need to explain their behaviour in both
-- | the subject and subject type.
data Grading g =
  Grading { gradingSubjectGrade :: g, gradingTypeGrade :: g }
  deriving (Show, Eq, Ord)


mkGrading :: g -> g -> Grading g
mkGrading sg tg = Grading { gradingSubjectGrade = sg, gradingTypeGrade = tg }


class IsGraded a g where
  grading :: a -> Grading g


subjectGrade :: (IsGraded a g) => a -> g
subjectGrade = gradingSubjectGrade . grading


subjectTypeGrade :: (IsGraded a g) => a -> g
subjectTypeGrade = gradingTypeGrade . grading


instance IsGraded (Grading g) g where
  grading = id


data Graded g a = Graded { gradedGrades :: (Grading g), unGraded :: a }
  deriving (Show, Eq, Ord)


instance Annotation (Graded g) (Grading g) where
  annot g u = Graded { gradedGrades = g, unGraded = u }


gradedWith :: a -> Grading g -> Graded g a
gradedWith = annotatedWith


instance Un (Graded g) where
  un = unGraded


instance IsGraded (Graded g a) g where
  grading = gradedGrades


instance (IsTyped a t) => IsTyped (Graded g a) t where
  typeOf = typeOf . un
