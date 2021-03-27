{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-| You'll probably want to import this qualified, and re-export. |-}
module Language.Gerty.Syntax.Common.Language
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

  -- * Binding
  , Binds(..)
  , BoundName
  , bindName
  , unBoundName
  , OneOrMoreBoundNames
  ) where


import qualified Data.List.NonEmpty as NE

import Language.Gerty.Util.Peekaboo
import Language.Gerty.Util.Pretty (Pretty(..), (<+>), colon, hsep)


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


instance (IsGraded a g) => IsGraded (Typed t a) g where
  grading = grading . un


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


------------
-- * Binding
------------


-- | A name in a binder.
data BoundName n = BoundName { unBoundName :: n }
  deriving (Show, Eq, Ord)


bindName :: n -> BoundName n
bindName = BoundName


type OneOrMoreBoundNames n = NE.NonEmpty (BoundName n)


instance (Pretty n) => Pretty (BoundName n) where
  isLexicallyAtomic = isLexicallyAtomic . unBoundName

  pprint = pprint . unBoundName


instance (Pretty n) => Pretty [BoundName n] where
  isLexicallyAtomic = (<=1) . length
  pprint = hsep . fmap pprint


instance (Pretty n) => Pretty (OneOrMoreBoundNames n) where
  isLexicallyAtomic = (==1) . NE.length
  pprint = pprint . NE.toList


class Binds a n where
  bindsWhat :: a -> [BoundName n]


instance (Binds a n) => Binds (Graded g a) n where
  bindsWhat = bindsWhat . un


instance (Binds a n) => Binds (Typed t a) n where
  bindsWhat = bindsWhat . un


instance Binds (BoundName n) n where
  bindsWhat = pure


instance Binds [BoundName n] n where
  bindsWhat = id


instance Binds (OneOrMoreBoundNames n) n where
  bindsWhat = bindsWhat . NE.toList


instance (Binds (t e) n, Binds e n) => Binds (MightBe t e) n where
  bindsWhat = idc bindsWhat bindsWhat


instance (Binds (t2 (t1 e)) n, Binds (t1 e) n) => Binds (ThenMightBe t1 t2 e) n where
  bindsWhat = idrc bindsWhat bindsWhat
