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

  -- * Grades
  , Grade(..)

  -- * Binding
  , Binds(..)
  , BoundName
  , bindName
  , unBoundName
  , OneOrMoreBoundNames
  ) where


import qualified Data.List.NonEmpty as NE

import Language.Dlam.Util.Peekaboo
import Language.Dlam.Util.Pretty (Pretty(..), (<+>), char, colon, hsep, integer, text)


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


-----------
-- * Grades
-----------


-- | We provide an algebra for grades (pre-ordered semiring).
-- |
-- | Anything that is a member of a pre-ordered semiring should be
-- | able to compile to this.
data Grade r
  -- | 0.
  = GZero
  -- | 1.
  | GOne
  -- | s + r.
  | GPlus (Grade r) (Grade r)
  -- | s * r
  | GTimes (Grade r) (Grade r)
  -- | Least-upper bound.
  | GLub (Grade r) (Grade r)
  -- | Special grade when unspecified.
  | GImplicit
  deriving (Show, Eq, Ord)


instance Pretty (Grade r) where
  pprint GZero = text ".0"
  pprint GOne  = text ".1"
  pprint (GPlus g1 g2) = pprintSquishy 0 (g1, g2)
    where pprintSquishy n (GZero, GZero) = char '.' <> integer n
          pprintSquishy n (GOne,  r) = pprintSquishy (n+1) (GZero, r)
          pprintSquishy n (s, GOne) = pprintSquishy (n+1) (s, GZero)
          pprintSquishy n (GPlus GOne s, r) = pprintSquishy (n+1) (s, r)
          pprintSquishy n (GPlus s GOne, r) = pprintSquishy (n+1) (s, r)
          pprintSquishy n (s, GPlus GOne r) = pprintSquishy (n+1) (s, r)
          pprintSquishy n (s, GPlus r GOne) = pprintSquishy (n+1) (s, r)
          pprintSquishy n (GZero, r) = (char '.' <> integer n) <+> char '+' <+> pprint r
          pprintSquishy n (s, GZero) = (char '.' <> integer n) <+> char '+' <+> pprint s
          pprintSquishy n (s, r) = (char '.' <> integer n) <+> char '+' <+> pprint s <+> char '+' <+> pprint r
  pprint (GTimes g1 g2) = pprint g1 <+> text "*" <+> pprint g2
  pprint (GLub g1 g2) = pprint g1 <+> text "lub" <+> pprint g2
  pprint GImplicit = text "._"


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
