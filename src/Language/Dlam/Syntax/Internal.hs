{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Language.Dlam.Syntax.Internal
  (
  -- * Terms
    Term(..)
  , Appable(..)
  , TypeTerm(..)
  , TyAppable(..)
  , Elim(..)
  , mkLam
  -- ** Arguments
  , Arg
  , argVar
  , mkArg
  -- * Levels
  , Level(..)
  , LevelAtom(..)
  , nextLevel
  , prevLevel
  , HasLevel(..)
  -- * Types
  , Type
  , unType
  , mkType
  , typeOf
  , typedWith
  -- * Grades
  , Grade
  , Grading
  , Graded
  , mkGrading
  , grading
  , gradedWith
  , subjectGrade
  , subjectTypeGrade
  , mkNatGrade
  , thatMagicalGrade
  , thatMagicalGrading
  , decrementGrade
  ) where


import Prelude hiding ((<>))

import Language.Dlam.Syntax.Abstract (Name)
-- import qualified Language.Dlam.Syntax.Common as Com
import qualified Language.Dlam.Syntax.Common.Language as Com
import Language.Dlam.Util.Peekaboo
import Language.Dlam.Util.Pretty


------------------------------
----- Language Specifics -----
------------------------------


-- | As we have dependent types, we should be able to treat grades
-- | as arbitrary expressions.
-- type BoundName = Com.BoundName Name
-- type Type = Expr
type Typed = Com.Typed Type
typedWith :: a -> Type -> Typed a
typedWith = Com.typedWith
typeOf :: (Com.IsTyped a Type) => a -> Type
typeOf = Com.typeOf
-- bindName :: Name -> BoundName
-- bindName = Com.bindName
-- unBoundName :: BoundName -> Name
-- unBoundName = Com.unBoundName



type VarId = Name


-----------------
----- Terms -----
-----------------


type Arg = Graded (Typed Name)


mkArg :: Name -> Grading -> Type -> Arg
mkArg n g t = n `typedWith` t `gradedWith` g


argVar :: Arg -> Name
argVar = un . un


-- | Terms that are only well-typed if they are types.
data TypeTerm
  -- | Dependent function space.
  = Pi Arg Type
  -- | A type universe.
  | Universe Level
  -- | An application resulting in a type.
  | TyApp TyAppable [Term]


data TyAppable
  -- | A type variable.
  = TyVar VarId


-- | Terms representing raw values.
data Term
  -- | A level.
  = Level Level
  -- | A type.
  | TypeTerm Type
  -- | An application.
  | App Appable [Term]
  -- | A lambda abstraction.
  | Lam Arg Term


data Appable
  -- | A free variable.
  = Var VarId


data Elim
  -- | Applied to a term.
  = Apply Term


instance Pretty Term where
  isLexicallyAtomic (Level l) = isLexicallyAtomic l
  isLexicallyAtomic (App t []) = isLexicallyAtomic t
  isLexicallyAtomic _ = False

  pprint (Level l) = pprint l
  pprint (TypeTerm t) = pprint t
  pprint (App t1 args) = pprintParened t1 <+> hsep (fmap pprintParened args)
  pprint (Lam arg body) = char '\\' <+> pprintParened arg <+> text "->" <+> pprint body


instance Pretty Appable where
  isLexicallyAtomic (Var _) = True

  pprint (Var v) = pprint v


instance Pretty Elim where
  pprint (Apply x) = (if isLexicallyAtomic x then id else parens) $ pprint x


instance Pretty TypeTerm where
  isLexicallyAtomic (TyApp t []) = isLexicallyAtomic t
  isLexicallyAtomic _ = False

  pprint (Universe l) = text "Type" <+> pprint l
  pprint (Pi arg resT) = pprintParened arg <+> text "->" <+> pprint resT
  pprint (TyApp t1 args) = pprintParened t1 <+> hsep (fmap pprintParened args)


instance Pretty (Graded (Typed Name)) where
  pprint x = pprint (un (un x)) <+> colon <+> pprint (grading x) <+> pprint (typeOf x)

instance Pretty Grading where
  pprint g = char '[' <>
             pprint (subjectGrade g) <> comma <+> pprint (subjectTypeGrade g) <> char ']'

instance Pretty Grade where
  pprint (GNat n) = integer n
  pprint GInf = text "INF"

instance Pretty TyAppable where
  isLexicallyAtomic (TyVar _) = True

  pprint (TyVar v) = pprint v


------------------
----- Levels -----
------------------


type Nat = Integer


data Level
  = Concrete Nat
  | Plus Nat LevelAtom
  | Max Level Level


-- | Atomic terms that are levels.
data LevelAtom
  = LTerm Term


class Inc a where
  inc :: a -> a


instance Inc Level where
  inc (Concrete n) = Concrete (succ n)
  inc (Plus n l) = Plus (succ n) l
  inc (Max x y) = Max (inc x) (inc y)


class Dec a where
  dec :: a -> a


instance Dec Level where
  dec (Concrete n)
    | n > 0 = Concrete (pred n)
    | otherwise = error "dec on already-zero level"
  dec (Plus n l)
    | n > 0 = Plus (pred n) l
    | otherwise = error "dec on already-zero level"
  dec (Max x y) = Max (dec x) (dec y)


-- | The next highest level.
nextLevel :: Level -> Level
nextLevel = inc


-- | The next lowest level (can fail).
prevLevel :: Level -> Level
prevLevel = dec


-- | Something with a level.
data Leveled a = Leveled { unLevel :: a, leveledLevel :: Level }


class HasLevel a where
  level :: a -> Level

instance HasLevel (Leveled a) where
  level = leveledLevel

instance Un Leveled where
  un = unLevel


instance Pretty Level where
  isLexicallyAtomic Concrete{} = True
  isLexicallyAtomic _ = False

  pprint (Concrete n) = integer n
  pprint (Plus n x) = integer n <+> char '+' <+> pprintParened x
  pprint (Max n m) = text "lmax" <+> pprintParened n <+> pprintParened m


instance Pretty LevelAtom where
  isLexicallyAtomic (LTerm t) = isLexicallyAtomic t
  pprint (LTerm t) = pprint t


-----------------
----- Types -----
-----------------


newtype Type' a = Type' { unType :: Leveled a }
  deriving (HasLevel, Un)

type Type = Type' TypeTerm


mkType :: TypeTerm -> Level -> Type
mkType t l = Type' (Leveled { leveledLevel = l, unLevel = t })


instance (Pretty a) => Pretty (Type' a) where
  pprint = pprint . un . unType


------------------
----- Grades -----
------------------


-- | For now we just support an exact-usage semiring.
data Grade = GNat Nat | GInf
type Grading = Com.Grading Grade
type Graded = Com.Graded Grade
mkGrading :: Grade -> Grade -> Grading
mkGrading = Com.mkGrading
grading :: (Com.IsGraded a Grade) => a -> Grading
grading = Com.grading
subjectGrade, subjectTypeGrade :: (Com.IsGraded a Grade) => a -> Grade
subjectGrade = Com.subjectGrade
subjectTypeGrade = Com.subjectTypeGrade
gradedWith :: a -> Grading -> Graded a
gradedWith = Com.gradedWith


-- | Make a grade from a natural number.
mkNatGrade :: Nat -> Grade
mkNatGrade = GNat


-- | Grade currently used as a stand-in for situations where
-- | a grade is not known.
thatMagicalGrade :: Grade
thatMagicalGrade = GInf

thatMagicalGrading :: Grading
thatMagicalGrading = mkGrading thatMagicalGrade thatMagicalGrade


decrementGrade :: Grade -> (Maybe Grade)
decrementGrade e =
  case e of
    GInf -> Just GInf
    GNat n | n > 0 -> Just . GNat $ pred n
           | otherwise -> Nothing


-------------------
----- Helpers -----
-------------------


mkLam :: Name -> Type -> Term -> Term
mkLam n ty body = Lam (n `typedWith` ty `gradedWith` thatMagicalGrading) body
