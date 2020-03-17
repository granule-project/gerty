{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Language.Dlam.Syntax.Internal
  (
  -- * Terms
    Term(..)
  , pattern App
  , pattern TypeTerm
  , pattern Lam
  , pattern PartialApp
  , pattern Level
  , TermThatCanBeApplied(..)
  , TermThatCannotBeApplied(..)
  , Appable(..)
  , TypeTermOfTermsThatCanBeApplied(..)
  , TypeTerm(..)
  , pattern Pi
  , Elim(..)
  , mkLam
  , PartiallyAppable(..)
  -- ** Type Constructors
  , TyCon
  , conTy
  , mkTyCon
  , PartiallyApplied
  , partiallyApplied
  , FullyApplied
  , fullyApplied
  -- ** Data Constructors
  , DCon
  , mkDCon
  , dconTy
  -- ** Arguments
  , Arg
  , argVar
  , mkArg
  , Applied(..)
  , Applicable(..)
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
  , TyAppable(..)
  , TypeOfTermsThatCanBeApplied
  , mkType'
  , toType
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
  -- * Helpers
  , mkTyVar
  -- * Naming
  , HasName(..)
  ) where


import Prelude hiding ((<>))

import Language.Dlam.Syntax.Abstract (Name(..))
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


type ConId = VarId


-- | Types of things that can be applied.
data TypeTermOfTermsThatCanBeApplied
  -- | Dependent function space.
  = IsPi Arg Type


-- | Terms that are only well-typed if they are types.
data TypeTerm
  -- | Applicable types.
  = TTForApp TypeTermOfTermsThatCanBeApplied
  -- | A type universe.
  | Universe Level
  -- | A type constructed from an application.
  | TyApp (FullyApplied TyAppable)


pattern Pi :: Arg -> Type -> TypeTerm
pattern Pi arg ty = TTForApp (IsPi arg ty)


data TyAppable
  -- | Free variable whose type ends in a universe.
  = AppTyVar VarId
  -- | Type constructor.
  | AppTyCon TyCon
  -- | Constant definition (axiom).
  | AppTyDef VarId


instance Eq TyAppable where
  -- free variables are equality compared on concrete names
  (AppTyVar v1) == (AppTyVar v2) = nameConcrete v1 == nameConcrete v2
  -- otherwise we require them to be the exact same name
  (AppTyCon t1) == (AppTyCon t2) = name t1 == name t2
  (AppTyDef d1) == (AppTyDef d2) = d1 == d2
  _ == _ = False


-- | A term that can be applied to another.
data TermThatCanBeApplied
  -- | A partial application.
  = IsPartialApp (PartiallyApplied PartiallyAppable)
  -- | A lambda abstraction.
  | IsLam Arg Term


-- | A term that cannot be applied to another.
data TermThatCannotBeApplied
  -- | A level.
  = IsLevel Level
  -- | A type.
  | IsTypeTerm Type
  -- | An application.
  | IsApp (FullyApplied Appable)


-- | Terms representing raw values.
data Term
  -- | Term that cannot be applied.
  = FullTerm TermThatCannotBeApplied
  -- | Term that can be applied.
  | PartialTerm TermThatCanBeApplied


pattern PartialApp :: PartiallyApplied PartiallyAppable -> Term
pattern PartialApp e = PartialTerm (IsPartialApp e)


pattern App :: FullyApplied Appable -> Term
pattern App app = FullTerm (IsApp app)


pattern TypeTerm :: Type -> Term
pattern TypeTerm ty = FullTerm (IsTypeTerm ty)


pattern Lam :: Arg -> Term -> Term
pattern Lam arg term = PartialTerm (IsLam arg term)


pattern Level :: Level -> Term
pattern Level l = FullTerm (IsLevel l)


-- | Things that when fully applied are terms (and not types).
data Appable
  -- | A free variable.
  = Var VarId
  -- | A data constructor.
  | ConData DCon
  -- | Constant (axiom).
  | AppDef VarId


instance Eq Appable where
  -- free variables are equality compared on concrete names
  (Var v1) == (Var v2) = nameConcrete v1 == nameConcrete v2
  -- otherwise we require them to be the exact same name
  (ConData c1) == (ConData c2) = name c1 == name c2
  (AppDef d1) == (AppDef d2) = d1 == d2
  _ == _ = False


-- | Things that can be partially applied.
data PartiallyAppable
  -- | Free variable.
  = VarPartial VarId
  -- | Type constructor.
  | TyConPartial TyCon
  -- | Data constructor.
  | DConPartial DCon
  -- | Constant (axiom).
  | DefPartial VarId


type ConArg = Arg

-- | Type constructor.
data TyCon = TyCon { conID :: ConId
                   , conArgs :: [ConArg]
                   , conTy :: Type
                   }


mkTyCon :: ConId -> [ConArg] -> Type -> TyCon
mkTyCon n args ty = TyCon { conID = n, conArgs = args, conTy = ty }


type DConId = VarId
type DConArg = Arg


-- | Data constructor.
data DCon = DCon { dconID :: DConId
                 , dconArgs :: [DConArg]
                 , dconTy :: FullyApplied TyCon
                 }


mkDCon :: DConId -> [DConArg] -> FullyApplied TyCon -> DCon
mkDCon n args tyC = DCon { dconID = n, dconArgs = args, dconTy = tyC }



data PartiallyApplied a = PartiallyApplied { partialArgs :: [Term], unPartiallyApplied :: a }


class Applicable a where
  args :: a -> [Arg]


instance Applicable TyCon where
  args = conArgs

instance Applicable DCon where
  args = dconArgs


class Applied a where
  appliedArgs :: a -> [Term]

instance Applied (PartiallyApplied c) where
  appliedArgs = partialArgs

instance Un PartiallyApplied where
  un = unPartiallyApplied

instance Applied (FullyApplied c) where
  appliedArgs = allArgs

instance Un FullyApplied where
  un = unFullyApplied

instance Functor FullyApplied where
  fmap f p = FullyApplied { unFullyApplied = f (un p), allArgs = allArgs p }

instance Functor PartiallyApplied where
  fmap f p = PartiallyApplied { unPartiallyApplied = f (un p), partialArgs = partialArgs p }


-- | Indicate that the thing is partially applied. ONLY FOR INTERNAL USE.
partiallyApplied :: a -> [Term] -> PartiallyApplied a
partiallyApplied c arg = PartiallyApplied { partialArgs = arg, unPartiallyApplied = c }


data FullyApplied c = FullyApplied { allArgs :: [Term], unFullyApplied :: c }


-- | Indicate that the thing is fully applied. ONLY FOR INTERNAL USE.
fullyApplied :: a -> [Term] -> FullyApplied a
fullyApplied c args = FullyApplied { allArgs = args, unFullyApplied = c }


data Elim
  -- | Applied to a term.
  = Apply Term


instance Pretty Term where
  isLexicallyAtomic (PartialTerm t) = isLexicallyAtomic t
  isLexicallyAtomic (FullTerm t)    = isLexicallyAtomic t

  pprint (FullTerm t)    = pprint t
  pprint (PartialTerm t) = pprint t


instance Pretty TermThatCannotBeApplied where
  isLexicallyAtomic (IsLevel l) = isLexicallyAtomic l
  isLexicallyAtomic (IsApp t) = length (appliedArgs t) == 0 && isLexicallyAtomic (un t)
  isLexicallyAtomic (IsTypeTerm t) = isLexicallyAtomic t

  pprint (IsLevel l) = pprint l
  pprint (IsTypeTerm t) = pprint t
  pprint (IsApp p) = pprintParened (un p) <+> hsep (fmap pprintParened (appliedArgs p))


instance Pretty TermThatCanBeApplied where
  isLexicallyAtomic (IsPartialApp t) = length (appliedArgs t) == 0 && isLexicallyAtomic (un t)
  isLexicallyAtomic _ = False

  pprint (IsLam arg body) = char '\\' <+> pprintParened arg <+> text "->" <+> pprint body
  pprint (IsPartialApp p) = pprintParened (un p) <+> hsep (fmap pprintParened (appliedArgs p))


instance Pretty Appable where
  isLexicallyAtomic (Var _) = True
  isLexicallyAtomic (ConData d) = isLexicallyAtomic d
  isLexicallyAtomic (AppDef d) = isLexicallyAtomic d

  pprint (Var v) = pprint v
  pprint (ConData d) = pprint d
  pprint (AppDef d) = pprint d


instance Pretty PartiallyAppable where
  isLexicallyAtomic (VarPartial v) = isLexicallyAtomic v
  isLexicallyAtomic (TyConPartial t) = isLexicallyAtomic t
  isLexicallyAtomic (DConPartial d) = isLexicallyAtomic d
  isLexicallyAtomic (DefPartial d) = isLexicallyAtomic d

  pprint (VarPartial v) = pprint v
  pprint (TyConPartial t) = pprint t
  pprint (DConPartial d) = pprint d
  pprint (DefPartial d) = pprint d


instance Pretty Elim where
  pprint (Apply x) = (if isLexicallyAtomic x then id else parens) $ pprint x


instance Pretty TypeTerm where
  isLexicallyAtomic (TyApp t) = length (appliedArgs t) == 0
  isLexicallyAtomic (TTForApp t) = isLexicallyAtomic t
  isLexicallyAtomic _ = False

  pprint (Universe l) = text "Type" <+> pprint l
  pprint (TTForApp t) = pprint t
  pprint (TyApp ty) = pprintParened (un ty) <+> hsep (fmap pprintParened (appliedArgs ty))


instance Pretty TypeTermOfTermsThatCanBeApplied where
  isLexicallyAtomic _ = False

  pprint (IsPi arg resT) = pprintParened arg <+> text "->" <+> pprint resT


instance Pretty TyAppable where
  isLexicallyAtomic (AppTyVar v) = isLexicallyAtomic v
  isLexicallyAtomic (AppTyCon t) = isLexicallyAtomic t
  isLexicallyAtomic (AppTyDef d) = isLexicallyAtomic d

  pprint (AppTyVar v) = pprint v
  pprint (AppTyCon t) = pprint t
  pprint (AppTyDef d) = pprint d


instance Pretty TyCon where
  isLexicallyAtomic _ = True
  pprint = pprint . name

instance Pretty DCon where
  isLexicallyAtomic _ = True
  pprint = pprint . name


instance Pretty (Graded (Typed Name)) where
  pprint x = pprint (un (un x)) <+> colon <+> pprint (grading x) <+> pprint (typeOf x)

instance Pretty Grading where
  pprint g = char '[' <>
             pprint (subjectGrade g) <> comma <+> pprint (subjectTypeGrade g) <> char ']'

instance Pretty Grade where
  pprint (GNat n) = integer n
  pprint GInf = text "INF"


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
  dec l@(Concrete n)
    | n > 0 = Concrete (pred n)
    | otherwise = error $ "dec on already-zero level (" ++ pprintShow l ++ ")"
  dec lev@(Plus n l)
    | n > 0 = Plus (pred n) l
    | otherwise = error $ "dec on already-zero level (" ++ pprintShow lev ++ ")"
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
  pprint (Plus 0 x) = pprint x
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
type TypeOfTermsThatCanBeApplied = Type' TypeTermOfTermsThatCanBeApplied


mkType :: TypeTerm -> Level -> Type
mkType t l = Type' (Leveled { leveledLevel = l, unLevel = t })


toType :: TypeOfTermsThatCanBeApplied -> Type
toType tt = mkType (TTForApp (un tt)) (level tt)


mkType' :: TypeTermOfTermsThatCanBeApplied -> Level -> TypeOfTermsThatCanBeApplied
mkType' t l = Type' (Leveled { leveledLevel = l, unLevel = t })


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


mkTyVar :: Name -> Level -> Type
mkTyVar n l = mkType (TyApp (fullyApplied (AppTyVar n) [])) l


class HasName a where
  name :: a -> Name


instance HasName Appable where
  name (Var x) = x
  name (ConData cd) = name cd
  name (AppDef cd) = cd


instance HasName TyAppable where
  name (AppTyVar x) = x
  name (AppTyDef d) = d
  name (AppTyCon cd) = name cd


instance HasName TyCon where
  name = conID


instance HasName DCon where
  name = dconID
