{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
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
  , Applied(..)
  , Applicable(..)

  -- *** FreeVar
  , FreeVar
  , mkFreeVar
  , freeVarName

  -- **** Var Sorts
  , VSort(..)
  , ISSort(..)
  , toVSort
  , standsFor
  , SortedName(..)
  , fvToSortedName

  -- * Levels
  , Level(..)
  , nextLevel
  , prevLevel
  , HasLevel(..)
  , LevelTerm(..)
  , LVarId
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
  , TyVarId
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
  , HasName(..)

  -- ** Constructing terms, types, etc.
  , levelZero
  , mkFunTy
  , mkFunTy'
  , mkFunTyNoBind
  , mkFunTyNoBind'
  , mkLam
  , mkLam'
  , mkLevelVar
  , mkPi
  , mkPi'
  , mkTermDef
  , mkTLevel
  , mkTyDef
  , mkTyVar
  , mkTypeVar
  , mkVar
  , nameForTerm
  , nameForType
  , termVarToTyVar
  , tyVarToTermVar

  -- *** Arguments
  , mkArg
  , mkArgAN
  , mkArg'
  , mkArgNoBind

  -- *** Names
  , aname2Name
  , nameFromString

  -- * Unbound
  , module Unbound.LocallyNameless
  ) where


import Prelude hiding ((<>))

import Language.Dlam.Syntax.Abstract (AName(..))
import qualified Language.Dlam.Syntax.Common.Language as Com
import Language.Dlam.Syntax.Common.Language (typedWith, gradedWith)
import Language.Dlam.Syntax.Common.Language (Graded, IsTyped)
import Language.Dlam.Syntax.Concrete.Name (CName(..))
import Language.Dlam.Syntax.Common (NameId(..))
import Language.Dlam.Util.Peekaboo
import Language.Dlam.Util.Pretty
import Unbound.LocallyNameless
import Unbound.LocallyNameless.Ops (unsafeUnbind) -- for pretty-printing


------------------------------
----- Language Specifics -----
------------------------------


typeOf :: (Com.HasType a Type) => a -> Type
typeOf = Com.typeOf


type VarId = Name Term


-----------------
----- Terms -----
-----------------


data FreeVar where
  FreeVar :: (ISSort t, Name t) -> FreeVar


freeVarName :: FreeVar -> AnyName
freeVarName (FreeVar (VISTerm, n)) = AnyName n
freeVarName (FreeVar (VISLevel, n)) = AnyName n
freeVarName (FreeVar (VISType{}, n)) = AnyName n


instance Eq FreeVar where
  (FreeVar (VISTerm, n1)) == (FreeVar (VISTerm, n2)) = n1 == n2
  (FreeVar (VISType{}, n1)) == (FreeVar (VISType{}, n2)) = n1 == n2
  (FreeVar (VISLevel, n1)) == (FreeVar (VISLevel, n2)) = n1 == n2
  _ == _ = False


instance Ord FreeVar where
  (FreeVar (VISTerm, n1)) `compare` (FreeVar (VISTerm, n2)) = compare n1 n2
  (FreeVar (VISType{}, n1)) `compare` (FreeVar (VISType{}, n2)) = compare n1 n2
  (FreeVar (VISLevel, n1)) `compare` (FreeVar (VISLevel, n2)) = compare n1 n2
  _ `compare` _ = error "tried to compare free vars of different sorts"


data SortedName where
  SortedName :: (ISSort t, Name t) -> SortedName


fvToSortedName :: FreeVar -> SortedName
fvToSortedName (FreeVar (s, n)) = SortedName (s, n)


mkFreeVar :: ISSort s -> Name s -> FreeVar
mkFreeVar s n = FreeVar (s, n)


data ISSort a where
  VISLevel :: ISSort Level
  VISType :: Level -> ISSort Type
  VISTerm :: ISSort Term


toVSort :: ISSort t -> VSort
toVSort VISLevel = VLevel
toVSort (VISType l) = VType l
toVSort VISTerm = VTerm


data VSort = VTerm | VLevel | VType Level


instance Pretty VSort where
  isLexicallyAtomic _ = True
  pprint VTerm = text "Term"
  pprint VLevel = text "Level"
  pprint VType{} = text "Type"


instance Eq VSort where
  VTerm == VTerm = True
  VLevel == VLevel = True
  -- ignoring Universes for now (2020-03-23, GD)
  VType{} == VType{} = True
  _ == _ = False


-- | The sort the variable belongs to.
standsFor :: FreeVar -> VSort
standsFor (FreeVar (s, _)) = toVSort s


newtype Arg = Arg { unArg :: Graded (Embed Grade) (IsTyped (Embed Type) FreeVar) }


instance Com.IsGraded Arg Grade where
  grading = Com.mapGrading (\(Embed e) -> e) . Com.grading . unArg
instance Com.HasType Arg Type where
  typeOf = (\(Embed e) -> e) . Com.typeOf . unArg


mkArg :: (ISSort a, Name a) -> Grading -> Type -> Arg
mkArg n g t = Arg $ (uncurry mkFreeVar n) `typedWith` (Embed t) `gradedWith` (Com.mapGrading Embed g)


mkArgAN :: FreeVar -> Grading -> Type -> Arg
mkArgAN n g t = Arg $ n `typedWith` (Embed t) `gradedWith` (Com.mapGrading Embed g)


argVar :: Arg -> FreeVar
argVar = un . un . unArg


type ConId = AName
type TyVarId = Name Type
type DefId = AName


-- | Types of things that can be applied.
data TypeTermOfTermsThatCanBeApplied
  -- | Dependent function space.
  = IsPi (Bind Arg Type)


-- | Terms that are only well-typed if they are types.
data TypeTerm
  -- | Applicable types.
  = TTForApp TypeTermOfTermsThatCanBeApplied
  -- | A type universe.
  | Universe Level
  -- | A type constructed from an application.
  | TyApp (FullyApplied TyAppable)


pattern Pi :: Bind Arg Type -> TypeTerm
pattern Pi pi = TTForApp (IsPi pi)


data TyAppable
  -- | Free variable whose type ends in a universe.
  = AppTyVar TyVarId
  -- | Type constructor.
  | AppTyCon TyCon
  -- | Constant definition (axiom).
  | AppTyDef DefId


instance Eq TyAppable where
  -- free variables are equality compared on concrete names
  (AppTyVar v1) == (AppTyVar v2) = name2String v1 == name2String v2
  -- otherwise we require them to be the exact same name
  (AppTyCon t1) == (AppTyCon t2) = getName t1 == getName t2
  (AppTyDef d1) == (AppTyDef d2) = d1 == d2
  _ == _ = False


-- | A term that can be applied to another.
data TermThatCanBeApplied
  -- | A partial application.
  = IsPartialApp (PartiallyApplied PartiallyAppable)
  -- | A lambda abstraction.
  | IsLam (Bind Arg Term)


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


pattern Lam :: Bind Arg Term -> Term
pattern Lam lam = PartialTerm (IsLam lam)


pattern Level :: Level -> Term
pattern Level l = FullTerm (IsLevel l)


-- | Things that when fully applied are terms (and not types).
data Appable
  -- | A free variable.
  = Var (Name Term)
  -- | A data constructor.
  | ConData DCon
  -- | Constant (axiom).
  | AppDef DefId


instance Eq Appable where
  -- free variables are equality compared on concrete names
  (Var v1) == (Var v2) = name2String v1 == name2String v2
  -- otherwise we require them to be the exact same name
  (ConData c1) == (ConData c2) = getName c1 == getName c2
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
  | DefPartial DefId


type ConArg = Arg

-- | Type constructor.
data TyCon = TyCon { conID :: ConId
                   , conArgs :: [ConArg]
                   , conTy :: Type
                   }


mkTyCon :: AName -> [ConArg] -> Type -> TyCon
mkTyCon n args ty = TyCon { conID = n, conArgs = args, conTy = ty }


type DConId = AName
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


instance (Pretty a) => Pretty (PartiallyApplied a) where
  isLexicallyAtomic app = length (appliedArgs app) == 0 && isLexicallyAtomic (un app)
  pprint app = pprintParened (un app) <+> hsep (fmap pprintParened (appliedArgs app))


instance (Pretty a) => Pretty (FullyApplied a) where
  isLexicallyAtomic app = length (appliedArgs app) == 0 && isLexicallyAtomic (un app)
  pprint app = pprintParened (un app) <+> hsep (fmap pprintParened (appliedArgs app))


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


instance Pretty Term where
  isLexicallyAtomic (PartialTerm t) = isLexicallyAtomic t
  isLexicallyAtomic (FullTerm t)    = isLexicallyAtomic t

  pprint (FullTerm t)    = pprint t
  pprint (PartialTerm t) = pprint t


instance Pretty TermThatCannotBeApplied where
  isLexicallyAtomic (IsLevel l) = isLexicallyAtomic l
  isLexicallyAtomic (IsApp t) = isLexicallyAtomic t
  isLexicallyAtomic (IsTypeTerm t) = isLexicallyAtomic t

  pprint (IsLevel l) = pprint l
  pprint (IsTypeTerm t) = pprint t
  pprint (IsApp p) = pprint p


instance Pretty TermThatCanBeApplied where
  isLexicallyAtomic (IsPartialApp t) = isLexicallyAtomic t
  isLexicallyAtomic IsLam{} = False

  pprint (IsLam lam) =
    let (arg, body) = unsafeUnbind lam in char '\\' <+> pprintParened arg <+> text "->" <+> pprint body
  pprint (IsPartialApp p) = pprint p


instance Pretty Appable where
  isLexicallyAtomic (Var d) = isLexicallyAtomic d
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


instance Pretty TypeTerm where
  isLexicallyAtomic (TyApp t) = isLexicallyAtomic t
  isLexicallyAtomic (TTForApp t) = isLexicallyAtomic t
  isLexicallyAtomic Universe{} = False

  pprint (Universe l) = text "Type" <+> pprint l
  pprint (TTForApp t) = pprint t
  pprint (TyApp ty) = pprint ty


instance Pretty TypeTermOfTermsThatCanBeApplied where
  isLexicallyAtomic IsPi{} = False

  pprint (IsPi pi) =
    let (arg, resT) = unsafeUnbind pi in pprintParened arg <+> text "->" <+> pprint resT


instance Pretty TyAppable where
  isLexicallyAtomic (AppTyVar v) = isLexicallyAtomic v
  isLexicallyAtomic (AppTyCon t) = isLexicallyAtomic t
  isLexicallyAtomic (AppTyDef d) = isLexicallyAtomic d

  pprint (AppTyVar v) = pprint v
  pprint (AppTyCon t) = pprint t
  pprint (AppTyDef d) = pprint d


instance Pretty TyCon where
  isLexicallyAtomic = isLexicallyAtomic . getName
  pprint = pprint . getName

instance Pretty DCon where
  isLexicallyAtomic = isLexicallyAtomic . getName
  pprint = pprint . getName


instance Pretty Arg where
  pprint x = pprint (argVar x) <+> colon <+> pprint (grading x) <+> pprint (typeOf x)


instance Pretty FreeVar where
  isLexicallyAtomic = isLexicallyAtomic . freeVarName
  pprint = pprint . freeVarName


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
  | Plus Nat LevelTerm
  | Max Level Level


-- | Atomic terms that are levels.
data LevelTerm
  = LApp (FullyApplied LAppable)


type LVarId = Name Level


data LAppable
  = LVar LVarId
  | LDef DefId


instance Eq LAppable where
  -- free variables are equality compared on concrete names
  (LVar v1) == (LVar v2) = name2String v1 == name2String v2
  (LDef d1) == (LDef d2) = d1 == d2
  _ == _ = False


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


instance Functor Leveled where
  fmap f (Leveled a l) = Leveled (f a) l


class HasLevel a where
  level :: a -> Level

instance HasLevel (Leveled a) where
  level = leveledLevel

instance Un Leveled where
  un = unLevel


instance Pretty Level where
  isLexicallyAtomic Concrete{} = True
  isLexicallyAtomic (Plus 0 x) = isLexicallyAtomic x
  isLexicallyAtomic _ = False

  pprint (Concrete n) = integer n
  pprint (Plus 0 x) = pprint x
  pprint (Plus n x) = integer n <+> char '+' <+> pprintParened x
  pprint (Max n m) = text "lmax" <+> pprintParened n <+> pprintParened m


instance Pretty LevelTerm where
  isLexicallyAtomic (LApp t) = isLexicallyAtomic t
  pprint (LApp t) = pprint t


instance Pretty LAppable where
  isLexicallyAtomic (LVar t) = isLexicallyAtomic t
  isLexicallyAtomic (LDef t) = isLexicallyAtomic t

  pprint (LVar t) = pprint t
  pprint (LDef t) = pprint t


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
mkGrading :: Grade -> Grade -> Grading
mkGrading = Com.mkGrading
grading :: (Com.IsGraded a Grade) => a -> Grading
grading = Com.grading
subjectGrade, subjectTypeGrade :: (Com.IsGraded a Grade) => a -> Grade
subjectGrade = Com.subjectGrade
subjectTypeGrade = Com.subjectTypeGrade


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


mkLam :: Name Term -> Type -> Term -> Term
mkLam n ty = mkLam' (mkArg (VISTerm, n) thatMagicalGrading ty)


mkLam' :: Arg -> Term -> Term
mkLam' arg body = Lam $ bind arg body


mkTyVar :: TyVarId -> Level -> Type
mkTyVar n l = mkType (TyApp (fullyApplied (AppTyVar n) [])) l


mkTyDef :: DefId -> Level -> [Term] -> Type
mkTyDef n l args = mkType (TyApp (fullyApplied (AppTyDef n) args)) l


mkTermDef :: DefId -> [Term] -> Term
mkTermDef n args = App (fullyApplied (AppDef n) args)


mkPi' :: Arg -> Type -> TypeTerm
mkPi' arg = Pi . bind arg


mkPi'' :: Name Term -> Type -> Type -> TypeTermOfTermsThatCanBeApplied
mkPi'' n argTy = IsPi . bind (mkArg (VISTerm, n) thatMagicalGrading argTy)


mkPi :: Name Term -> Type -> Type -> TypeTerm
mkPi n argTy = mkPi' (mkArg (VISTerm, n) thatMagicalGrading argTy)


mkFunTy :: Name Term -> Type -> Type -> Type
mkFunTy n t e = mkType (mkPi n t e) (nextLevel $ Max (level t) (level e))


mkFunTy' :: Arg -> Type -> Type
mkFunTy' arg ty = mkType (mkPi' arg ty) (nextLevel $ Max (level (typeOf arg)) (level ty))


mkFunTyNoBind :: Type -> Type -> Type
mkFunTyNoBind t e = mkType (mkPi (nameFromString "_") t e) (nextLevel $ Max (level t) (level e))


mkFunTyNoBind' :: Type -> Type -> TypeOfTermsThatCanBeApplied
mkFunTyNoBind' t e = mkType' (mkPi'' (nameFromString "_") t e) (nextLevel $ Max (level t) (level e))


levelZero :: Level
levelZero = Concrete 0


mkTLevel :: LevelTerm -> Level
mkTLevel = Plus 0


-- TODO: switch this to be 'Name Level' (2020-03-20)
mkLevelVar :: LVarId -> Level
mkLevelVar n = mkTLevel (LApp (fullyApplied (LVar n) []))


-- | Make a new (fully-applied) type variable.
mkTypeVar :: TyVarId -> Level -> Type
mkTypeVar n = mkType (TyApp (fullyApplied (AppTyVar n) []))


-- | Make a new (fully-applied) free variable.
mkVar :: VarId -> Term
mkVar n = App (fullyApplied (Var n) [])


mkArg' :: VarId -> Type -> Arg
mkArg' n t = mkArg (VISTerm, n) thatMagicalGrading t


mkArgNoBind :: Type -> Arg
mkArgNoBind = mkArg' (nameFromString "_")


tyVarToTermVar :: TyVarId -> VarId
tyVarToTermVar = nameForTerm


termVarToTyVar :: VarId -> TyVarId
termVarToTyVar = nameForType


nameForTerm :: Name a -> VarId
nameForTerm = translate


nameForType :: Name a -> TyVarId
nameForType = translate


nameFromString :: (Rep a) => String -> Name a
nameFromString = s2n


aname2Name :: (Rep a) => AName -> Name a
aname2Name = nameFromString . pprintShow . nameConcrete


class HasName a where
  getName :: a -> AName


instance HasName TyCon where
  getName = conID


instance HasName DCon where
  getName = dconID


-----------------------
----- For Unbound -----
-----------------------


$(derive
  [ ''Appable
  , ''Arg
  , ''DCon
  , ''FullyApplied
  , ''Grade
  , ''LAppable
  , ''Level
  , ''Leveled
  , ''LevelTerm
  , ''PartiallyAppable
  , ''PartiallyApplied
  , ''Term
  , ''TermThatCanBeApplied
  , ''TermThatCannotBeApplied
  , ''TyAppable
  , ''TyCon
  , ''Type'
  , ''TypeTerm
  , ''TypeTermOfTermsThatCanBeApplied
  , ''VSort
  ])


$(derive_abstract [''FreeVar])


instance Alpha Arg
instance (Alpha a) => Alpha (Type' a)
instance (Alpha a) => Alpha (PartiallyApplied a)
instance (Alpha a) => Alpha (FullyApplied a)
instance (Alpha a) => Alpha (Leveled a)
-- we have to provide definitions for aeq' and acompare' as FreeVar is
-- abstract (see
-- https://hackage.haskell.org/package/unbound-0.5.1.1/docs/Unbound-LocallyNameless-Alpha.html#t:Alpha)
instance Alpha FreeVar where
  aeq' _c x y = x == y
  acompare' _c x y = compare x y
instance Alpha Grade
instance Alpha Term
instance Alpha TermThatCannotBeApplied
instance Alpha TermThatCanBeApplied
instance Alpha TypeTermOfTermsThatCanBeApplied
instance Alpha TypeTerm
instance Alpha LAppable
instance Alpha Level
instance Alpha LevelTerm
instance Alpha Appable
instance Alpha PartiallyAppable
instance Alpha TyAppable
instance Alpha DCon
instance Alpha TyCon
instance Alpha VSort


instance (Subst Term a) => Subst Term (Leveled a) where
instance (Subst Term a) => Subst Term (FullyApplied a) where
instance (Subst Term a) => Subst Term (PartiallyApplied a) where
instance (Subst Term a, Subst Term t) => Subst Term (IsTyped t a) where
instance (Subst Term a, Subst Term g) => Subst Term (Graded g a) where
instance Subst Term Type where
instance Subst Term LAppable where
instance Subst Term LevelTerm where
instance Subst Term Level where
instance Subst Term TypeTerm where
instance Subst Term Term where
instance Subst Term TypeTermOfTermsThatCanBeApplied where
instance Subst Term TyAppable where
instance Subst Term TermThatCannotBeApplied where
instance Subst Term TermThatCanBeApplied where
instance Subst Term Arg where
instance Subst Term FreeVar where
instance Subst Term TyCon where
instance Subst Term AName where
instance Subst Term Appable where
instance Subst Term Grade where
instance Subst Term NameId where
instance Subst Term CName where
instance Subst Term DCon where
instance Subst Term PartiallyAppable where
instance Subst Term VSort where


instance (Subst Level a) => Subst Level (Leveled a) where
instance (Subst Level a) => Subst Level (FullyApplied a) where
instance (Subst Level a) => Subst Level (PartiallyApplied a) where
instance (Subst Level a, Subst Level t) => Subst Level (IsTyped t a) where
instance (Subst Level a, Subst Level g) => Subst Level (Graded g a) where
instance Subst Level Type where
instance Subst Level LAppable where
instance Subst Level LevelTerm where
instance Subst Level Level where
instance Subst Level TypeTerm where
instance Subst Level Term where
instance Subst Level TypeTermOfTermsThatCanBeApplied where
instance Subst Level TyAppable where
instance Subst Level TermThatCannotBeApplied where
instance Subst Level TermThatCanBeApplied where
instance Subst Level Arg where
instance Subst Level FreeVar where
instance Subst Level TyCon where
instance Subst Level AName where
instance Subst Level Appable where
instance Subst Level Grade where
instance Subst Level NameId where
instance Subst Level CName where
instance Subst Level DCon where
instance Subst Level PartiallyAppable where
instance Subst Level VSort where


instance (Subst Type a) => Subst Type (Leveled a) where
instance (Subst Type a) => Subst Type (FullyApplied a) where
instance (Subst Type a) => Subst Type (PartiallyApplied a) where
instance (Subst Type a, Subst Type t) => Subst Type (IsTyped t a) where
instance (Subst Type a, Subst Type g) => Subst Type (Graded g a) where
instance Subst Type Type where
instance Subst Type LAppable where
instance Subst Type LevelTerm where
instance Subst Type Level where
instance Subst Type TypeTerm where
instance Subst Type Term where
instance Subst Type TypeTermOfTermsThatCanBeApplied where
instance Subst Type TyAppable where
instance Subst Type TermThatCannotBeApplied where
instance Subst Type TermThatCanBeApplied where
instance Subst Type Arg where
instance Subst Type FreeVar where
instance Subst Type TyCon where
instance Subst Type AName where
instance Subst Type Appable where
instance Subst Type Grade where
instance Subst Type NameId where
instance Subst Type CName where
instance Subst Type DCon where
instance Subst Type PartiallyAppable where
instance Subst Type VSort where
