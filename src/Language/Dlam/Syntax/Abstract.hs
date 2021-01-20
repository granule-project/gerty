{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}

module Language.Dlam.Syntax.Abstract
  (
   -- * Expressions
    Expr(..)
  , Name(..)
  , mkIdent
  , ident
  , ignoreVar
  , mkAbs'
  , mkAbsGr
  , absVar
  , absTy
  , absExpr
  -- ** Case bindings
  , CaseBinding(..)
  , Pattern(..)
  , BindName(..)
  , patBoundVars
  -- ** Levels and Universes
  , Level(..)
  , levelZero
  , univMeta
  , PlusLevel(..)
  -- * AST
  , AST(..)
  -- ** Declarations
  , FLHS(..)
  , FRHS(..)
  , Declaration(..)
  , Abstraction

  -- * Metas
  , MetaId
  , mkMetaId
  , mkImplicit
  , mkHole
  , implicitToName

  -- * Grading
  , Grade(..)
  , gradeZero
  , gradeOne
  , gradeInf
  , pattern GZero
  , pattern GOne
  , pattern GInf
  , atSpec
  , mkGrade
  , mkGradePlus
  , mkGradeTimes
  , mkGradeLub
  , GradeSpec(..)
  , Grade'(..)
  , Grading
  , mkGrading
  , grading
  , subjectGrade
  , subjectTypeGrade

  -- * Bindings
  , TypedBinding
  , unTB
  , mkTypedBinding
  , bindName
  , unBoundName
  , LambdaArg
  , mkLambdaArg
  ) where


import Prelude hiding ((<>))
import qualified Data.Set as Set

import Language.Dlam.Syntax.Common hiding (Arg)
import qualified Language.Dlam.Syntax.Common as Com
import qualified Language.Dlam.Syntax.Common.Language as Com
import qualified Language.Dlam.Syntax.Concrete as C
import Language.Dlam.Util.Pretty


------------------------------
----- Language Specifics -----
------------------------------


type Grading = Com.Grading Grade
type Graded = Com.Graded Grade
type BoundName = Com.BoundName Name
type Type = Expr
type Typed = Com.Typed Expr
typedWith :: a -> Type -> Typed a
typedWith = Com.typedWith
typeOf :: (Com.IsTyped a Type) => a -> Type
typeOf = Com.typeOf
gradedWith :: a -> Grading -> Graded a
gradedWith = Com.gradedWith
bindName :: Name -> BoundName
bindName = Com.bindName
mkGrading :: Grade -> Grade -> Grading
mkGrading = Com.mkGrading
unBoundName :: BoundName -> Name
unBoundName = Com.unBoundName
grading :: (Com.IsGraded a Grade) => a -> Grading
grading = Com.grading
subjectGrade, subjectTypeGrade :: (Com.IsGraded a Grade) => a -> Grade
subjectGrade = Com.subjectGrade
subjectTypeGrade = Com.subjectTypeGrade


-- TODO: update this to support binding multiple names at once (see
-- Agda discussion at
-- https://hackage.haskell.org/package/Agda-2.6.0.1/docs/Agda-Syntax-Abstract.html#t:TypedBinding)
-- (2020-03-11)
-- | Typed binders are optionally graded, and can contain many bound names.
newtype TypedBinding = TB { unTB :: Com.Arg (Graded (Typed BoundName)) }
  deriving (Show, Eq, Ord, Hiding)


mkTypedBinding :: IsHiddenOrNot -> Grading -> Type -> BoundName -> TypedBinding
mkTypedBinding isHid gr ty n = TB (mkArg isHid (n `typedWith` ty `gradedWith` gr))


instance Com.IsTyped TypedBinding Expr where
  typeOf = typeOf . un . un . unTB


instance Com.IsGraded TypedBinding Grade where
  grading = grading . un . unTB


-- TODO: update this to support binding multiple names at once (see
-- Agda discussion at
-- https://hackage.haskell.org/package/Agda-2.6.0.1/docs/Agda-Syntax-Abstract.html#t:TypedBinding)
-- (2020-03-11)
-- | Lambda abstraction binder.
type LambdaArg = TypedBinding


mkLambdaArg :: IsHiddenOrNot -> Grading -> Type -> BoundName -> LambdaArg
mkLambdaArg isHid gr ty n = TB (mkArg isHid (n `typedWith` ty `gradedWith` gr))


------------------
-- Declarations --
------------------


newtype AST = AST [Declaration]
  deriving Show


-- | A function clause's left-hand side.
data FLHS =
  -- Currently we only support simple identifiers.
  FLHSName Name
  deriving (Show)

-- | Right-hand side of a function clause.
data FRHS =
  -- Currently we only support simple expressions.
  FRHSAssign Expr
  deriving (Show)


data Declaration =
  -- ^ A single clause for a function.
    FunEqn FLHS FRHS
  -- ^ A type signature.
  | TypeSig Name Expr
  deriving (Show)


type Arg = Com.Arg (Typed (Graded BindName))


-- | Name of the argument.
argName :: Arg -> BindName
argName = un . un . un


-- | Argument type.
argTy :: Arg -> Expr
argTy = typeOf


data Abstraction = Abst
  {
  -- | Argument of the abstraction.
    absArg :: Arg
  -- | Target expression of the abstraction.
  , absExpr :: Expr
  } deriving (Show, Eq, Ord)


instance Com.IsGraded Abstraction Grade where
  grading = grading . absArg


instance Com.Hiding Abstraction where
  isHidden = isHidden . absArg


-- | Variable bound in the abstraction.
absVar :: Abstraction -> Name
absVar = unBindName . argName . absArg


-- | Type of the bound variable in the abstraction.
absTy :: Abstraction -> Expr
absTy = argTy . absArg


mkAbsGr :: Name -> Expr -> Grade -> Grade -> Expr -> Abstraction
mkAbsGr v e1 r s e2 = Abst { absArg = mkArg NotHidden (BindName v `gradedWith` (mkGrading r s) `typedWith` e1), absExpr = e2 }


mkAbs' :: IsHiddenOrNot -> Name -> Grading -> Expr -> Expr -> Abstraction
mkAbs' isHid v g e1 e2 = Abst { absArg = mkArg isHid (BindName v `gradedWith` g `typedWith` e1), absExpr = e2 }


newtype MetaId = MetaId { getMetaId :: Integer }
  deriving (Show, Eq, Ord, Enum, Num, Real, Integral)


mkMetaId :: Integer -> MetaId
mkMetaId = MetaId


-- | Levels, in the style of Agda: https://hackage.haskell.org/package/Agda-2.6.0.1/docs/Agda-Syntax-Internal.html#t:Level
data Level
  -- | The maximum of some number of levels, with the empty maximum representing level 0.
  = LMax [PlusLevel]
  deriving (Show, Eq, Ord)


data PlusLevel
  = LitLevel Integer
  | LPlus Integer MetaId
  deriving (Show, Eq, Ord)


levelZero :: Level
levelZero = LMax []


univMeta :: MetaId -> Expr
univMeta i = Universe (LMax [LPlus 0 i])


data Expr
  -- | Variable.
  = Var Name

  -- | Name standing for a constant.
  | Def Name

  -- | Dependent function type.
  | FunTy Abstraction

  -- | Lambda abstraction.
  | Lam Abstraction

  -- | Dependent tensor type.
  | ProductTy Abstraction

  -- | Pairs.
  | Pair Expr Expr

  | App Expr Expr -- e1 e2

  | Sig Expr Expr -- e : A

  -- | Typing universe.
  | Universe Level

  -- | Graded modal types.
  | BoxTy (Grade, Grade) Expr

  -- | Box value.
  | Box Expr

  -- | Unit type.
  | UnitTy

  -- | Unit value.
  | Unit

  -- | Holes for inference.
  -- |
  -- | Holes represent values that the programmer intends to fill out,
  -- | but would like some additional information/guidance from the
  -- | typechecker (e.g., type, constraints, etc.).
  | Hole MetaId

  -- | Implicits for synthesis.
  -- |
  -- | Implicits are resolved by the type checker and SMT solver.
  | Implicit MetaId

  -- | Natural number type.
  | NatTy

  -- | Natural number successor.
  | NSucc

  -- | Natural number zero.
  | NZero

  -- | Case binding.
  | Case Expr (Maybe (Pattern, Expr)) [CaseBinding]
  deriving (Show, Eq, Ord)


-- | Make a new, unnamed, implicit term.
mkImplicit :: MetaId -> Expr
mkImplicit = Implicit


-- | Make a new hole.
mkHole :: MetaId -> Expr
mkHole = Hole


implicitToName :: MetaId -> Name
implicitToName m = let nid = NameId (fromIntegral m) in Name nid (C.NoName nid)


-------------------
-- Case bindings --
-------------------


data CaseBinding
  = CasePatBound Pattern Expr
  deriving (Show, Eq, Ord)


-- TODO: update this to compare equality on concrete name as well (see
-- https://hackage.haskell.org/package/Agda-2.6.0.1/docs/Agda-Syntax-Abstract.html#t:BindName)
-- (2020-03-04)
newtype BindName = BindName { unBindName :: Name }
  deriving (Show, Eq, Ord)


type ConName = Name


data Pattern
  = PVar BindName
  -- ^ x.
  | PPair Pattern Pattern
  -- ^ (p1, p2).
  | PUnit
  -- ^ unit (*).
  | PCon ConName [Pattern]
  -- ^ Constructor application.
  | PBox Pattern
  -- ^ Box pattern.
  | PBoxTy Pattern
  -- ^ BoxTy pattern.
  deriving (Show, Eq, Ord)


-- | The set of names bound in a pattern.
patBoundVars :: Pattern -> Set.Set BindName
patBoundVars (PPair l r) = patBoundVars l `Set.union` patBoundVars r
patBoundVars (PVar n) = Set.singleton n
patBoundVars PUnit = mempty
patBoundVars (PCon _ args) = Set.unions $ fmap patBoundVars args
patBoundVars (PBox p) = patBoundVars p
patBoundVars (PBoxTy p) = patBoundVars p


---------
-- * Name
---------


data Name = Name
  { nameId :: NameId
    -- ^ Unique identifier of the name.
  , nameConcrete :: C.Name
    -- ^ Concrete representation of the name.
  } deriving (Show, Eq, Ord)



-- TODO: move builtins to a different phase so we don't need these
-- (names might not be unique!) (2020-03-05)
ignoreVar :: Name
ignoreVar = Name { nameId = NameId 0, nameConcrete = C.NoName (NameId 0) }

mkIdent :: String -> Name
mkIdent s = Name { nameId = NameId 0, nameConcrete = C.Name s }


ident :: Name -> String
ident (Name _ (C.Name s)) = s
ident (Name _ (C.NoName _)) = "_"


------------------
----- Grades -----
------------------


-- | We provide an algebra for grades (pre-ordered semiring).
-- |
-- | Anything that is a member of a pre-ordered semiring should be
-- | able to compile to this.
data Grade'
  -- | Allows grades to be compiled down to integers.
  -- |
  -- | Reserved values are as follows:
  -- |
  -- | 0 = zero grade
  -- | 1 = one  grade
  -- | -1 = infinity grade
  = GEnc Integer

  -- | Grade addition.
  | GPlus Grade' Grade'

  -- | Grade multiplication.
  | GTimes Grade' Grade'

  -- | Least-upper bound.
  | GLub Grade' Grade'

  -- | Representation for other grade elements.
  | GExpr Expr

  -- | Grade with signature.
  | GSig Grade' GradeSpec
  deriving (Show, Eq, Ord)


pattern GZero :: Grade'
pattern GZero = GEnc 0

pattern GOne :: Grade'
pattern GOne = GEnc 1

pattern GInf :: Grade'
pattern GInf = GEnc (-1)


-- | Grade specification, i.e., the pre-ordered semiring.
data GradeSpec

  -- | Privacy levels.
  = PrivacyLevel

  -- | Security levels.
  | SecurityLevel

  -- | Unspecified, to resolve.
  | GSImplicit

  -- | Natural numbers
  | ExactUsage

  -- | Intervals over some other types
  | Interval GradeSpec

  -- | 0, 1, omega
  | NoneOneTons

  -- Top-completed version of some other type
  | Extended GradeSpec

  -- | Arbitrary expression.
  | GSExpr Expr
  deriving (Show, Eq, Ord)


-- | A grade with the type of resource algebra it belongs to.
data Grade = Grade { grade :: Grade', gradeTy :: GradeSpec }
  deriving (Show, Eq, Ord)


mkGrade :: Grade' -> GradeSpec -> Grade
mkGrade = Grade

atSpec :: Grade' -> Grade -> Grade
atSpec g (Grade _ gradeTy) = Grade g gradeTy

gradeZero, gradeOne, gradeInf :: Grade
gradeZero     = mkGrade GZero     GSImplicit
gradeOne      = mkGrade GOne      GSImplicit
gradeInf      = mkGrade GInf      GSImplicit


-- NOTE: these should only be used in ConcreteToAbstract, and they are
-- very hacky (they just assume the grades are well-typed)
mkGradePlus, mkGradeTimes, mkGradeLub :: Grade -> Grade -> Grade
mkGradePlus  g1 g2 = Grade (GPlus  (grade g1) (grade g2)) (gradeTy g1)
mkGradeTimes g1 g2 = Grade (GTimes (grade g1) (grade g2)) (gradeTy g1)
mkGradeLub   g1 g2 = Grade (GLub   (grade g1) (grade g2)) (gradeTy g1)


---------------------------
----- Pretty printing -----
---------------------------


-- | Pretty-print an Abstraction, separating the (possibly named)
-- | binder from the expression using the given separator.
pprintAbs :: Doc -> Abstraction -> Doc
pprintAbs sep ab =
  let leftTyDoc =
        case (absVar ab, subjectGrade ab, subjectTypeGrade ab) of
          -- special case, we render (_ : [.1, .0] A) -> B as A -> B
          ( Name _ C.NoName{}, Grade{grade=GOne,gradeTy=GSImplicit}
                             , Grade{grade=GZero,gradeTy=GSImplicit}) -> pprint (absTy ab)
          _        -> parens (pprint (absVar ab) <+> colon <+> pprint (grading ab) <+> pprint (absTy ab))
  in leftTyDoc <+> sep <+> pprint (absExpr ab)


arrow :: Doc
arrow = text "->"


instance Pretty Expr where
    isLexicallyAtomic (Var _) = True
    isLexicallyAtomic Pair{}     = True
    isLexicallyAtomic Hole{}     = True
    isLexicallyAtomic Implicit{} = True
    isLexicallyAtomic UnitTy = True
    isLexicallyAtomic Unit = True
    isLexicallyAtomic NatTy = True
    isLexicallyAtomic NSucc = True
    isLexicallyAtomic NZero = True
    isLexicallyAtomic Box{} = True
    isLexicallyAtomic _       = False

    pprint (Universe l)           = text "Type" <+> pprintParened l
    pprint NatTy  = text "Nat"
    pprint NSucc  = text "succ"
    pprint NZero  = text "zero"
    pprint UnitTy = text "Unit"
    pprint Unit = text "unit"
    pprint (BoxTy (g1, g2) e) =
      brackets ((pprint g1 <> char ',') <+> pprint g2) <+> pprintParened e
    pprint (Box e) = brackets (pprint e)
    pprint (Lam ab) = text "\\ " <> pprintAbs arrow ab
    pprint (FunTy ab) = pprintAbs arrow ab
    pprint (ProductTy ab) =
      let leftTyDoc =
            case absVar ab of
              Name _ C.NoName{} -> pprint (absTy ab)
              _        -> pprint (absVar ab) <+> brackets (pprint (subjectTypeGrade ab)) <+> colon <+> pprint (absTy ab)
      in angles (leftTyDoc <+> char '*' <+> pprint (absExpr ab))
    pprint (App lam@Lam{} e2) =
      pprintParened lam <+> pprintParened e2
    pprint (App (Sig e1 t) e2) =
      pprintParened (Sig e1 t) <+> pprintParened e2
    pprint (App e1 e2) = pprint e1 <+> pprintParened e2
    pprint (Pair e1 e2) = angles (pprint e1 <> comma <+> pprint e2)
    pprint (Var var) = pprint var
    pprint (Def name) = pprint name
    pprint (Sig e t) = pprintParened e <+> colon <+> pprint t
    pprint (Hole m) = identifier (toInteger m) ("?" :: String)
    pprint (Implicit m) = identifier (toInteger m) ("_" :: String)
    pprint (Case e Nothing binds) =
      hang ("case" <+> pprint e <+> "of") 1 (vcat $ fmap pprint binds)
    pprint (Case e (Just (p, t)) binds) =
      hang ("case" <+> pprint e <+> "as" <+> pprint p <+> "in" <+> pprint t <+> "of")
             1 (vcat $ fmap pprint binds)

instance Pretty CaseBinding where
  pprint (CasePatBound p e) = pprint p <+> arrow <+> pprint e

instance Pretty Pattern where
  pprint (PVar v) = pprint v
  pprint (PPair l r) = angles $ pprint l <> comma <+> pprint r
  pprint PUnit = text "unit"
  pprint (PCon c args) = pprint c <+> (hsep $ fmap pprintParened args)
  pprint (PBox p) = brackets $ pprint p
  pprint (PBoxTy p) = "." <> (brackets $ pprint p)

instance Pretty BindName where
  pprint = pprint . unBindName

instance Pretty Name where
  isLexicallyAtomic _ = True
  pprint n = identifier (toInteger $ nameId n) (nameConcrete n)

instance Pretty AST where
  pprint (AST decls) = vcat $ fmap pprint decls

instance Pretty FLHS where
  pprint (FLHSName n) = pprint n

instance Pretty FRHS where
  pprint (FRHSAssign e) = equals <+> pprint e

instance Pretty Declaration where
  pprint (TypeSig n t) = pprint n <+> colon <+> pprint t
  pprint (FunEqn lhs rhs) = pprint lhs <+> pprint rhs

instance Pretty Grade' where
  isLexicallyAtomic GEnc{} = True
  isLexicallyAtomic (GExpr g) = isLexicallyAtomic g
  isLexicallyAtomic _ = False

  pprint GZero = text ".0"
  pprint GOne  = text ".1"
  pprint GInf = text ".inf"
  pprint (GPlus g1 g2) = pprintSquishy 0 (g1, g2)
    where pprintSquishy n (GZero, GZero) = char '.' <> integer n
          pprintSquishy n (GOne,  r) = pprintSquishy (n+1) (GZero, r)
          pprintSquishy n (s, GOne) = pprintSquishy (n+1) (s, GZero)
          pprintSquishy n (GPlus GOne s, r) =
            pprintSquishy (n+1) (s, r)
          pprintSquishy n (GPlus s GOne, r) =
            pprintSquishy (n+1) (s, r)
          pprintSquishy n (s, GPlus GOne r) =
            pprintSquishy (n+1) (s, r)
          pprintSquishy n (s, GPlus r GOne) =
            pprintSquishy (n+1) (s, r)
          pprintSquishy n (GZero, r) =
            (char '.' <> integer n) <+> char '+' <+> pprintParened r
          pprintSquishy n (s, GZero) =
            (char '.' <> integer n) <+> char '+' <+> pprintParened s
          pprintSquishy n (s, r) =
            (char '.' <> integer n) <+> char '+' <+> pprintParened s <+> char '+' <+> pprint r
  -- TODO: have this display correct value based on semiring (will
  -- need to be done in "Grade" rather than "Grade'", as only that has
  -- access to the type (2020-06-21)
  pprint (GEnc n) = integer n
  pprint (GTimes g1 g2) = pprintParened g1 <+> text "*" <+> pprintParened g2
  pprint (GLub g1 g2) = pprintParened g1 <+> text "lub" <+> pprintParened g2
  pprint (GExpr g) = pprint g
  pprint (GSig g s) = pprintParened g <+> char ':' <+> pprintParened s

instance Pretty GradeSpec where
  isLexicallyAtomic PrivacyLevel = True
  isLexicallyAtomic SecurityLevel = True
  isLexicallyAtomic GSImplicit = True
  isLexicallyAtomic ExactUsage = True
  isLexicallyAtomic NoneOneTons = True
  isLexicallyAtomic (GSExpr e) = isLexicallyAtomic e
  isLexicallyAtomic _ = False

  pprint PrivacyLevel = "Privacy"
  pprint SecurityLevel = "Security"
  pprint GSImplicit = "_"
  pprint (GSExpr e) = pprint e
  pprint ExactUsage = "Nat"
  pprint (Interval g) = "Interval " <> pprint g
  pprint (Extended g) = "Ext " <> pprint g
  pprint NoneOneTons  = "ntw"

instance Pretty Grade where
  isLexicallyAtomic (Grade { grade = g }) = isLexicallyAtomic g
  -- TODO: provide an annotation to indicate the type (2020-06-21)
  pprint (Grade { grade = GZero, gradeTy = PrivacyLevel }) = text "Irrelevant"
  pprint (Grade { grade = GOne, gradeTy = PrivacyLevel }) = text "Private"
  pprint (Grade { grade = GEnc 2, gradeTy = PrivacyLevel }) = text "Public"
  pprint (Grade { grade = GZero, gradeTy = SecurityLevel }) = text "Hi"
  pprint (Grade { grade = GOne, gradeTy = SecurityLevel }) = text "Lo"
  pprint (Grade { grade = g }) = pprint g

instance Pretty Grading where
  pprint g = parens (pprint (subjectGrade g) <> comma <+> pprint (subjectTypeGrade g))

instance Pretty Level where
  isLexicallyAtomic (LMax []) = True
  isLexicallyAtomic (LMax [x]) = isLexicallyAtomic x
  isLexicallyAtomic (LMax (_:_)) = False

  pprint (LMax ls) =
    case ls of
      []  -> pprint (LitLevel 0)
      [l] -> pprint l
      _   -> foldr1 (\a b -> text "lub" <+> a <+> b) $ map pprintParened ls

instance Pretty PlusLevel where
  isLexicallyAtomic LitLevel{} = True
  isLexicallyAtomic (LPlus 0 l) = isLexicallyAtomic l
  isLexicallyAtomic LPlus{} = False

  pprint (LitLevel n) = integer n
  pprint (LPlus 0 l) = pprint l
  pprint (LPlus n l) = integer n <+> text "+" <+> pprint l


instance Pretty MetaId where
  isLexicallyAtomic _ = True

  pprint (MetaId n) = text "?{" <> integer n <> text "}"
