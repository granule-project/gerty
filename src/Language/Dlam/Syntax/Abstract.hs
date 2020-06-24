{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
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
  , mkAbs
  , mkAbs'
  , mkAbsGr
  , absVar
  , absTy
  , absExpr
  -- ** Case bindings
  , CaseBinding(..)
  , Pattern(..)
  , BindName(..)
  , boundTypingVars
  , boundSubjectVars
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
  , mkImplicit

  -- * Metas
  , MetaId(..)

  -- * Grading
  , Grade(..)
  , gradeZero
  , gradeOne
  , gradeInf
  , pattern GZero
  , pattern GOne
  , pattern GInf
  , gradeImplicit
  , mkGrade
  , mkGradePlus
  , mkGradeTimes
  , mkGradeLub
  , GradeSpec(..)
  , Grade'(..)
  , Grading
  , implicitGrading
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


mkAbs :: Name -> Expr -> Expr -> Abstraction
mkAbs v e1 e2 = Abst { absArg = mkArg NotHidden (BindName v `gradedWith` implicitGrading `typedWith` e1), absExpr = e2 }

mkAbsGr :: Name -> Expr -> Grade -> Grade -> Expr -> Abstraction
mkAbsGr v e1 r s e2 = Abst { absArg = mkArg NotHidden (BindName v `gradedWith` (mkGrading r s) `typedWith` e1), absExpr = e2 }


mkAbs' :: IsHiddenOrNot -> Name -> Grading -> Expr -> Expr -> Abstraction
mkAbs' isHid v g e1 e2 = Abst { absArg = mkArg isHid (BindName v `gradedWith` g `typedWith` e1), absExpr = e2 }


newtype MetaId = MetaId { getMetaId :: Integer }
  deriving (Show, Eq, Ord)


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
  | Hole

  -- | Implicits for synthesis.
  | Implicit

  -- | Case binding.
  | Case Expr (Maybe (Pattern, Expr)) [CaseBinding]
  deriving (Show, Eq, Ord)


-- | Make a new, unnamed, implicit term.
mkImplicit :: Expr
mkImplicit = Implicit


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
  | PAt  BindName Pattern
  -- ^ x@p.
  | PPair Pattern Pattern
  -- ^ (p1, p2).
  | PUnit
  -- ^ unit (*).
  | PCon ConName [Pattern]
  -- ^ Constructor application.
  | PBox Pattern
  -- ^ Box pattern.
  deriving (Show, Eq, Ord)


boundTypingVars :: Pattern -> Set.Set BindName
boundTypingVars (PPair l r) = boundTypingVars l `Set.union` boundTypingVars r
boundTypingVars (PVar _) = mempty
boundTypingVars (PAt n p) = Set.singleton n `Set.union` boundTypingVars p
boundTypingVars PUnit = mempty
boundTypingVars (PCon _ args) = Set.unions $ fmap boundTypingVars args
boundTypingVars (PBox p) = boundTypingVars p


boundSubjectVars :: Pattern -> Set.Set BindName
boundSubjectVars (PPair l r) = boundSubjectVars l `Set.union` boundSubjectVars r
boundSubjectVars (PVar n) = Set.singleton n
boundSubjectVars (PAt _ p) = boundSubjectVars p
boundSubjectVars PUnit = mempty
boundSubjectVars (PCon _ args) = Set.unions $ fmap boundSubjectVars args
boundSubjectVars (PBox p) = boundSubjectVars p


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
  | GPlus Grade Grade

  -- | Grade multiplication.
  | GTimes Grade Grade

  -- | Least-upper bound.
  | GLub Grade Grade

  -- | Special grade when unspecified.
  | GImplicit

  -- | Representation for other grade elements.
  | GExpr Expr

  -- | Grade with signature.
  | GSig Grade GradeSpec
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

  -- | Unspecified, to resolve.
  | GSImplicit

  -- | Arbitrary expression.
  | GSExpr Expr
  deriving (Show, Eq, Ord)


-- | A grade with the type of resource algebra it belongs to.
data Grade = Grade { grade :: Grade', gradeTy :: GradeSpec }
  deriving (Show, Eq, Ord)


mkGrade :: Grade' -> GradeSpec -> Grade
mkGrade = Grade


gradeZero, gradeOne, gradeInf, gradeImplicit :: Grade
gradeZero     = mkGrade GZero     GSImplicit
gradeOne      = mkGrade GOne      GSImplicit
gradeInf      = mkGrade GInf      GSImplicit
gradeImplicit = mkGrade GImplicit GSImplicit


-- NOTE: these should only be used in ConcreteToAbstract, and they are
-- very hacky (they just assume the grades are well-typed)
mkGradePlus, mkGradeTimes, mkGradeLub :: Grade -> Grade -> Grade
mkGradePlus  g1 g2 = mkGrade (GPlus  g1 g2) (gradeTy g1)
mkGradeTimes g1 g2 = mkGrade (GTimes g1 g2) (gradeTy g1)
mkGradeLub   g1 g2 = mkGrade (GLub   g1 g2) (gradeTy g1)


implicitGrading :: Grading
implicitGrading = mkGrading gradeImplicit gradeImplicit


---------------------------
----- Pretty printing -----
---------------------------


-- | Pretty-print an Abstraction, separating the (possibly named)
-- | binder from the expression using the given separator.
pprintAbs :: Doc -> Abstraction -> Doc
pprintAbs sep ab =
  let leftTyDoc =
        case absVar ab of
          Name _ C.NoName{} -> pprint (absTy ab)
          _        -> parens (pprint (absVar ab) <+> colon <+> pprint (grading ab) <+> pprint (absTy ab))
  in leftTyDoc <+> sep <+> pprint (absExpr ab)


arrow, at :: Doc
arrow = text "->"
at = char '@'


instance Pretty Expr where
    isLexicallyAtomic (Var _) = True
    isLexicallyAtomic Pair{}     = True
    isLexicallyAtomic Hole{}     = True
    isLexicallyAtomic Implicit{} = True
    isLexicallyAtomic UnitTy = True
    isLexicallyAtomic Unit = True
    isLexicallyAtomic _       = False

    pprint (Universe l)           = text "Type" <+> pprintParened l
    pprint UnitTy = text "Unit"
    pprint Unit = text "unit"
    pprint (BoxTy (g1, g2) e) =
      pprintParened e <+> brackets ((pprint g1 <> char ',') <+> pprint g2)
    pprint (Box e) = brackets (pprint e)
    pprint (Lam ab) = text "\\ " <> pprintAbs arrow ab
    pprint (FunTy ab) = pprintAbs arrow ab
    pprint (ProductTy ab) =
      let leftTyDoc =
            case absVar ab of
              Name _ C.NoName{} -> pprint (absTy ab)
              _        -> pprint (absVar ab) <+> colon <> colon <+> char '[' <> pprint (subjectTypeGrade ab) <> char ']' <+> pprint (absTy ab)
      in leftTyDoc <+> char '*' <+> pprint (absExpr ab)
    pprint (App lam@Lam{} e2) =
      pprintParened lam <+> pprintParened e2
    pprint (App (Sig e1 t) e2) =
      pprintParened (Sig e1 t) <+> pprintParened e2
    pprint (App e1 e2) = pprint e1 <+> pprintParened e2
    pprint (Pair e1 e2) = parens (pprint e1 <> comma <+> pprint e2)
    pprint (Var var) = pprint var
    pprint (Def name) = pprint name
    pprint (Sig e t) = pprintParened e <+> colon <+> pprint t
    pprint Hole = char '?'
    pprint Implicit{} = char '_'
    pprint (Case e Nothing binds) =
      hang ("case" <+> pprint e <+> "of") 1 (vcat $ fmap pprint binds)
    pprint (Case e (Just (p, t)) binds) =
      hang ("case" <+> pprint e <+> "as" <+> pprint p <+> "in" <+> pprint t <+> "of")
             1 (vcat $ fmap pprint binds)

instance Pretty CaseBinding where
  pprint (CasePatBound p e) = pprint p <+> arrow <+> pprint e

instance Pretty Pattern where
  pprint (PVar v) = pprint v
  pprint (PPair l r) = parens $ pprint l <> comma <+> pprint r
  pprint (PAt v p) = pprint v <> at <> pprint p
  pprint PUnit = text "unit"
  pprint (PCon c args) = pprint c <+> (hsep $ fmap pprintParened args)
  pprint (PBox p) = brackets $ pprint p

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
  isLexicallyAtomic GImplicit = True
  isLexicallyAtomic (GExpr g) = isLexicallyAtomic g
  isLexicallyAtomic _ = False

  pprint GZero = text ".0"
  pprint GOne  = text ".1"
  pprint GInf = text ".inf"
  pprint (GPlus Grade{grade=g1} Grade{grade=g2}) = pprintSquishy 0 (g1, g2)
    where pprintSquishy n (GZero, GZero) = char '.' <> integer n
          pprintSquishy n (GOne,  r) = pprintSquishy (n+1) (GZero, r)
          pprintSquishy n (s, GOne) = pprintSquishy (n+1) (s, GZero)
          pprintSquishy n (GPlus Grade{grade=GOne} Grade{grade=s}, r) =
            pprintSquishy (n+1) (s, r)
          pprintSquishy n (GPlus Grade{grade=s} Grade{grade=GOne}, r) =
            pprintSquishy (n+1) (s, r)
          pprintSquishy n (s, GPlus (Grade{grade=GOne}) Grade{grade=r}) =
            pprintSquishy (n+1) (s, r)
          pprintSquishy n (s, GPlus Grade{grade=r} Grade{grade=GOne}) =
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
  pprint GImplicit = text "._"
  pprint (GExpr g) = pprint g
  pprint (GSig g s) = pprintParened g <+> char ':' <+> pprintParened s

instance Pretty GradeSpec where
  isLexicallyAtomic PrivacyLevel = True
  isLexicallyAtomic GSImplicit = True
  isLexicallyAtomic (GSExpr e) = isLexicallyAtomic e

  pprint PrivacyLevel = "Privacy"
  pprint GSImplicit = "_"
  pprint (GSExpr e) = pprint e

instance Pretty Grade where
  isLexicallyAtomic (Grade { grade = g }) = isLexicallyAtomic g
  -- TODO: provide an annotation to indicate the type (2020-06-21)
  pprint (Grade { grade = GZero, gradeTy = PrivacyLevel }) = text "Irrelevant"
  pprint (Grade { grade = GOne, gradeTy = PrivacyLevel }) = text "Private"
  pprint (Grade { grade = GEnc 2, gradeTy = PrivacyLevel }) = text "Public"
  pprint (Grade { grade = g }) = pprint g

instance Pretty Grading where
  pprint g = char '[' <>
             pprint (subjectGrade g) <> comma <+> pprint (subjectTypeGrade g) <> char ']'

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
