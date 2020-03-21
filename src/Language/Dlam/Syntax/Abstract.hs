{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Dlam.Syntax.Abstract
  (
   -- * Expressions
    Expr(..)
  , FVName
  , AName(..)
  , mkIdent
  , ignoreVar
  , nameFromString
  , mkAbs
  , mkAbs'
  , argTy
  , argName
  -- ** Let bindings
  , LetBinding(..)
  , Pattern(..)
  , boundTypingVars
  , boundSubjectVars
  -- * AST
  , AST(..)
  -- ** Declarations
  , FLHS(..)
  , FRHS(..)
  , Declaration(..)
  , Abstraction
  , mkImplicit

  -- * Grading
  , Grade
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
  , LambdaArg
  , mkLambdaArg

  -- * Unbound
  , module Unbound.LocallyNameless
  ) where


import Prelude hiding ((<>))
import qualified Data.Set as Set

import Unbound.LocallyNameless
import Unbound.LocallyNameless.Ops (unsafeUnbind) -- for pretty-printing

import Language.Dlam.Syntax.Common hiding (Arg)
import qualified Language.Dlam.Syntax.Common as Com
import qualified Language.Dlam.Syntax.Common.Language as Com
import qualified Language.Dlam.Syntax.Concrete as C
import Language.Dlam.Util.Pretty


------------------------------
----- Language Specifics -----
------------------------------


-- | As we have dependent types, we should be able to treat grades
-- | as arbitrary expressions.
type Grade   = Expr
type Grading = Com.Grading Grade
type Graded = Com.Graded Grade
type BoundName = Com.BoundName AName
type Type = Expr
type IsTyped = Com.IsTyped Expr
typedWith :: a -> Type -> IsTyped a
typedWith = Com.typedWith
typeOf :: (Com.HasType a Type) => a -> Type
typeOf = Com.typeOf
gradedWith :: a -> Grading -> Graded a
gradedWith = Com.gradedWith
bindName :: AName -> BoundName
bindName = Com.bindName
mkGrading :: Grade -> Grade -> Grading
mkGrading = Com.mkGrading
grading :: (Com.IsGraded a Grade) => a -> Grading
grading = Com.grading
subjectGrade, subjectTypeGrade :: (Com.IsGraded a Grade) => a -> Grade
subjectGrade = Com.subjectGrade
subjectTypeGrade = Com.subjectTypeGrade


implicitGrading :: Grading
implicitGrading = mkGrading Implicit Implicit


-- TODO: update this to support binding multiple names at once (see
-- Agda discussion at
-- https://hackage.haskell.org/package/Agda-2.6.0.1/docs/Agda-Syntax-Abstract.html#t:TypedBinding)
-- (2020-03-11)
-- | Typed binders are optionally graded, and can contain many bound names.
newtype TypedBinding = TB { unTB :: Com.Arg (Graded (IsTyped FVName)) }
  deriving (Show, Hiding)


mkTypedBinding :: IsHiddenOrNot -> Grading -> Type -> FVName -> TypedBinding
mkTypedBinding isHid gr ty n = TB (mkArg isHid (n `typedWith` ty `gradedWith` gr))


instance Com.HasType TypedBinding Expr where
  typeOf = typeOf . un . un . unTB


instance Com.IsGraded TypedBinding Grade where
  grading = grading . un . unTB


-- TODO: update this to support binding multiple names at once (see
-- Agda discussion at
-- https://hackage.haskell.org/package/Agda-2.6.0.1/docs/Agda-Syntax-Abstract.html#t:TypedBinding)
-- (2020-03-11)
-- | Lambda abstraction binder.
type LambdaArg = TypedBinding


mkLambdaArg :: IsHiddenOrNot -> Grading -> Type -> FVName -> LambdaArg
mkLambdaArg isHid gr ty n = TB (mkArg isHid (n `typedWith` ty `gradedWith` gr))


------------------
-- Declarations --
------------------


newtype AST = AST [Declaration]
  deriving Show


-- | A function clause's left-hand side.
data FLHS =
  -- Currently we only support simple identifiers.
  FLHSName AName
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
  | TypeSig AName Expr
  deriving (Show)


type Arg = Com.Arg (IsTyped (Graded FVName))


-- | Name of the argument.
argName :: Arg -> FVName
argName = un . un . un


-- | Argument type.
argTy :: Arg -> Expr
argTy = typeOf


type Abstraction = Bind Arg Expr


mkAbs :: FVName -> Expr -> Expr -> Abstraction
mkAbs v = mkAbs' NotHidden v implicitGrading


mkAbs' :: IsHiddenOrNot -> FVName -> Grading -> Expr -> Expr -> Abstraction
mkAbs' isHid v g e1 e2 = bind (mkArg isHid (v `gradedWith` g `typedWith` e1)) e2


type FVName = Name Expr


data Expr
  -- | Free variable.
  = Var FVName

  -- | Constant.
  | Def AName

  -- | Level literals.
  | LitLevel Integer

  -- | Dependent function type.
  | FunTy Abstraction

  -- | Lambda abstraction.
  | Lam Abstraction

  -- | Dependent tensor type.
  | ProductTy Abstraction

  -- | Pairs.
  | Pair Expr Expr

  -- | Coproduct type.
  | Coproduct Expr Expr

  -- | Coproduct eliminator.
  | CoproductCase (BindName, Expr) (BindName, Expr) (BindName, Expr) Expr

  -- | Natural number eliminator.
  | NatCase (BindName, Expr) Expr (BindName, BindName, Expr) Expr

  -- | Identity eliminator.
  | RewriteExpr (BindName, BindName, BindName, Expr) (BindName, Expr) Expr Expr Expr

  -- | Empty eliminator.
  | EmptyElim (BindName, Expr) Expr

  | App Expr Expr -- e1 e2

  | Sig Expr Expr -- e : A

  -- | Holes for inference.
  | Hole

  -- | Implicits for synthesis.
  | Implicit

  | Let LetBinding Expr

  -- 'Type'.
  | EType
  deriving (Show)


-- | Make a new, unnamed, implicit term.
mkImplicit :: Expr
mkImplicit = Implicit


------------------
-- Let bindings --
------------------


data LetBinding
  = LetPatBound Pattern Expr
  deriving (Show)


-- TODO: update this to compare equality on concrete name as well (see
-- https://hackage.haskell.org/package/Agda-2.6.0.1/docs/Agda-Syntax-Abstract.html#t:BindName)
-- (2020-03-04)
type BindName = FVName


type ConName = AName


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
  deriving (Show)


boundTypingVars :: Pattern -> Set.Set BindName
boundTypingVars (PPair l r) = boundTypingVars l `Set.union` boundTypingVars r
boundTypingVars (PVar _) = mempty
boundTypingVars (PAt n p) = Set.singleton n `Set.union` boundTypingVars p
boundTypingVars PUnit = mempty
boundTypingVars (PCon _ args) = Set.unions $ fmap boundTypingVars args


boundSubjectVars :: Pattern -> Set.Set BindName
boundSubjectVars (PPair l r) = boundSubjectVars l `Set.union` boundSubjectVars r
boundSubjectVars (PVar n) = Set.singleton n
boundSubjectVars (PAt _ p) = boundSubjectVars p
boundSubjectVars PUnit = mempty
boundSubjectVars (PCon _ args) = Set.unions $ fmap boundSubjectVars args


----------
-- * AName
----------


data AName = AName
  { nameId :: NameId
    -- ^ Unique identifier of the name.
  , nameConcrete :: C.CName
    -- ^ Concrete representation of the name.
  } deriving (Show, Eq, Ord)



-- (names might not be unique!) (2020-03-05)
ignoreVar :: FVName
ignoreVar = nameFromString "_"

mkIdent :: String -> AName
mkIdent s = AName { nameId = NameId 0, nameConcrete = C.CName s }

nameFromString :: String -> FVName
nameFromString = s2n


---------------------------
----- Pretty printing -----
---------------------------


-- | Pretty-print an Abstraction, separating the (possibly named)
-- | binder from the expression using the given separator.
pprintAbs :: Doc -> Abstraction -> Doc
pprintAbs sep ab =
  let (absArg, absExpr) = unsafeUnbind ab
      absVar = argName absArg
      absTy  = argTy absArg
      leftTyDoc =
        case name2String absVar of
          -- TODO: add better (more type-safe?) support for ignored name (2020-03-20)
          "_" -> pprint absTy
          _   -> parens (pprint absVar <+> colon <+> pprint (grading absArg) <+> pprint absTy)
  in leftTyDoc <+> sep <+> pprint absExpr


arrow, at, caset :: Doc
arrow = text "->"
at = char '@'
caset = text "case"


instance Pretty Expr where
    isLexicallyAtomic (Var _) = True
    isLexicallyAtomic LitLevel{} = True
    isLexicallyAtomic Pair{}     = True
    isLexicallyAtomic Hole{}     = True
    isLexicallyAtomic Implicit{} = True
    isLexicallyAtomic EType      = True
    isLexicallyAtomic _       = False

    pprint (LitLevel n)           = integer n
    pprint (Lam ab) = text "\\ " <> pprintAbs arrow ab
    pprint (FunTy ab) = pprintAbs arrow ab
    pprint (ProductTy ab) =
      let (absArg, absExpr) = unsafeUnbind ab
          absVar = argName absArg
          absTy  = argTy  absArg
          leftTyDoc =
            case name2String absVar of
              "_"      -> pprint absTy
              _        -> pprint absVar <+> colon <> colon <+> pprint absTy
      in leftTyDoc <+> char '*' <+> pprint absExpr
    pprint (App lam@Lam{} e2) =
      pprintParened lam <+> pprintParened e2
    pprint (App (Sig e1 t) e2) =
      pprintParened (Sig e1 t) <+> pprintParened e2
    pprint (App e1 e2) = pprint e1 <+> pprintParened e2
    pprint (Pair e1 e2) = parens (pprint e1 <> comma <+> pprint e2)
    pprint (Coproduct e1 e2) = pprint e1 <+> char '+' <+> pprint e2
    pprint (CoproductCase (_, Implicit) (x, c) (y, d) e) =
      caset <+> pprint e <+> text "of"
              <+> text "Inl" <+> pprint x <+> arrow <+> pprint c <> semi
              <+> text "Inr" <+> pprint y <+> arrow <+> pprint d
    pprint (CoproductCase (z, tC) (x, c) (y, d) e) =
      caset <+> pprint z <> at <> pprintParened e <+> text "of" <> parens
              (text "Inl" <+> pprint x <+> arrow <+> pprint c <> semi
              <+> text "Inr" <+> pprint y <+> arrow <+> pprint d) <+> colon <+> pprint tC
    pprint (NatCase (x, tC) cz (w, y, cs) n) =
      caset <+> pprint x <> at <> pprintParened n <+> text "of" <+> parens
              (text "Zero" <+> arrow <+> pprint cz <> semi
              <+> text "Succ" <+> pprint w <> at <> pprint y <+> arrow <+> pprint cs)
              <+> colon <+> pprint tC
    pprint (RewriteExpr (x, y, p, tC) (z, c) a b p') =
      text "rewrite" <> parens
        (hcat $ punctuate (space <> char '|' <> space)
         [ char '\\' <> hsep [pprint x, pprint y, pprint p, arrow, pprint tC]
         , char '\\' <> pprint z <+> arrow <+> pprint c
         , pprint a
         , pprint b
         , pprint p'])
    pprint (Var var) = pprint var
    pprint (Def var) = pprint var
    pprint (Sig e t) = pprintParened e <+> colon <+> pprint t
    pprint Hole = char '?'
    pprint Implicit{} = char '_'
    pprint (EmptyElim (x, tC) a) =
      text "let" <+> pprint x <> at <> text "()" <+> equals <+> pprint a <+> colon <+> pprint tC
    pprint (Let lb e) = text "let" <+> pprint lb <+> text "in" <+> pprint e
    pprint EType = text "Type"

instance Pretty LetBinding where
  pprint (LetPatBound p e) = pprint p <+> equals <+> pprint e

instance Pretty Pattern where
  isLexicallyAtomic (PVar v) = isLexicallyAtomic v
  isLexicallyAtomic PPair{} = True
  isLexicallyAtomic PAt{} = True
  isLexicallyAtomic PUnit{} = True
  isLexicallyAtomic PCon{} = False

  pprint (PVar v) = pprint v
  pprint (PPair l r) = parens $ pprint l <> comma <+> pprint r
  pprint (PAt v p) = pprint v <> at <> pprint p
  pprint PUnit = char '*'
  pprint (PCon c args) = pprint c <+> (hsep $ fmap pprintParened args)

instance Pretty AName where
  isLexicallyAtomic _ = True
  pprint = pprint . nameConcrete

instance Pretty AST where
  pprint (AST decls) = vcat $ fmap pprint decls

instance Pretty FLHS where
  pprint (FLHSName n) = pprint n

instance Pretty FRHS where
  pprint (FRHSAssign e) = equals <+> pprint e

instance Pretty Declaration where
  pprint (TypeSig n t) = pprint n <+> colon <+> pprint t
  pprint (FunEqn lhs rhs) = pprint lhs <+> pprint rhs

instance Pretty Grading where
  pprint g = char '[' <>
             pprint (subjectGrade g) <> comma <+> pprint (subjectTypeGrade g) <> char ']'


-----------------------
----- For Unbound -----
-----------------------


$(derive
  [ ''AName
  , ''Expr
  , ''LetBinding
  , ''Pattern
  ])


instance Alpha AName
instance Alpha Expr
instance Alpha LetBinding
instance Alpha Pattern
