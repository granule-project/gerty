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
  , pattern AType
  , pattern Inl'
  , pattern Inr'
  , pattern LSuc'
  , pattern Succ'
  , pattern Zero'
  , Name(..)
  , mkIdent
  , ignoreVar
  , mkAbs
  , mkAbs'
  , absVar
  , absTy
  , absExpr
  -- ** Let bindings
  , LetBinding(..)
  , Pattern(..)
  , BindName(..)
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

  -- * Builtins
  , BuiltinTerm(..)

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


-- | As we have dependent types, we should be able to treat grades
-- | as arbitrary expressions.
type Grade   = Expr
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


implicitGrading :: Grading
implicitGrading = mkGrading Implicit Implicit


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


mkAbs' :: IsHiddenOrNot -> Name -> Grading -> Expr -> Expr -> Abstraction
mkAbs' isHid v g e1 e2 = Abst { absArg = mkArg isHid (BindName v `gradedWith` g `typedWith` e1), absExpr = e2 }


data Expr
  -- | Variable.
  = Var Name

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
  | CoproductCase (Name, Expr) (Name, Expr) (Name, Expr) Expr

  -- | Natural number eliminator.
  | NatCase (Name, Expr) Expr (Name, Name, Expr) Expr

  -- | Identity eliminator.
  | RewriteExpr (Name, Name, Name, Expr) (Name, Expr) Expr Expr Expr

  -- | Empty eliminator.
  | EmptyElim (Name, Expr) Expr

  | App Expr Expr -- e1 e2

  | Sig Expr Expr -- e : A

  -- | Holes for inference.
  | Hole

  -- | Implicits for synthesis.
  | Implicit

  -- | Builtin terms, with a unique identifying name.
  | Builtin BuiltinTerm

  | Let LetBinding Expr

  -- 'Type'.
  | EType
  deriving (Show, Eq, Ord)


pattern AType :: Expr -> Expr
pattern AType l = App EType l


pattern Inl' :: Expr -> Expr -> Expr -> Expr -> Expr -> Expr
pattern Inl' l1 l2 a b l = App (App (App (App (App (Builtin Inl) l1) l2) a) b) l


pattern Inr' :: Expr -> Expr -> Expr -> Expr -> Expr -> Expr
pattern Inr' l1 l2 a b r = App (App (App (App (App (Builtin Inr) l1) l2) a) b) r


pattern LSuc' :: Expr -> Expr
pattern LSuc' l = App (Builtin LSuc) l


pattern Succ' :: Expr -> Expr
pattern Succ' l = App (Builtin DNSucc) l


pattern Zero' :: Expr
pattern Zero' = Builtin DNZero


-- | Make a new, unnamed, implicit term.
mkImplicit :: Expr
mkImplicit = Implicit


------------------
-- Let bindings --
------------------


data LetBinding
  = LetPatBound Pattern Expr
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
  deriving (Show, Eq, Ord)


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

--------------------
----- Builtins -----
--------------------


data BuiltinTerm =
  -- | Level type.
    LevelTy

  -- | Level zero.
  | LZero

  -- | Level successor.
  | LSuc

  -- | Level maximum.
  | LMax

  -- | Coproduct type.
  | DCoproduct

  -- | inl.
  | Inl

  -- | inr.
  | Inr

  -- | Unit term.
  | DUnitTerm

  -- | Unit type.
  | DUnitTy

  -- | Identity type.
  | IdTy

  -- | Reflexivity.
  | DRefl

  -- | Natural number type.
  | DNat

  -- | Natural number zero.
  | DNZero

  -- | Natural number successor.
  | DNSucc

  -- | Empty type.
  | DEmptyTy
  deriving (Show, Eq, Ord)


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


arrow, at, caset :: Doc
arrow = text "->"
at = char '@'
caset = text "case"


instance Pretty Expr where
    isLexicallyAtomic (Var _) = True
    isLexicallyAtomic LitLevel{} = True
    isLexicallyAtomic Builtin{}  = True
    isLexicallyAtomic Pair{}     = True
    isLexicallyAtomic Hole{}     = True
    isLexicallyAtomic Implicit{} = True
    isLexicallyAtomic EType      = True
    isLexicallyAtomic _       = False

    pprint (LitLevel n)           = integer n
    pprint (Lam ab) = text "\\ " <> pprintAbs arrow ab
    pprint (FunTy ab) = pprintAbs arrow ab
    pprint (ProductTy ab) =
      let leftTyDoc =
            case absVar ab of
              Name _ C.NoName{} -> pprint (absTy ab)
              _        -> pprint (absVar ab) <+> colon <> colon <+> pprint (absTy ab)
      in leftTyDoc <+> char '*' <+> pprint (absExpr ab)
    pprint (App lam@Lam{} e2) =
      pprintParened lam <+> pprintParened e2
    pprint (App (Sig e1 t) e2) =
      pprintParened (Sig e1 t) <+> pprintParened e2
    pprint (App e1 e2) = pprint e1 <+> pprintParened e2
    pprint (Pair e1 e2) = parens (pprint e1 <> comma <+> pprint e2)
    pprint (Coproduct e1 e2) = pprint e1 <+> char '+' <+> pprint e2
    pprint (CoproductCase (Name _ C.NoName{}, Implicit) (x, c) (y, d) e) =
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
    pprint (Sig e t) = pprintParened e <+> colon <+> pprint t
    pprint Hole = char '?'
    pprint Implicit{} = char '_'
    pprint (Builtin s) = pprint s
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

instance Pretty BindName where
  isLexicallyAtomic = isLexicallyAtomic . unBindName
  pprint = pprint . unBindName

instance Pretty BuiltinTerm where
  isLexicallyAtomic _ = True
  pprint LZero     = text "lzero"
  pprint LMax      = text "lmax"
  pprint LSuc      = text "lsuc"
  pprint LevelTy   = text "Level"
  pprint DCoproduct = text "(_+_)"
  pprint Inl       = text "inl"
  pprint Inr       = text "inr"
  pprint DNat      = text "Nat"
  pprint DNZero    = text "zero"
  pprint DNSucc    = text "succ"
  pprint DUnitTy   = text "Unit"
  pprint DUnitTerm = text "unit"
  pprint IdTy      = text "Id"
  pprint DRefl     = text "refl"
  pprint DEmptyTy  = text "Empty"

instance Pretty Name where
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
