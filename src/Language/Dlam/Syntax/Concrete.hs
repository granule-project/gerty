{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}

module Language.Dlam.Syntax.Concrete
  (
  -- * Names
    module Language.Dlam.Syntax.Concrete.Name
  , OneOrMoreBoundNames
  -- * Expressions
  , Expr(..)

  -- ** Grading
  , Grade(..)
  , Grading
  , mkGrading
  , grading
  , subjectGrade
  , subjectTypeGrade
  , implicitGrade

  -- ** Naming
  , MaybeNamed(..)
  -- ** Bindings
  , Binds(..)
  , mkArg
  , BoundName
  , bindName
  , unBoundName
  , Param(..)
  , LambdaBinding
  , LambdaArg
  , LambdaArgs
  , TypedBinding
  , unTB
  , mkTypedBinding
  , PiBindings(..)
  , lambdaBindingFromTyped
  , lambdaArgFromTypedBinding
  -- ** Let bindings and patterns
  , CaseBinding(..)
  , Pattern(..)
  -- * AST
  , AST(..)
  -- ** Declarations
  , FLHS(..)
  , FRHS(..)
  , Declaration(..)
  , mkImplicit
  ) where


import Prelude hiding ((<>))
import qualified Data.List.NonEmpty as NE

import Language.Dlam.Syntax.Concrete.Name
import Language.Dlam.Syntax.Common
import qualified Language.Dlam.Syntax.Common.Language as C
import Language.Dlam.Syntax.Common.Language (Binds, IsTyped)
import Language.Dlam.Util.Pretty


------------------------------
----- Language Specifics -----
------------------------------


type Type = Expr
type Typed = C.Typed Expr
type Grading = C.Grading Grade
type Graded = C.Graded Grade
type BoundName = C.BoundName Name
type OneOrMoreBoundNames = C.OneOrMoreBoundNames Name
typedWith :: a -> Type -> Typed a
typedWith = C.typedWith
gradedWith :: a -> Grading -> Graded a
gradedWith = C.gradedWith
typeOf :: (IsTyped a Type) => a -> Type
typeOf = C.typeOf
grading :: (C.IsGraded a Grade) => a -> Grading
grading = C.grading
subjectGrade, subjectTypeGrade :: (C.IsGraded a Grade) => a -> Grade
subjectGrade = C.subjectGrade
subjectTypeGrade = C.subjectTypeGrade
mkGrading :: Grade -> Grade -> Grading
mkGrading = C.mkGrading
bindName :: Name -> BoundName
bindName = C.bindName
unBoundName :: BoundName -> Name
unBoundName = C.unBoundName
bindsWhat :: (Binds a Name) => a -> [BoundName]
bindsWhat = C.bindsWhat


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


-- | A Param either captures some typed names, or an @a@.
data Param a = ParamNamed TypedBinding | ParamUnnamed a
  deriving (Show, Eq, Ord)


-- | Lambda abstraction binder.
type LambdaArg = Arg (MightBe (Typed `ThenMightBe` Graded) OneOrMoreBoundNames)


mkLambdaArg :: IsHiddenOrNot -> OneOrMoreBoundNames -> Maybe (Expr, Maybe Grading) -> LambdaArg
mkLambdaArg isHid names tyGrad =
  mkArg isHid
    (maybe (itIsNot names)                                          -- no type or grades
     (\(ty, mg) -> itIs (maybe                                      -- at least a type
       (onlyFirst (`typedWith` ty))                                 -- type but no grades
       (\g -> wasBoth (`typedWith` ty) (`gradedWith` g)) mg) names) -- type and grades
     tyGrad)


lambdaArgFromTypedBinding :: TypedBinding -> LambdaArg
lambdaArgFromTypedBinding e =
  let isHid = isHidden  e
      ty    = typeOf    e
      names = bindsWhat e
      grades = tryIt grading (un (unTB e))
  in mkLambdaArg isHid (NE.fromList names) (Just (ty, grades))


type LambdaArgs = [LambdaArg]


data BoundTo b e = BoundTo { boundToWhat :: b, whatWasBound :: e }
  deriving (Show, Eq, Ord)


instance (Pretty b, Pretty e) => Pretty (BoundTo b e) where
  pprint b = pprint (boundToWhat b) <+> colon <+> pprint (whatWasBound b)


-- | The left-hand-side of a function type.
type LambdaBinding = Arg (MightBe (BoundTo OneOrMoreBoundNames) Expr)


lambdaBindingFromTyped :: TypedBinding -> LambdaBinding
lambdaBindingFromTyped tb =
  let boundNames = NE.fromList $ bindsWhat tb
      ty         = typeOf tb
  in mkArg (isHidden tb) (itIs (BoundTo boundNames) ty)


------------------
----- Naming -----
------------------


data MaybeNamed a = Named Name a | Unnamed a
  deriving (Show, Eq, Ord)


instance Un MaybeNamed where
  un (Named _ e) = e
  un (Unnamed e) = e


instance (Pretty e) => Pretty (Graded (Typed e)) where
  pprint x =
    let ty = typeOf x
        grades = grading x
        val = un . un $ x
    in pprint val <+> colon <+> pprint grades <+> pprint ty


-- | Typed binders are optionally graded, and can contain many bound names.
newtype TypedBinding = TB { unTB :: Arg (MightBe Graded (Typed OneOrMoreBoundNames)) }
  deriving (Show, Eq, Ord, Hiding)


instance Binds TypedBinding Name where
  bindsWhat = bindsWhat . unTB


instance IsTyped TypedBinding Expr where
  typeOf = typeOf . un . un . unTB


mkTypedBinding :: IsHiddenOrNot -> OneOrMoreBoundNames -> Maybe Grading -> Expr -> TypedBinding
mkTypedBinding isHid names grading t =
  let typedNames = names `typedWith` t
  in TB . mkArg isHid $ maybe
       (itIsNot typedNames)                             -- we just have a type
       (\g -> itIs (`gradedWith` g) typedNames) grading -- we have a type and grade


-- | A list of typed bindings in a dependent function space.
newtype PiBindings = PiBindings [TypedBinding]
  deriving (Show, Eq, Ord)


data Declaration
  -- | A single clause for a function.
  = FunEqn FLHS FRHS
  -- | A type signature.
  | TypeSig Name Expr
  -- | A record definition.
  | RecordDef Name (Maybe Name) [LambdaBinding] Expr [Declaration]
  -- | A record field.
  | Field Name Expr
  deriving (Show)


data Expr
  -- | Variable.
  = Ident QName

  -- | Dependent function space.
  | Pi PiBindings Expr

  -- | Non-dependent function space.
  | Fun Expr Expr

  -- | Lambda abstraction.
  | Lam LambdaArgs Expr

  -- | Non-dependent tensor type.
  | NondepProductTy Expr Expr

  -- | Dependent tensor type.
  | ProductTy (Name, Grade, Expr) Expr

  -- | Pairs.
  | Pair Expr Expr

  | App Expr Expr -- e1 e2

  | Sig Expr Expr -- e : A

  -- | Typing universe without a specified level (@Type@).
  | UniverseNoLevel

  -- | Typing universe with a specified level (@Type l@).
  | Universe Integer

  -- | Holes for inference.
  | Hole

  -- | Implicits for synthesis.
  | Implicit

  | Case Expr (Maybe (Pattern, Expr)) (NE.NonEmpty CaseBinding)
  -- ^ Case binding (@case t1 of pat1 -> e1;... patn -> en@).

  -- | Argument wrapped in braces.
  | BraceArg (MaybeNamed Expr)

  -- | Graded modal type @A [s, r]@.
  | BoxTy (Grade, Grade) Expr

  -- | Graded modal intro @[t]@.
  | Box Expr

  -- | Unit type @Unit@.
  | UnitTy

  -- | Unit value @*@.
  | Unit

  -- | An expression in parentheses.
  | Parens Expr
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


data Pattern
  = PIdent QName
  -- ^ x. (or could be a constructor).
  | PAt  Name Pattern
  -- ^ x@p.
  | PPair Pattern Pattern
  -- ^ (p1, p2).
  | PUnit
  -- ^ unit (*).
  | PApp QName [Pattern]
  -- ^ Constructor application.
  | PParens Pattern
  -- ^ Pattern in parentheses.
  | PBox Pattern
  -- ^ Pattern in box.
  deriving (Show, Eq, Ord)


------------------
----- Grades -----
------------------


-- | Syntactic form of grades.
data Grade

  -- | Zero grade @0@.
  = GZero

  -- | One grade @1@.
  | GOne

  -- | Arbitrary use grade @.inf@.
  | GInf

  -- | Grade addition @s .+ r@.
  | GPlus Grade Grade

  -- | Grade multiplication @s .* r@.
  | GTimes Grade Grade

  -- | Least-upper bound @s .lub r@.
  | GLub Grade Grade

  -- | Representation for other grade elements.
  | GExpr Expr

  -- | Grade with signature @s : t@.
  | GSig Grade Expr

  -- | Grade in parentheses @( s )@.
  | GParens Grade
  deriving (Show, Eq, Ord)


implicitGrade :: Grade
implicitGrade = GExpr Implicit


---------------------------
----- Pretty printing -----
---------------------------


arrow, at :: Doc
arrow = text "->"
at = char '@'


instance (Pretty e) => Pretty (MaybeNamed e) where
  isLexicallyAtomic (Unnamed e) = isLexicallyAtomic e
  isLexicallyAtomic _ = False

  pprint (Named n e) = pprint n <+> equals <+> pprint e
  pprint (Unnamed e) = pprint e


instance Pretty Expr where
    isLexicallyAtomic (Ident _)  = True
    isLexicallyAtomic Pair{}     = True
    isLexicallyAtomic Hole{}     = True
    isLexicallyAtomic Implicit{} = True
    isLexicallyAtomic BraceArg{} = True
    isLexicallyAtomic Parens{}   = True
    isLexicallyAtomic UniverseNoLevel = True
    isLexicallyAtomic _          = False

    pprint UniverseNoLevel        = text "Type"
    pprint UnitTy                 = text "Unit"
    pprint Unit                   = text "unit"
    pprint (BoxTy (g1, g2) e) =
      pprintParened e <+> brackets ((pprint g1 <> char ',') <+> pprint g2)
    pprint (Box e) = brackets (pprint e)
    pprint (Universe l)           = text "Type" <+> integer l
    pprint (Lam binders finE) =
      text "\\" <+> (hsep $ fmap pprint binders) <+> arrow <+> pprint finE
    pprint (Pi binders finTy) = pprint binders <+> arrow <+> pprint finTy
    pprint (Fun i@Fun{} o) = pprintParened i <+> arrow <+> pprint o
    pprint (Fun i o) = pprint i <+> arrow <+> pprint o
    pprint (NondepProductTy t1 t2) = pprintParened t1 <+> char '*' <+> pprintParened t2
    pprint (ProductTy (n, r, t1) t2) =
      pprint n <+> colon <> colon <+> pprintParened r <+> pprint t1
        <+> char '*' <+> pprint t2
    pprint (App lam@Lam{} e2) =
      pprintParened lam <+> pprintParened e2
    pprint (App (Sig e1 t) e2) =
      pprintParened (Sig e1 t) <+> pprintParened e2
    pprint (App e1 e2) = pprint e1 <+> pprintParened e2
    pprint (Pair e1 e2) = parens (pprint e1 <> comma <+> pprint e2)
    pprint (Ident var) = pprint var
    pprint (Sig e t) = pprintParened e <+> colon <+> pprint t
    pprint Hole = char '?'
    pprint Implicit{} = char '_'
    pprint (Case e Nothing binds) =
      hang ("case" <+> pprint e <+> "of") 1 (vcat . NE.toList $ fmap pprint binds)
    pprint (Case e (Just (p, t)) binds) =
      hang ("case" <+> pprint e <+> "as" <+> pprint p <+> "in" <+> pprint t <+> "of")
             1 (vcat . NE.toList $ fmap pprint binds)
    pprint (BraceArg e) = braces $ pprint e
    pprint (Parens e)   = parens $ pprint e

instance Pretty CaseBinding where
  pprint (CasePatBound p e) = pprint p <+> arrow <+> pprint e

instance Pretty Pattern where
  isLexicallyAtomic PIdent{} = True
  isLexicallyAtomic PPair{}  = True
  isLexicallyAtomic PAt{}    = True
  isLexicallyAtomic PUnit    = True
  isLexicallyAtomic _        = False

  pprint (PIdent v) = pprint v
  pprint (PPair l r) = parens $ pprint l <> comma <+> pprint r
  pprint (PAt v p) = pprint v <> at <> pprint p
  pprint (PApp v args) = pprint v <+> (hsep $ fmap pprintParened args)
  pprint PUnit = text "unit"
  pprint (PParens p) = parens $ pprint p
  pprint (PBox p) = brackets $ pprint p

instance Pretty Grade where
  isLexicallyAtomic GZero = True
  isLexicallyAtomic GOne = True
  isLexicallyAtomic GInf = True
  isLexicallyAtomic (GExpr g) = isLexicallyAtomic g
  isLexicallyAtomic _ = False

  pprint GZero = text ".0"
  pprint GOne  = text ".1"
  pprint GInf = text ".inf"
  pprint (GPlus g1 g2) = pprintSquishy 0 (g1, g2)
    where pprintSquishy n (GZero, GZero) = char '.' <> integer n
          pprintSquishy n (GOne,  r) = pprintSquishy (n+1) (GZero, r)
          pprintSquishy n (s, GOne) = pprintSquishy (n+1) (s, GZero)
          pprintSquishy n (GPlus GOne s, r) = pprintSquishy (n+1) (s, r)
          pprintSquishy n (GPlus s GOne, r) = pprintSquishy (n+1) (s, r)
          pprintSquishy n (s, GPlus GOne r) = pprintSquishy (n+1) (s, r)
          pprintSquishy n (s, GPlus r GOne) = pprintSquishy (n+1) (s, r)
          pprintSquishy n (GZero, r) = (char '.' <> integer n) <+> char '+' <+> pprintParened r
          pprintSquishy n (s, GZero) = (char '.' <> integer n) <+> char '+' <+> pprintParened s
          pprintSquishy n (s, r) = (char '.' <> integer n) <+> char '+' <+> pprintParened s <+> char '+' <+> pprint r
  pprint (GTimes g1 g2) = pprintParened g1 <+> text "*" <+> pprintParened g2
  pprint (GLub g1 g2) = pprintParened g1 <+> text "lub" <+> pprintParened g2
  pprint (GExpr g) = pprint g
  pprint (GSig g s) = pprintParened g <+> char ':' <+> pprintParened s
  pprint (GParens g) = parens (pprint g)

instance Pretty Grading where
  pprint g = char '[' <>
             pprint (subjectGrade g) <> comma <+> pprint (subjectTypeGrade g) <> char ']'

instance Pretty TypedBinding where
  isLexicallyAtomic _ = True

  pprint tb =
    let names = bindsWhat tb
        ty    = typeOf tb
        grads = tryIt grading (un $ unTB tb)
    in (if isHidden' tb then braces else parens) $
       pprint names <+> colon <+> maybe empty pprint grads <+> pprint ty

instance Pretty PiBindings where
  pprint (PiBindings binds) = hsep (fmap pprint binds)

instance Pretty AST where
  pprint (AST decls) = vcat $ fmap pprint decls

instance Pretty FLHS where
  pprint (FLHSName n) = pprint n

instance Pretty FRHS where
  pprint (FRHSAssign e) = equals <+> pprint e

instance (Pretty a) => Pretty (Param a) where
  isLexicallyAtomic (ParamNamed nb) = isLexicallyAtomic nb
  isLexicallyAtomic (ParamUnnamed a) = isLexicallyAtomic a

  pprint (ParamNamed nb) = pprint nb
  pprint (ParamUnnamed a) = pprint a

instance Pretty Declaration where
  pprint (TypeSig n t) = pprint n <+> colon <+> pprint t
  pprint (FunEqn lhs rhs) = pprint lhs <+> pprint rhs
  pprint (RecordDef n con params ty decls) =
    text "record" <+> pprint n <+> hsep (fmap pprint params) <+> colon <+> pprint ty <+> text "where"
         $+$ vcat (fmap (nest 2) $ (maybe empty (\conName -> (text "constructor" <+> pprint conName)) con) : fmap pprint decls)
  pprint (Field n e) = text "field" <+> pprint n <+> colon <+> pprint e
