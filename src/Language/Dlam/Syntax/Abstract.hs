{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}

module Language.Dlam.Syntax.Abstract
  (
   -- * Expressions
    Expr(..)
  , Name(..)
  , mkIdent
  , ignoreVar
  , mkAbs
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
  , Builtin
  , builtinName
  , builtinBody
  , builtinType
  -- ** Levels
  , levelTy
  , lzero
  , lsuc
  , lsucApp
  , lmax
  , lmaxApp
  -- ** Type Universes
  , typeTy
  , mkUnivTy
  -- ** Coproducts
  , inlTerm
  , inlTermApp
  , inrTerm
  , inrTermApp
  -- ** Natural numbers
  , natTy
  , dnzero
  , dnsucc
  , dnsuccApp
  -- ** Unit
  , unitTy
  , unitTerm
  -- ** Empty type
  , emptyTy
  -- ** Identity
  , idTy
  , idTyApp
  , reflTerm
  , reflTermApp
  ) where


import Prelude hiding ((<>))
import qualified Data.Set as Set

import Language.Dlam.Syntax.Common (NameId(..))
import qualified Language.Dlam.Syntax.Concrete.Name as C
import Language.Dlam.Util.Pretty


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

newtype Abstraction = Abst { getAbst :: (Name, Expr, Expr) }
  deriving (Show, Eq, Ord)

-- | Variable bound in the abstraction.
absVar :: Abstraction -> Name
absVar (Abst (v, _, _)) = v

-- | Type of the bound variable in the abstraction.
absTy :: Abstraction -> Expr
absTy (Abst (_, t, _)) = t

-- | Target expression of the abstraction.
absExpr :: Abstraction -> Expr
absExpr (Abst (_, _, t)) = t

mkAbs :: Name -> Expr -> Expr -> Abstraction
mkAbs v e1 e2 = Abst (v, e1, e2)

data Expr
  -- | Variable.
  = Var Name

  -- | Level literals.
  | LitLevel Int

  -- | Dependent function type.
  | FunTy Abstraction

  -- | Lambda abstraction.
  | Abs Abstraction

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
  deriving (Show, Eq, Ord)


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

  -- | Universe type.
  | TypeTy

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


newtype Builtin = MkBuiltin (Name, BuiltinTerm, Expr)

mkBuiltin :: String -> BuiltinTerm -> Expr -> Builtin
mkBuiltin name exprRef ty = MkBuiltin (mkIdent name, exprRef, ty)

-- | Syntactic name of a builtin term.
builtinName :: Builtin -> Name
builtinName (MkBuiltin (n, _, _)) = n

-- | Body for a builtin term (essentially an Agda postulate).
builtinBody :: Builtin -> Expr
builtinBody (MkBuiltin (_, e, _)) = Builtin e

-- | The type of a builtin term.
builtinType :: Builtin -> Expr
builtinType (MkBuiltin (_, _, t)) = t


mkFunTy :: Name -> Expr -> Expr -> Expr
mkFunTy n t e = FunTy $ mkAbs n t e

typeZero, levelTy', natTy' :: Expr
typeZero = mkUnivTy (LitLevel 0)

mkApp :: Expr -> Expr -> Expr
mkApp = App

levelTy' = builtinBody levelTy

levelTy, lzero, lsuc, lmax,
 typeTy,
 inlTerm, inrTerm,
 unitTy, unitTerm,
 idTy, reflTerm,
 natTy, dnzero, dnsucc,
 emptyTy :: Builtin

levelTy = mkBuiltin "Level" LevelTy typeZero
lzero = mkBuiltin "lzero" LZero levelTy'
lsuc = mkBuiltin "lsuc" LSuc (mkFunTy ignoreVar levelTy' levelTy')
lmax = mkBuiltin "lmax" LMax (mkFunTy ignoreVar levelTy' (mkFunTy ignoreVar levelTy' levelTy'))
typeTy = mkBuiltin "Type" TypeTy
         (let l = mkIdent "l" in mkFunTy l levelTy' (mkUnivTy (lsucApp (Var l))))
inlTerm = mkBuiltin "inl" Inl inlTermTY
  where
    inlTermTY =
      let l1 = mkIdent "l1"; l1v = Var l1
          l2 = mkIdent "l2"; l2v = Var l2
          a = mkIdent "a"; av = Var a
          b = mkIdent "b"; bv = Var b
      in mkFunTy l1 levelTy'
          (mkFunTy l2 levelTy'
           (mkFunTy a (mkUnivTy l1v)
            (mkFunTy b (mkUnivTy l2v)
             (mkFunTy ignoreVar av (Coproduct av bv)))))
inrTerm = mkBuiltin "inr" Inr inrTermTY
  where
    inrTermTY =
      let l1 = mkIdent "l1"; l1v = Var l1
          l2 = mkIdent "l2"; l2v = Var l2
          a = mkIdent "a"; av = Var a
          b = mkIdent "b"; bv = Var b
      in mkFunTy l1 levelTy'
          (mkFunTy l2 levelTy'
           (mkFunTy a (mkUnivTy l1v)
            (mkFunTy b (mkUnivTy l2v)
             (mkFunTy ignoreVar bv (Coproduct av bv)))))

unitTy = mkBuiltin "Unit" DUnitTy typeZero

unitTerm = mkBuiltin "unit" DUnitTerm (builtinBody unitTy)

idTy = mkBuiltin "Id" IdTy idTyTY
  where
    idTyTY :: Expr
    idTyTY =
      let l = mkIdent "l"
          lv = Var l
          a = mkIdent "a"
          av = Var a
      in mkFunTy l levelTy' (mkFunTy a (mkUnivTy lv) (mkFunTy ignoreVar av (mkFunTy ignoreVar av (mkUnivTy lv))))

reflTerm = mkBuiltin "refl" DRefl reflTermTY
  where
    reflTermTY :: Expr
    reflTermTY =
      let l = mkIdent "l"
          lv = Var l
          a = mkIdent "a"
          av = Var a
          x = mkIdent "x"
          xv = Var x
      in mkFunTy l levelTy' (mkFunTy a (mkUnivTy lv) (mkFunTy x av (idTyApp lv av xv xv)))

natTy = mkBuiltin "Nat" DNat typeZero
natTy' = builtinBody natTy
dnzero = mkBuiltin "zero" DNZero natTy'
dnsucc = mkBuiltin "succ" DNSucc (mkFunTy ignoreVar natTy' natTy')
emptyTy = mkBuiltin "Empty" DEmptyTy typeZero


lsucApp :: Expr -> Expr
lsucApp = mkApp (builtinBody lsuc)

lmaxApp :: Expr -> Expr -> Expr
lmaxApp l1 l2 = mkApp (mkApp (builtinBody lmax) l1) l2

mkUnivTy :: Expr -> Expr
mkUnivTy = mkApp (builtinBody typeTy)

inlTermApp :: Expr -> Expr -> Expr -> Expr -> Expr -> Expr
inlTermApp l1 l2 a b v = mkApp (mkApp (mkApp (mkApp (mkApp (builtinBody inlTerm) l1) l2) a) b) v

inrTermApp :: Expr -> Expr -> Expr -> Expr -> Expr -> Expr
inrTermApp l1 l2 a b v = mkApp (mkApp (mkApp (mkApp (mkApp (builtinBody inrTerm) l1) l2) a) b) v

idTyApp :: Expr -> Expr -> Expr -> Expr -> Expr
idTyApp l t x y = mkApp (mkApp (mkApp (mkApp (builtinBody idTy) l) t) x) y

reflTermApp :: Expr -> Expr -> Expr -> Expr
reflTermApp l t x = mkApp (mkApp (mkApp (builtinBody reflTerm) l) t) x

dnsuccApp :: Expr -> Expr
dnsuccApp = mkApp (builtinBody dnsucc)


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
          _        -> parens (pprint (absVar ab) <+> colon <+> pprint (absTy ab))
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
    isLexicallyAtomic _       = False

    pprint (LitLevel n)           = int n
    pprint (Abs ab) = text "\\ " <> pprintAbs arrow ab
    pprint (FunTy ab) = pprintAbs arrow ab
    pprint (ProductTy ab) = pprintAbs (char '*') ab
    pprint (App abs@(Abs _) e2) =
      pprintParened abs <+> pprintParened e2
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
        (hcat $ punctuate (comma <> space)
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

instance Pretty LetBinding where
  pprint (LetPatBound p e) = pprint p <+> equals <+> pprint e

instance Pretty Pattern where
  pprint (PVar v) = pprint v
  pprint (PPair l r) = parens $ pprint l <> comma <+> pprint r
  pprint (PAt v p) = pprint v <> at <> pprint p
  pprint PUnit = char '*'
  pprint (PCon c args) = pprint c <+> (hsep $ fmap pprintParened args)

instance Pretty BindName where
  pprint = pprint . unBindName

instance Pretty BuiltinTerm where
  pprint LZero     = pprint . builtinName $ lzero
  pprint LMax      = pprint . builtinName $ lmax
  pprint LSuc      = pprint . builtinName $ lsuc
  pprint LevelTy   = pprint . builtinName $ levelTy
  pprint TypeTy    = pprint . builtinName $ typeTy
  pprint Inl       = pprint . builtinName $ inlTerm
  pprint Inr       = pprint . builtinName $ inrTerm
  pprint DNat      = pprint . builtinName $ natTy
  pprint DNZero    = pprint . builtinName $ dnzero
  pprint DNSucc    = pprint . builtinName $ dnsucc
  pprint DUnitTy   = pprint . builtinName $ unitTy
  pprint DUnitTerm = pprint . builtinName $ unitTerm
  pprint IdTy      = pprint . builtinName $ idTy
  pprint DRefl     = pprint . builtinName $ reflTerm
  pprint DEmptyTy  = pprint . builtinName $ emptyTy

instance Pretty Name where
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
