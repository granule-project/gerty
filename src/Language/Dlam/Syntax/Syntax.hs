{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Language.Dlam.Syntax.Syntax
  ( Expr(..)
  , Name(..)
  , mkIdent
  , ignoreVar
  , mkAbs
  , absVar
  , absTy
  , absExpr
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

data Name = Ident String | GenIdent (String, Int) | Ignore
  deriving (Show, Eq, Ord)

-- | Create a new identifier from a (syntactic) string.
mkIdent :: String -> Name
mkIdent = Ident

-- | Name for use when the value is unused.
ignoreVar :: Name
ignoreVar = Ignore

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

data Expr where
  -- | Variable.
  Var :: Name -> Expr

  -- | Level literals.
  LitLevel :: Int -> Expr

  -- | Dependent function type.
  FunTy :: Abstraction -> Expr

  -- | Lambda abstraction.
  Abs :: Abstraction -> Expr

  -- | Dependent tensor type.
  ProductTy :: Abstraction -> Expr

  -- | Pairs.
  Pair :: Expr -> Expr -> Expr

  -- | Pair eliminator.
  PairElim :: (Name, Expr) -> (Name, Name, Expr) -> Expr -> Expr

  -- | Coproduct type.
  Coproduct :: Expr -> Expr -> Expr

  -- | Coproduct eliminator.
  CoproductCase :: (Name, Expr) -> (Name, Expr) -> (Name, Expr) -> Expr -> Expr

  -- | Natural number eliminator.
  NatCase :: (Name, Expr) -> Expr -> (Name, Name, Expr) -> Expr -> Expr

  -- | Identity eliminator.
  RewriteExpr :: Name -> Name -> Name -> Expr -> Name -> Expr -> Expr -> Expr -> Expr -> Expr

  -- | Unit eliminator.
  UnitElim :: (Name, Expr) -> Expr -> Expr -> Expr

  -- | Empty eliminator.
  EmptyElim :: (Name, Expr) -> Expr -> Expr

  App :: Expr ->  Expr   -> Expr -- e1 e2

  Sig :: Expr -> Expr       -> Expr -- e : A

  -- | Holes for inference.
  Hole :: Expr

  -- | Implicits for synthesis.
  Implicit :: Expr

  -- | Builtin terms, with a unique identifying name.
  Builtin :: BuiltinTerm -> Expr
  deriving (Show, Eq, Ord)


-- | Make a new, unnamed, implicit term.
mkImplicit :: Expr
mkImplicit = Implicit


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
