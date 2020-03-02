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
  , Term(..)
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

import qualified Data.Set as Set


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


----------------------------

class Term t where
  boundVars :: t -> Set.Set Name
  freeVars  :: t -> Set.Set Name


boundVarsAbs :: Abstraction -> Set.Set Name
boundVarsAbs ab = absVar ab `Set.insert` boundVars (absExpr ab)

freeVarsAbs :: Abstraction -> Set.Set Name
freeVarsAbs ab = Set.delete (absVar ab) (freeVars (absExpr ab))

instance Term Expr where
  boundVars (Abs ab)                     = boundVarsAbs ab
  boundVars (FunTy ab)                   = boundVarsAbs ab
  boundVars (ProductTy ab)               = boundVarsAbs ab
  boundVars (App e1 e2)                  = boundVars e1 `Set.union` boundVars e2
  boundVars (Pair e1 e2)                 = boundVars e1 `Set.union` boundVars e2
  boundVars (Coproduct t1 t2) = boundVars t1 `Set.union` boundVars t2
  boundVars (CoproductCase (_z, _tC) (x, c) (y, d) _e) =
    Set.insert x (Set.insert y (boundVars c `Set.union` boundVars d))
  boundVars (NatCase (x, tC) cz (w, y, cs) _n) =
    Set.insert w $ Set.insert x $ Set.insert y (boundVars cz `Set.union` boundVars cs `Set.union` boundVars tC)
  boundVars (Var _)                      = Set.empty
  boundVars (Sig e _)                    = boundVars e
  boundVars Hole                         = Set.empty
  boundVars Implicit                     = Set.empty
  boundVars LitLevel{}                   = Set.empty
  boundVars Builtin{}                    = Set.empty
  boundVars (PairElim (z, tC) (x, y, g) p) =
    Set.insert z (x `Set.insert` (y `Set.insert` (boundVars g `Set.union` boundVars p `Set.union` boundVars tC)))
  -- TODO: I'm not entirely convinced the boundVars for RewriteExpr is actually correct (2020-02-27)
  boundVars (RewriteExpr _x _y _p _tC _z c _a _b _p') = boundVars c
  boundVars (UnitElim (x, tC) c a) =
    Set.insert x $ boundVars tC `Set.union` boundVars c `Set.union` boundVars a
  boundVars (EmptyElim (x, tC) a) =
    Set.insert x $ boundVars tC `Set.union` boundVars a

  freeVars (FunTy ab)                    = freeVarsAbs ab
  freeVars (Abs ab)                      = freeVarsAbs ab
  freeVars (ProductTy ab)                = freeVarsAbs ab
  freeVars (App e1 e2)                   = freeVars e1 `Set.union` freeVars e2
  freeVars (Pair e1 e2)                  = freeVars e1 `Set.union` freeVars e2
  freeVars (Coproduct t1 t2) = freeVars t1 `Set.union` freeVars t2
  freeVars (CoproductCase (_z, _tC) (x, c) (y, d) _e) =
    Set.delete x (Set.delete y (freeVars c `Set.union` freeVars d))
  freeVars (NatCase (x, tC) cz (w, y, cs) _n) =
    (Set.delete x (freeVars tC)) `Set.union` (freeVars cz) `Set.union` (Set.delete w $ Set.delete y $ freeVars cs)
  freeVars (Var var)                     = Set.singleton var
  freeVars (Sig e _)                     = freeVars e
  freeVars (PairElim (z, tC) (x, y, g) p) =
    Set.delete z (Set.delete x (Set.delete y (freeVars g `Set.union` freeVars p `Set.union` freeVars tC)))
  -- TODO: I'm not entirely convinced the freeVars for RewriteExpr is actually correct (2020-02-27)
  freeVars (RewriteExpr _x _y _p _tC _z c _a _b _p') = freeVars c
  freeVars (UnitElim (x, tC) c a) =
    Set.delete x $ freeVars tC `Set.union` (freeVars c `Set.union` freeVars a)
  freeVars (EmptyElim (x, tC) a) =
    Set.delete x $ freeVars tC `Set.union` freeVars a
  freeVars Hole                          = Set.empty
  freeVars Implicit                      = Set.empty
  freeVars LitLevel{}                    = Set.empty
  freeVars Builtin{}                     = Set.empty
