{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Language.Dlam.Syntax.Syntax
  ( Expr(..)
  , Identifier(..)
  , mkIdent
  , ignoreVar
  , NoExt
  , Term(..)
  , mkAbs
  , absVar
  , absTy
  , absExpr
  , AST(..)
  , Stmt(..)
  , NAST(..)
  , NStmt(..)
  , normaliseAST
  , Abstraction
  , mkImplicit

  -- * Helpers
  , Default(..)

  -- * Annotations
  , NoAnn

  -- * Builtins
  , BuiltinTerm(..)
  , builtinTerm
  -- ** Levels
  , levelTy
  , levelTyTY
  , lzero
  , lzeroTY
  , lsuc
  , lsucTY
  , lsucApp
  , lmax
  , lmaxTY
  , lmaxApp
  -- ** Type Universes
  , typeTy
  , typeTyTY
  , mkUnivTy
  -- ** Booleans
  , dBool
  , dBoolTY
  , dtrue
  , dtrueTY
  , dfalse
  , dfalseTY
  -- ** Unit
  , unitTy
  , unitTyTY
  , unitTerm
  , unitTermTY
  ) where

import qualified Data.Set as Set


-------------------
----- Helpers -----
-------------------


-- | Class for types that have a default value.
class Default a where
  -- | The default value.
  def :: a


----------------
-- Statements --
----------------

newtype AST ann e = AST [Stmt ann e]
  deriving Show

data Stmt ann e =
  -- | Assignment to a name.
    StmtAssign String (Expr ann e)
  -- | Type assignment.
  | StmtType String (Expr ann e)
  deriving Show

newtype NAST ann e = NAST [NStmt ann e]
  deriving Show

data NStmt ann e =
  -- | An assignment with an optional type, and mandatory definition.
  Decl String (Maybe (Expr ann e)) (Expr ann e)
  deriving Show

-- | Normalise the raw AST into a form appropriate for further analyses.
-- TODO: add a better error system (2020-02-19)
normaliseAST :: AST ann e -> NAST ann e
normaliseAST (AST []) = NAST []
normaliseAST (AST ((StmtType v t):(StmtAssign v' e):sts))
  | v == v' = let (NAST xs) = normaliseAST (AST sts) in NAST ((Decl v (Just t) e):xs)
  | otherwise = error $ "type declaration for '" <> v <> "' followed by an assignment to '" <> v' <> "'"
normaliseAST (AST ((StmtAssign v e):sts)) =
  let (NAST xs) = normaliseAST (AST sts) in NAST ((Decl v Nothing e) : xs)
normaliseAST (AST [StmtType v _]) =
  error $ "expected an assignment to '" <> v <> "' but reached end of file"
normaliseAST (AST ((StmtType v _):StmtType{}:_)) =
  error $ "expected an assignment to '" <> v <> "' but got another type assignment"

data Identifier = Ident String | GenIdent (String, Int) | Ignore
  deriving (Show, Eq, Ord)

-- | Create a new identifier from a (syntactic) string.
mkIdent :: String -> Identifier
mkIdent = Ident

-- | Identifier for use when the value is unused.
ignoreVar :: Identifier
ignoreVar = Ignore

newtype Abstraction ann ext = Abst { getAbst :: (Identifier, Expr ann ext, Expr ann ext) }
  deriving (Show, Eq, Ord)

-- | Variable bound in the abstraction.
absVar :: Abstraction ann ex -> Identifier
absVar (Abst (v, _, _)) = v

-- | Type of the bound variable in the abstraction.
absTy :: Abstraction ann ex -> Expr ann ex
absTy (Abst (_, t, _)) = t

-- | Target expression of the abstraction.
absExpr :: Abstraction ann ex -> Expr ann ex
absExpr (Abst (_, _, t)) = t

mkAbs :: Identifier -> Expr ann ext -> Expr ann ext -> Abstraction ann ext
mkAbs v e1 e2 = Abst (v, e1, e2)

-- Abstract-syntax tree for LambdaCore
-- parameterised by an additional type `ex`
-- used to represent the abstract syntax
-- tree of additional commands
data Expr ann ex where
  -- | Variable.
  Var :: ann -> Identifier -> Expr ann ex

  -- | Level literals.
  LitLevel :: ann -> Int -> Expr ann ex

  -- | Dependent function type.
  FunTy :: ann -> Abstraction ann ex -> Expr ann ex

  -- | Lambda abstraction.
  Abs :: ann -> Abstraction ann ex -> Expr ann ex

  -- | Dependent tensor type.
  ProductTy :: ann -> Abstraction ann ex -> Expr ann ex

  -- | Pairs.
  Pair :: ann -> Expr ann ex -> Expr ann ex -> Expr ann ex

  -- | Pair eliminator.
  PairElim :: ann -> Identifier -> Identifier -> Identifier -> Expr ann ex -> Expr ann ex -> Expr ann ex -> Expr ann ex

  -- | Conditional eliminator.
  IfExpr :: ann -> Expr ann ex -> Expr ann ex -> Expr ann ex -> Expr ann ex

  App :: ann -> Expr ann ex ->  Expr ann ex   -> Expr ann ex -- e1 e2

  Sig :: ann -> Expr ann ex -> Expr ann ex       -> Expr ann ex -- e : A

  -- | Holes for inference.
  Hole :: ann -> Expr ann ex

  -- | Implicits for synthesis.
  Implicit :: ann -> Expr ann ex

  -- | Builtin terms, with a unique identifying name.
  Builtin :: ann -> BuiltinTerm -> Expr ann ex

  -- ML
  GenLet :: ann -> Identifier -> Expr ann ex -> Expr ann ex -> Expr ann ex -- let x = e1 in e2 (ML-style polymorphism)

  -- | AST extensions.
  Ext :: ann -> ex -> Expr ann ex
  deriving (Show, Eq, Ord)


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

  -- | Boolean type.
  | DBool

  -- | True.
  | DTrue

  -- | False.
  | DFalse

  -- | Unit term.
  | DUnitTerm

  -- | Unit type.
  | DUnitTy
  deriving (Show, Eq, Ord)


------------------------------------
-- Helpers for constructing terms --
------------------------------------


-- | Make a new, unnamed, implicit term.
mkImplicit :: (Default ann) => Expr ann e
mkImplicit = Implicit def


-- | 'Type 0' term.
typeZero :: (Default ann) => Expr ann e
typeZero = mkUnivTy (LitLevel def 0)


-- | Body for a builtin term (essentially an Agda postulate).
builtinTerm :: (Default ann) => BuiltinTerm -> Expr ann e
builtinTerm = Builtin def


levelTy, levelTyTY, lzero, lzeroTY, lsuc, lsucTY, lmax, lmaxTY, typeTy,
  typeTyTY, dBool, dBoolTY, dtrue, dtrueTY, dfalse, dfalseTY, unitTy,
  unitTyTY, unitTerm, unitTermTY ::
  (Default ann) => Expr ann e


levelTy = builtinTerm LevelTy

levelTyTY = typeZero

lzero = builtinTerm LZero

lzeroTY = levelTy

lsuc = builtinTerm LSuc

lsucTY = FunTy def (mkAbs ignoreVar levelTy levelTy)

lsucApp :: (Default ann) => Expr ann e -> Expr ann e
lsucApp = App def lsuc

lmax = builtinTerm LMax

lmaxTY = FunTy def (mkAbs ignoreVar levelTy (FunTy def (mkAbs ignoreVar levelTy levelTy)))

lmaxApp :: (Default ann) => Expr ann e -> Expr ann e -> Expr ann e
lmaxApp l1 l2 = App def (App def lmax l1) l2

typeTy = builtinTerm TypeTy

typeTyTY = let l = mkIdent "l" in FunTy def (mkAbs l levelTy (mkUnivTy (lsucApp (Var def l))))

mkUnivTy :: (Default ann) => Expr ann e -> Expr ann e
mkUnivTy = App def typeTy

dBool = builtinTerm DBool

dBoolTY = typeZero

dtrue = builtinTerm DTrue

dtrueTY = dBool

dfalse = builtinTerm DFalse

dfalseTY = dBool

unitTy = builtinTerm DUnitTy

unitTyTY = typeZero

unitTerm = builtinTerm DUnitTerm

unitTermTY = unitTy

----------------------------

class Term t where
  boundVars :: t -> Set.Set Identifier
  freeVars  :: t -> Set.Set Identifier

-- | For minimal language with no extensions.
data NoExt
  deriving Ord

instance Eq NoExt where
  _ == _ = True

instance Show NoExt where
  show _ = undefined


type NoAnn = ()


instance Default NoAnn where
  def = ()


boundVarsAbs :: (Term (Expr ann e)) => Abstraction ann e -> Set.Set Identifier
boundVarsAbs ab = absVar ab `Set.insert` boundVars (absExpr ab)

freeVarsAbs :: (Term (Expr ann e)) => Abstraction ann e -> Set.Set Identifier
freeVarsAbs ab = Set.delete (absVar ab) (freeVars (absExpr ab))

instance (Term e) => Term (Expr ann e) where
  boundVars (Abs _ ab)                     = boundVarsAbs ab
  boundVars (FunTy _ ab)                   = boundVarsAbs ab
  boundVars (ProductTy _ ab)               = boundVarsAbs ab
  boundVars (App _ e1 e2)                  = boundVars e1 `Set.union` boundVars e2
  boundVars (Pair _ e1 e2)                 = boundVars e1 `Set.union` boundVars e2
  boundVars (IfExpr _ e1 e2 e3)            = boundVars e1 `Set.union` boundVars e2 `Set.union` boundVars e3
  boundVars (Var _ _)                      = Set.empty
  boundVars (Sig _ e _)                    = boundVars e
  boundVars (GenLet _ var e1 e2)           = var `Set.insert` (boundVars e1 `Set.union` boundVars e2)
  boundVars (Ext _ e)                      = boundVars e
  boundVars Hole{}                       = Set.empty
  boundVars Implicit{}                   = Set.empty
  boundVars LitLevel{}                   = Set.empty
  boundVars Builtin{}                    = Set.empty
  boundVars (PairElim _ z x y e1 e2 e3)  =
    Set.insert z (x `Set.insert` (y `Set.insert` (boundVars e1 `Set.union` boundVars e2 `Set.union` boundVars e3)))

  freeVars (FunTy _ ab)                    = freeVarsAbs ab
  freeVars (Abs _ ab)                      = freeVarsAbs ab
  freeVars (ProductTy _ ab)                = freeVarsAbs ab
  freeVars (App _ e1 e2)                   = freeVars e1 `Set.union` freeVars e2
  freeVars (Pair _ e1 e2)                  = freeVars e1 `Set.union` freeVars e2
  freeVars (IfExpr _ e1 e2 e3)             = freeVars e1 `Set.union` freeVars e2 `Set.union` freeVars e3
  freeVars (Var _ var)                     = Set.singleton var
  freeVars (Sig _ e _)                     = freeVars e
  freeVars (GenLet _ var e1 e2)            = Set.delete var (freeVars e1 `Set.union` freeVars e2)
  freeVars (PairElim _ z x y e1 e2 e3)     =
    Set.delete z (Set.delete x (Set.delete y (freeVars e1 `Set.union` freeVars e2 `Set.union` freeVars e3)))
  freeVars (Ext _ e)                       = freeVars e
  freeVars Hole{}                        = Set.empty
  freeVars Implicit{}                    = Set.empty
  freeVars LitLevel{}                    = Set.empty
  freeVars Builtin{}                     = Set.empty

instance Term NoExt where
  boundVars _ = undefined
  freeVars  _ = undefined
