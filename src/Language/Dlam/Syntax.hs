{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Language.Dlam.Syntax
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

----------------
-- Statements --
----------------

newtype AST e = AST [Stmt e]
  deriving Show

data Stmt e =
  -- | Assignment to a name.
    StmtAssign String (Expr e)
  -- | Type assignment.
  | StmtType String (Expr e)
  deriving Show

newtype NAST e = NAST [NStmt e]
  deriving Show

data NStmt e =
  -- | An assignment with an optional type, and mandatory definition.
  Decl String (Expr e) (Expr e)
  deriving Show

-- | Normalise the raw AST into a form appropriate for further analyses.
-- TODO: add a better error system (2020-02-19)
normaliseAST :: AST e -> NAST e
normaliseAST (AST []) = NAST []
normaliseAST (AST ((StmtType v t):(StmtAssign v' e):sts))
  | v == v' = let (NAST xs) = normaliseAST (AST sts) in NAST ((Decl v t e):xs)
  | otherwise = error $ "type declaration for '" <> v <> "' followed by an assignment to '" <> v' <> "'"
normaliseAST (AST ((StmtAssign v e):sts)) =
  let (NAST xs) = normaliseAST (AST sts) in NAST ((Decl v Wild e) : xs)
normaliseAST (AST [StmtType v _]) =
  error $ "expected an assignment to '" <> v <> "' but reached end of file"
normaliseAST (AST ((StmtType v _):(StmtType _ _):_)) =
  error $ "expected an assignment to '" <> v <> "' but got another type assignment"

data Identifier = Ident String | GenIdent (String, Int) | Ignore
  deriving (Show, Eq, Ord)

-- | Create a new identifier from a (syntactic) string.
mkIdent :: String -> Identifier
mkIdent = Ident

-- | Identifier for use when the value is unused.
ignoreVar :: Identifier
ignoreVar = Ignore

newtype Abstraction ext = Abst { getAbst :: (Identifier, Expr ext, Expr ext) }
  deriving (Show, Ord)

deriving instance (Eq ext) => Eq (Abstraction ext)

-- | Variable bound in the abstraction.
absVar :: Abstraction ex -> Identifier
absVar (Abst (v, _, _)) = v

-- | Type of the bound variable in the abstraction.
absTy :: Abstraction ex -> Expr ex
absTy (Abst (_, t, _)) = t

-- | Target expression of the abstraction.
absExpr :: Abstraction ex -> Expr ex
absExpr (Abst (_, _, t)) = t

mkAbs :: Identifier -> Expr ext -> Expr ext -> Abstraction ext
mkAbs v e1 e2 = Abst (v, e1, e2)

-- Abstract-syntax tree for LambdaCore
-- parameterised by an additional type `ex`
-- used to represent the abstract syntax
-- tree of additional commands
data Expr ex where
  -- | Variable.
  Var :: Identifier -> Expr ex

  -- | Level literals.
  LitLevel :: Int -> Expr ex

  -- | Dependent function type.
  FunTy :: Abstraction ex -> Expr ex

  -- | Lambda abstraction.
  Abs :: Abstraction ex -> Expr ex

  -- | Dependent tensor type.
  ProductTy :: Abstraction ex -> Expr ex

  -- | Pairs.
  Pair :: Expr ex -> Expr ex -> Expr ex

  -- | Pair eliminator.
  PairElim :: Identifier -> Identifier -> Identifier -> Expr ex -> Expr ex -> Expr ex -> Expr ex

  -- | Conditional eliminator.
  IfExpr :: Expr ex -> Expr ex -> Expr ex -> Expr ex

  App :: Expr ex ->  Expr ex   -> Expr ex -- e1 e2

  Sig :: Expr ex -> Expr ex       -> Expr ex -- e : A

  -- | Wildcards for inference.
  Wild :: Expr ex

  -- | Builtin terms, with a unique identifying name.
  Builtin :: BuiltinTerm -> Expr ex

  -- ML
  GenLet :: Identifier -> Expr ex -> Expr ex -> Expr ex -- let x = e1 in e2 (ML-style polymorphism)

  -- | AST extensions.
  Ext :: ex -> Expr ex
  deriving (Show, Ord)

deriving instance (Eq ext) => Eq (Expr ext)


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


-- | Body for a builtin term (essentially an Agda postulate).
builtinTerm :: BuiltinTerm -> Expr e
builtinTerm = Builtin

levelTy :: Expr e
levelTy = builtinTerm LevelTy

levelTyTY :: Expr e
levelTyTY = mkUnivTy (LitLevel 0)

lzero :: Expr e
lzero = builtinTerm LZero

lzeroTY :: Expr e
lzeroTY = levelTy

lsuc :: Expr e
lsuc = builtinTerm LSuc

lsucTY :: Expr e
lsucTY = FunTy (mkAbs ignoreVar levelTy levelTy)

lsucApp :: Expr e -> Expr e
lsucApp = App lsuc

lmax :: Expr e
lmax = builtinTerm LMax

lmaxTY :: Expr e
lmaxTY = FunTy (mkAbs ignoreVar levelTy (FunTy (mkAbs ignoreVar levelTy levelTy)))

lmaxApp :: Expr e -> Expr e -> Expr e
lmaxApp l1 l2 = App (App lmax l1) l2

typeTy :: Expr e
typeTy = builtinTerm TypeTy

typeTyTY :: Expr e
typeTyTY = let l = mkIdent "l" in FunTy (mkAbs l levelTy (mkUnivTy (lsucApp (Var l))))

mkUnivTy :: Expr e -> Expr e
mkUnivTy = App typeTy

dBool :: Expr e
dBool = builtinTerm DBool

dBoolTY :: Expr e
dBoolTY = mkUnivTy (LitLevel 0)

dtrue :: Expr e
dtrue = builtinTerm DTrue

dtrueTY :: Expr e
dtrueTY = dBool

dfalse :: Expr e
dfalse = builtinTerm DFalse

dfalseTY :: Expr e
dfalseTY = dBool

unitTy :: Expr e
unitTy = builtinTerm DUnitTy

unitTyTY :: Expr e
unitTyTY = mkUnivTy (LitLevel 0)

unitTerm :: Expr e
unitTerm = builtinTerm DUnitTerm

unitTermTY :: Expr e
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


boundVarsAbs :: (Term (Expr e)) => Abstraction e -> Set.Set Identifier
boundVarsAbs ab = absVar ab `Set.insert` boundVars (absExpr ab)

freeVarsAbs :: (Term (Expr e)) => Abstraction e -> Set.Set Identifier
freeVarsAbs ab = Set.delete (absVar ab) (freeVars (absExpr ab))

instance (Term e) => Term (Expr e) where
  boundVars (Abs ab)                     = boundVarsAbs ab
  boundVars (FunTy ab)                   = boundVarsAbs ab
  boundVars (ProductTy ab)               = boundVarsAbs ab
  boundVars (App e1 e2)                  = boundVars e1 `Set.union` boundVars e2
  boundVars (Pair e1 e2)                 = boundVars e1 `Set.union` boundVars e2
  boundVars (IfExpr e1 e2 e3)            = boundVars e1 `Set.union` boundVars e2 `Set.union` boundVars e3
  boundVars (Var _)                      = Set.empty
  boundVars (Sig e _)                    = boundVars e
  boundVars (GenLet var e1 e2)           = var `Set.insert` (boundVars e1 `Set.union` boundVars e2)
  boundVars (Ext e)                      = boundVars e
  boundVars Wild                         = Set.empty
  boundVars LitLevel{}                   = Set.empty
  boundVars Builtin{}                    = Set.empty
  boundVars (PairElim z x y e1 e2 e3)    =
    Set.insert z (x `Set.insert` (y `Set.insert` (boundVars e1 `Set.union` boundVars e2 `Set.union` boundVars e3)))

  freeVars (FunTy ab)                    = freeVarsAbs ab
  freeVars (Abs ab)                      = freeVarsAbs ab
  freeVars (ProductTy ab)                = freeVarsAbs ab
  freeVars (App e1 e2)                   = freeVars e1 `Set.union` freeVars e2
  freeVars (Pair e1 e2)                  = freeVars e1 `Set.union` freeVars e2
  freeVars (IfExpr e1 e2 e3)             = freeVars e1 `Set.union` freeVars e2 `Set.union` freeVars e3
  freeVars (Var var)                     = Set.singleton var
  freeVars (Sig e _)                     = freeVars e
  freeVars (GenLet var e1 e2)            = Set.delete var (freeVars e1 `Set.union` freeVars e2)
  freeVars (PairElim z x y e1 e2 e3)     =
    Set.delete z (Set.delete x (Set.delete y (freeVars e1 `Set.union` freeVars e2 `Set.union` freeVars e3)))
  freeVars (Ext e)                       = freeVars e
  freeVars Wild                          = Set.empty
  freeVars LitLevel{}                    = Set.empty
  freeVars Builtin{}                     = Set.empty

instance Term NoExt where
  boundVars _ = undefined
  freeVars  _ = undefined
