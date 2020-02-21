{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Dlam.Syntax
  ( Expr(..)
  , Identifier
  , mkIdent
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

type Identifier = String

-- | Create a new identifier from a (syntactic) string.
mkIdent :: String -> Identifier
mkIdent s = s

newtype Abstraction ext = Abst { getAbst :: (Identifier, Expr ext, Expr ext) }
  deriving Show

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
  deriving Show

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
  deriving (Show, Eq)


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
lsucTY = FunTy (mkAbs "_" levelTy levelTy)

lsucApp :: Expr e -> Expr e
lsucApp = App lsuc

lmax :: Expr e
lmax = builtinTerm LMax

lmaxTY :: Expr e
lmaxTY = FunTy (mkAbs "_" levelTy (FunTy (mkAbs "_" levelTy levelTy)))

lmaxApp :: Expr e -> Expr e -> Expr e
lmaxApp l1 l2 = App (App lmax l1) l2

typeTy :: Expr e
typeTy = builtinTerm TypeTy

typeTyTY :: Expr e
typeTyTY = FunTy (mkAbs "_" levelTy (mkUnivTy (LitLevel 0)))

mkUnivTy :: Expr e -> Expr e
mkUnivTy = App typeTy


----------------------------

class Term t where
  boundVars :: t -> Set.Set Identifier
  freeVars  :: t -> Set.Set Identifier
  mkVar     :: Identifier -> t

-- | For minimal language with no extensions.
data NoExt

instance Eq NoExt where
  _ == _ = True

instance Show NoExt where
  show _ = undefined


boundVarsAbs :: (Term (Expr e)) => Abstraction e -> Set.Set Identifier
boundVarsAbs ab = absVar ab `Set.insert` boundVars (absExpr ab)

freeVarsAbs :: (Term (Expr e)) => Abstraction e -> Set.Set Identifier
freeVarsAbs ab = Set.delete (absVar ab) (freeVars (absExpr ab))

instance Term (Expr NoExt) where
  boundVars (Abs ab)                     = boundVarsAbs ab
  boundVars (FunTy ab)                   = boundVarsAbs ab
  boundVars (App e1 e2)                  = boundVars e1 `Set.union` boundVars e2
  boundVars (Var _)                      = Set.empty
  boundVars (Sig e _)                    = boundVars e
  boundVars (GenLet var e1 e2)           = var `Set.insert` (boundVars e1 `Set.union` boundVars e2)
  boundVars (Ext _)                      = Set.empty
  boundVars Wild                         = Set.empty
  boundVars LitLevel{}                   = Set.empty
  boundVars Builtin{}                    = Set.empty

  freeVars (FunTy ab)                    = freeVarsAbs ab
  freeVars (Abs ab)                      = freeVarsAbs ab
  freeVars (App e1 e2)                   = freeVars e1 `Set.union` freeVars e2
  freeVars (Var var)                     = Set.singleton var
  freeVars (Sig e _)                     = freeVars e
  freeVars (GenLet var e1 e2)            = Set.delete var (freeVars e1 `Set.union` freeVars e2)
  freeVars (Ext _)                       = Set.empty
  freeVars Wild                          = Set.empty
  freeVars LitLevel{}                    = Set.empty
  freeVars Builtin{}                     = Set.empty

  mkVar = Var
