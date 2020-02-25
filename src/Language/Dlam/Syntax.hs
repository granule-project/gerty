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
  , mkImplicit

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
  Decl String (Expr ann e) (Expr ann e)
  deriving Show

-- | Normalise the raw AST into a form appropriate for further analyses.
-- TODO: add a better error system (2020-02-19)
normaliseAST :: AST ann e -> NAST ann e
normaliseAST (AST []) = NAST []
normaliseAST (AST ((StmtType v t):(StmtAssign v' e):sts))
  | v == v' = let (NAST xs) = normaliseAST (AST sts) in NAST ((Decl v t e):xs)
  | otherwise = error $ "type declaration for '" <> v <> "' followed by an assignment to '" <> v' <> "'"
normaliseAST (AST ((StmtAssign v e):sts)) =
  let (NAST xs) = normaliseAST (AST sts) in NAST ((Decl v mkImplicit e) : xs)
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
  deriving (Show, Ord)

deriving instance (Eq ext) => Eq (Abstraction ann ext)

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
  Var :: Identifier -> Expr ann ex

  -- | Level literals.
  LitLevel :: Int -> Expr ann ex

  -- | Dependent function type.
  FunTy :: Abstraction ann ex -> Expr ann ex

  -- | Lambda abstraction.
  Abs :: Abstraction ann ex -> Expr ann ex

  -- | Dependent tensor type.
  ProductTy :: Abstraction ann ex -> Expr ann ex

  -- | Pairs.
  Pair :: Expr ann ex -> Expr ann ex -> Expr ann ex

  -- | Pair eliminator.
  PairElim :: Identifier -> Identifier -> Identifier -> Expr ann ex -> Expr ann ex -> Expr ann ex -> Expr ann ex

  -- | Conditional eliminator.
  IfExpr :: Expr ann ex -> Expr ann ex -> Expr ann ex -> Expr ann ex

  App :: Expr ann ex ->  Expr ann ex   -> Expr ann ex -- e1 e2

  Sig :: Expr ann ex -> Expr ann ex       -> Expr ann ex -- e : A

  -- | Holes for inference.
  Hole :: Expr ann ex

  -- | Implicits for synthesis.
  Implicit :: Expr ann ex

  -- | Builtin terms, with a unique identifying name.
  Builtin :: BuiltinTerm -> Expr ann ex

  -- ML
  GenLet :: Identifier -> Expr ann ex -> Expr ann ex -> Expr ann ex -- let x = e1 in e2 (ML-style polymorphism)

  -- | AST extensions.
  Ext :: ex -> Expr ann ex
  deriving (Show, Ord)

deriving instance (Eq ext) => Eq (Expr ann ext)


-- | Make a new, unnamed, implicit term.
mkImplicit :: Expr ann e
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
builtinTerm :: BuiltinTerm -> Expr ann e
builtinTerm = Builtin

levelTy :: Expr ann e
levelTy = builtinTerm LevelTy

levelTyTY :: Expr ann e
levelTyTY = mkUnivTy (LitLevel 0)

lzero :: Expr ann e
lzero = builtinTerm LZero

lzeroTY :: Expr ann e
lzeroTY = levelTy

lsuc :: Expr ann e
lsuc = builtinTerm LSuc

lsucTY :: Expr ann e
lsucTY = FunTy (mkAbs ignoreVar levelTy levelTy)

lsucApp :: Expr ann e -> Expr ann e
lsucApp = App lsuc

lmax :: Expr ann e
lmax = builtinTerm LMax

lmaxTY :: Expr ann e
lmaxTY = FunTy (mkAbs ignoreVar levelTy (FunTy (mkAbs ignoreVar levelTy levelTy)))

lmaxApp :: Expr ann e -> Expr ann e -> Expr ann e
lmaxApp l1 l2 = App (App lmax l1) l2

typeTy :: Expr ann e
typeTy = builtinTerm TypeTy

typeTyTY :: Expr ann e
typeTyTY = let l = mkIdent "l" in FunTy (mkAbs l levelTy (mkUnivTy (lsucApp (Var l))))

mkUnivTy :: Expr ann e -> Expr ann e
mkUnivTy = App typeTy

dBool :: Expr ann e
dBool = builtinTerm DBool

dBoolTY :: Expr ann e
dBoolTY = mkUnivTy (LitLevel 0)

dtrue :: Expr ann e
dtrue = builtinTerm DTrue

dtrueTY :: Expr ann e
dtrueTY = dBool

dfalse :: Expr ann e
dfalse = builtinTerm DFalse

dfalseTY :: Expr ann e
dfalseTY = dBool

unitTy :: Expr ann e
unitTy = builtinTerm DUnitTy

unitTyTY :: Expr ann e
unitTyTY = mkUnivTy (LitLevel 0)

unitTerm :: Expr ann e
unitTerm = builtinTerm DUnitTerm

unitTermTY :: Expr ann e
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


boundVarsAbs :: (Term (Expr ann e)) => Abstraction ann e -> Set.Set Identifier
boundVarsAbs ab = absVar ab `Set.insert` boundVars (absExpr ab)

freeVarsAbs :: (Term (Expr ann e)) => Abstraction ann e -> Set.Set Identifier
freeVarsAbs ab = Set.delete (absVar ab) (freeVars (absExpr ab))

instance (Term e) => Term (Expr ann e) where
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
  boundVars Hole                         = Set.empty
  boundVars Implicit                     = Set.empty
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
  freeVars Hole                          = Set.empty
  freeVars Implicit                      = Set.empty
  freeVars LitLevel{}                    = Set.empty
  freeVars Builtin{}                     = Set.empty

instance Term NoExt where
  boundVars _ = undefined
  freeVars  _ = undefined
