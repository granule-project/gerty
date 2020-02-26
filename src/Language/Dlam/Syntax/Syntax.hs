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
  -- ** Identity
  , idTy
  , idTyTY
  , idTyApp
  , reflTerm
  , reflTermTY
  , reflTermApp
  ) where

import qualified Data.Set as Set

----------------
-- Statements --
----------------

newtype AST = AST [Stmt]
  deriving Show

data Stmt =
  -- | Assignment to a name.
    StmtAssign String Expr
  -- | Type assignment.
  | StmtType String Expr
  deriving Show

newtype NAST = NAST [NStmt]
  deriving Show

data NStmt =
  -- | An assignment with an optional type, and mandatory definition.
  Decl String (Maybe Expr) Expr
  deriving Show

-- | Normalise the raw AST into a form appropriate for further analyses.
-- TODO: add a better error system (2020-02-19)
normaliseAST :: AST -> NAST
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

newtype Abstraction = Abst { getAbst :: (Identifier, Expr, Expr) }
  deriving (Show, Eq, Ord)

-- | Variable bound in the abstraction.
absVar :: Abstraction -> Identifier
absVar (Abst (v, _, _)) = v

-- | Type of the bound variable in the abstraction.
absTy :: Abstraction -> Expr
absTy (Abst (_, t, _)) = t

-- | Target expression of the abstraction.
absExpr :: Abstraction -> Expr
absExpr (Abst (_, _, t)) = t

mkAbs :: Identifier -> Expr -> Expr -> Abstraction
mkAbs v e1 e2 = Abst (v, e1, e2)

-- Abstract-syntax tree for LambdaCore
-- parameterised by an additional type `ex`
-- used to represent the abstract syntax
-- tree of additional commands
data Expr where
  -- | Variable.
  Var :: Identifier -> Expr

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
  PairElim :: Identifier -> Identifier -> Identifier -> Expr -> Expr -> Expr -> Expr

  -- | Conditional eliminator.
  IfExpr :: Expr -> Expr -> Expr -> Expr

  -- | Identity eliminator.
  RewriteExpr :: Identifier -> Identifier -> Identifier -> Expr -> Identifier -> Expr -> Expr -> Expr -> Expr -> Expr

  App :: Expr ->  Expr   -> Expr -- e1 e2

  Sig :: Expr -> Expr       -> Expr -- e : A

  -- | Holes for inference.
  Hole :: Expr

  -- | Implicits for synthesis.
  Implicit :: Expr

  -- | Builtin terms, with a unique identifying name.
  Builtin :: BuiltinTerm -> Expr

  -- ML
  GenLet :: Identifier -> Expr -> Expr -> Expr -- let x = e1 in e2 (ML-style polymorphism)
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

  -- | Identity type.
  | IdTy

  -- | Reflexivity.
  | DRefl
  deriving (Show, Eq, Ord)


mkFunTy :: Identifier -> Expr -> Expr -> Expr
mkFunTy n t e = FunTy $ mkAbs n t e


-- | Body for a builtin term (essentially an Agda postulate).
builtinTerm :: BuiltinTerm -> Expr
builtinTerm = Builtin

levelTy :: Expr
levelTy = builtinTerm LevelTy

levelTyTY :: Expr
levelTyTY = mkUnivTy (LitLevel 0)

lzero :: Expr
lzero = builtinTerm LZero

lzeroTY :: Expr
lzeroTY = levelTy

lsuc :: Expr
lsuc = builtinTerm LSuc

lsucTY :: Expr
lsucTY = FunTy (mkAbs ignoreVar levelTy levelTy)

lsucApp :: Expr -> Expr
lsucApp = App lsuc

lmax :: Expr
lmax = builtinTerm LMax

lmaxTY :: Expr
lmaxTY = FunTy (mkAbs ignoreVar levelTy (FunTy (mkAbs ignoreVar levelTy levelTy)))

lmaxApp :: Expr -> Expr -> Expr
lmaxApp l1 l2 = App (App lmax l1) l2

typeTy :: Expr
typeTy = builtinTerm TypeTy

typeTyTY :: Expr
typeTyTY = let l = mkIdent "l" in FunTy (mkAbs l levelTy (mkUnivTy (lsucApp (Var l))))

mkUnivTy :: Expr -> Expr
mkUnivTy = App typeTy

dBool :: Expr
dBool = builtinTerm DBool

dBoolTY :: Expr
dBoolTY = mkUnivTy (LitLevel 0)

dtrue :: Expr
dtrue = builtinTerm DTrue

dtrueTY :: Expr
dtrueTY = dBool

dfalse :: Expr
dfalse = builtinTerm DFalse

dfalseTY :: Expr
dfalseTY = dBool

unitTy :: Expr
unitTy = builtinTerm DUnitTy

unitTyTY :: Expr
unitTyTY = mkUnivTy (LitLevel 0)

unitTerm :: Expr
unitTerm = builtinTerm DUnitTerm

unitTermTY :: Expr
unitTermTY = unitTy

idTy :: Expr
idTy = builtinTerm IdTy

idTyTY :: Expr
idTyTY =
  let l = mkIdent "l"
      lv = Var l
      a = mkIdent "a"
      av = Var a
  in mkFunTy l levelTy (mkFunTy a (mkUnivTy lv) (mkFunTy ignoreVar av (mkFunTy ignoreVar av (mkUnivTy lv))))

idTyApp :: Expr -> Expr -> Expr -> Expr -> Expr
idTyApp l t x y = App (App (App (App idTy l) t) x) y

reflTerm :: Expr
reflTerm = builtinTerm DRefl

reflTermTY :: Expr
reflTermTY =
  let l = mkIdent "l"
      lv = Var l
      a = mkIdent "a"
      av = Var a
      x = mkIdent "x"
      xv = Var x
  in mkFunTy l levelTy (mkFunTy a (mkUnivTy lv) (mkFunTy x av (idTyApp lv av xv xv)))


reflTermApp :: Expr -> Expr -> Expr -> Expr
reflTermApp l t x = App (App (App reflTerm l) t) x

----------------------------

class Term t where
  boundVars :: t -> Set.Set Identifier
  freeVars  :: t -> Set.Set Identifier


boundVarsAbs :: Abstraction -> Set.Set Identifier
boundVarsAbs ab = absVar ab `Set.insert` boundVars (absExpr ab)

freeVarsAbs :: Abstraction -> Set.Set Identifier
freeVarsAbs ab = Set.delete (absVar ab) (freeVars (absExpr ab))

instance Term Expr where
  boundVars (Abs ab)                     = boundVarsAbs ab
  boundVars (FunTy ab)                   = boundVarsAbs ab
  boundVars (ProductTy ab)               = boundVarsAbs ab
  boundVars (App e1 e2)                  = boundVars e1 `Set.union` boundVars e2
  boundVars (Pair e1 e2)                 = boundVars e1 `Set.union` boundVars e2
  boundVars (IfExpr e1 e2 e3)            = boundVars e1 `Set.union` boundVars e2 `Set.union` boundVars e3
  boundVars (Var _)                      = Set.empty
  boundVars (Sig e _)                    = boundVars e
  boundVars (GenLet var e1 e2)           = var `Set.insert` (boundVars e1 `Set.union` boundVars e2)
  boundVars Hole                         = Set.empty
  boundVars Implicit                     = Set.empty
  boundVars LitLevel{}                   = Set.empty
  boundVars Builtin{}                    = Set.empty
  boundVars (PairElim z x y e1 e2 e3)    =
    Set.insert z (x `Set.insert` (y `Set.insert` (boundVars e1 `Set.union` boundVars e2 `Set.union` boundVars e3)))
  boundVars (RewriteExpr{}) = error "boundVars for RewriteExpr not yet implemented"

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
  freeVars (RewriteExpr{}) = error "freeVars for RewriteExpr not yet implemented"
  freeVars Hole                          = Set.empty
  freeVars Implicit                      = Set.empty
  freeVars LitLevel{}                    = Set.empty
  freeVars Builtin{}                     = Set.empty
