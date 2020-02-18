{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}

module Dlam.Syntax where

import qualified Data.Set as Set

type Identifier = String

newtype Abstraction ext = Abst { getAbst :: (Identifier, Expr ext, Expr ext) }
  deriving Show

-- | Variable bound in the abstraction.
absVar :: Abstraction ex -> Identifier
absVar (Abst (v, _, _)) = v

-- | Type of the bound variable in the abstraction.
absTy :: Abstraction ex -> Expr ex
absTy (Abst (_, t, _)) = t

-- | Target expression of the abstraction.
absTarget :: Abstraction ex -> Expr ex
absTarget (Abst (_, _, t)) = t

mkAbs :: Identifier -> Expr ext -> Expr ext -> Abstraction ext
mkAbs v e1 e2 = Abst (v, e1, e2)

-- Abstract-syntax tree for LambdaCore
-- parameterised by an additional type `ex`
-- used to represent the abstract syntax
-- tree of additional commands
data Expr ex where
  -- | Variable.
  Var :: Identifier -> Expr ex

  -- | Type universe.
  TypeTy :: ULevel -> Expr ex

  -- | Dependent function type.
  FunTy :: Abstraction ex -> Expr ex

  Abs :: Identifier -> Maybe Type -> Expr ex -> Expr ex
                                          -- \x -> e  [λ x . e] (Curry style)
                                          -- or
                                          -- \(x : A) -> e (Church style)
  App :: Expr ex ->  Expr ex   -> Expr ex -- e1 e2

  Sig :: Expr ex -> Type       -> Expr ex -- e : A

  -- Poly
  TyAbs   :: Identifier -> Expr ex -> Expr ex -- /\ a -> e
  TyEmbed :: Type                  -> Expr ex -- @A

  -- ML
  GenLet :: Identifier -> Expr ex -> Expr ex -> Expr ex -- let x = e1 in e2 (ML-style polymorphism)

  -- | AST extensions.
  Ext :: ex -> Expr ex
  deriving Show

-- | Universe level.
type ULevel = Int

------------------------------
-- Type syntax

data Type =
  -- Polymorphic lambda calculus
    TyVar Identifier       -- a
  | Forall Identifier Type -- forall a . A
  deriving (Show, Eq)

----------------------------

class Term t where
  boundVars :: t -> Set.Set Identifier
  freeVars  :: t -> Set.Set Identifier
  mkVar     :: Identifier -> t

-- | For minimal language with no extensions.
data NoExt

instance Show NoExt where
  show _ = undefined

instance Term (Expr NoExt) where
  boundVars (Abs var _ e)                = var `Set.insert` boundVars e
  boundVars (FunTy ab)                   =
    absVar ab `Set.insert` boundVars (absTarget ab)
  boundVars (TyAbs var e)                = var `Set.insert` boundVars e
  boundVars (TyEmbed t)                  = boundVars t
  boundVars (App e1 e2)                  = boundVars e1 `Set.union` boundVars e2
  boundVars (Var var)                    = Set.empty
  boundVars (Sig e _)                    = boundVars e
  boundVars TypeTy{}                     = Set.empty
  boundVars (GenLet var e1 e2)           = var `Set.insert` (boundVars e1 `Set.union` boundVars e2)
  boundVars (Ext _)                      = Set.empty

  freeVars (FunTy ab)                    =
    Set.delete (absVar ab) (freeVars (absTarget ab))
  freeVars (Abs var _ e)                 = Set.delete var (freeVars e)
  freeVars (TyAbs var e)                 = Set.delete var (freeVars e)
  freeVars (TyEmbed t)                   = freeVars t
  freeVars (App e1 e2)                   = freeVars e1 `Set.union` freeVars e2
  freeVars (Var var)                     = Set.singleton var
  freeVars (Sig e _)                     = freeVars e
  freeVars TypeTy{}                      = Set.empty
  freeVars (GenLet var e1 e2)            = Set.delete var (freeVars e1 `Set.union` freeVars e2)
  freeVars (Ext _)                       = Set.empty

  mkVar = Var

instance Term Type where
  boundVars (TyVar var)    = Set.empty
  boundVars (Forall var t) = var `Set.insert` boundVars t

  freeVars (TyVar var)    = Set.singleton var
  freeVars (Forall var t) = var `Set.delete` freeVars t

  mkVar = TyVar

  ----------------------------
-- Fresh variable with respect to a set of variables
-- By adding apostrophes to a supplied initial variable

fresh_var :: Identifier -> Set.Set Identifier -> Identifier
fresh_var var vars =
  if var `Set.member` vars then fresh_var (var ++ "'") vars else var
