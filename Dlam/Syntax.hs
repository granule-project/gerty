{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}

module Dlam.Syntax where

import qualified Data.Set as Set

type Identifier = String

-- Abstract-syntax tree for LambdaCore
-- parameterised by an additional type `ex`
-- used to represent the abstract syntax
-- tree of additional commands
data Expr ex where
    Abs :: Identifier -> Maybe Type -> Expr ex -> Expr ex
                                            -- \x -> e  [λ x . e] (Curry style)
                                            -- or
                                            -- \(x : A) -> e (Church style)
    App :: Expr ex ->  Expr ex   -> Expr ex -- e1 e2
    Var :: Identifier            -> Expr ex -- x

    Sig :: Expr ex -> Type       -> Expr ex -- e : A

    -- Poly
    TyAbs   :: Identifier -> Expr ex -> Expr ex -- /\ a -> e
    TyEmbed :: Type                  -> Expr ex -- @A

    -- ML
    GenLet :: Identifier -> Expr ex -> Expr ex -> Expr ex -- let x = e1 in e2 (ML-style polymorphism)

    -- Extend the ast at this point
    Ext :: ex -> Expr ex
  deriving Show

----------------------------
-- Extend the language to PCF (natural number constructors
-- and deconstructor + fixed point)

data PCF =
    NatCase (Expr PCF) (Expr PCF) (Identifier, Expr PCF)
                               -- case e of zero -> e1 | succ x -> e2
  | Fix (Expr PCF)             -- fix(e)
  | Succ                       -- succ (function)
  | Zero                       -- zero
  | Pair (Expr PCF) (Expr PCF) -- <e1, e2>
  | Fst (Expr PCF)             -- fst(e)
  | Snd (Expr PCF)             -- snd(e)
  | Inl (Expr PCF)             -- inl(e)
  | Inr (Expr PCF)             -- inr(e)
  | Case (Expr PCF) (Identifier, Expr PCF) (Identifier, Expr PCF)
                               -- case e of inl x -> e1 | inr y -> e2
  deriving Show

isValue :: Expr PCF -> Bool
isValue Abs{}   = True
isValue TyAbs{} = True
isValue Var{}   = True
isValue e       = isNatVal e

isNatVal :: Expr PCF -> Bool
isNatVal (Ext Zero)  = True
isNatVal (Ext Succ)  = True
isNatVal (App e1 e2) = isNatVal e1 && isNatVal e2
isNatVal _           = False

------------------------------
-- Type syntax

data Type =
  -- Simply-typed lambda calculus
    FunTy Type Type  -- A -> B

  -- PCF types
  | NatTy            -- Nat
  | ProdTy Type Type -- A * B
  | SumTy Type Type  -- A + B

  -- Polymorphic lambda calculus
  | TyVar Identifier       -- a
  | Forall Identifier Type -- forall a . A
  deriving (Show, Eq)

----------------------------

class Term t where
  boundVars :: t -> Set.Set Identifier
  freeVars  :: t -> Set.Set Identifier
  mkVar     :: Identifier -> t

instance Term (Expr PCF) where
  boundVars (Abs var _ e)                = var `Set.insert` boundVars e
  boundVars (TyAbs var e)                = var `Set.insert` boundVars e
  boundVars (TyEmbed t)                  = boundVars t
  boundVars (App e1 e2)                  = boundVars e1 `Set.union` boundVars e2
  boundVars (Var var)                    = Set.empty
  boundVars (Sig e _)                    = boundVars e
  boundVars (GenLet var e1 e2)           = var `Set.insert` (boundVars e1 `Set.union` boundVars e2)
  boundVars (Ext (NatCase e e1 (x,e2)))  =
    x `Set.insert` (boundVars e `Set.union` boundVars e1 `Set.union` boundVars e2)
  boundVars (Ext (Fix e))                = boundVars e
  boundVars (Ext (Pair e1 e2))           = boundVars e1 `Set.union` boundVars e2
  boundVars (Ext (Fst e))                = boundVars e
  boundVars (Ext (Snd e))                = boundVars e
  boundVars (Ext (Inl e))                = boundVars e
  boundVars (Ext (Inr e))                = boundVars e
  boundVars (Ext (Case e (x,e1) (y,e2))) =
    boundVars e `Set.union` (x `Set.insert` boundVars e1) `Set.union` (y `Set.insert` boundVars e2)
  boundVars (Ext _)                      = Set.empty

  freeVars (Abs var _ e)                 = Set.delete var (freeVars e)
  freeVars (TyAbs var e)                 = Set.delete var (freeVars e)
  freeVars (TyEmbed t)                   = freeVars t
  freeVars (App e1 e2)                   = freeVars e1 `Set.union` freeVars e2
  freeVars (Var var)                     = Set.singleton var
  freeVars (Sig e _)                     = freeVars e
  freeVars (GenLet var e1 e2)            = Set.delete var (freeVars e1 `Set.union` freeVars e2)
  freeVars (Ext (NatCase e e1 (x,e2)))   =
    freeVars e `Set.union` freeVars e1 `Set.union` (Set.delete x (freeVars e2))
  freeVars (Ext (Fix e))                 = freeVars e
  freeVars (Ext (Pair e1 e2))            = freeVars e1 `Set.union` freeVars e2
  freeVars (Ext (Fst e))                 = freeVars e
  freeVars (Ext (Snd e))                 = freeVars e
  freeVars (Ext (Inl e))                 = freeVars e
  freeVars (Ext (Inr e))                 = freeVars e
  freeVars (Ext (Case e (x,e1) (y,e2)))  =
    freeVars e `Set.union` (Set.delete x (freeVars e1)) `Set.union` (Set.delete y (freeVars e2))
  freeVars (Ext _)                       = Set.empty

  mkVar = Var

instance Term Type where
  boundVars (FunTy t1 t2)  = boundVars t1 `Set.union` boundVars t2
  boundVars (ProdTy t1 t2) = boundVars t1 `Set.union` boundVars t2
  boundVars (SumTy t1 t2)  = boundVars t1 `Set.union` boundVars t2
  boundVars NatTy          = Set.empty
  boundVars (TyVar var)    = Set.empty
  boundVars (Forall var t) = var `Set.insert` boundVars t

  freeVars (FunTy t1 t2)  = freeVars t1 `Set.union` freeVars t2
  freeVars (ProdTy t1 t2) = freeVars t1 `Set.union` freeVars t2
  freeVars (SumTy t1 t2)  = freeVars t1 `Set.union` freeVars t2
  freeVars NatTy          = Set.empty
  freeVars (TyVar var)    = Set.singleton var
  freeVars (Forall var t) = var `Set.delete` freeVars t

  mkVar = TyVar

  ----------------------------
-- Fresh variable with respect to a set of variables
-- By adding apostrophes to a supplied initial variable

fresh_var :: Identifier -> Set.Set Identifier -> Identifier
fresh_var var vars =
  if var `Set.member` vars then fresh_var (var ++ "'") vars else var
