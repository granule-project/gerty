{-# LANGUAGE FlexibleInstances #-}

module Dlam.Semantics
  ( Substitutable(..)
  ) where

import Dlam.Syntax

import qualified Data.Set as Set

class Substitutable e where
  substitute :: e -> (Identifier, e) -> e

instance Substitutable (Expr NoExt) where
  substitute = substituteExpr

-- Syntactic substitution - `substituteExpr e (x, e')` means e[e'/x]
substituteExpr :: Expr NoExt -> (Identifier, Expr NoExt) -> Expr NoExt
substituteExpr (Var y) (x, e')
  | x == y = e'
  | otherwise = Var y

substituteExpr (FunTy ab) s@(varS, _)
  | absVar ab == varS =
    FunTy (mkAbs (absVar ab) (substituteExpr (absTy ab) s) (absExpr ab))
  | otherwise   =
    FunTy (mkAbs (absVar ab) (substituteExpr (absTy ab) s) (substituteExpr (absExpr ab) s))

substituteExpr t@TypeTy{} _ = t

substituteExpr (App e1 e2) s =
  App (substituteExpr e1 s) (substituteExpr e2 s)

substituteExpr (Abs y mt e) s =
  let (y', e') = substitute_binding y e s in Abs y' mt e'

substituteExpr (Sig e t) s = Sig (substituteExpr e s) t

-- ML

substituteExpr (GenLet x e1 e2) s =
  let (x' , e2') = substitute_binding x e2 s in GenLet x' (substituteExpr e1 s) e2'

-- Poly

substituteExpr (Ext _) _ = undefined


-- substitute_binding x e (y,e') substitutes e' into e for y,
-- but assumes e has just had binder x introduced
substitute_binding :: (Term t, Substitutable t) => Identifier -> t -> (Identifier, t) -> (Identifier, t)
substitute_binding x e (y,e')
  -- Name clash in binding - we are done
  | x == y = (x, e)
  -- If expression to be bound contains already bound variable
  | x `Set.member` freeVars e' =
    let x' = fresh_var x (freeVars e `Set.union` freeVars e')
    in (x', substitute (substitute e (x, mkVar x')) (y, e'))
  | otherwise = (x, substitute e (y,e'))
