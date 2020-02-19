{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Dlam.Semantics where

import Dlam.Syntax
import Dlam.Options

import qualified Data.Set as Set

-- | Class for theories which support reductions and values.
class (Substitutable (Expr ext)) => Semantic ext where
  isValue :: Expr ext -> Bool
  reduceExt :: Reducer (Expr ext) -> Reducer (Expr ext)

instance Semantic NoExt where
  isValue Abs{}    = True
  isValue Var{}    = True
  isValue TypeTy{} = True
  isValue e       = False

  reduceExt _ _ = undefined


-- Keep doing small step reductions until normal form reached
multiStep :: (Semantic ext) => [Option] -> Expr ext -> (Expr ext, Int)
multiStep _    e              = multiStep' fullBeta e 0

type Reducer a = a -> Maybe a

multiStep' :: Reducer (Expr ext) -> Expr ext -> Int -> (Expr ext, Int)
multiStep' step t n =
  case step t of
    -- Normal form reached
    Nothing -> (t, n)
    -- Can do more reduction
    Just t' -> multiStep' step t' (n+1)

fullBeta :: (Semantic ext) => Reducer (Expr ext)
fullBeta (Var _) = Nothing
fullBeta (FunTy ab) = Nothing
fullBeta TypeTy{} = Nothing
fullBeta (App (Abs x _ e) e') = beta e x e'
-- Poly beta
fullBeta (App e1 e2) =
  -- Prefer fully zeta1 reducing before zeta2 reducing
  case zeta1 fullBeta e1 e2 of
    Just e -> Just e
    Nothing -> zeta2 fullBeta e1 e2
fullBeta (Abs x _ e) = zeta3 fullBeta x e
fullBeta (Sig e _) = Just e
fullBeta (Ext e) = reduceExt fullBeta (Ext e)
-- ML
fullBeta (GenLet x e' e) = beta e x e'


-- Base case
beta :: (Substitutable t) => t -> Identifier -> t -> Maybe t
beta e x e' = Just (substitute e (x, e'))

-- Inductive rules
zeta1 :: Reducer (Expr ext) -> Expr ext -> Expr ext -> Maybe (Expr ext)
zeta1 step e1 e2 = (\e1' -> App e1' e2) <$> step e1

zeta2 :: Reducer (Expr ext)  -> Expr ext -> Expr ext -> Maybe (Expr ext)
zeta2 step e1 e2 = (\e2' -> App e1 e2') <$> step e2

zeta3 :: Reducer (Expr ext)  -> Identifier -> Expr ext -> Maybe (Expr ext)
zeta3 step x e = (\e' -> Abs x Nothing e') <$> step e


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
