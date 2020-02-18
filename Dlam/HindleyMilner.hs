{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Dlam.HindleyMilner where

import Dlam.Syntax
import Dlam.PrettyPrint
import Data.Set (toList, unions, (\\))

data TypeScheme = ForallTy [Identifier] Type
unpackType :: TypeScheme -> Type
unpackType (ForallTy _ ty) = ty

type Context = [(Identifier, TypeScheme)]

-- Top-level of Algorithm W (Hindley Milner algorithm)
inferType :: Context -> Expr PCF -> Maybe Type
inferType ctxt ast = let (s, ty, _) = infer ctxt ast 0 in Just (substitute s ty)

type TypeVariable = String
type Substitution = TypeVariable -> Type

-- Inner main function of Algorithm W
-- Takes:
--   * a typing context
--   * the expression whose type we are infering
--   * an integer acting as the seed for doing gensym
-- Returns (if succesful) a:
--   * a substitution on type variables
--   * a type (if succesful)
--   * an updated gensym seed
infer :: Context -> Expr PCF -> Int -> (Substitution, Type, Int)
infer ctxt (Abs var _ e) fv =
  let alpha     = "a" ++ show fv
      (s , tyB , fv') = infer ((var , ForallTy [] (TyVar alpha)) : ctxt) e (fv+1)
  in (s, FunTy Nothing (s alpha) tyB, fv')

infer ctxt (App e1 e2) fv =
  let (s1, t1, fv') = infer ctxt e1 fv
      (s2, t2, fv'') = infer (substitute s1 ctxt) e2 fv'
      alpha          = "a" ++ show fv''
      s3 = mgu (substitute s2 t1) (FunTy Nothing t2 (TyVar alpha))
  in (s3 <.> s2 <.> s1, s3 alpha, fv'' + 1)

infer ctxt (Var x) fv =
    case lookup x ctxt of
      Just (ForallTy alphas ty) ->
        let (tyFreshened, fv') = freshen alphas ty fv
        in (idSubst, tyFreshened, fv')
      Nothing -> error $ "I don't know the type of " ++ x
  where
    freshen [] ty fv = (ty, fv)
    freshen (x:xs) ty fv =
      freshen xs (substitute (singletonSubst x (TyVar $ "a" ++ show fv)) ty) (fv + 1)

infer ctxt (GenLet x e1 e2) fv =
  let (s1, t1, fv') = infer ctxt e1 fv
      freeTyVarsOfContext = unions $ map (freeVars . unpackType . snd) (substitute s1 ctxt)
      alphas = freeVars t1 \\ freeTyVarsOfContext
      (s2, t2, fv'') = infer ((x, ForallTy (toList alphas) t1) : substitute s1 ctxt) e2 fv'
  in (s2 <.> s1, t2, fv'')

infer ctxt (Ext Zero) fv = (idSubst, NatTy, fv)
infer ctxt (Ext Succ) fv = (idSubst, FunTy Nothing NatTy NatTy, fv)

infer ctxt t fv =
  error $ "I don't know how to infer the type of " ++ pprint t


-- (a -> Bool) `mgu` (Int -> b)
--   = Just [a |-> Int, b |-> Bool]

-- t1 `mgu` t2 = Just s   =>  s(t1) = s(t2)
-- forall s' . s'(t1)=s'(t2) => exists s'' . (s'' . s) = s'

-- {a -> Int} <.> {b -> (a, Int)}
--    = {b -> (Int, Int), a -> Int}

idSubst :: Substitution
idSubst var = TyVar var

singletonSubst :: TypeVariable -> Type -> Substitution
singletonSubst var ty =
  \var' -> if var == var' then ty else TyVar var'

-- idSubst <.> s = s
-- s <.> idSubst = s

-- substitute s2 (substitute s1 t) =
--  substitute (s2 <.> s1) t

(<.>) :: Substitution -> Substitution -> Substitution
s2 <.> s1 =
  \v ->
    if s1 v == TyVar v
      then s2 v
      else substitute s2 (s1 v)

-- Calculate the most general unified of two types
mgu :: Type -> Type -> Substitution
mgu (FunTy Nothing t1 t2) (FunTy Nothing t1' t2') =
  let s = mgu t1 t1'
      s' = mgu (substitute s t2) (substitute s t2')
  in s' <.> s
mgu (ProdTy t1 t2) (ProdTy t1' t2') =
  let s  = mgu t1 t1'
      s' = mgu (substitute s t2) (substitute s t2')
  in s' <.> s
mgu (SumTy t1 t2) (SumTy t1' t2') =
  let s = mgu t1 t1'
      s' = mgu (substitute s t2) (substitute s t2')
  in s' <.> s
mgu NatTy NatTy  = idSubst
mgu (TyVar a) ty = singletonSubst a ty
mgu ty (TyVar a) = singletonSubst a ty
mgu t1 t2 = error $ "Cannot unify " ++ pprint t1 ++ " and " ++ pprint t2


-- Apply a substitution to a type
class Substitutable t where
  substitute :: Substitution -> t -> t

instance Substitutable Type where
  substitute subst NatTy = NatTy
  substitute subst t@(TypeTy{}) = t
  substitute subst (FunTy Nothing t1 t2)  = FunTy Nothing (substitute subst t1) (substitute subst t2)
  substitute subst t@(FunTy (Just var) t1 t2) =
    error $ "substitution on '" <> pprint t <> "' unsupported"
  substitute subst (ProdTy t1 t2) = ProdTy (substitute subst t1) (substitute subst t2)
  substitute subst (SumTy t1 t2)  = SumTy (substitute subst t1) (substitute subst t2)
  substitute subst (TyVar var)    = subst var
  substitute subst (Forall{}) =
    error "Polymorphic lambda calculus type showing up in ML types"

instance Substitutable Context where
  substitute subst ctxt =
    map (\(var, ForallTy ids ty) -> (var, ForallTy ids (substitute subst ty))) ctxt
