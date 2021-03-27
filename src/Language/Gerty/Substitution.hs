{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
module Language.Gerty.Substitution
  (
  -- * Substitution
    Substitutable(..)

  -- * Freshening
  , Fresh(..)
  , Freshenable(..)
  , freshen
  ) where


import qualified Data.Foldable as F
import qualified Data.Set as Set

import Language.Gerty.Syntax.Abstract
import Language.Gerty.Syntax.Common (NameId)
import qualified Language.Gerty.Scoping.Monad as SM
import Language.Gerty.Scoping.Monad (SM)
import qualified Language.Gerty.TypeChecking.Monad as CM
import Language.Gerty.TypeChecking.Monad (CM)


class Fresh m i | m -> i where
  fresh :: m i


class (Fresh m i) => Freshenable m i e | m -> i where
  freshenWithSeed :: i -> e -> m e


freshen :: (Monad m, Freshenable m i e) => e -> m e
freshen e = fresh >>= (`freshenWithSeed` e)


class Substitutable m n e where
  substitute :: n -> e -> m e


-- TODO: with first-class grades, ensure substitutions propagate throuh them (2020-06-20)
substAbs :: (Name, Expr) -> Abstraction -> CM Abstraction
substAbs s ab = do
  let v = absVar ab
  v' <- freshen v
  t <- substitute s (absTy ab)
  CM.withTypedVariable v' t $ do
    e <- substitute (v, Var v') (absExpr ab) >>= substitute s
    pure $ mkAbsGr v' t (subjectGrade ab) (subjectTypeGrade ab) e


-- | Substitute into an expression that's guarded by a pattern.
substitutePatGuarded :: (Name, Expr) -> Pattern -> Expr -> CM Expr
substitutePatGuarded s@(v, _) p e = do
    if v `Set.member` (Set.map unBindName (patBoundVars p)) then pure e else substitute s e


instance {-# OVERLAPPABLE #-} (Monad m, Substitutable m n e, Foldable t) => Substitutable m (t n) e where
  substitute n e = F.foldrM substitute e n


instance {-# OVERLAPS #-} Substitutable CM (Name, Level) Level where
  -- TODO: add support for full substitutions if we add variables to levels (2020-06-13)
  substitute _ l = pure l

instance {-# OVERLAPS #-} Substitutable CM (Name, Expr) CaseBinding where
  substitute s (CasePatBound p e) = do
    e <- substitutePatGuarded s p e
    pure (CasePatBound p e)

instance {-# OVERLAPS #-} Substitutable CM (Name, Expr) Expr where
  substitute (v, e) (Var x)
    | v == x    = pure e
    | otherwise = pure (Var x)
  substitute _ (Def n) = pure (Def n)
  substitute _ UnitTy = pure UnitTy
  substitute _ Unit = pure Unit
  substitute s (FunTy abs) = FunTy <$> substAbs s abs
  -- TODO: when support for grades is added, substitute into the grades here (2020-06-21)
  substitute s (BoxTy g e) = BoxTy g <$> substitute s e
  substitute s (Box e) = Box <$> substitute s e
  substitute s (Lam   abs) = Lam   <$> substAbs s abs
  substitute s (ProductTy abs) = ProductTy <$> substAbs s abs
  substitute s (Pair e1 e2) = Pair <$> substitute s e1 <*> substitute s e2
  substitute s (App e1 e2) = do
    e1' <- substitute s e1
    e2' <- substitute s e2
    pure (App e1' e2')
  substitute _ e@Universe{} = pure e
  substitute _ e@Hole{} = pure e
  substitute _ e@Implicit{} = pure e
  substitute _ e@NatTy = pure e
  substitute _ e@NZero = pure e
  substitute _ e@NSucc = pure e
  substitute s (Sig e t) = Sig <$> substitute s e <*> substitute s t
  substitute s (Case e Nothing binds) = do
    e <- substitute s e
    binds <- mapM (substitute s) binds
    pure $ Case e Nothing binds
  substitute s (Case e (Just (p, t)) binds) = do
    e <- substitute s e
    binds <- mapM (substitute s) binds
    t <- substitutePatGuarded s p t
    pure $ Case e (Just (p, t)) binds


instance Fresh CM NameId where
  fresh = CM.getFreshNameId

instance Fresh SM NameId where
  fresh = SM.getFreshNameId

instance Freshenable CM NameId Name where
  freshenWithSeed i v = pure $ v { nameId = i }
