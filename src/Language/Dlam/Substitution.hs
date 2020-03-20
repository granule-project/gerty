{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
module Language.Dlam.Substitution
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

import Language.Dlam.Syntax.Abstract
import Language.Dlam.Syntax.Common (NameId)
import qualified Language.Dlam.Scoping.Monad as SM
import Language.Dlam.Scoping.Monad (SM)
import qualified Language.Dlam.TypeChecking.Monad as CM
import Language.Dlam.TypeChecking.Monad (CM)


class Fresh m i | m -> i where
  fresh :: m i


class (Fresh m i) => Freshenable m i e | m -> i where
  freshenWithSeed :: i -> e -> m e


freshen :: (Monad m, Freshenable m i e) => e -> m e
freshen e = fresh >>= (`freshenWithSeed` e)


class Substitutable m n e where
  substitute :: n -> e -> m e


substAbs :: (AName, Expr) -> Abstraction -> CM Abstraction
substAbs s ab = do
  let v = absVar ab
  v' <- freshen v
  t <- substitute s (absTy ab)
  CM.withTypedVariable v' t $ do
    e <- substitute (v, Var v') (absExpr ab) >>= substitute s
    pure $ mkAbs v' t e


instance {-# OVERLAPPABLE #-} (Monad m, Substitutable m n e, Foldable t) => Substitutable m (t n) e where
  substitute n e = F.foldrM substitute e n


instance {-# OVERLAPS #-} Substitutable CM (AName, Expr) Expr where
  substitute (v, e) (Var x)
    | v == x    = pure e
    | otherwise = pure (Var x)
  substitute s (FunTy abs) = FunTy <$> substAbs s abs
  substitute s (Lam   abs) = Lam   <$> substAbs s abs
  substitute s (ProductTy abs) = ProductTy <$> substAbs s abs
  substitute s (Pair e1 e2) = Pair <$> substitute s e1 <*> substitute s e2
  substitute s (App e1 e2) = do
    e1' <- substitute s e1
    e2' <- substitute s e2
    pure (App e1' e2')
  substitute s (Coproduct e1 e2) = Coproduct <$> substitute s e1 <*> substitute s e2
  substitute s@(v, _) (CoproductCase (z, tC) (x, c) (y, d) e) = do
    e' <- substitute s e
    tC' <- if v == z then pure tC else substitute s tC
    c'  <- if v == x then pure c else substitute s c
    d'  <- if v == y then pure d else substitute s d
    pure $ CoproductCase (z, tC') (x, c') (y, d') e'
  substitute s@(v, _) (NatCase (x, tC) cz (w, y, cs) n) = do
    tC' <- if v == x then pure tC else substitute s tC
    cz' <- substitute s cz
    cs' <- if v == y || v == w then pure cs else substitute s cs
    n'  <- substitute s n
    pure $ NatCase (x, tC') cz' (w, y, cs') n'
  substitute _ e@LitLevel{} = pure e
  substitute _ e@Hole{} = pure e
  substitute _ e@Implicit = pure e
  substitute s (Sig e t) = Sig <$> substitute s e <*> substitute s t
  substitute s@(v, _) (RewriteExpr (x, y, pv, tC) (z, c) a b pe) = do
    tC' <- if v `elem` [x, y, pv] then pure tC else substitute s tC
    c' <- if v == z then pure c else substitute s c
    a' <- substitute s a
    b' <- substitute s b
    pe' <- substitute s pe
    pure $ RewriteExpr (x, y, pv, tC') (z, c') a' b' pe'
  substitute s@(v, _) (EmptyElim (x, tC) a) = do
    tC' <- if v == x then pure tC else substitute s tC
    a' <- substitute s a
    pure $ EmptyElim (x, tC') a'
  substitute _ e@Builtin{} = pure e
  substitute s@(v, _) (Let (LetPatBound p e) (Sig r t)) = do
    e' <- substitute s e
    r' <- if v `Set.member` (Set.map unBindName (boundSubjectVars p)) then pure r else substitute s r
    t' <- if v `Set.member` (Set.map unBindName (boundTypingVars p)) then pure t else substitute s t
    pure $ Let (LetPatBound p e') (Sig r' t')
  substitute s@(v, _) (Let (LetPatBound p e) r) = do
    e' <- substitute s e
    r' <- if v `Set.member` (Set.map unBindName (boundSubjectVars p)) then pure r else substitute s r
    pure $ Let (LetPatBound p e') r'
  substitute _ EType = pure EType

instance Fresh CM NameId where
  fresh = CM.getFreshNameId

instance Fresh SM NameId where
  fresh = SM.getFreshNameId

instance Freshenable CM NameId AName where
  freshenWithSeed i v = pure $ v { nameId = i }
