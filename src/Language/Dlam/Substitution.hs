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
import qualified Language.Dlam.Syntax.Internal as I
import qualified Language.Dlam.Scoping.Monad as SM
import Language.Dlam.Scoping.Monad (SM)
import qualified Language.Dlam.TypeChecking.Monad as CM
import Language.Dlam.TypeChecking.Monad (CM)
import Language.Dlam.Util.Peekaboo
import Language.Dlam.Util.Pretty (pprintShow)


class Fresh m i | m -> i where
  fresh :: m i


class (Fresh m i) => Freshenable m i e | m -> i where
  freshenWithSeed :: i -> e -> m e


freshen :: (Monad m, Freshenable m i e) => e -> m e
freshen e = fresh >>= (`freshenWithSeed` e)


class Substitutable m n e where
  substitute :: n -> e -> m e


substAbs :: (Name, Expr) -> Abstraction -> CM Abstraction
substAbs s ab = do
  let v = absVar ab
  v' <- freshen v
  t <- substitute s (absTy ab)
  CM.withTypedVariable v' t $ do
    e <- substitute (v, Var v') (absExpr ab) >>= substitute s
    pure $ mkAbs v' t e


instance {-# OVERLAPPABLE #-} (Monad m, Substitutable m n e, Foldable t) => Substitutable m (t n) e where
  substitute n e = F.foldrM substitute e n


instance {-# OVERLAPS #-} Substitutable CM (Name, Expr) Expr where
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


instance {-# OVERLAPS #-} Substitutable CM (Name, I.Term) (I.FullyApplied a) where
  substitute s t = I.fullyApplied (un t) <$> mapM (substitute s) (I.appliedArgs t)


instance {-# OVERLAPS #-} Substitutable CM (Name, I.Term) I.Type where
  substitute s@(v, _t') t = do
    l <- substitute s (I.level t)
    case un t of
      (I.Universe ul) -> I.mkType . I.Universe <$> substitute s ul <*> pure l
      (I.TyApp ap) ->
        case un ap of
          I.AppTyCon{} -> I.mkType . I.TyApp <$> substitute s ap <*> pure l
          I.AppTyDef{} -> I.mkType . I.TyApp <$> substitute s ap <*> pure l
          va@I.AppTyVar{}
            | length (I.appliedArgs ap) == 0 -> pure $ I.mkType (I.TyApp ap) l
            | otherwise -> I.mkType . I.TyApp . I.fullyApplied va <$> mapM (substitute s) (I.appliedArgs ap) <*> pure l
      (I.TTForApp (I.IsPi arg resTy)) -> do
        let v' = I.argVar arg
        arg' <- substitute s arg
        resTy' <- if v == v' then pure resTy else substitute s resTy
        pure $ I.mkType (I.Pi arg' resTy') l


instance {-# OVERLAPS #-} Substitutable CM (Name, I.Term) I.Grading where
  -- grades are simple nats at the moment, so no substitution (2020-03-16, GD)
  substitute _ g = pure g


instance {-# OVERLAPS #-} Substitutable CM (Name, I.Term) I.Arg where
  substitute s arg = do
    g <- substitute s (I.grading arg)
    ty <- substitute s (I.typeOf arg)
    pure $ I.mkArg (I.argVar arg) g ty


instance {-# OVERLAPS #-} Substitutable CM (Name, I.Term) I.Level where
  -- [t/x](Concrete n) === Concrete n
  substitute _ l@I.Concrete{} = pure l
  -- [t/x](Plus n t') === Plus n [t/x]t'
  substitute s (I.Plus n t) = I.Plus n <$> substitute s t
  substitute s (I.Max l1 l2) = I.Max <$> substitute s l1 <*> substitute s l2


instance {-# OVERLAPS #-} Substitutable CM (Name, I.Term) I.LevelAtom where
  substitute s (I.LTerm t) = I.LTerm <$> substitute s t


instance {-# OVERLAPS #-} Substitutable CM (Name, I.Term) I.Term where
  substitute s (I.TypeTerm t) = I.TypeTerm <$> substitute s t
  substitute s (I.Level l) = I.Level <$> substitute s l
  substitute s@(v, _) (I.Lam arg body) = do
    let v' = I.argVar arg
    arg' <- substitute s arg
    body' <- if v == v' then pure body else substitute s body
    pure $ I.Lam arg' body'
  substitute s@(v, t) t'@(I.App f) =
    case un f of
      I.Var v' | length (I.appliedArgs f) == 0 -> pure $ if v == v' then t else t'
      _ -> I.App . I.fullyApplied (un f) <$> mapM (substitute s) (I.appliedArgs f)
  substitute (v, t) t' =
    CM.notImplemented $ "substituting '" <> pprintShow t <> "' for '" <> pprintShow v <> "' in term '" <> pprintShow t' <> "'"


instance Fresh CM NameId where
  fresh = CM.getFreshNameId

instance Fresh SM NameId where
  fresh = SM.getFreshNameId

instance Freshenable CM NameId Name where
  freshenWithSeed i v = pure $ v { nameId = i }
