{-# LANGUAGE FlexibleContexts #-}
module Dlam.Types
  ( doNASTInference
  ) where

import Dlam.Binders
  ( HasBinders(..)
  , HasTyVal(fromTyVal)
  , getBinderValue
  , getBinderType
  , withBinding
  )
import Dlam.Substitution
  ( Substitutable(substitute)
  )
import Dlam.Syntax
import Dlam.PrettyPrint


-------------------
----- Helpers -----
-------------------


-- | Indicate that an identifier is not known to be defined.
unknownIdentifierErr :: Identifier -> m a
unknownIdentifierErr x = error $ "unknown identifier " <> show x


-------------------------
----- Normalisation -----
-------------------------


normalise :: (PrettyPrint e, Monad m, HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => Expr e -> m (Expr e)
normalise (Var x) = do
  val <- getBinderValue x
  case val of
    -- TODO: improve error system (2020-02-20)
    Nothing -> unknownIdentifierErr x
    Just Nothing  -> pure $ Var x
    Just (Just e) -> normalise e
normalise r@TypeTy{} = pure r
normalise (FunTy ab) = FunTy <$> normaliseAbs ab
  where normaliseAbs ab = do
          t <- normalise (absTy ab)
          e <- withBinding (absVar ab, (fromTyVal (Nothing, t))) (normalise (absExpr ab))
          pure (mkAbs (absVar ab) t e)
normalise e = error $ "normalise does not yet support '" <> pprint e <> "'"


------------------------------
----- AST Type Inference -----
------------------------------


-- | Check if two expressions are equal.
equalExprs :: (PrettyPrint e, Monad m, Eq e, Substitutable m Identifier (Expr e), HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => Expr e -> Expr e -> m Bool
equalExprs e1 e2 = do
  ne1 <- normalise e1
  ne2 <- normalise e2
  case (ne1, ne2) of
    (Var v1, Var v2) -> pure (v1 == v2)
    (App f1 v1, App f2 v2) -> (&&) <$> equalExprs f1 f2 <*> equalExprs v1 v2
    (TypeTy l1, TypeTy l2) -> pure (l1 == l2)
    (FunTy ab1, FunTy ab2) -> equalAbs ab1 ab2
    (Abs x (Just t1) e1, Abs y (Just t2) e2) ->
      equalAbs (mkAbs x t1 e1) (mkAbs y t2 e2)
    (_, _) -> pure False
  where equalAbs ab1 ab2 = do
          e2s <- substitute (absVar ab2, Var (absVar ab1)) (absExpr ab2)
          (&&) <$> equalExprs (absTy ab1) (absTy ab2) <*> equalExprs (absExpr ab1) e2s


-- | Attempt to infer the types of a definition, and check this against the declared
-- | type, if any.
doNStmtInference :: (Eq e, PrettyPrint e, Show e, Monad m, Substitutable m Identifier (Expr e), HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => NStmt e -> m (NStmt e)
doNStmtInference r@(Decl v (Just t) e) = do
  setBinder (mkIdent v) (fromTyVal ((Just e), t))
  exprTy <- inferType e
  typesEqual <- equalExprs exprTy t
  if typesEqual
  then pure r
  -- TODO: improve error system (2020-02-20)
  else error $ "for definition of '" <> v <> "', the type of '" <> pprint e <> "' was found to be '" <> pprint exprTy <> "' but the expected type was '" <> pprint t <> "'"
doNStmtInference (Decl v Nothing e) = do
  exprTy <- inferType e
  setBinder (mkIdent v) (fromTyVal (Just e, exprTy))
  pure (Decl v (Just exprTy) e)

-- | Attempt to infer the types of each definition in the AST, failing if a type
-- | mismatch is found.
doNASTInference :: (Eq e, PrettyPrint e, Show e, Monad m, Substitutable m Identifier (Expr e), HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => NAST e -> m (NAST e)
doNASTInference (NAST ds) = fmap NAST $ mapM doNStmtInference ds


inferUniverseLevel :: (Monad m, Show e, PrettyPrint e, Substitutable m Identifier (Expr e), HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => Expr e -> m Int
inferUniverseLevel e = do
  u <- inferType e
  norm <- normalise u
  case norm of
    TypeTy l -> pure l
    -- TODO: improve error system (2020-02-20)
    e'       -> error $ "expected '" <> pprint e <> "' to be a type, but instead it had type '" <> pprint norm <> "'"


inferType :: (PrettyPrint ext, Show ext, Monad m, Substitutable m Identifier (Expr ext), HasBinders m Identifier v, HasTyVal v (Maybe (Expr ext)) (Expr ext)) => Expr ext -> m (Expr ext)
inferType (Var x) = do
  ty <- getBinderType x
  case ty of
    -- TODO: update this to use a better error system (2020-02-19)
    Nothing -> unknownIdentifierErr x
    Just t  -> pure t
inferType (FunTy ab) = do
  k1 <- inferUniverseLevel (absTy ab)
  k2 <- inferUniverseLevel (absExpr ab)
  pure $ TypeTy (max k1 k2)
inferType (Abs x (Just tyX) e) = do
  _ <- inferUniverseLevel tyX
  withBinding (x, (fromTyVal (Nothing, tyX))) $ do
    te <- inferType e
    pure $ FunTy (mkAbs x tyX te)
inferType (TypeTy l) = pure $ TypeTy (succ l)
inferType e = error $ "type inference not implemented for '" <> pprint e <> "' (" <> show e <> ")"
