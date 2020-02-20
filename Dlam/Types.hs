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
normalise Wild = pure Wild
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
equalExprs :: (PrettyPrint e, Monad m, Substitutable m Identifier (Expr e), HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => Expr e -> Expr e -> m Bool
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
    -- Wilds always match.
    (Wild, _) -> pure True
    (_, Wild) -> pure True
    (_, _) -> pure False
  where equalAbs ab1 ab2 = do
          e2s <- substitute (absVar ab2, Var (absVar ab1)) (absExpr ab2)
          withBinding (absVar ab1, (fromTyVal (Nothing, absTy ab1))) $
            (&&) <$> equalExprs (absTy ab1) (absTy ab2) <*> equalExprs (absExpr ab1) e2s


-- | Attempt to infer the types of a definition, and check this against the declared
-- | type, if any.
doNStmtInference :: (PrettyPrint e, Show e, Monad m, Substitutable m Identifier (Expr e), HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => NStmt e -> m (NStmt e)
doNStmtInference r@(Decl v (Just t) e) = do
  setBinder (mkIdent v) (fromTyVal ((Just e), t))
  _ <- checkOrInferType t e
  pure r
doNStmtInference (Decl v Nothing e) = do
  exprTy <- checkOrInferType Wild e
  setBinder (mkIdent v) (fromTyVal (Just e, exprTy))
  pure (Decl v (Just exprTy) e)

-- | Attempt to infer the types of each definition in the AST, failing if a type
-- | mismatch is found.
doNASTInference :: (PrettyPrint e, Show e, Monad m, Substitutable m Identifier (Expr e), HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => NAST e -> m (NAST e)
doNASTInference (NAST ds) = fmap NAST $ mapM doNStmtInference ds


inferUniverseLevel :: (Monad m, Show e, PrettyPrint e, Substitutable m Identifier (Expr e), HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => Expr e -> m Int
inferUniverseLevel e = do
  u <- checkOrInferType Wild e
  norm <- normalise u
  case norm of
    TypeTy l -> pure l
    -- TODO: improve error system (2020-02-20)
    _        -> error $ "expected '" <> pprint e <> "' to be a type, but instead it had type '" <> pprint norm <> "'"


tyMismatch :: (PrettyPrint e) => Expr e -> Expr e -> Expr e -> m a
tyMismatch expr tyExpected tyActual =
  error $ "Error when checking the type of '" <> pprint expr <> "', expected '" <> pprint tyExpected <> "' but got '" <> pprint tyActual <> "'"


ensureEqualTypes :: (PrettyPrint e, Monad m, Substitutable m Identifier (Expr e), HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) =>
  Expr e -> Expr e -> Expr e -> m (Expr e)
ensureEqualTypes expr tyExpected tyActual = do
  typesEqual <- equalExprs tyActual tyExpected
  if typesEqual then pure tyActual
  else tyMismatch expr tyExpected tyActual


-- | 'checkOrInferType ty ex' checks that the type of 'ex' matches 'ty', or infers
-- | it 'ty' is a wild. Evaluates to the calculated type.
checkOrInferType :: (PrettyPrint ext, Show ext, Monad m, Substitutable m Identifier (Expr ext), HasBinders m Identifier v, HasTyVal v (Maybe (Expr ext)) (Expr ext)) =>
  Expr ext -> Expr ext -> m (Expr ext)
checkOrInferType t expr@(Var x) = do
  xTy <- getBinderType x
  case xTy of
    -- TODO: update this to use a better error system (2020-02-19)
    Nothing -> unknownIdentifierErr x
    Just t'  -> do
      typesEqual <- equalExprs t t'
      if typesEqual then pure t'
      else tyMismatch expr t t'
checkOrInferType t@(TypeTy l) expr@(TypeTy l')
  | l == succ l' = pure t
  | otherwise    = tyMismatch expr (TypeTy (succ l')) t
checkOrInferType t expr@(FunTy ab) = do
  k1 <- inferUniverseLevel (absTy ab)
  withBinding (absVar ab, (fromTyVal (Nothing, absTy ab))) $ do
    k2 <- inferUniverseLevel (absExpr ab)
    ensureEqualTypes expr t (TypeTy (max k1 k2))
checkOrInferType (FunTy ab) expr@(Abs x (Just tyX) e) = do
  _ <- ensureEqualTypes expr (absTy ab) tyX
  _ <- inferUniverseLevel tyX
  withBinding (x, (fromTyVal (Nothing, tyX))) $ do
    te <- checkOrInferType (absExpr ab) e
    pure $ FunTy (mkAbs x tyX te)
checkOrInferType (FunTy ab) (Abs x Nothing e) =
  checkOrInferType (FunTy ab) (Abs x (Just (absTy ab)) e)
checkOrInferType t expr@(App e1 e2) = do
  ab <- inferFunTy e1
  withBinding (absVar ab, (fromTyVal (Nothing, absTy ab))) $ do
    argTy <- checkOrInferType (absTy ab) e2
    _ <- ensureEqualTypes e1 (absTy ab) argTy
    appTy <- substitute (absVar ab, e2) (absExpr ab)
    ensureEqualTypes expr t appTy
  where inferFunTy e = do
          t <- checkOrInferType Wild e >>= normalise
          case t of
            FunTy ab -> pure ab
            -- TODO: improve error system (2020-02-20)
            t        -> error $ "Inferred a type '" <> pprint t <> "' for '" <> pprint e <> "' when a function type was expected."
checkOrInferType Wild expr@(Abs x Nothing _) = do
  checkOrInferType (FunTy (mkAbs x Wild Wild)) expr
checkOrInferType Wild expr@(Abs x (Just t) _) = do
  checkOrInferType (FunTy (mkAbs x t Wild)) expr
checkOrInferType Wild (TypeTy l) = pure (TypeTy (succ l))
checkOrInferType t e =
  error $ "Error when checking '" <> pprint e <> "' has type '" <> pprint t <> "'"
