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


-- | Normalise an abstraction via a series of reductions.
normaliseAbs :: (Substitutable m Identifier (Expr e), PrettyPrint e, Monad m, HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => Abstraction e -> m (Abstraction e)
normaliseAbs ab = do
  t <- normalise (absTy ab)
  e <- withBinding (absVar ab, (fromTyVal (Nothing, t))) (normalise (absExpr ab))
  pure (mkAbs (absVar ab) t e)


-- | Normalise the expression via a series of reductions.
normalise :: (Substitutable m Identifier (Expr e), PrettyPrint e, Monad m, HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => Expr e -> m (Expr e)
normalise Wild = pure Wild
normalise (Var x) = do
  val <- getBinderValue x
  case val of
    -- TODO: improve error system (2020-02-20)
    Nothing -> unknownIdentifierErr x
    Just Nothing  -> pure $ Var x
    Just (Just e) -> normalise e
normalise (FunTy ab) = FunTy <$> normaliseAbs ab
normalise (Abs x (Just xTy) expr) = do
  abs <- normaliseAbs (mkAbs x xTy expr)
  pure $ Abs (absVar abs) (Just (absTy abs)) (absExpr abs)
normalise (App e1 e2) = do
  e1' <- normalise e1
  e2' <- normalise e2
  case e1' of
    Builtin LSuc -> pure $
      case e2' of
        LitLevel n -> LitLevel (succ n)
        _          -> App e1' e2'
    (App (Builtin LMax) (LitLevel n)) ->
      case e2' of
        -- if the expression is of the form 'lmax m n' where 'm' and 'n' are literal
        -- numbers, then normalise by taking the maximum.
        LitLevel m -> pure $ LitLevel (max n m)
        _          -> pure $ App e1' e2'
    -- (\x -> e) e' ----> [e'/x] e
    (Abs x _ xE) -> substitute (x, e2') xE >>= normalise
    _              -> pure $ App e1' e2'
normalise (Builtin LZero) = pure $ LitLevel 0
normalise e@Builtin{} = pure e
normalise e@LitLevel{} = pure e
normalise e = error $ "normalise does not yet support '" <> pprint e <> "'"


------------------------------
----- AST Type Inference -----
------------------------------


-- | Check if two expressions are equal under normalisation.
equalExprs :: (PrettyPrint e, Monad m, Substitutable m Identifier (Expr e), HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => Expr e -> Expr e -> m Bool
equalExprs e1 e2 = do
  ne1 <- normalise e1
  ne2 <- normalise e2
  case (ne1, ne2) of
    (Var v1, Var v2) -> pure (v1 == v2)
    (App f1 v1, App f2 v2) -> (&&) <$> equalExprs f1 f2 <*> equalExprs v1 v2
    (FunTy ab1, FunTy ab2) -> equalAbs ab1 ab2
    (Abs x (Just t1) e1, Abs y (Just t2) e2) ->
      equalAbs (mkAbs x t1 e1) (mkAbs y t2 e2)
    -- Wilds always match.
    (Wild, _) -> pure True
    (_, Wild) -> pure True
    (Builtin b1, Builtin b2) -> pure (b1 == b2)
    (LitLevel n, LitLevel m) -> pure (n == m)
    (_, _) -> pure False
  where equalAbs ab1 ab2 = do
          -- checking \(x : a) -> b = \(y : c) -> d
          -- we say:
          -- d' = [y/x]d
          -- then check:
          -- a = c and b = d' (with (x : a) in scope)
          e2s <- substitute (absVar ab2, Var (absVar ab1)) (absExpr ab2)
          withBinding (absVar ab1, (fromTyVal (Nothing, absTy ab1))) $
            (&&) <$> equalExprs (absTy ab1) (absTy ab2) <*> equalExprs (absExpr ab1) e2s


-- | Attempt to infer the types of a definition, and check this against the declared
-- | type, if any.
doNStmtInference :: (PrettyPrint e, Show e, Monad m, Substitutable m Identifier (Expr e), HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => NStmt e -> m (NStmt e)
doNStmtInference (Decl v Wild e) = do
  exprTy <- checkOrInferType Wild e
  setBinder (mkIdent v) (fromTyVal (Just e, exprTy))
  pure (Decl v exprTy e)
doNStmtInference r@(Decl v t e) = do
  setBinder (mkIdent v) (fromTyVal ((Just e), t))
  _ <- checkOrInferType t e
  pure r

-- | Attempt to infer the types of each definition in the AST, failing if a type
-- | mismatch is found.
doNASTInference :: (PrettyPrint e, Show e, Monad m, Substitutable m Identifier (Expr e), HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => NAST e -> m (NAST e)
doNASTInference (NAST ds) = fmap NAST $ mapM doNStmtInference ds


-- | Infer a level for the given type.
inferUniverseLevel :: (Monad m, Show e, PrettyPrint e, Substitutable m Identifier (Expr e), HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => Expr e -> m (Expr e)
inferUniverseLevel e = do
  u <- checkOrInferType Wild e
  norm <- normalise u
  case norm of
    (App (Builtin TypeTy) l) -> pure l
    -- TODO: improve error system (2020-02-20)
    _        -> error $ "expected '" <> pprint e <> "' to be a type, but instead it had type '" <> pprint norm <> "'"


-- | 'tyMismatch expr tyExpected tyActual' generates failure, indicating
-- | that an expression was found to have a type that differs from expected.
tyMismatch :: (PrettyPrint e) => Expr e -> Expr e -> Expr e -> m a
tyMismatch expr tyExpected tyActual =
  error $ "Error when checking the type of '" <> pprint expr <> "', expected '" <> pprint tyExpected <> "' but got '" <> pprint tyActual <> "'"


-- | 'ensureEqualTypes expr tyExpected tyActual' checks that 'tyExpected' and 'tyActual'
-- | represent the same type (under normalisation), and fails if they differ.
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
checkOrInferType t expr@(FunTy ab) = do
  k1 <- inferUniverseLevel (absTy ab)
  withBinding (absVar ab, (fromTyVal (Nothing, absTy ab))) $ do
    k2 <- inferUniverseLevel (absExpr ab)
    normalise (lmaxApp k1 k2) >>= ensureEqualTypes expr t . mkUnivTy
checkOrInferType (FunTy ab) expr@(Abs x (Just tyX) e) = do
  _ <- ensureEqualTypes expr (absTy ab) tyX
  _ <- inferUniverseLevel tyX
  withBinding (x, (fromTyVal (Nothing, tyX))) $ do
    te <- checkOrInferType (absExpr ab) e
    pure $ FunTy (mkAbs x tyX te)
checkOrInferType (FunTy ab) (Abs x Nothing e) =
  checkOrInferType (FunTy ab) (Abs x (Just (absTy ab)) e)
checkOrInferType t@App{} expr = do
  t' <- normalise t
  case t' of
    -- TODO: improve error system (2020-02-21)
    App (Builtin TypeTy) l -> do
      expr' <- normalise expr
      case expr' of
        (App (Builtin TypeTy) l') -> do
          -- checkOrInferType t@(TypeTy l) expr@(TypeTy l') = do
          ln <- normalise l
          ln' <- normalise l'
          case (ln, ln') of
            (LitLevel n, LitLevel n') ->
              -- TODO: replace with ensureEqualTypes (2020-02-21)
              if n == succ n' then pure t' else tyMismatch expr (App typeTy (LitLevel (succ n'))) t
            (LitLevel{}, _) ->
              error $ concat [ "When checking the expression '", pprint expr
                             , "' against the type '", pprint t
                             , "' I was expecting '", pprint ln'
                             , "' to be a level, but I couldn't determine that it was."]
            (_, LitLevel{}) ->
              error $ concat [ "When checking the expression '", pprint expr
                             , "' against the type '", pprint t
                             , "' I was expecting '", pprint ln
                             , "' to be a level, but I couldn't determine that it was."]
            (_, _) ->
              error $ concat [ "When checking the expression '", pprint expr
                             , "' against the type '", pprint t
                             , "' I was expecting '", pprint ln, "' and '", pprint ln'
                             , "' to be levels, but I couldn't determine that they were."]
        _ -> error $ "Don't yet know how to check the type of '" <> pprint expr <> "' against the application '" <> pprint t <> "'"
    App{} -> error $ "Don't yet know how to check the type of '" <> pprint expr <> "' against the application '" <> pprint t <> "'"
    _     -> checkOrInferType t' expr
checkOrInferType t expr@(App e1 e2) = do
  ab <- inferFunTy e1
  expr' <- normalise expr
  case expr' of
    (App (Builtin TypeTy) (LitLevel n)) -> pure $ mkUnivTy (LitLevel (succ n))
    _ -> do
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
checkOrInferType t expr@LitLevel{} = ensureEqualTypes expr t levelTy
checkOrInferType Wild expr@(Abs x (Just t) _) = do
  checkOrInferType (FunTy (mkAbs x t Wild)) expr
checkOrInferType t e =
  error $ "Error when checking '" <> pprint e <> "' has type '" <> pprint t <> "'"
