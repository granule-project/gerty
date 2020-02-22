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
unknownIdentifierErr x = error $ "unknown identifier '" <> pprint x <> "'"


-------------------------
----- Normalisation -----
-------------------------


-- | Execute the action with the given identifier bound with the given type.
withTypedVariable :: (Monad m, HasTyVal v (Maybe t) (Expr e), HasBinders m Identifier v) =>
  Identifier -> Expr e -> m a -> m a
withTypedVariable v t = withBinding (v, fromTyVal (Nothing, t))


-- | Execute the action with the binder from the abstraction active.
withAbsBinding :: (Monad m, HasTyVal v (Maybe t) (Expr e), HasBinders m Identifier v) =>
  Abstraction e -> m a -> m a
withAbsBinding ab = withTypedVariable (absVar ab) (absTy ab)


-- | Normalise an abstraction via a series of reductions.
normaliseAbs :: (Substitutable m Identifier (Expr e), PrettyPrint e, Monad m, HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => Abstraction e -> m (Abstraction e)
normaliseAbs ab = do
  t <- normalise (absTy ab)
  e <- withAbsBinding ab (normalise (absExpr ab))
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
normalise (Abs ab) = Abs <$> normaliseAbs ab
normalise (ProductTy ab) = ProductTy <$> normaliseAbs ab
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
    (Abs ab) -> substitute (absVar ab, e2') (absExpr ab) >>= normalise
    _              -> pure $ App e1' e2'
normalise (PairElim v1 v2 e1 e2) = do
  e1' <- normalise e1
  case e1' of
    (Pair l r) -> substitute (v1, l) e2 >>= substitute (v2, r) >>= normalise
    _          -> pure $ PairElim v1 v2 e1' e2
normalise (Pair e1 e2) = Pair <$> normalise e1 <*> normalise e2
normalise (Builtin LZero) = pure $ LitLevel 0
normalise e@Builtin{} = pure e
normalise e@LitLevel{} = pure e
normalise e = error $ "normalise does not yet support '" <> pprint e <> "'"


-- | Normalise the expression, performing basic type sanity checks.
normaliseWithCheck :: (Substitutable m Identifier (Expr e), PrettyPrint e, Monad m, HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => Expr e -> m (Expr e)
normaliseWithCheck expr@App{} = do
  _ <- synthType expr
  normalise expr
normaliseWithCheck expr = normalise expr


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
    (Abs ab1, Abs ab2) -> equalAbs ab1 ab2
    (ProductTy ab1, ProductTy ab2) -> equalAbs ab1 ab2
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
          withAbsBinding ab1 $
            (&&) <$> equalExprs (absTy ab1) (absTy ab2) <*> equalExprs (absExpr ab1) e2s


-- | Attempt to infer the types of a definition, and check this against the declared
-- | type, if any.
doNStmtInference :: (PrettyPrint e, Monad m, Substitutable m Identifier (Expr e), HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => NStmt e -> m (NStmt e)
doNStmtInference (Decl v t e) = do
  setBinder (mkIdent v) (fromTyVal (Just e, t))
  exprTy <- checkOrInferType t e
  setBinder (mkIdent v) (fromTyVal (Just e, exprTy))
  pure (Decl v exprTy e)

-- | Attempt to infer the types of each definition in the AST, failing if a type
-- | mismatch is found.
doNASTInference :: (PrettyPrint e, Monad m, Substitutable m Identifier (Expr e), HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => NAST e -> m (NAST e)
doNASTInference (NAST ds) = fmap NAST $ mapM doNStmtInference ds


-- | Infer a level for the given type.
inferUniverseLevel :: (Monad m, PrettyPrint e, Substitutable m Identifier (Expr e), HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => Expr e -> m (Expr e)
inferUniverseLevel e = do
  u <- synthType e
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
checkOrInferType :: (PrettyPrint ext, Monad m, Substitutable m Identifier (Expr ext), HasBinders m Identifier v, HasTyVal v (Maybe (Expr ext)) (Expr ext)) =>
  Expr ext -> Expr ext -> m (Expr ext)
--------------
-- Builtins --
--------------
checkOrInferType t expr@(Builtin e) =
  let genTy = case e of
                LZero -> lzeroTY
                LSuc  -> lsucTY
                TypeTy -> typeTyTY
                LevelTy -> levelTyTY
                LMax -> lmaxTY
  in ensureEqualTypes expr t genTy
-------------------------
-- Variable expression --
-------------------------
checkOrInferType t expr@(Var x) = do
  xTy <- getBinderType x
  case xTy of
    -- TODO: update this to use a better error system (2020-02-19)
    Nothing -> unknownIdentifierErr x
    Just t'  -> do
      typesEqual <- equalExprs t t'
      if typesEqual then pure t'
      else tyMismatch expr t t'
------------------------
-- Pi-type expression --
------------------------
checkOrInferType t expr@(FunTy ab) = do
  k1 <- inferUniverseLevel (absTy ab)
  withAbsBinding ab $ do
    k2 <- inferUniverseLevel (absExpr ab)
    normalise (lmaxApp k1 k2) >>= ensureEqualTypes expr t . mkUnivTy
---------------------------
-- Dependent tensor type --
---------------------------
checkOrInferType t expr@(ProductTy ab) = do
  k1 <- inferUniverseLevel (absTy ab)
  withAbsBinding ab $ do
    k2 <- inferUniverseLevel (absExpr ab)
    normalise (lmaxApp k1 k2) >>= ensureEqualTypes expr t . mkUnivTy
-----------------------
-- Pair introduction --
-----------------------
checkOrInferType (ProductTy abT) expr@(Pair e1 e2) = do
  e1Ty <- checkOrInferType (absTy abT) e1
  let x   = absVar abT
      tyX = absTy  abT
  _ <- ensureEqualTypes expr (absTy abT) e1Ty
  _ <- inferUniverseLevel e1Ty
  withAbsBinding abT $ do
    absT <- substitute (x, e1) (absExpr abT)
    te <- checkOrInferType absT e2
    pure $ ProductTy (mkAbs x tyX te)
---------------------
-- Pair eliminator --
---------------------
checkOrInferType t expr@(PairElim v1 v2 e1 e2) = do
  ab <- inferProductTy e1
  withTypedVariable v1 (absTy ab) $ do
   sndTy <- substitute (absVar ab, e1) (absExpr ab)
   withTypedVariable v2 sndTy $ do
     checkOrInferType t e2
  where inferProductTy e = do
          t <- synthType e >>= normalise
          case t of
            ProductTy ab -> pure ab
            -- TODO: improve error system (2020-02-20)
            t        -> error $ "Inferred a type '" <> pprint t <> "' for '" <> pprint e <> "' when a product type was expected."
------------------------------------------
-- Function type with Lambda expression --
------------------------------------------
checkOrInferType t@(FunTy abT) expr@(Abs abE) =
  case absTy abE of
    Wild ->
      case absTy abT of
        Wild -> error $ concat
                [ "Unable to determine a type for '", pprint (absVar abE)
                , "' in the expression '", pprint expr, "'"]
        ty -> checkOrInferType t (Abs (mkAbs (absVar abE) ty (absExpr abE)))
    _    -> do
      let x   = absVar abE
          tyX = absTy  abE
      _ <- ensureEqualTypes expr (absTy abT) tyX
      _ <- inferUniverseLevel tyX
      withAbsBinding abE $ do
        absT <- substitute (absVar abT, Var x) (absExpr abT)
        te <- checkOrInferType absT (absExpr abE)
        pure $ FunTy (mkAbs x tyX te)
-------------------------
-- Application in type --
-------------------------
checkOrInferType t@App{} expr = do
  t' <- normaliseWithCheck t
  expr' <- normaliseWithCheck expr
  case (t', expr') of
    -- TODO: improve error system (2020-02-21)
    (App (Builtin TypeTy) l, App (Builtin TypeTy) l') -> do
      ln <- normalise l
      ln' <- normalise l'
      case (ln, ln') of
        (Wild, LitLevel{}) -> synthType expr'
        (LitLevel n, LitLevel n') ->
          if n == succ n' then pure t' else tyMismatch expr t (App typeTy (LitLevel (succ n')))
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
    (App{}, _) -> error $ "Don't yet know how to check the type of '" <> pprint expr <> "' against the application '" <> pprint t <> "'"
    _     -> checkOrInferType t' expr
----------------------------
-- Application expression --
----------------------------
checkOrInferType t expr@(App e1 e2) = do
  ab <- inferFunTy e1
  expr' <- normalise expr
  case expr' of
    (App (Builtin TypeTy) (LitLevel n)) -> ensureEqualTypes expr t (mkUnivTy (LitLevel (succ n)))
    _ -> do
      withAbsBinding ab $ do
        argTy <- checkOrInferType (absTy ab) e2
        _ <- ensureEqualTypes e1 (absTy ab) argTy
        appTy <- substitute (absVar ab, e2) (absExpr ab)
        ensureEqualTypes expr t appTy
  where inferFunTy e = do
          t <- synthType e >>= normalise
          case t of
            FunTy ab -> pure ab
            -- TODO: improve error system (2020-02-20)
            t        -> error $ "Inferred a type '" <> pprint t <> "' for '" <> pprint e <> "' when a function type was expected."
----------------------
-- Level expression --
----------------------
checkOrInferType t expr@LitLevel{} = ensureEqualTypes expr t levelTy
--------------------------------------------
-- Abstraction expression, with wild type --
--------------------------------------------
checkOrInferType Wild expr@(Abs ab) = do
  checkOrInferType (FunTy (mkAbs (absVar ab) (absTy ab) Wild)) expr
-------------------------------------
-- When we don't know how to synth --
-------------------------------------
checkOrInferType Wild expr =
  error $ "I was asked to try and synthesise a type for '" <> pprint expr <> "' but I wasn't able to do so."
----------------------------------
-- Currently unsupported checks --
----------------------------------
checkOrInferType t e =
  error $ "Error when checking '" <> pprint e <> "' has type '" <> pprint t <> "'"


-- | Attempt to synthesise a type for the given expression.
synthType :: (PrettyPrint ext, Monad m, Substitutable m Identifier (Expr ext), HasBinders m Identifier v, HasTyVal v (Maybe (Expr ext)) (Expr ext)) =>
  Expr ext -> m (Expr ext)
synthType = checkOrInferType Wild
