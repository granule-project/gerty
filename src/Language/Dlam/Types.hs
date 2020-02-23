{-# LANGUAGE FlexibleContexts #-}
module Language.Dlam.Types
  ( doNASTInference
  ) where

import Control.Monad (when)

import Language.Dlam.Binders
  ( HasBinders(..)
  , HasTyVal(fromTyVal)
  , getBinderValue
  , getBinderType
  , withBinding
  )
import Language.Dlam.Substitution
  ( Substitutable(substitute)
  )
import Language.Dlam.Syntax
import Language.Dlam.PrettyPrint


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
    Nothing -> pure $ Var x
    Just Nothing  -> pure $ Var x
    Just (Just e) -> normalise e
normalise (FunTy ab) = FunTy <$> normaliseAbs ab
normalise (Abs ab) = Abs <$> normaliseAbs ab
normalise (ProductTy ab) = ProductTy <$> normaliseAbs ab
normalise (App e1 e2) = do
  e1' <- normalise e1
  e2' <- normalise e2
  case e1' of
    Builtin LSuc ->
      case e2' of

        -- lsuc (lmax l1 l2) = lmax (lsuc l1) (lsuc l2)
        (App (App (Builtin LMax) l1) l2) ->
          normalise $ App (App (Builtin LMax) (App (Builtin LSuc) l1)) (App (Builtin LSuc) l2)

        -- lsuc n = SUCC n
        LitLevel n -> pure $ LitLevel (succ n)
        _          -> pure $ App e1' e2'

    -- lmax 0 l = l
    (App (Builtin LMax) (LitLevel 0)) -> pure e2'

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
normalise (IfExpr e1 e2 e3) = do
  e1' <- normalise e1
  e2' <- normalise e2
  e3' <- normalise e3
  case e1' of
    (Builtin DFalse) -> pure e3'
    (Builtin DTrue)  -> pure e2'
    _                -> do
      e2e3equal <- equalExprs e2' e3'
      pure $ if e2e3equal then e2' else IfExpr e1' e2' e3'
normalise (Pair e1 e2) = Pair <$> normalise e1 <*> normalise e2
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
    (Abs ab1, Abs ab2) -> equalAbs ab1 ab2
    (ProductTy ab1, ProductTy ab2) -> equalAbs ab1 ab2
    -- TODO: add proper equality (like Abs) for PairElim (2020-02-22)
    -- Wilds always match.
    (IfExpr e1 e2 e3, IfExpr e1' e2' e3') ->
      (&&) <$> equalExprs e1 e1' <*> ((&&) <$> equalExprs e2 e2' <*> equalExprs e3 e3')
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
doNStmtInference :: (Term e, PrettyPrint e, Monad m, Substitutable m Identifier (Expr e), HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => NStmt e -> m (NStmt e)
doNStmtInference (Decl v t e) = do
  -- make sure that the definition's type is actually a type
  checkExprValidForSignature t

  exprTy <- checkOrInferType t e
  setBinder (mkIdent v) (fromTyVal (Just e, exprTy))
  pure (Decl v exprTy e)
  where
    -- | Check that the given expression is valid as a type signature.
    -- |
    -- | This usually means that the expression is a type, but allows
    -- | for the possibility of holes that haven't yet been resolved.
    checkExprValidForSignature :: (Term e, Monad m, PrettyPrint e, Substitutable m Identifier (Expr e), HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => Expr e -> m ()
    checkExprValidForSignature Wild = pure ()
    checkExprValidForSignature expr = inferUniverseLevel expr >> pure ()


-- | Attempt to infer the types of each definition in the AST, failing if a type
-- | mismatch is found.
doNASTInference :: (Term e, PrettyPrint e, Monad m, Substitutable m Identifier (Expr e), HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => NAST e -> m (NAST e)
doNASTInference (NAST ds) = fmap NAST $ mapM doNStmtInference ds


-- | Infer a level for the given type.
inferUniverseLevel :: (Term e, Monad m, PrettyPrint e, Substitutable m Identifier (Expr e), HasBinders m Identifier v, HasTyVal v (Maybe (Expr e)) (Expr e)) => Expr e -> m (Expr e)
inferUniverseLevel e = do
  u <- synthType e
  norm <- normalise u
  case norm of
    (App (Builtin TypeTy) l) -> pure l
    (IfExpr _ e2 e3) -> do
      l1 <- inferUniverseLevel e2
      l2 <- inferUniverseLevel e3
      normalise (lmaxApp l1 l2)
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


-- | Retrieve an Abstraction from a function type expression, failing if the
-- | expression is not a function type.
getAbsFromFunTy :: (PrettyPrint e, Applicative m) => Expr e -> m (Abstraction e)
getAbsFromFunTy t =
  case t of
    FunTy ab -> pure ab
    -- TODO: improve error system (2020-02-20)
    t        -> error $ "Expected '" <> pprint t <> "' to be a function type, but it wasn't."


-- | Retrieve an Abstraction from a product type expression, failing if the
-- | expression is not a product type.
getAbsFromProductTy :: (PrettyPrint e, Applicative m) => Expr e -> m (Abstraction e)
getAbsFromProductTy t =
  case t of
    ProductTy ab -> pure ab
    -- TODO: improve error system (2020-02-20)
    t        -> error $ "Expected '" <> pprint t <> "' to be a product type, but it wasn't."


-- | 'checkOrInferType ty ex' checks that the type of 'ex' matches 'ty', or infers
-- | it 'ty' is a wild. Evaluates to the calculated type.
checkOrInferType :: (Term ext, PrettyPrint ext, Monad m, Substitutable m Identifier (Expr ext), HasBinders m Identifier v, HasTyVal v (Maybe (Expr ext)) (Expr ext)) =>
  Expr ext -> Expr ext -> m (Expr ext)
--------------
-- Builtins --
--------------
checkOrInferType t expr@(Builtin e) =
  -- here we simply check that the expected type
  -- matches the type defined for the builtin
  ensureEqualTypes expr t $
    case e of
      -- lzero : Level
      LZero -> lzeroTY

      -- lsuc : Level -> Level
      LSuc  -> lsucTY

      -- Type : (l : Level) -> Type (lsuc l)
      TypeTy -> typeTyTY

      -- Level : Type 0
      LevelTy -> levelTyTY

      -- lmax : Level -> Level -> Level
      LMax -> lmaxTY

      -- | Bool : Type 0
      DBool -> dBoolTY

      -- | true : Bool
      DTrue -> dtrueTY

      -- | false : Bool
      DFalse -> dfalseTY
-------------------------
-- Variable expression --
-------------------------
{-
   x : A in G
   G |- A : Type l
   --------------- :: Var
   G |- x : A
-}
checkOrInferType t expr@(Var x) = do
  -- x : A in G
  tA <- getBinderType x >>= maybe (unknownIdentifierErr x) pure

  -- G |- A : Type l
  _l <- inferUniverseLevel tA
  tA <- normalise tA

  -- G |- x : A
  ensureEqualTypes expr t tA
------------------------
-- Pi-type expression --
------------------------
{-
   G |- A : Type l1
   G, x : A |- B : Type l2
   ------------------------------------- :: FunTy
   G |- (x : A) -> B : Type (lmax l1 l2)
-}
checkOrInferType t expr@(FunTy ab) = do
  -- G |- A : Type l1
  l1 <- inferUniverseLevel (absTy ab)

  -- G, x : A |- B : Type l2
  l2 <- withAbsBinding ab $ inferUniverseLevel (absExpr ab)

  -- G |- (x : A) -> B : Type (lmax l1 l2)
  lmaxl1l2 <- normalise (lmaxApp l1 l2)
  ensureEqualTypes expr t (mkUnivTy lmaxl1l2)
---------------------------
-- Dependent tensor type --
---------------------------
{-
   G |- A : Type l1
   G, x : A |- B : Type l2
   ------------------------------------ :: ProductTy
   G |- (x : A) * B : Type (lmax l1 l2)
-}
checkOrInferType t expr@(ProductTy ab) = do
  -- G |- A : Type l1
  l1 <- inferUniverseLevel (absTy ab)

  -- G, x : A |- B : Type l2
  l2 <- withAbsBinding ab $ inferUniverseLevel (absExpr ab)

  -- G |- (x : A) * B : Type (lmax l1 l2)
  lmaxl1l2 <- normalise (lmaxApp l1 l2)
  ensureEqualTypes expr t (mkUnivTy lmaxl1l2)
-----------------------
-- Pair introduction --
-----------------------
{-
   G |- t1 : A
   G |- t2 : [t1/x]B
   G, x : A |- B : Type l
   --------------------------- :: Pair
   G |- (t1, t2) : (x : A) * B
-}
checkOrInferType t expr@(Pair e1 e2) = do
  _l <- inferUniverseLevel t
  abT <- normalise t >>= getAbsFromProductTy

  let x = absVar abT
      tB = absExpr abT

  -- G |- t1 : A
  tA <- checkOrInferType (absTy abT) e1

  -- G, x : A |- B : Type l
  _l <- withTypedVariable x tA (inferUniverseLevel tB)
  tB <- normalise tB

  -- G |- t2 : [t1/x]B
  t1forXinB <- substitute (x, e1) tB
  _e2Ty <- checkOrInferType t1forXinB e2

  -- G |- (t1, t2) : (x : A) * B
  ensureEqualTypes expr t (ProductTy (mkAbs x tA tB))
---------------------
-- Pair eliminator --
---------------------
{-
   x, y nin FV(C)
   G |- t1 : (x : A) * B
   G, x : A |- B : Type l
   G, x : A, y : B |- t2 : C
   ------------------------------ :: PairElim
   G |- let (x, y) = t1 in t2 : C
-}
checkOrInferType t expr@(PairElim x y e1 e2) = do

  -- G |- t1 : (x : A) * B
  e1Ty <- inferProductTy x e1
  tA <- substitute (absVar e1Ty, Var x) (absTy e1Ty)
  tB <- substitute (absVar e1Ty, Var x) (absExpr e1Ty)

  -- G, x : A |- B : Type l
  _l <- withTypedVariable x tA (inferUniverseLevel tB)

  -- G, x : A, y : B |- t2 : C
  tC <- withTypedVariable x tA $ withTypedVariable y tB $ checkOrInferType t e2

  -- x, y nin FV(C)
  when (x `elem` freeVars tC || y `elem` freeVars tC) $
       error $ concat [ "neither '", pprint x, "' nor '", pprint y
                      , "' are allowed to occur in the type of '", pprint e2
                      , "' (which was found to be '", pprint tC, "'), but one or more of them did."
                      ]

  -- G |- let (x, y) = t1 in t2 : C
  ensureEqualTypes expr t tC

  where inferProductTy x e = do
          t <- checkOrInferType (ProductTy (mkAbs x Wild Wild)) e >>= normalise
          getAbsFromProductTy t
--------------------------------------------
-- Abstraction expression, with wild type --
--------------------------------------------
checkOrInferType Wild expr@(Abs ab) = do
  rTy <- withAbsBinding ab $ checkOrInferType Wild (absExpr ab)
  checkOrInferType (FunTy (mkAbs (absVar ab) (absTy ab) rTy)) expr
------------------------
-- Lambda abstraction --
------------------------
{-
   G, x : A |- e : B
   --------------------------------- :: Abs
   G |- \(x : A) -> e : (x : A) -> B
-}
checkOrInferType t expr@(Abs abE) = do
  _l <- inferUniverseLevel t
  abT <- normalise t >>= getAbsFromFunTy

  let x = absVar  abE
      e = absExpr abE
      tA = absTy abT

  -- G, x : A |- e : B
  let tB = absExpr abT
  -- TODO: I feel like we ought to be substituting here, to ensure
  -- the names coming from the abstraction and from the type both get unified? (2020-02-22)
  -- tB <- substitute (absVar abT, Var x) (absExpr abT)
  tB <- withTypedVariable x tA (checkOrInferType tB e)

  -- G |- \x -> e : (x : A) -> B
  ensureEqualTypes expr t (FunTy (mkAbs x tA tB))
----------------------------
-- Application expression --
----------------------------
{-
   G |- t1 : (x : A) -> B
   G |- t2 : A
   ---------------------- :: App
   G |- t1 t2 : [t2/x]B
-}
checkOrInferType t expr@(App e1 e2) = do

  -- G |- t1 : (x : A) -> B
  e1Ty <- inferFunTy e1

  let x  = absVar e1Ty
      tA = absTy  e1Ty
      tB = absExpr e1Ty

  -- G |- t2 : A
  _e2Ty <- checkOrInferType tA e2

  -- G |- t1 t2 : [t2/x]B
  t2forXinB <- substitute (x, e2) tB
  ensureEqualTypes expr t t2forXinB

  where inferFunTy e = do
          t <- synthType e >>= normalise
          getAbsFromFunTy t
-----------------
-- Conditional --
-----------------
{-
   G |- t1 : Bool
   G |- t2 : A
   G |- t3 : B
   ------------------------------------------------ :: IfExpr
   G |- if t1 then t2 else t3 : if t1 then A else B
-}
checkOrInferType t expr@(IfExpr e1 e2 e3) = do

  -- G |- t1 : Bool
  _e1Ty <- inferBoolTy e1

  -- G |- t2 : A
  tA <- synthType e2

  -- G |- t3 : B
  tB <- synthType e3

  -- G |- if t1 then t2 else t3 : if t1 then A else B
  ensureEqualTypes expr t =<< normalise (IfExpr e1 tA tB)

  where inferBoolTy e = do
          t <- synthType e >>= normalise
          case t of
            (Builtin DBool) -> pure t
            -- TODO: improve error system (2020-02-20)
            t        -> error $ "Expected '" <> pprint t <> "' to be a boolean type, but it wasn't."

----------------------
-- Level expression --
----------------------
checkOrInferType t expr@LitLevel{} = ensureEqualTypes expr t levelTy
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
synthType :: (Term ext, PrettyPrint ext, Monad m, Substitutable m Identifier (Expr ext), HasBinders m Identifier v, HasTyVal v (Maybe (Expr ext)) (Expr ext)) =>
  Expr ext -> m (Expr ext)
synthType = checkOrInferType Wild
