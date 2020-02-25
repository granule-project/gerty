{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
module Language.Dlam.Types
  ( doNASTInference
  , Checkable
  ) where

import Control.Monad (when)
import Control.Monad.Except (MonadError)

import Language.Dlam.Binders
  ( HasNamedMap(..)
  , HasBinderMap
  , BinderMap
  , HasNormalFormMap
  , NormalFormMap
  , IsTag(..)
  , HasTyVal(fromTyVal)
  , getBinder
  , getBinderValue
  , getBinderType
  , withBinding
  )
import Language.Dlam.Exception
import Language.Dlam.Substitution
  ( Substitutable(substitute)
  )
import Language.Dlam.Syntax.Syntax
import Language.Dlam.Syntax.PrettyPrint


-------------------
----- Helpers -----
-------------------


-- | Common constraints required for type checking.
type Checkable m err ann e v =
  ( Ord e, PrettyPrint e
  , Ord ann
  , Default ann
  , Monad m
  , Substitutable m Identifier (Expr ann e)
  , HasBinderMap m Identifier v
  , HasNormalFormMap m (Expr ann e) (Expr ann e)
  , HasTyVal v (Maybe (Expr ann e)) (Expr ann e)
  , MonadError err m
  , InjErr (SynthError ann e) err
  , InjErr (TypeError ann e) err
  , InjErr ImplementationError err
  , InjErr ScopeError err
  )


-------------------------
----- Normalisation -----
-------------------------


-- | Execute the action with the given identifier bound with the given type.
withTypedVariable :: (Monad m, HasTyVal v (Maybe t) (Expr ann e), HasBinderMap m Identifier v) =>
  Identifier -> Expr ann e -> m a -> m a
withTypedVariable v t = withBinding (mkTag :: BinderMap) (v, fromTyVal (Nothing, t))


-- | Execute the action with the binder from the abstraction active.
withAbsBinding :: (Monad m, HasTyVal v (Maybe t) (Expr ann e), HasBinderMap m Identifier v) =>
  Abstraction ann e -> m a -> m a
withAbsBinding ab = withTypedVariable (absVar ab) (absTy ab)


-- | 'withExprNormalisingTo e nf m' runs 'm', but causes
-- | any expressions that would usually normalise to (the normal form of)
-- | 'e' to instead normalise to 'nf'.
withExprNormalisingTo :: (Checkable m err ann e v) => Expr ann e -> Expr ann e -> m a -> m a
withExprNormalisingTo e nf m = normalise e >>= \e -> withBinding (mkTag :: NormalFormMap) (e, nf) m


-- | Normalise an abstraction via a series of reductions.
normaliseAbs :: (Checkable m err ann e v) => Abstraction ann e -> m (Abstraction ann e)
normaliseAbs ab = do
  t <- normalise (absTy ab)
  e <- withAbsBinding ab (normalise (absExpr ab))
  pure (mkAbs (absVar ab) t e)


-- | Indicate that the expresion is now in an irreducible normal form.
-- |
-- | This allows for e.g., substituting normal forms.
finalNormalForm :: (Functor m, Ord e, Ord ann, HasNormalFormMap m (Expr ann e) (Expr ann e)) => (Expr ann e) -> m (Expr ann e)
finalNormalForm e = maybe e id <$> getBinder (mkTag :: NormalFormMap) e


-- | Normalise the expression via a series of reductions.
normalise :: (Checkable m err ann e v) => Expr ann e -> m (Expr ann e)
normalise e@Implicit{} = finalNormalForm e
normalise (Var ann x) = do
  val <- getBinderValue (mkTag :: BinderMap) x
  case val of
    Nothing -> finalNormalForm $ Var ann x
    Just Nothing  -> finalNormalForm $ Var ann x
    Just (Just e) -> normalise e
normalise (FunTy ann ab) = finalNormalForm =<< FunTy ann <$> normaliseAbs ab
normalise (Abs ann ab) = finalNormalForm =<< Abs ann <$> normaliseAbs ab
normalise (ProductTy ann ab) = finalNormalForm =<< ProductTy ann <$> normaliseAbs ab
normalise (App ann e1 e2) = do
  e1' <- normalise e1
  e2' <- normalise e2
  case e1' of
    Builtin _ LSuc ->
      case e2' of

        -- lsuc (lmax l1 l2) = lmax (lsuc l1) (lsuc l2)
        (App _ (App _ (Builtin _ LMax) l1) l2) ->
          normalise $ App ann (App def (Builtin def LMax) (App def (Builtin def LSuc) l1)) (App def (Builtin def LSuc) l2)

        -- lsuc n = SUCC n
        LitLevel ann n -> finalNormalForm $ LitLevel ann (succ n)
        _          -> finalNormalForm $ App ann e1' e2'

    -- lmax 0 l = l
    (App _ (Builtin _ LMax) (LitLevel _ 0)) -> finalNormalForm e2'

    (App _ (Builtin _ LMax) (LitLevel _ n)) ->
      case e2' of
        -- lmax (n + 1) (lsuc m) = lsuc m
        (App _ (Builtin _ LSuc) _) | n > 0 -> finalNormalForm e2'
        -- if the expression is of the form 'lmax m n' where 'm' and 'n' are literal
        -- numbers, then normalise by taking the maximum.
        LitLevel ann m -> finalNormalForm $ LitLevel ann (max n m)
        _          -> finalNormalForm $ App ann e1' e2'
    -- (\x -> e) e' ----> [e'/x] e
    (Abs _ ab) -> substitute (absVar ab, e2') (absExpr ab) >>= normalise
    _              -> finalNormalForm $ App ann e1' e2'
normalise (PairElim ann v0 v1 v2 e1 e2 e3) = do
  e1' <- normalise e1
  e3' <- normalise e3
  case e1' of
    (Pair _ l r) -> substitute (v1, l) e2 >>= substitute (v2, r) >>= normalise
    _          -> finalNormalForm $ PairElim ann v0 v1 v2 e1' e2 e3'
normalise (IfExpr ann e1 e2 e3) = do
  e1' <- normalise e1
  e2' <- normalise e2
  e3' <- normalise e3
  case e1' of
    (Builtin _ DFalse) -> finalNormalForm e3'
    (Builtin _ DTrue)  -> finalNormalForm e2'
    _                -> do
      e2e3equal <- equalExprs e2' e3'
      finalNormalForm $ if e2e3equal then e2' else IfExpr ann e1' e2' e3'
normalise (Pair ann e1 e2) = finalNormalForm =<< Pair ann <$> normalise e1 <*> normalise e2
normalise (Builtin ann LZero) = finalNormalForm $ LitLevel ann 0
normalise e@Builtin{} = finalNormalForm e
normalise e@LitLevel{} = finalNormalForm e
normalise e = notImplemented $ "normalise does not yet support '" <> pprint e <> "'"


------------------------------
----- AST Type Inference -----
------------------------------


-- | Check if two expressions are equal under normalisation.
equalExprs :: (Checkable m err ann e v) => Expr ann e -> Expr ann e -> m Bool
equalExprs e1 e2 = do
  ne1 <- normalise e1
  ne2 <- normalise e2
  case (ne1, ne2) of
    (Var _ v1, Var _ v2) -> pure (v1 == v2)
    (App _ f1 v1, App _ f2 v2) -> (&&) <$> equalExprs f1 f2 <*> equalExprs v1 v2
    (FunTy _ ab1, FunTy _ ab2) -> equalAbs ab1 ab2
    (Abs _ ab1, Abs _ ab2) -> equalAbs ab1 ab2
    (ProductTy _ ab1, ProductTy _ ab2) -> equalAbs ab1 ab2
    -- TODO: add proper equality (like Abs) for PairElim (2020-02-22)
    (IfExpr _ e1 e2 e3, IfExpr _ e1' e2' e3') ->
      (&&) <$> equalExprs e1 e1' <*> ((&&) <$> equalExprs e2 e2' <*> equalExprs e3 e3')
    -- Implicits always match.
    (Implicit{}, _) -> pure True
    (_, Implicit{}) -> pure True
    (Builtin _ b1, Builtin _ b2) -> pure (b1 == b2)
    (LitLevel _ n, LitLevel _ m) -> pure (n == m)
    (_, _) -> pure False
  where equalAbs ab1 ab2 = do
          -- checking \(x : a) -> b = \(y : c) -> d
          -- we say:
          -- d' = [y/x]d
          -- then check:
          -- a = c and b = d' (with (x : a) in scope)
          e2s <- substitute (absVar ab2, Var def (absVar ab1)) (absExpr ab2)
          withAbsBinding ab1 $
            (&&) <$> equalExprs (absTy ab1) (absTy ab2) <*> equalExprs (absExpr ab1) e2s


-- | Attempt to infer the types of a definition, and check this against the declared
-- | type, if any.
doNStmtInference :: (Checkable m err ann e v, Term e) => NStmt ann e -> m (NStmt ann e)
doNStmtInference (Decl v Nothing e) =
  doNStmtInference (Decl v (Just (Implicit def)) e)
doNStmtInference (Decl v (Just t) e) = do
  -- make sure that the definition's type is actually a type
  checkExprValidForSignature t

  exprTy <- checkOrInferType t e
  setBinder (mkTag :: BinderMap) (mkIdent v) (fromTyVal (Just e, exprTy))
  pure (Decl v (Just exprTy) e)
  where
    -- | Check that the given expression is valid as a type signature.
    -- |
    -- | This usually means that the expression is a type, but allows
    -- | for the possibility of holes that haven't yet been resolved.
    checkExprValidForSignature :: (Checkable m err ann e v, Term e) => Expr ann e -> m ()
    checkExprValidForSignature Implicit{} = pure ()
    checkExprValidForSignature expr = inferUniverseLevel expr >> pure ()


-- | Attempt to infer the types of each definition in the AST, failing if a type
-- | mismatch is found.
doNASTInference :: (Checkable m err ann e v, Term e) => NAST ann e -> m (NAST ann e)
doNASTInference (NAST ds) = fmap NAST $ mapM doNStmtInference ds


-- | Infer a level for the given type.
inferUniverseLevel :: (Checkable m err ann e v, Term e) => Expr ann e -> m (Expr ann e)
inferUniverseLevel e = do
  u <- synthType e
  norm <- normalise u
  case norm of
    (App _ (Builtin _ TypeTy) l) -> pure l
    (IfExpr _ _ e2 e3) -> do
      l1 <- inferUniverseLevel e2
      l2 <- inferUniverseLevel e3
      normalise (lmaxApp l1 l2)
    _        -> expectedInferredTypeForm "universe" e norm


-- | 'ensureEqualTypes expr tyExpected tyActual' checks that 'tyExpected' and 'tyActual'
-- | represent the same type (under normalisation), and fails if they differ.
ensureEqualTypes :: (Checkable m err ann e v) =>
  Expr ann e -> Expr ann e -> Expr ann e -> m (Expr ann e)
ensureEqualTypes expr tyExpected tyActual = do
  typesEqual <- equalExprs tyActual tyExpected
  if typesEqual then pure tyActual
  else tyMismatch expr tyExpected tyActual


-- | Retrieve an Abstraction from a function type expression, failing if the
-- | expression is not a function type.
getAbsFromFunTy :: (MonadError err m, InjErr (TypeError ann e) err) => Expr ann e -> Expr ann e -> m (Abstraction ann e)
getAbsFromFunTy expr t =
  case t of
    FunTy _ ab -> pure ab
    t          -> expectedInferredTypeForm "function" expr t


-- | Retrieve an Abstraction from a product type expression, failing if the
-- | expression is not a product type.
getAbsFromProductTy :: (MonadError err m, InjErr (TypeError ann e) err) => Expr ann e -> Expr ann e -> m (Abstraction ann e)
getAbsFromProductTy expr t =
  case t of
    ProductTy _ ab -> pure ab
    t              -> expectedInferredTypeForm "product" expr t


-- | 'checkOrInferType ty ex' checks that the type of 'ex' matches 'ty', or infers
-- | it 'ty' is a wild. Evaluates to the calculated type.
checkOrInferType :: (Checkable m err ann e v, Term e) => Expr ann e -> Expr ann e -> m (Expr ann e)
--------------
-- Builtins --
--------------
checkOrInferType t expr@(Builtin _ e) =
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

      -- Unit : Type 0
      DUnitTy -> unitTyTY

      -- unit : Unit
      DUnitTerm -> unitTermTY
----------------------
-- Level expression --
----------------------
checkOrInferType t expr@LitLevel{} = ensureEqualTypes expr t levelTy
-------------------------
-- Variable expression --
-------------------------
{-
   x : A in G
   G |- A : Type l
   --------------- :: Var
   G |- x : A
-}
checkOrInferType t expr@(Var _ x) = do
  -- x : A in G
  tA <- getBinderType (mkTag :: BinderMap) x >>= maybe (unknownIdentifierErr x) pure

  -- G |- A : Type l
  _l <- inferUniverseLevel tA
  tA <- normalise tA

  -- G |- x : A
  ensureEqualTypes expr t tA

-------------------------------
----- Dependent Functions -----
-------------------------------

{-
   G |- A : Type l1
   G, x : A |- B : Type l2
   ------------------------------------- :: FunTy
   G |- (x : A) -> B : Type (lmax l1 l2)
-}
checkOrInferType t expr@(FunTy _ ab) = do
  -- G |- A : Type l1
  l1 <- inferUniverseLevel (absTy ab)

  -- G, x : A |- B : Type l2
  l2 <- withAbsBinding ab $ inferUniverseLevel (absExpr ab)

  -- G |- (x : A) -> B : Type (lmax l1 l2)
  lmaxl1l2 <- normalise (lmaxApp l1 l2)
  ensureEqualTypes expr t (mkUnivTy lmaxl1l2)

--------------------------------------------
-- Abstraction expression, with wild type --
--------------------------------------------
checkOrInferType Implicit{} expr@(Abs _ ab) = do
  rTy <- withAbsBinding ab $ checkOrInferType mkImplicit (absExpr ab)
  checkOrInferType (FunTy def (mkAbs (absVar ab) (absTy ab) rTy)) expr

{-
   G, x : A |- e : B
   --------------------------------- :: Abs
   G |- \(x : A) -> e : (x : A) -> B
-}
checkOrInferType t expr@(Abs _ abE) = do
  _l <- inferUniverseLevel t
  abT <- normalise t >>= getAbsFromFunTy expr

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
  ensureEqualTypes expr t (FunTy def (mkAbs x tA tB))

{-
   G |- t1 : (x : A) -> B
   G |- t2 : A
   ---------------------- :: App
   G |- t1 t2 : [t2/x]B
-}
checkOrInferType t expr@(App _ e1 e2) = do

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
          getAbsFromFunTy e t

-----------------------------
----- Dependent Tensors -----
-----------------------------

{-
   G |- A : Type l1
   G, x : A |- B : Type l2
   ------------------------------------ :: ProductTy
   G |- (x : A) * B : Type (lmax l1 l2)
-}
checkOrInferType t expr@(ProductTy _ ab) = do
  -- G |- A : Type l1
  l1 <- inferUniverseLevel (absTy ab)

  -- G, x : A |- B : Type l2
  l2 <- withAbsBinding ab $ inferUniverseLevel (absExpr ab)

  -- G |- (x : A) * B : Type (lmax l1 l2)
  lmaxl1l2 <- normalise (lmaxApp l1 l2)
  ensureEqualTypes expr t (mkUnivTy lmaxl1l2)

{-
   G |- t1 : A
   G |- t2 : [t1/x]B
   G, x : A |- B : Type l
   --------------------------- :: Pair
   G |- (t1, t2) : (x : A) * B
-}
checkOrInferType t expr@(Pair _ e1 e2) = do
  _l <- inferUniverseLevel t
  abT <- normalise t >>= getAbsFromProductTy expr

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
  ensureEqualTypes expr t (ProductTy def (mkAbs x tA tB))

{-
   G, z : (x : A) * B |- C : Type l
   G, x : A, y : B |- t2 : [(x, y)/z]C
   G |- t1 : (x : A) * B
   ------------------------------------ :: PairElim
   G |- let (x, y) = t1 in t2 : [t1/z]C
-}
checkOrInferType t expr@(PairElim _ z x y e1 e2 tC) = do

  -- G |- t1 : (x : A) * B
  e1Ty <- inferProductTy x e1
  tA <- substitute (absVar e1Ty, Var def x) (absTy e1Ty)
  tB <- substitute (absVar e1Ty, Var def x) (absExpr e1Ty)

  -- G, z : (x : A) * B |- C : Type l
  tC <- case tC of
          -- if tC is implicit then assume it is okay for now, as we don't have unification variables
          Implicit{} -> normalise t
          _ -> do
            _l <- withTypedVariable z (ProductTy def (mkAbs x tA tB)) $ inferUniverseLevel tC
            normalise tC

  -- G, x : A, y : B |- t2 : [(x, y)/z]C
  xyForZinC <- withTypedVariable x tA $ withTypedVariable y tB $ substitute (z, Pair def (Var def x) (Var def y)) tC
  _ <- withTypedVariable x tA $ withTypedVariable y tB $ checkOrInferType xyForZinC e2

  -- x, y nin FV(C)
  when (x `elem` freeVars tC || y `elem` freeVars tC) $
       error $ concat [ "neither '", pprint x, "' nor '", pprint y
                      , "' are allowed to occur in the type of '", pprint e2
                      , "' (which was found to be '", pprint tC, "'), but one or more of them did."
                      ]

  -- G |- let (z, x, y) = t1 in (t2 : C) : [t1/z]C
  t1ForZinC <- substitute (z, e1) tC
  ensureEqualTypes expr t t1ForZinC

  where inferProductTy x e = do
          t <- checkOrInferType (ProductTy def (mkAbs x mkImplicit mkImplicit)) e >>= normalise
          getAbsFromProductTy e t

--------------------
----- Booleans -----
--------------------

{-
   G |- t1 : Bool
   G |- t2 : A
   G |- t3 : B
   ------------------------------------------------ :: IfExpr
   G |- if t1 then t2 else t3 : if t1 then A else B
-}
checkOrInferType t expr@(IfExpr _ e1 e2 e3) = do

  -- G |- t1 : Bool
  _e1Ty <- inferBoolTy e1

  -- G |- t2 : A
  tA <- withExprNormalisingTo e1 (Builtin def DTrue) $ synthType e2

  -- G |- t3 : B
  tB <- withExprNormalisingTo e1 (Builtin def DFalse) $ synthType e3

  -- G |- if t1 then t2 else t3 : if t1 then A else B
  ensureEqualTypes expr t =<< normalise (IfExpr def e1 tA tB)

  where inferBoolTy e = do
          t <- synthType e >>= normalise
          case t of
            (Builtin _ DBool) -> pure t
            t -> expectedInferredTypeForm "boolean" e t

-------------------------------------
-- When we don't know how to synth --
-------------------------------------
checkOrInferType Implicit{} expr = cannotSynthTypeForExpr expr
checkOrInferType t Implicit{}    = cannotSynthExprForType t
----------------------------------
-- Currently unsupported checks --
----------------------------------
checkOrInferType t e =
  notImplemented $ "I don't yet know how to check the type of expression '" <> pprint e <> "' against the type '" <> pprint t


-- | Attempt to synthesise a type for the given expression.
synthType :: (Checkable m err ann e v, Term e) => Expr ann e -> m (Expr ann e)
synthType = checkOrInferType mkImplicit
