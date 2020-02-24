{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
module Language.Dlam.Types
  ( doNASTInference
  ) where

import Control.Monad (when)

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
import Language.Dlam.Substitution
  ( Substitutable(substitute)
  )
import Language.Dlam.Syntax
import Language.Dlam.PrettyPrint


-------------------
----- Helpers -----
-------------------


-- | Common constraints required for type checking.
type Checkable m e v =
  ( Ord e, PrettyPrint e
  , Monad m
  , Substitutable m Identifier (Expr e)
  , HasBinderMap m Identifier v
  , HasNormalFormMap m (Expr e) (Expr e)
  , HasTyVal v (Maybe (Expr e)) (Expr e)
  )


-- | Indicate that an identifier is not known to be defined.
unknownIdentifierErr :: Identifier -> m a
unknownIdentifierErr x = error $ "unknown identifier '" <> pprint x <> "'"


-------------------------
----- Normalisation -----
-------------------------


-- | Execute the action with the given identifier bound with the given type.
withTypedVariable :: (Monad m, HasTyVal v (Maybe t) (Expr e), HasBinderMap m Identifier v) =>
  Identifier -> Expr e -> m a -> m a
withTypedVariable v t = withBinding (mkTag :: BinderMap) (v, fromTyVal (Nothing, t))


-- | Execute the action with the binder from the abstraction active.
withAbsBinding :: (Monad m, HasTyVal v (Maybe t) (Expr e), HasBinderMap m Identifier v) =>
  Abstraction e -> m a -> m a
withAbsBinding ab = withTypedVariable (absVar ab) (absTy ab)


-- | 'withExprNormalisingTo e nf m' runs 'm', but causes
-- | any expressions that would usually normalise to (the normal form of)
-- | 'e' to instead normalise to 'nf'.
withExprNormalisingTo :: (Checkable m e v) => Expr e -> Expr e -> m a -> m a
withExprNormalisingTo e nf m = normalise e >>= \e -> withBinding (mkTag :: NormalFormMap) (e, nf) m


-- | Normalise an abstraction via a series of reductions.
normaliseAbs :: (Checkable m e v) => Abstraction e -> m (Abstraction e)
normaliseAbs ab = do
  t <- normalise (absTy ab)
  e <- withAbsBinding ab (normalise (absExpr ab))
  pure (mkAbs (absVar ab) t e)


-- | Indicate that the expresion is now in an irreducible normal form.
-- |
-- | This allows for e.g., substituting normal forms.
finalNormalForm :: (Functor m, Ord e, HasNormalFormMap m (Expr e) (Expr e)) => (Expr e) -> m (Expr e)
finalNormalForm e = maybe e id <$> getBinder (mkTag :: NormalFormMap) e


-- | Normalise the expression via a series of reductions.
normalise :: (Checkable m e v) => Expr e -> m (Expr e)
normalise Wild = finalNormalForm Wild
normalise (Var x) = do
  val <- getBinderValue (mkTag :: BinderMap) x
  case val of
    -- TODO: improve error system (2020-02-20)
    Nothing -> finalNormalForm $ Var x
    Just Nothing  -> finalNormalForm $ Var x
    Just (Just e) -> normalise e
normalise (FunTy ab) = finalNormalForm =<< FunTy <$> normaliseAbs ab
normalise (Abs ab) = finalNormalForm =<< Abs <$> normaliseAbs ab
normalise (ProductTy ab) = finalNormalForm =<< ProductTy <$> normaliseAbs ab
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
        LitLevel n -> finalNormalForm $ LitLevel (succ n)
        _          -> finalNormalForm $ App e1' e2'

    -- lmax 0 l = l
    (App (Builtin LMax) (LitLevel 0)) -> finalNormalForm e2'

    (App (Builtin LMax) (LitLevel n)) ->
      case e2' of
        -- lmax (n + 1) (lsuc m) = lsuc m
        (App (Builtin LSuc) _) | n > 0 -> finalNormalForm e2'
        -- if the expression is of the form 'lmax m n' where 'm' and 'n' are literal
        -- numbers, then normalise by taking the maximum.
        LitLevel m -> finalNormalForm $ LitLevel (max n m)
        _          -> finalNormalForm $ App e1' e2'
    -- (\x -> e) e' ----> [e'/x] e
    (Abs ab) -> substitute (absVar ab, e2') (absExpr ab) >>= normalise
    _              -> finalNormalForm $ App e1' e2'
normalise (PairElim v1 v2 e1 e2) = do
  e1' <- normalise e1
  case e1' of
    (Pair l r) -> substitute (v1, l) e2 >>= substitute (v2, r) >>= normalise
    _          -> finalNormalForm $ PairElim v1 v2 e1' e2
normalise (IfExpr e1 e2 e3) = do
  e1' <- normalise e1
  e2' <- normalise e2
  e3' <- normalise e3
  case e1' of
    (Builtin DFalse) -> finalNormalForm e3'
    (Builtin DTrue)  -> finalNormalForm e2'
    _                -> do
      e2e3equal <- equalExprs e2' e3'
      finalNormalForm $ if e2e3equal then e2' else IfExpr e1' e2' e3'
normalise (Pair e1 e2) = finalNormalForm =<< Pair <$> normalise e1 <*> normalise e2
normalise (Builtin LZero) = finalNormalForm $ LitLevel 0
normalise e@Builtin{} = finalNormalForm e
normalise e@LitLevel{} = finalNormalForm e
normalise e = error $ "normalise does not yet support '" <> pprint e <> "'"


------------------------------
----- AST Type Inference -----
------------------------------


-- | Check if two expressions are equal under normalisation.
equalExprs :: (Checkable m e v) => Expr e -> Expr e -> m Bool
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
doNStmtInference :: (Checkable m e v, Term e) => NStmt e -> m (NStmt e)
doNStmtInference (Decl v t e) = do
  -- make sure that the definition's type is actually a type
  checkExprValidForSignature t

  exprTy <- checkOrInferType t e
  setBinder (mkTag :: BinderMap) (mkIdent v) (fromTyVal (Just e, exprTy))
  pure (Decl v exprTy e)
  where
    -- | Check that the given expression is valid as a type signature.
    -- |
    -- | This usually means that the expression is a type, but allows
    -- | for the possibility of holes that haven't yet been resolved.
    checkExprValidForSignature :: (Checkable m e v, Term e) => Expr e -> m ()
    checkExprValidForSignature Wild = pure ()
    checkExprValidForSignature expr = inferUniverseLevel expr >> pure ()


-- | Attempt to infer the types of each definition in the AST, failing if a type
-- | mismatch is found.
doNASTInference :: (Checkable m e v, Term e) => NAST e -> m (NAST e)
doNASTInference (NAST ds) = fmap NAST $ mapM doNStmtInference ds


-- | Infer a level for the given type.
inferUniverseLevel :: (Checkable m e v, Term e) => Expr e -> m (Expr e)
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
ensureEqualTypes :: (Checkable m e v) =>
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
checkOrInferType :: (Checkable m e v, Term e) => Expr e -> Expr e -> m (Expr e)
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

      -- Unit : Type 0
      DUnitTy -> unitTyTY

      -- unit : Unit
      DUnitTerm -> unitTermTY
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
  tA <- getBinderType (mkTag :: BinderMap) x >>= maybe (unknownIdentifierErr x) pure

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
  tA <- withExprNormalisingTo e1 (Builtin DTrue) $ synthType e2

  -- G |- t3 : B
  tB <- withExprNormalisingTo e1 (Builtin DFalse) $ synthType e3

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
synthType :: (Checkable m e v, Term e) => Expr e -> m (Expr e)
synthType = checkOrInferType Wild
