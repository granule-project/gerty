{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
module Language.Dlam.Types
  ( doASTInference
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
type Checkable m err v =
  ( Monad m
  , Substitutable m Identifier Expr
  , HasBinderMap m Identifier v
  , HasNormalFormMap m Expr Expr
  , HasTyVal v (Maybe Expr) Expr
  , MonadError err m
  , InjErr SynthError err
  , InjErr TypeError err
  , InjErr ImplementationError err
  , InjErr ScopeError err
  )


-------------------------
----- Normalisation -----
-------------------------


-- | Execute the action with the given identifier bound with the given type.
withTypedVariable :: (Monad m, HasTyVal v (Maybe t) Expr, HasBinderMap m Identifier v) =>
  Identifier -> Expr -> m a -> m a
withTypedVariable v t = withBinding (mkTag :: BinderMap) (v, fromTyVal (Nothing, t))


-- | Execute the action with the binder from the abstraction active.
withAbsBinding :: (Monad m, HasTyVal v (Maybe t) Expr, HasBinderMap m Identifier v) =>
  Abstraction -> m a -> m a
withAbsBinding ab = withTypedVariable (absVar ab) (absTy ab)


-- | 'withExprNormalisingTo e nf m' runs 'm', but causes
-- | any expressions that would usually normalise to (the normal form of)
-- | 'e' to instead normalise to 'nf'.
withExprNormalisingTo :: (Checkable m err v) => Expr -> Expr -> m a -> m a
withExprNormalisingTo e nf m = normalise e >>= \e -> withBinding (mkTag :: NormalFormMap) (e, nf) m


-- | Normalise an abstraction via a series of reductions.
normaliseAbs :: (Checkable m err v) => Abstraction -> m Abstraction
normaliseAbs ab = do
  t <- normalise (absTy ab)
  e <- withAbsBinding ab (normalise (absExpr ab))
  pure (mkAbs (absVar ab) t e)


-- | Indicate that the expresion is now in an irreducible normal form.
-- |
-- | This allows for e.g., substituting normal forms.
finalNormalForm :: (Functor m, HasNormalFormMap m Expr Expr) => Expr -> m Expr
finalNormalForm e = maybe e id <$> getBinder (mkTag :: NormalFormMap) e


-- | Normalise the expression via a series of reductions.
normalise :: (Checkable m err v) => Expr -> m Expr
normalise Implicit = finalNormalForm Implicit
normalise (Var x) = do
  val <- getBinderValue (mkTag :: BinderMap) x
  case val of
    Nothing -> finalNormalForm $ Var x
    Just Nothing  -> finalNormalForm $ Var x
    Just (Just e) -> normalise e
normalise (FunTy ab) = finalNormalForm =<< FunTy <$> normaliseAbs ab
normalise (Abs ab) = finalNormalForm =<< Abs <$> normaliseAbs ab
normalise (ProductTy ab) = finalNormalForm =<< ProductTy <$> normaliseAbs ab
-- VALUE: LitLevel
normalise (LitLevel n) = finalNormalForm $ LitLevel n
-- lzero ---> 0
normalise (Builtin LZero) = finalNormalForm $ LitLevel 0
normalise (App e1 e2) = do
  e1' <- normalise e1
  e2' <- normalise e2
  case e1' of

    ------------------
    -- Builtin lsuc --
    ------------------

    Builtin LSuc -> do
      let l = e2'
      case l of

        -- lsuc n ---> SUCC n
        (LitLevel n) -> finalNormalForm (LitLevel (succ n))

        -- otherwise we can't reduce further
        _ ->
          finalNormalForm $ lsucApp l

    ------------------
    -- Builtin lmax --
    ------------------

    (App (Builtin LMax) l1) -> do
      let l2 = e2'
      case (l1, l2) of

        -- lmax 0 l2 ---> l2
        (LitLevel 0, l2) ->
          finalNormalForm $ l2

        -- lmax l1 0 ---> l1
        (l1, LitLevel 0) ->
          finalNormalForm $ l1

        -- lmax m n ---> MAX m n
        (LitLevel m, LitLevel n) ->
          finalNormalForm $ LitLevel (max m n)

        -- lmax (lsuc l1) (lsuc l2) ---> lsuc (lmax l1 l2)
        (App (Builtin LSuc) l1, App (Builtin LSuc) l2) ->
          normalise $ lsucApp (lmaxApp l1 l2)

        -- lmax (m + 1) (lsuc l2) ---> lsuc (lmax m l2)
        (LitLevel m, App (Builtin LSuc) l2') | m > 0 ->
          normalise $ lsucApp (lmaxApp (LitLevel (pred m)) l2')

        -- lmax (lsuc l1) (n + 1) ---> lsuc (lmax l1 n)
        (App (Builtin LSuc) l1', LitLevel n) | n > 0 ->
          normalise $ lsucApp (lmaxApp l1' (LitLevel (pred n)))

        -- otherwise we can't reduce further
        _ ->
          finalNormalForm $ lmaxApp l1 l2

    ------------------------
    -- Lambda abstraction --
    ------------------------

    -- (\x -> e) e' ----> [e'/x] e
    (Abs ab) -> substitute (absVar ab, e2') (absExpr ab) >>= normalise

    ------------------------
    -- Other applications --
    ------------------------

    _ -> finalNormalForm $ App e1' e2'
normalise (PairElim (z, tC) (x, y, g) p) = do
  p' <- normalise p
  tC' <- normalise tC
  case p' of
    (Pair l r) -> substitute (x, l) g >>= substitute (y, r) >>= normalise
    _          -> finalNormalForm $ PairElim (z, tC') (x, y, g) p'
normalise (CoproductCase (z, tC) (x, c) (y, d) e) = do
  e' <- normalise e
  case e' of
    App (App (App (App (App (Builtin Inl) _l1) _l2) _a) _b) l -> normalise =<< substitute (x, l) c
    App (App (App (App (App (Builtin Inr) _l1) _l2) _a) _b) r -> normalise =<< substitute (y, r) d
    _ -> do
      tC' <- normalise tC
      c' <- normalise c
      d' <- normalise d
      finalNormalForm $ CoproductCase (z, tC') (x, c') (y, d') e'
normalise (NatCase (x, tC) cz (w, y, cs) n) = do
  n' <- normalise n
  case n' of

    {-
       case x@zero of (Zero -> cz; Succ w@y -> cs) : C
       --->
       cz : [zero/x]C
    -}
    Builtin DNZero -> normalise cz

    {-
       case x@(succ n) of (Zero -> cz; Succ w@y -> cs) : C
       --->
       [n/w][case x@n of (Zero -> cz; Succ w@y -> cs) : C/y]cs : [succ(n)/x]C
    -}
    (App (Builtin DNSucc) k) ->
      -- [case x@n of (Zero -> cz; Succ w@y -> cs) : C/y]
      substitute (y, NatCase (x, tC) cz (w, y, cs) k) cs >>=
      -- [n/w]
      substitute (w, k) >>= normalise

    -- otherwise we can't reduce further (just reduce the components)
    _ -> do
      tC' <- normalise tC
      cz' <- normalise cz
      cs'  <- normalise cs
      finalNormalForm $ NatCase (x, tC') cz' (w, y, cs') n'
normalise (Coproduct e1 e2) = finalNormalForm =<< Coproduct <$> normalise e1 <*> normalise e2
normalise (Pair e1 e2) = finalNormalForm =<< Pair <$> normalise e1 <*> normalise e2
normalise e@Builtin{} = finalNormalForm e
normalise e = notImplemented $ "normalise does not yet support '" <> pprint e <> "'"


------------------------------
----- AST Type Inference -----
------------------------------


-- | Check if two expressions are equal under normalisation.
equalExprs :: (Checkable m err v) => Expr -> Expr -> m Bool
equalExprs e1 e2 = do
  ne1 <- normalise e1
  ne2 <- normalise e2
  case (ne1, ne2) of
    (Var v1, Var v2) -> pure (v1 == v2)
    (App f1 v1, App f2 v2) -> (&&) <$> equalExprs f1 f2 <*> equalExprs v1 v2
    (FunTy ab1, FunTy ab2) -> equalAbs ab1 ab2
    (Abs ab1, Abs ab2) -> equalAbs ab1 ab2
    (ProductTy ab1, ProductTy ab2) -> equalAbs ab1 ab2
    (Coproduct t1 t2, Coproduct t1' t2') -> (&&) <$> equalExprs t1 t1' <*> equalExprs t2 t2'
    (CoproductCase (z, tC) (x, c) (y, d) e, CoproductCase (z', tC') (x', c') (y', d') e') -> do
      typesOK <- equalExprs tC' =<< substitute (z, Var z') tC
      csOK <- equalExprs c' =<< substitute (x, Var x') c
      dsOK <- equalExprs d' =<< substitute (y, Var y') d
      esOK <- equalExprs e e'
      pure $ typesOK && csOK && dsOK && esOK
    (PairElim (z, tC) (x, y, g) p, PairElim (z', tC') (x', y', g') p') -> do
      typesOK <- equalExprs tC' =<< substitute (z, Var z') tC
      gsOK <- equalExprs g' =<< (substitute (x, Var x') g >>= substitute (y, Var y'))
      psOK <- equalExprs p p'
      pure $ typesOK && gsOK && psOK
    (NatCase (x, tC) cz (w, y, cs) n, NatCase (x', tC') cz' (w', y', cs') n') -> do
      typesOK <- equalExprs tC' =<< substitute (x, Var x') tC
      csOK <- equalExprs cs' =<< (substitute (w, Var w') cs >>= substitute (y, Var y'))
      czsOK <- equalExprs cz cz'
      nsOK <- equalExprs n n'
      pure $ typesOK && csOK && czsOK && nsOK
    -- Implicits always match.
    (Implicit, _) -> pure True
    (_, Implicit) -> pure True
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
doDeclarationInference :: (Checkable m err v) => Declaration -> m Declaration
doDeclarationInference (TypeSig n t) = do
  -- make sure that the type is actually a type
  checkExprValidForSignature t

  registerTypeForName n t
  pure (TypeSig n t)
  where
    -- | Check that the given expression is valid as a type signature.
    -- |
    -- | This usually means that the expression is a type, but allows
    -- | for the possibility of holes that haven't yet been resolved.
    checkExprValidForSignature :: (Checkable m err v) => Expr -> m ()
    checkExprValidForSignature Implicit = pure ()
    checkExprValidForSignature expr = inferUniverseLevel expr >> pure ()

doDeclarationInference (FunEqn (FLHSName v) (FRHSAssign e)) = do

  -- try and get a prescribed type for the equation,
  -- treating it as an implicit if no type is given
  t <- getBinderType (mkTag :: BinderMap) v
  exprTy <- case t of
              Nothing -> checkOrInferType mkImplicit e
              Just ty -> checkOrInferType ty e

  -- assign the appopriate equation and normalised/inferred type for the name
  setBinder (mkTag :: BinderMap) v (fromTyVal (Just e, exprTy))
  pure (FunEqn (FLHSName v) (FRHSAssign e))


-- | Attempt to infer the types of each definition in the AST, failing if a type
-- | mismatch is found.
doASTInference :: (Checkable m err v) => AST -> m AST
doASTInference (AST ds) = fmap AST $ mapM doDeclarationInference ds


-- | Infer a level for the given type.
inferUniverseLevel :: (Checkable m err v) => Expr -> m Expr
inferUniverseLevel e = do
  u <- synthType e
  norm <- normalise u
  case norm of
    (App (Builtin TypeTy) l) -> pure l
    _        -> expectedInferredTypeForm "universe" e norm


-- | 'ensureEqualTypes expr tyExpected tyActual' checks that 'tyExpected' and 'tyActual'
-- | represent the same type (under normalisation), and fails if they differ.
ensureEqualTypes :: (Checkable m err v) => Expr -> Expr -> Expr -> m Expr
ensureEqualTypes expr tyExpected tyActual = do
  typesEqual <- equalExprs tyActual tyExpected
  if typesEqual then pure tyActual
  else tyMismatch expr tyExpected tyActual


-- | Retrieve an Abstraction from a function type expression, failing if the
-- | expression is not a function type.
getAbsFromFunTy :: (MonadError err m, InjErr TypeError err) => Expr -> Expr -> m Abstraction
getAbsFromFunTy expr t =
  case t of
    FunTy ab -> pure ab
    t        -> expectedInferredTypeForm "function" expr t


-- | Retrieve an Abstraction from a product type expression, failing if the
-- | expression is not a product type.
getAbsFromProductTy :: (MonadError err m, InjErr TypeError err) => Expr -> Expr -> m Abstraction
getAbsFromProductTy expr t =
  case t of
    ProductTy ab -> pure ab
    t            -> expectedInferredTypeForm "product" expr t


-- | 'checkOrInferType ty ex' checks that the type of 'ex' matches 'ty', or infers
-- | it 'ty' is a wild. Evaluates to the calculated type.
checkOrInferType :: (Checkable m err v) => Expr -> Expr -> m Expr
--------------
-- Builtins --
--------------
checkOrInferType t expr@(Builtin e) =
  -- here we simply check that the expected type
  -- matches the type defined for the builtin
  ensureEqualTypes expr t $
    case e of
      -- lzero : Level
      LZero -> builtinType lzero

      -- lsuc : Level -> Level
      LSuc  -> builtinType lsuc

      -- Type : (l : Level) -> Type (lsuc l)
      TypeTy -> builtinType typeTy

      -- Level : Type 0
      LevelTy -> builtinType levelTy

      -- lmax : Level -> Level -> Level
      LMax -> builtinType lmax

      -- | inl : (l1 l2 : Level) (a : Type l1) (b : Type l2) -> a -> a + b
      Inl -> builtinType inlTerm

      -- | inr : (l1 l2 : Level) (a : Type l1) (b : Type l2) -> b -> a + b
      Inr -> builtinType inrTerm

      -- | Nat : Type 0
      DNat -> builtinType natTy

      -- | zero : Nat
      DNZero -> builtinType dnzero

      -- | succ : Nat -> Nat
      DNSucc -> builtinType dnsucc

      -- Unit : Type 0
      DUnitTy -> builtinType unitTy

      -- unit : Unit
      DUnitTerm -> builtinType unitTerm

      -- Id : (l : Level) (a : Type l) -> a -> a -> Type l
      IdTy -> builtinType idTy

      -- refl : (l : Level) (a : Type l) (x : a) -> Id l a x x
      DRefl -> builtinType reflTerm
----------------------
-- Level expression --
----------------------
checkOrInferType t expr@LitLevel{} = ensureEqualTypes expr t (builtinBody levelTy)
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

-------------------------------
----- Dependent Functions -----
-------------------------------

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

--------------------------------------------
-- Abstraction expression, with wild type --
--------------------------------------------
checkOrInferType Implicit expr@(Abs ab) = do
  rTy <- withAbsBinding ab $ checkOrInferType mkImplicit (absExpr ab)
  checkOrInferType (FunTy (mkAbs (absVar ab) (absTy ab) rTy)) expr

{-
   G, x : A |- e : B
   --------------------------------- :: Abs
   G |- \(x : A) -> e : (x : A) -> B
-}
checkOrInferType t expr@(Abs abE) = do
  _l <- inferUniverseLevel t
  abT <- normalise t >>= getAbsFromFunTy expr

  let x = absVar  abE
      e = absExpr abE
      tA = absTy abT

  -- G, x : A |- e : B

  -- make sure that we are considering the name
  -- coming from the abstraction, rather than the type
  tB <- substitute (absVar abT, Var $ x) (absExpr abT)

  tB <- withTypedVariable x tA (checkOrInferType tB e)

  -- G |- \x -> e : (x : A) -> B
  ensureEqualTypes expr t (FunTy (mkAbs x tA tB))

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
checkOrInferType t expr@(ProductTy ab) = do
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
checkOrInferType t expr@(Pair e1 e2) = do
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
  ensureEqualTypes expr t (ProductTy (mkAbs x tA tB))

{-
   G, z : (x : A) * B |- C : Type l
   G, x : A, y : B |- t2 : [(x, y)/z]C
   G |- t1 : (x : A) * B
   -------------------------------------------- :: PairElim
   G |- let z@(x, y) = t1 in (t2 : C) : [t1/z]C
-}
checkOrInferType t expr@(PairElim (z, tC) (x, y, g) p) = do

  -- G |- t1 : (x : A) * B
  pTy <- inferProductTy x p
  tA <- substitute (absVar pTy, Var x) (absTy pTy)
  tB <- substitute (absVar pTy, Var x) (absExpr pTy)

  -- G, z : (x : A) * B |- C : Type l
  tC <- case tC of
          -- if tC is implicit then assume it is okay for now, as we don't have unification variables
          Implicit -> normalise t
          _ -> do
            _l <- withTypedVariable z (ProductTy (mkAbs x tA tB)) $ inferUniverseLevel tC
            normalise tC

  -- G, x : A, y : B |- t2 : [(x, y)/z]C
  let pairXY = Pair (Var x) (Var y)
  xyForZinC <- withTypedVariable x tA $ withTypedVariable y tB $ substitute (z, pairXY) tC
  _ <- withTypedVariable x tA $ withTypedVariable y tB $ withExprNormalisingTo p pairXY $ checkOrInferType xyForZinC g

  -- x, y nin FV(C)
  when (x `elem` freeVars tC || y `elem` freeVars tC) $
       error $ concat [ "neither '", pprint x, "' nor '", pprint y
                      , "' are allowed to occur in the type of '", pprint g
                      , "' (which was found to be '", pprint tC, "'), but one or more of them did."
                      ]

  -- G |- let (z, x, y) = t1 in (t2 : C) : [t1/z]C
  t1ForZinC <- substitute (z, p) tC
  ensureEqualTypes expr t t1ForZinC

  where inferProductTy x e = do
          t <- checkOrInferType (ProductTy (mkAbs x mkImplicit mkImplicit)) e >>= normalise
          getAbsFromProductTy e t

----------------
-- Coproducts --
----------------

{-
   G |- A : Type l1
   G |- B : Type l2
   ------------------------------ :: Coproduct
   G |- A + B : Type (lmax l1 l2)
-}
checkOrInferType t expr@(Coproduct tA tB) = do
  -- G |- A : Type l1
  l1 <- inferUniverseLevel tA

  -- G |- B : Type l2
  l2 <- inferUniverseLevel tB

  -- G |- (x : A) -> B : Type (lmax l1 l2)
  lmaxl1l2 <- normalise (lmaxApp l1 l2)
  ensureEqualTypes expr t (mkUnivTy lmaxl1l2)

{-
   G, z : A + B |- C : Type l
   G, x : A |- c : [inl x/z]C
   G, y : B |- d : [inr y/z]C
   G |- e : A + B
   ------------------------------------------------------ :: CoproductCase
   G |- case z@e of (Inl x -> c; Inr y -> d) : C : [e/z]C
-}
checkOrInferType t expr@(CoproductCase (z, tC) (x, c) (y, d) e) = do
  -- G |- e : A + B
  (tA, tB) <- inferCoproductTy e
  l1 <- inferUniverseLevel tA
  l2 <- inferUniverseLevel tB

  -- G, z : A + B |- C : Type l
  _l <- withTypedVariable z (Coproduct tA tB) $ inferUniverseLevel tC

  -- G, x : A |- c : [inl x/z]C
  let inlX = inlTermApp l1 l2 tA tB (Var x)
  inlxforzinC <- substitute (z, inlX) tC
  _ <- withTypedVariable x tA $ withExprNormalisingTo e inlX $ checkOrInferType inlxforzinC c

  -- G, y : B |- d : [inr y/z]C
  let inrY = inrTermApp l1 l2 tA tB (Var y)
  inryforzinC <- substitute (z, inrY) tC
  _ <- withTypedVariable y tB $ withExprNormalisingTo e inrY $ checkOrInferType inryforzinC d

  -- G |- case z@e of (Inl x -> c; Inr y -> d) : C : [e/z]C
  eforzinC <- substitute (z, e) tC
  ensureEqualTypes expr t eforzinC

  where inferCoproductTy e = do
          t <- synthType e >>= normalise
          case t of
            (Coproduct tA tB) -> pure (tA, tB)
            t -> expectedInferredTypeForm "coproduct" e t

---------------------------
----- Natural numbers -----
---------------------------

{-
   G, x : Nat |- C : Type l
   G |- cz : [zero/x]C
   G, w : Nat, y : [w/x]C |- cs : [succ w/x]C
   G |- n : Nat
   ---------------------------------------------------------- :: NatCase
   G |- case x@n of (Zero -> cz; Succ w@y -> cs) : C : [n/x]C
-}
checkOrInferType t expr@(NatCase (x, tC) cz (w, y, cs) n) = do
  -- G, x : Nat |- C : Type l
  let natTy' = builtinBody natTy
  _l <- withTypedVariable x natTy' $ inferUniverseLevel tC

  -- G |- cz : [zero/x]C
  zeroforxinC <- substitute (x, builtinBody dnzero) tC
  _ <- checkOrInferType zeroforxinC cz

  -- G, w : Nat, y : [w/x]C |- cs : [succ w/x]C
  succwforxinC <- substitute (x, dnsuccApp (Var w)) tC
  wforxinC <- substitute (x, Var w) tC
  _ <-   withTypedVariable y wforxinC
       $ withTypedVariable w natTy'
       $ checkOrInferType succwforxinC cs

  -- G |- n : Nat
  _Nat <- checkOrInferType natTy' n

  -- G |- case x@n of (Zero -> cz; Succ w@y -> cs) : C : [n/x]C
  nforxinC <- substitute (x, n) tC
  ensureEqualTypes expr t nforxinC

--------------------
----- Identity -----
--------------------

{-
   G |- A : Type l1
   G, x : A, y : A, p : Id l1 A x y |- C : Type l2
   G, z : A |- c : [z/x][z/y][refl l1 A z/p]C
   G |- a : A
   G |- b : A
   G |- p' : Id l1 A a b
   --------------------------------------------------------- :: RewriteExpr
   G |- rewrite(x.y.p.C, l1, A, a, b, p) : [a/x][b/y][p'/p]C
-}
checkOrInferType t expr@(RewriteExpr x y p tC z c a b p') = do
  -- G |- a : A
  tA <- synthType a

  -- G |- A : Type l1
  l1 <- inferUniverseLevel tA

  -- G |- b : A
  _ <- checkOrInferType tA b

  -- G |- p' : Id l1 A a b
  _ <- checkOrInferType (idTyApp l1 tA a b) p'

  -- G, x : A, y : A, p : Id l1 A x y |- C : Type l2
  _l2 <- withTypedVariable x tA $ withTypedVariable y tA $ withTypedVariable p (idTyApp l1 tA (Var x) (Var y)) $ inferUniverseLevel tC

  -- G, z : A |- c : [z/x][z/y][refl l1 A z/p]C
  zForyinzforyinreflforpC <-
    substitute (x, Var z) =<< substitute (y, Var z) =<< substitute (p, reflTermApp l1 tA (Var z)) tC
  _ <- withTypedVariable z tA $ checkOrInferType zForyinzforyinreflforpC c

  -- G |- rewrite(x.y.p.C, l1, A, a, b, p) : [a/x][b/y][p'/p]C
  aforxbforypforpinC <-
    substitute (x, a) tC >>= substitute (y, b) >>= substitute (p, p')
  ensureEqualTypes expr t aforxbforypforpinC

-------------------------------------
-- When we don't know how to synth --
-------------------------------------
checkOrInferType Implicit expr = cannotSynthTypeForExpr expr
checkOrInferType t Implicit    = cannotSynthExprForType t
----------------------------------
-- Currently unsupported checks --
----------------------------------
checkOrInferType t e =
  notImplemented $ "I don't yet know how to check the type of expression '" <> pprint e <> "' against the type '" <> pprint t


-- | Attempt to synthesise a type for the given expression.
synthType :: (Checkable m err v) => Expr -> m Expr
synthType = checkOrInferType mkImplicit
