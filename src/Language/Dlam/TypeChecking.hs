{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Dlam.TypeChecking
  ( checkExpr
  , checkAST
  ) where


import Control.Monad (when)
import Debug.Trace

-- import Language.Dlam.Builtins
import Language.Dlam.Builtins2
import Language.Dlam.Substitution (Substitutable(substitute))
--   , freshen
--   )
import Language.Dlam.Syntax.Abstract
-- import Language.Dlam.Syntax.Common
-- import qualified Language.Dlam.Syntax.Concrete as C
import Language.Dlam.Syntax.Internal hiding (Var, App, Lam)
import qualified Language.Dlam.Syntax.Internal as I
import Language.Dlam.TypeChecking.Monad
import Language.Dlam.Util.Pretty (pprintShow, pprintParened)
-- import qualified Language.Dlam.Scoping.Monad as SE
import Language.Dlam.Util.Peekaboo


-- | Require that the expression is a valid level.
checkExprIsLevel :: Expr -> CM Level
checkExprIsLevel e = withLocalCheckingOf e $ checkExprIsLevel_ e


checkExprIsLevel_ :: Expr -> CM Level
checkExprIsLevel_ l = do
  -- traceM $ "levelTy': " <> pprintShow levelTy'
  t <- checkExpr l levelTy'
  case t of
    Level l' -> pure l'
    _ -> error "checkExprIsLevel_: hit impossible clause."


-- | Require that the term is a valid type (of unknown sort).
checkTermIsType :: Term -> CM Type
checkTermIsType (TypeTerm t) = pure t
checkTermIsType (I.App (I.Var v) []) = do
  l <- fmap theUniverseWeLiveIn (lookupType' v >>= universeOrNotAType)
  pure $ mkType (TyApp (TyVar v) []) l
checkTermIsType _ = notAType


-- | Require that the expression is a valid type (of unknown sort).
checkExprIsType :: Expr -> CM Type
checkExprIsType e = do
  traceM $ "checkExprIsType: checking that '" <> pprintShow e <> "' is a type expression"
  res <- withLocalCheckingOf e $ checkExprIsType_ e
  traceM $ "checkExprIsType: found a type representation '" <> pprintShow res <> "' for expression '" <> pprintShow e <> "'"
  pure res


checkExprIsType_ :: Expr -> CM Type
checkExprIsType_ (Builtin e) = universeOrNotAType (getBuiltinType e)
checkExprIsType_ (Var x) = lookupValue' x >>= checkTermIsType
-- checkExprIsType_ (Var x) = lookupValue' x >>= checkTermIsType
checkExprIsType_ (App (Var x) e) = do
  vTy <- lookupType' x
  case un vTy of
    Pi arg resTy -> do
      let argTy = typeOf arg
      -- make sure the argument matches the required argument type
      e' <- checkExpr e argTy
      resTy <- substituteAndNormalise (un (un arg), e') resTy
      case un resTy of
        Universe l -> pure $ mkType (Universe (prevLevel l)) (prevLevel l)
        _ -> notAType
      -- pure resTy
    _ -> withLocalCheckingOf (Var x) $ expectedInferredTypeForm' "function" vTy
-- checkExprIsType_ (App f e) = do
checkExprIsType_ (AType l) = do
  lev <- checkExprIsLevel l
  -- pure $ mkType (Universe lev) lev
  pure $ mkType (Universe lev) (nextLevel lev)
checkExprIsType_ (FunTy ab) = do
  let x = absVar ab
  argTy <- checkExprIsType (absTy ab)
  ty <- withTypedVariable' x argTy $ checkExprIsType (absExpr ab)
  -- pure $ mkType (Pi (x `typedWith` argTy `gradedWith` thatMagicalGrading) ty) (Max (level argTy) (level ty))
  pure $ mkType (Pi (x `typedWith` argTy `gradedWith` thatMagicalGrading) ty) (nextLevel (Max (level argTy) (level ty)))
checkExprIsType_ _e = notAType
-- -- | Infer a level for the given type.
-- inferUniverseLevel :: Type -> CM Level
-- inferUniverseLevel e = withLocalCheckingOf e $ do
--   u <- synthType e
--   norm <- normalise u
--   case norm of
--     (App (Builtin TypeTy) l) -> pure l
--     _        -> expectedInferredTypeForm "universe" norm


-- | Try and register the name with the given type
registerTypeForName :: Name -> Type -> CM ()
registerTypeForName n t = do
  t' <- normalise t
  setType' n t'


-- | Type-check a declaration.
checkDeclaration :: Declaration -> CM ()
checkDeclaration ts@(TypeSig n t) = do
  traceM $ "checkDeclaration: checking signature: " <> pprintShow ts
  -- make sure that the type is actually a type
  ty <- checkExprIsType t
  -- checkExprValidForSignature t

  registerTypeForName n ty
  -- pure (TypeSig n t)
  where
    -- | Check that the given expression is valid as a type signature.
    -- |
    -- | This usually means that the expression is a type, but allows
    -- | for the possibility of holes that haven't yet been resolved.
    -- checkExprValidForSignature :: Expr -> CM ()
    -- checkExprValidForSignature Implicit = pure ()
    -- checkExprValidForSignature expr = inferUniverseLevel expr >> pure ()

checkDeclaration eqn@(FunEqn (FLHSName v) (FRHSAssign e)) = do
  traceM $ "checkDeclaration: checking equation: " <> pprintShow eqn

  -- try and get a prescribed type for the equation,
  -- treating it as an implicit if no type is given
  t <- maybeLookupType v
  (val, ty) <- case t of
                 -- if we don't have a type (from a signature), try and infer one as well
                 Nothing -> inferExpr e
                 Just ty -> (,) <$> checkExpr e ty <*> pure ty

  -- assign the appopriate equation and normalised/inferred type for the name
  val <- normalise val
  setValue' v val
  setType' v ty


-- | Attempt to infer the types of each definition in the AST, failing if a type
-- | mismatch is found.
checkAST :: AST -> CM ()
checkAST (AST ds) = mapM_ checkDeclaration ds


  {-
-- | Check if two expressions are equal under normalisation.
equalExprs :: Expr -> Expr -> CM Bool
equalExprs e1 e2 = do
  ne1 <- normalise e1
  ne2 <- normalise e2
  case (ne1, ne2) of
    (Var v1, Var v2) -> pure (v1 == v2)
    (App f1 v1, App f2 v2) -> (&&) <$> equalExprs f1 f2 <*> equalExprs v1 v2
    (FunTy ab1, FunTy ab2) -> equalAbs ab1 ab2
    (Lam ab1, Lam ab2) -> equalAbs ab1 ab2
    (ProductTy ab1, ProductTy ab2) -> equalAbs ab1 ab2
    (Coproduct t1 t2, Coproduct t1' t2') -> (&&) <$> equalExprs t1 t1' <*> equalExprs t2 t2'
    (CoproductCase (z, tC) (x, c) (y, d) e, CoproductCase (z', tC') (x', c') (y', d') e') -> do
      typesOK <- equalExprs tC' =<< substitute (z, Var z') tC
      csOK <- equalExprs c' =<< substitute (x, Var x') c
      dsOK <- equalExprs d' =<< substitute (y, Var y') d
      esOK <- equalExprs e e'
      pure $ typesOK && csOK && dsOK && esOK
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

    (Let (LetPatBound p e1) e2, Let (LetPatBound p' e1') e2') -> do
      case maybeGetPatternUnificationSubst p p' of
        Nothing -> pure False
        Just subst -> do
          e1sOK <- equalExprs e1 e1'
          -- check that e2 and e2' are equal under the pattern substitution
          e2sOK <- (`equalExprs` e2') =<< substitute subst e2
          pure $ e1sOK && e2sOK

    -- when there are two Sigs, we make sure their expressions and types are the same
    (Sig e1 t1, Sig e2 t2) -> (&&) <$> equalExprs e1 e2 <*> equalExprs t1 t2
    -- otherwise we just ignore the type in the Sig
    (Sig e1 _, e2) -> equalExprs e1 e2
    (e1, Sig e2 _) -> equalExprs e1 e2

    (_, _) -> pure False
  where equalAbs :: Abstraction -> Abstraction -> CM Bool
        equalAbs ab1 ab2 = do
          -- checking \(x : a) -> b = \(y : c) -> d
          -- we say:
          -- d' = [y/x]d
          -- then check:
          -- a = c and b = d' (with (x : a) in scope)
          e2s <- substitute (absVar ab2, Var (absVar ab1)) (absExpr ab2)
          (&&) <$> equalExprs (absTy ab1) (absTy ab2)
               <*> withAbsBinding ab1 (equalExprs (absExpr ab1) e2s)


-- | 'ensureEqualTypes tyExpected tyActual' checks that 'tyExpected' and 'tyActual'
-- | represent the same type (under normalisation), and fails if they differ.
ensureEqualTypes :: Type -> Type -> CM Type
ensureEqualTypes tyExpected tyActual = do
  typesEqual <- equalExprs tyActual tyExpected
  if typesEqual then pure tyActual
  else tyMismatch tyExpected tyActual
       -}


-- | Are the terms equal in the current context?
termsAreEqual :: Term -> Term -> CM Bool
-- TODO: support remaining cases (2020-03-14)
termsAreEqual (Level l1) (Level l2) = levelsAreEqual l1 l2
termsAreEqual t1 t2 = notImplemented $ "termsAreEqual: TODO: equality of terms '" <> pprintShow t1 <> "' and '" <> pprintShow t2 <> "'"


-- | Are the levels equal in the current context?
levelsAreEqual :: Level -> Level -> CM Bool
levelsAreEqual (Concrete n) (Concrete m) = pure $ n == m
levelsAreEqual (Plus n (LTerm t1)) (Plus m (LTerm t2)) =
  (&&) <$> pure (n == m) <*> termsAreEqual t1 t2
-- TODO: support remaining cases (2020-03-14)
levelsAreEqual l1 l2 = notImplemented $ "levelsAreEqual: TODO: equality of levels '" <> pprintShow l1 <> "' and '" <> pprintShow l2 <> "'"


-- | Are the types equal in the current context?
typesAreEqual :: Type -> Type -> CM Bool
typesAreEqual t1 t2 = do
  -- TODO: figure out whether we should actually care whether the levels are equal (2020-03-15)
  -- _levEq <- levelsAreEqual (level t1) (level t2)
  case (un t1, un t2) of
    -- TODO: add proper equality here (2020-03-14)
    (TyApp (TyVar x) xs, TyApp (TyVar y) ys) ->
      (&&) <$> pure (x == y) <*> (and <$> (mapM (uncurry termsAreEqual) (zip xs ys)))
    (Universe l1, Universe l2) -> levelsAreEqual l1 l2
    _ -> notImplemented $ "typesAreEqual: TODO: equality of types '" <> pprintShow t1 <> "' and '" <> pprintShow t2 <> "'"
    -- (_, _) -> pure False


-- | 'ensureEqualTypes tyExpected tyActual' checks that 'tyExpected'
-- | and 'tyActual' represent the same type, and fails if they differ.
ensureEqualTypes :: Type -> Type -> CM ()
ensureEqualTypes tyExpected tyActual = do
  tyE <- normalise tyExpected
  tyA <- normalise tyActual
  typesEqual <- typesAreEqual tyE tyA
  -- typesEqual <- typesAreEqual tyExpected tyActual
  when (not typesEqual) (tyMismatch' tyExpected tyActual)


-- | Check the expression against the given type, and
-- | if it is well-typed, yield the underlying term.
checkExpr :: Expr -> Type -> CM Term
checkExpr e t = do
  traceM $ "checkExpr_: checking expression '" <> pprintShow e <> "' against type '" <> pprintShow t <> "'"
  res <- withLocalCheckingOf e $ checkExpr_ e t
  traceM $ "checkExpr: found term '" <> pprintShow res <> "' for expression '" <> pprintShow e <> "'"
  pure res


checkExpr_ :: Expr -> Type -> CM Term
-------------------------
-- Variable expression --
-------------------------
{-
   x @ (k+1, n) : A in G
   G |- A : Type l
   --------------------- :: Var
   x @ (k, n) : A in G
   G |- x : A
-}
checkExpr_ (Var x) t = do
  -- x @ (k+1, n) : A in G
  tA <- lookupType' x
  -- traceM $ "checkExpr_: got type '" <> pprintShow tA <> "' for variable '" <> pprintShow x <> "'"
  kplus1 <- lookupSubjectRemaining' x
  k <- case kplus1 of
         -- as the scope checker ensures that all local variables are
         -- in scope, the only way something could not be assigned
         -- here is if it is a top-level definition, in which case we
         -- treat its usage as implicit
         -- TODO: assign implicit grades to top-level definitions (2020-03-12)
         Nothing -> pure thatMagicalGrade
         Just kplus1 -> maybe (usedTooManyTimes x) pure $ I.decrementGrade kplus1

  -- G |- A : Type l
  -- ensured by the fact that tA is a type from context

  -- _l <- inferUniverseLevel tA
  -- tA <- normalise tA

  -- x @ (k, n) : A in G
  -- G |- x : A
  setSubjectRemaining' x k
  ensureEqualTypes t tA
  val <- maybeLookupValue x
  case val of
    Nothing -> pure (I.App (I.Var x) [])
    Just r  -> pure r
               {-
-------------------------------
----- Dependent Functions -----
-------------------------------

{-
   G |- A : Type l1
   G, x : A |- B : Type l2
   ------------------------------------- :: FunTy
   G |- (x : A) -> B : Type (lmax l1 l2)
-}
checkOrInferType' t (FunTy ab) = do
  -- G |- A : Type l1
  l1 <- inferUniverseLevel (absTy ab)

  -- G, x : A |- B : Type l2
  l2 <- withAbsBindingForType ab $ inferUniverseLevel (absExpr ab)

  -- G |- (x : A) -> B : Type (lmax l1 l2)
  lmaxl1l2 <- normalise (lmaxApp l1 l2)
  ensureEqualTypes t (mkUnivTy lmaxl1l2)

--------------------------------------------
-- Abstraction expression, with wild type --
--------------------------------------------
checkOrInferType' Implicit expr@(Lam ab) = do
  rTy <- withAbsBinding ab $ checkOrInferType mkImplicit (absExpr ab)
  checkOrInferType (FunTy (mkAbs' (isHidden ab) (absVar ab) (grading ab) (absTy ab) rTy)) expr
-}


{-
   G, x : A |- e : B
   --------------------------------- :: Lam
   G |- \(x : A) -> e : (x : A) -> B
-}
checkExpr_ (Lam abE) t = do
  (_tv, gr, tA, resTy) <- case un t of
    (Pi arg resTy) -> pure (un arg, I.grading arg, typeOf arg, resTy)
    _ -> expectedInferredTypeForm' "function" t

  let x = absVar  abE
      e = absExpr abE

  -- G, x : A |- e : B

  -- make sure that we are considering the name
  -- coming from the abstraction, rather than the type
  let tB = resTy
  -- tB <- substitute (tv, Var $ x) resTy

  e' <- withGradedVariable' x gr $ withTypedVariable' x tA (checkExpr e tB)

  -- TODO: check grading (2020-03-14)
  pure (I.Lam (x `typedWith` tA `gradedWith` gr) e')

  -- G |- \x -> e : (x : A) -> B
  -- ensureEqualTypes
  -- pure $ mkType (Pi (x `typedWith` tA `gradedWith` thatMagicalGrading) tB) (nextLevel (Max (level tA) (level tB)))
  -- ensureEqualTypes t (FunTy (mkAbs x tA tB))

{-
   G |- t1 : (x : A) -> B
   G |- t2 : A
   ---------------------- :: App
   G |- t1 t2 : [t2/x]B
-}
checkExpr_ (App e1 e2) t = do
  -- (_tv, gr, tA, resTy) <- case un t of
  --   (Pi arg resTy) -> pure (un arg, I.grading arg, typeOf arg, resTy)
  --   _ -> expectedInferredTypeForm' "function" t

  -- G |- t1 : (x : A) -> B
  (e1Term, e1Ty) <- inferExpr e1
  -- e1Ty <- inferFunTy e1
  (x, tA, tB) <-
    case un e1Ty of
      Pi arg resTy -> pure (un (un arg), typeOf arg, resTy)
      _ -> expectedInferredTypeForm' "function" e1Ty

  -- let x  = absVar e1Ty
  --     tA = absTy  e1Ty
  --     tB = absExpr e1Ty

  -- G |- t2 : A
  e2Term <- checkExpr e2 tA
  -- _e2Ty <- checkOrInferType tA e2

  -- G |- t1 t2 : [t2/x]B
  t2forXinB <- substituteAndNormalise (x, e2Term) tB
  -- t2forXinB <- substitute (x, e2) tB
  ensureEqualTypes t t2forXinB
  case e1Term of
    (I.App f xs) -> pure $ I.App f (xs ++ [e2Term])
    (I.Lam arg body) -> substituteAndNormalise (un (un arg), e2Term) body
    (TypeTerm t) ->
      case un t of
        (TyApp f xs) -> pure . TypeTerm $ mkType (TyApp f (xs ++ [e2Term])) (level t)
        _ -> notImplemented "checkExpr_: hit a supposedly impossible clause"
    _ -> notImplemented "checkExpr_: hit a supposedly impossible clause"

  -- where inferFunTy :: Expr -> CM Abstraction
  --       inferFunTy e = withLocalCheckingOf e $ do
  --         t <- synthType e >>= normalise
  --         getAbsFromFunTy t
---------
-- Sig --
---------

{-
  For a Sig, we simply check that the expression has the stated type
  (and this matches the final expected type).
-}
{-
checkExpr_ (Sig e t') t = do
  ty <- checkExprIsType t'
  ensureEqualTypes t ty
  checkExpr e ty
-}
----------------------
-- Level expression --
----------------------
checkExpr_ (LitLevel l) t = do
  ensureEqualTypes t levelTy'
  pure (Level $ Concrete l)
checkExpr_ _ _ = error "checkExpr_: TODO"


                           {-
-------------------------
----- Normalisation -----
-------------------------


-- | Execute the action with the binder from the abstraction active
-- | (for checking the body of the abstraction in a subject context).
withAbsBinding :: Abstraction -> CM a -> CM a
withAbsBinding ab act =
  let x = absVar ab
  in withGradedVariable x (grading ab) $ withTypedVariable x (absTy ab) act


-- | Execute the action with the binder from the abstraction active
-- | (for checking the body of the abstraction in a subject type
-- | context).
withAbsBindingForType :: Abstraction -> CM a -> CM a
withAbsBindingForType ab act =
  let x = absVar ab
      g = grading ab
      stgrade = subjectTypeGrade g
  -- bind the subject-type grade to the subject grade since we are
  -- checking the remainder of the type (probably!?)
  in withGradedVariable x (mkGrading stgrade Implicit) $ withTypedVariable x (absTy ab) act


-- | Normalise an abstraction via a series of reductions.
normaliseAbs :: Abstraction -> CM Abstraction
normaliseAbs ab = do
  t <- normalise (absTy ab)
  g <- mkGrading <$> normalise (subjectGrade ab) <*> normalise (subjectTypeGrade ab)
  e <- withAbsBinding ab (normalise (absExpr ab))
  pure (mkAbs' (isHidden ab) (absVar ab) g t e)


-- | Indicate that the expresion is now in an irreducible normal form.
finalNormalForm :: Expr -> CM Expr
finalNormalForm = pure


-- | Normalise the expression via a series of reductions.
normalise :: Expr -> CM Expr
normalise Implicit = finalNormalForm Implicit
normalise (Var x) = do
  val <- lookupValue x
  case val of
    Nothing -> finalNormalForm $ Var x
    Just e -> normalise e
normalise (FunTy ab) = finalNormalForm =<< FunTy <$> normaliseAbs ab
normalise (Lam ab) = finalNormalForm =<< Lam <$> normaliseAbs ab
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
        (LSuc' l1, LSuc' l2) ->
          normalise $ lsucApp (lmaxApp l1 l2)

        -- lmax (m + 1) (lsuc l2) ---> lsuc (lmax m l2)
        (LitLevel m, LSuc' l2') | m > 0 ->
          normalise $ lsucApp (lmaxApp (LitLevel (pred m)) l2')

        -- lmax (lsuc l1) (n + 1) ---> lsuc (lmax l1 n)
        (LSuc' l1', LitLevel n) | n > 0 ->
          normalise $ lsucApp (lmaxApp l1' (LitLevel (pred n)))

        -- otherwise we can't reduce further
        _ ->
          finalNormalForm $ lmaxApp l1 l2

    ------------------------
    -- Lambda abstraction --
    ------------------------

    -- (\x -> e) e' ----> [e'/x] e
    (Lam ab) -> substitute (absVar ab, e2') (absExpr ab) >>= normalise

    ------------------------
    -- Other applications --
    ------------------------

    _ -> finalNormalForm $ App e1' e2'
normalise (CoproductCase (z, tC) (x, c) (y, d) e) = do
  e' <- normalise e
  case e' of
    Inl' _l1 _l2 _a _b l -> normalise =<< substitute (x, l) c
    Inr' _l1 _l2 _a _b r -> normalise =<< substitute (y, r) d
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

normalise (Let (LetPatBound p e1) e2) = do
  e1' <- normalise e1
  case maybeGetPatternSubst p e1' of
    Nothing -> normalise e2 >>= finalNormalForm . Let (LetPatBound p e1')
    -- TODO: perform the subject-type substitution only in the type (2020-03-04)
    Just (ssubst, tsubst) -> normalise =<< substitute tsubst =<< substitute ssubst e2
normalise (Sig e t) = Sig <$> normalise e <*> normalise t
normalise e = notImplemented $ "normalise does not yet support '" <> pprintShow e <> "'"


------------------------------
----- AST Type Inference -----
------------------------------


-- | Check if two expressions are equal under normalisation.
equalExprs :: Expr -> Expr -> CM Bool
equalExprs e1 e2 = do
  ne1 <- normalise e1
  ne2 <- normalise e2
  case (ne1, ne2) of
    (Var v1, Var v2) -> pure (v1 == v2)
    (App f1 v1, App f2 v2) -> (&&) <$> equalExprs f1 f2 <*> equalExprs v1 v2
    (FunTy ab1, FunTy ab2) -> equalAbs ab1 ab2
    (Lam ab1, Lam ab2) -> equalAbs ab1 ab2
    (ProductTy ab1, ProductTy ab2) -> equalAbs ab1 ab2
    (Coproduct t1 t2, Coproduct t1' t2') -> (&&) <$> equalExprs t1 t1' <*> equalExprs t2 t2'
    (CoproductCase (z, tC) (x, c) (y, d) e, CoproductCase (z', tC') (x', c') (y', d') e') -> do
      typesOK <- equalExprs tC' =<< substitute (z, Var z') tC
      csOK <- equalExprs c' =<< substitute (x, Var x') c
      dsOK <- equalExprs d' =<< substitute (y, Var y') d
      esOK <- equalExprs e e'
      pure $ typesOK && csOK && dsOK && esOK
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

    (Let (LetPatBound p e1) e2, Let (LetPatBound p' e1') e2') -> do
      case maybeGetPatternUnificationSubst p p' of
        Nothing -> pure False
        Just subst -> do
          e1sOK <- equalExprs e1 e1'
          -- check that e2 and e2' are equal under the pattern substitution
          e2sOK <- (`equalExprs` e2') =<< substitute subst e2
          pure $ e1sOK && e2sOK

    -- when there are two Sigs, we make sure their expressions and types are the same
    (Sig e1 t1, Sig e2 t2) -> (&&) <$> equalExprs e1 e2 <*> equalExprs t1 t2
    -- otherwise we just ignore the type in the Sig
    (Sig e1 _, e2) -> equalExprs e1 e2
    (e1, Sig e2 _) -> equalExprs e1 e2

    (_, _) -> pure False
  where equalAbs :: Abstraction -> Abstraction -> CM Bool
        equalAbs ab1 ab2 = do
          -- checking \(x : a) -> b = \(y : c) -> d
          -- we say:
          -- d' = [y/x]d
          -- then check:
          -- a = c and b = d' (with (x : a) in scope)
          e2s <- substitute (absVar ab2, Var (absVar ab1)) (absExpr ab2)
          (&&) <$> equalExprs (absTy ab1) (absTy ab2)
               <*> withAbsBinding ab1 (equalExprs (absExpr ab1) e2s)


-- | Try and register the name with the given type
registerTypeForName :: Name -> Type -> CM ()
registerTypeForName n t = do
  setType n t


-- | Attempt to infer the types of a definition, and check this against the declared
-- | type, if any.
doDeclarationInference :: Declaration -> CM Declaration
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
    checkExprValidForSignature :: Expr -> CM ()
    checkExprValidForSignature Implicit = pure ()
    checkExprValidForSignature expr = inferUniverseLevel expr >> pure ()

doDeclarationInference (FunEqn (FLHSName v) (FRHSAssign e)) = do

  -- try and get a prescribed type for the equation,
  -- treating it as an implicit if no type is given
  t <- lookupType v
  exprTy <- case t of
              Nothing -> checkOrInferType mkImplicit e
              Just ty -> checkOrInferType ty e

  -- assign the appopriate equation and normalised/inferred type for the name
  setValue v e
  setType v exprTy
  pure (FunEqn (FLHSName v) (FRHSAssign e))


-- | Attempt to infer the types of each definition in the AST, failing if a type
-- | mismatch is found.
doASTInference :: AST -> CM AST
doASTInference (AST ds) = fmap AST $ mapM doDeclarationInference ds


-- | Infer a level for the given type.
inferUniverseLevel :: Type -> CM Level
inferUniverseLevel e = withLocalCheckingOf e $ do
  u <- synthType e
  norm <- normalise u
  case norm of
    (App (Builtin TypeTy) l) -> pure l
    _        -> expectedInferredTypeForm "universe" norm


-- | 'ensureEqualTypes tyExpected tyActual' checks that 'tyExpected' and 'tyActual'
-- | represent the same type (under normalisation), and fails if they differ.
ensureEqualTypes :: Type -> Type -> CM Type
ensureEqualTypes tyExpected tyActual = do
  typesEqual <- equalExprs tyActual tyExpected
  if typesEqual then pure tyActual
  else tyMismatch tyExpected tyActual


-- | Retrieve an Abstraction from a function type expression, failing if the
-- | expression is not a function type.
getAbsFromFunTy :: Type -> CM Abstraction
getAbsFromFunTy t =
  case t of
    FunTy ab -> pure ab
    t        -> expectedInferredTypeForm "function" t


-- | Retrieve an Abstraction from a product type expression, failing if the
-- | expression is not a product type.
getAbsFromProductTy :: Type -> CM Abstraction
getAbsFromProductTy t =
  case t of
    ProductTy ab -> pure ab
    t            -> expectedInferredTypeForm "product" t


-- | 'checkOrInferType ty ex' checks that the type of 'ex' matches 'ty', or infers
-- | it 'ty' is a wild. Evaluates to the calculated type.
checkOrInferType :: Type -> Expr -> CM Expr
checkOrInferType t e = withLocalCheckingOf e $ checkOrInferType' t e


checkOrInferType' :: Type -> Expr -> CM Expr
----------------------
-- Level expression --
----------------------
checkOrInferType' t LitLevel{} = ensureEqualTypes t (builtinBody levelTy)
-------------------------------
----- Dependent Functions -----
-------------------------------

{-
   G |- A : Type l1
   G, x : A |- B : Type l2
   ------------------------------------- :: FunTy
   G |- (x : A) -> B : Type (lmax l1 l2)
-}
checkOrInferType' t (FunTy ab) = do
  -- G |- A : Type l1
  l1 <- inferUniverseLevel (absTy ab)

  -- G, x : A |- B : Type l2
  l2 <- withAbsBindingForType ab $ inferUniverseLevel (absExpr ab)

  -- G |- (x : A) -> B : Type (lmax l1 l2)
  lmaxl1l2 <- normalise (lmaxApp l1 l2)
  ensureEqualTypes t (mkUnivTy lmaxl1l2)

--------------------------------------------
-- Abstraction expression, with wild type --
--------------------------------------------
checkOrInferType' Implicit expr@(Lam ab) = do
  rTy <- withAbsBinding ab $ checkOrInferType mkImplicit (absExpr ab)
  checkOrInferType (FunTy (mkAbs' (isHidden ab) (absVar ab) (grading ab) (absTy ab) rTy)) expr

{-
   G, x : A |- e : B
   --------------------------------- :: Lam
   G |- \(x : A) -> e : (x : A) -> B
-}
checkOrInferType' t (Lam abE) = do
  _l <- inferUniverseLevel t
  abT <- normalise t >>= getAbsFromFunTy

  let x = absVar  abE
      e = absExpr abE
      tA = absTy abT
      gr = grading abT

  -- G, x : A |- e : B

  -- make sure that we are considering the name
  -- coming from the abstraction, rather than the type
  tB <- substitute (absVar abT, Var $ x) (absExpr abT)

  tB <- withGradedVariable x gr $ withTypedVariable x tA (checkOrInferType tB e)

  -- G |- \x -> e : (x : A) -> B
  ensureEqualTypes t (FunTy (mkAbs x tA tB))

{-
   G |- t1 : (x : A) -> B
   G |- t2 : A
   ---------------------- :: App
   G |- t1 t2 : [t2/x]B
-}
checkOrInferType' t (App e1 e2) = do

  -- G |- t1 : (x : A) -> B
  e1Ty <- inferFunTy e1

  let x  = absVar e1Ty
      tA = absTy  e1Ty
      tB = absExpr e1Ty

  -- G |- t2 : A
  _e2Ty <- checkOrInferType tA e2

  -- G |- t1 t2 : [t2/x]B
  t2forXinB <- substitute (x, e2) tB
  ensureEqualTypes t t2forXinB

  where inferFunTy :: Expr -> CM Abstraction
        inferFunTy e = withLocalCheckingOf e $ do
          t <- synthType e >>= normalise
          getAbsFromFunTy t

-----------------------------
----- Dependent Tensors -----
-----------------------------

{-
   G |- A : Type l1
   G, x : A |- B : Type l2
   ------------------------------------ :: ProductTy
   G |- (x : A) * B : Type (lmax l1 l2)
-}
checkOrInferType' t (ProductTy ab) = do
  -- G |- A : Type l1
  l1 <- inferUniverseLevel (absTy ab)

  -- G, x : A |- B : Type l2
  l2 <- withAbsBindingForType ab $ inferUniverseLevel (absExpr ab)

  -- G |- (x : A) * B : Type (lmax l1 l2)
  lmaxl1l2 <- normalise (lmaxApp l1 l2)
  ensureEqualTypes t (mkUnivTy lmaxl1l2)

{-
   G |- t1 : A
   G |- t2 : [t1/x]B
   G, x : A |- B : Type l
   --------------------------- :: Pair
   G |- (t1, t2) : (x : A) * B
-}
checkOrInferType' t (Pair e1 e2) = do
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
  ensureEqualTypes t (ProductTy (mkAbs x tA tB))

----------------
-- Coproducts --
----------------

{-
   G |- A : Type l1
   G |- B : Type l2
   ------------------------------ :: Coproduct
   G |- A + B : Type (lmax l1 l2)
-}
checkOrInferType' t (Coproduct tA tB) = do
  -- G |- A : Type l1
  l1 <- inferUniverseLevel tA

  -- G |- B : Type l2
  l2 <- inferUniverseLevel tB

  -- G |- (x : A) -> B : Type (lmax l1 l2)
  lmaxl1l2 <- normalise (lmaxApp l1 l2)
  ensureEqualTypes t (mkUnivTy lmaxl1l2)

{-
   G, z : A + B |- C : Type l
   G, x : A |- c : [inl x/z]C
   G, y : B |- d : [inr y/z]C
   G |- e : A + B
   ------------------------------------------------------ :: CoproductCase
   G |- case z@e of (Inl x -> c; Inr y -> d) : C : [e/z]C
-}
checkOrInferType' t (CoproductCase (z, tC) (x, c) (y, d) e) = do
  -- G |- e : A + B
  (tA, tB) <- inferCoproductTy e
  l1 <- inferUniverseLevel tA
  l2 <- inferUniverseLevel tB

  -- G, z : A + B |- C : Type l
  _l <- withTypedVariable z (Coproduct tA tB) $ inferUniverseLevel tC

  -- G, x : A |- c : [inl x/z]C
  let inlX = inlTermApp l1 l2 tA tB (Var x)
  e' <- normalise e
  inlxforzinC <- substitute (z, inlX) tC
  _ <- withTypedVariable x tA $ withActivePattern e' inlX
       $ checkOrInferType inlxforzinC c

  -- G, y : B |- d : [inr y/z]C
  let inrY = inrTermApp l1 l2 tA tB (Var y)
  inryforzinC <- substitute (z, inrY) tC
  _ <- withTypedVariable y tB $ withActivePattern e' inrY
       $ checkOrInferType inryforzinC d

  -- G |- case z@e of (Inl x -> c; Inr y -> d) : C : [e/z]C
  eforzinC <- substitute (z, e) tC
  ensureEqualTypes t eforzinC

  where inferCoproductTy :: Expr -> CM (Expr, Expr)
        inferCoproductTy e = withLocalCheckingOf e $ do
          t <- synthType e >>= normalise
          case t of
            (Coproduct tA tB) -> pure (tA, tB)
            t -> expectedInferredTypeForm "coproduct" t

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
checkOrInferType' t (NatCase (x, tC) cz (w, y, cs) n) = do
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
  ensureEqualTypes t nforxinC

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
checkOrInferType' t (RewriteExpr (x, y, p, tC) (z, c) a b p') = do
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
  ensureEqualTypes t aforxbforypforpinC

-----------
-- Empty --
-----------

{-
   G, x : Empty |- C : Type l
   G |- a : Empty
   ------------------------------ :: EmptyElim
   G |- let x@() = a : C : [a/x]C
-}
checkOrInferType' t (EmptyElim (x, tC) a) = do
  let emptyTy' = builtinBody emptyTy

  -- G, x : Empty |- C : Type l
  _l <- withTypedVariable x emptyTy' $ inferUniverseLevel tC

  -- G |- a : Empty
  _ <- checkOrInferType emptyTy' a


  -- G |- let x@() = a : C : [a/x]C
  aforxinC <- substitute (x, a) tC
  ensureEqualTypes t aforxinC

{-
   G, tass(pat) |- C : Type l
   G, sass(pats) |- e2 : [Intro(T, sass(pat))/z]C
   G |- e1 : T
   ---------------------------------------------- :: Let
   G |- let z@pat = e1 in e2 : [e1/z]C
-}
checkOrInferType' t (Let (LetPatBound p e1) e2) = do

  -- G |- e1 : T
  -- the type we are going to try and eliminate
  toElimTy <- synthTypePatGuided p e1

  -- TODO: support cases when e2 isn't a Sig (but normalises to one,
  -- when it is well-typed) (2020-03-04)
  let (e2', tC) =
        case e2 of
          (Sig e2'' tC') -> (e2'', tC')
          -- if we don't have an explicit type for e2, just assume it
          -- is t for now (2020-03-04)
          _           -> (e2, t)

  -- gather some information about the constructor
  (svars, tvars) <- patternVarsForType p toElimTy
  con <- findConstructorForType toElimTy

  -- TODO: generalise the 'z' to arbitrary type vars---make sure the
  -- introConstructed gets substituted in for the vars
  -- correctly(2020-03-04)
  let z = patTyVar p

  -- G, tass(pat) |- C : Type l
  _l <- withBinders tvars $ inferUniverseLevel tC

  -- G, sass(pat) |- e2 : [Intro(T, sass...)/z]C

  -- build the general element
  let introConstructed = applyCon con svars

  e1 <- normalise e1
  introForzinC <- maybe (pure tC) (\z -> substitute (z, introConstructed) tC) z
  _ <- withBinders svars $ withActivePattern e1 introConstructed
       $ checkOrInferType introForzinC e2'

  e1forzinC <- maybe (pure tC) (\z -> substitute (z, e1) tC) z
  ensureEqualTypes t e1forzinC

  where
        withBinders :: [(Name, Expr)] -> CM a -> CM a
        withBinders [] m = m
        withBinders (b:bs) m = uncurry withTypedVariable b $ withBinders bs m

        -- TODO (maybe?): support arbitrarily nested typing patterns (e.g.,
        -- (x@(y, z), a)) (2020-03-04)
        -- | Get the typing variable of a pattern.
        patTyVar :: Pattern -> Maybe Name
        patTyVar (PAt b _) = Just (unBindName b)
        patTyVar _ = Nothing

        applyCon :: Expr -> [(Name, Expr)] -> Expr
        applyCon con args = foldl App con (fmap (Var . fst) args)

        findConstructorForType :: Expr -> CM Expr
        -- constructor for (x : A) * B
        -- is
        -- \(x : A) -> \(y : B) -> (x, y)
        findConstructorForType (ProductTy ab) = do
          xv <- freshen (absVar ab)
          yv <- freshen xv
          pure $ Lam (mkAbs xv (absTy ab)
                      (Lam (mkAbs yv (absExpr ab) (Pair (Var xv) (Var yv)))))
        findConstructorForType (Builtin DUnitTy) = pure (Builtin DUnitTerm)
        findConstructorForType t = notImplemented
          $ "I don't yet know how to form a constructor of type '" <> pprintShow t <> "'"


---------
-- Sig --
---------

{-
  For a Sig, we simply check that the expression has the stated type
  (and this matches the final expected type).
-}
checkOrInferType' t (Sig e t') = do
  ty <- checkOrInferType t' e
  ensureEqualTypes t ty
-------------------------------------
-- When we don't know how to synth --
-------------------------------------
checkOrInferType' Implicit _ = cannotSynthTypeForExpr
checkOrInferType' t Implicit = cannotSynthExprForType t
----------------------------------
-- Currently unsupported checks --
----------------------------------
checkOrInferType' t e =
  notImplemented $ "I don't yet know how to check the type of expression '" <> pprintShow e <> "' against the type '" <> pprintShow t


-- | Attempt to synthesise a type for the given expression.
synthType :: Expr -> CM Expr
synthType = checkOrInferType mkImplicit


--------------------
----- Patterns -----
--------------------


-- | Compare a pattern against a type, and attempt to build a mapping
-- | from subject binders and subject type binders to their
-- | respective types.
patternVarsForType :: Pattern -> Type -> CM ([(Name, Type)], [(Name, Type)])
patternVarsForType (PPair pl pr) (ProductTy ab) =
  (<>) <$> patternVarsForType pl (absTy ab)
       <*> patternVarsForType pr (absExpr ab)
patternVarsForType (PAt n p) t =
  (([], [(unBindName n, t)]) <>) <$> patternVarsForType p t
patternVarsForType (PVar n) t = pure ([(unBindName n, t)], [])
patternVarsForType PUnit (Builtin DUnitTy) = pure ([], [])
patternVarsForType p t = patternMismatch p t


-- | Try and map components of a term to names in a pattern.
maybeGetPatternSubst :: Pattern -> Expr -> Maybe ([(Name, Expr)], [(Name, Expr)])
maybeGetPatternSubst (PPair p1 p2) (Pair l r) =
  maybeGetPatternSubst p1 l <> maybeGetPatternSubst p2 r
-- maybeGetPatternSubst PUnit (Builtin DUnitTerm) = pure []
maybeGetPatternSubst (PAt n p) e =
  (([], [(unBindName n, e)]) <>) <$> maybeGetPatternSubst p e
maybeGetPatternSubst PUnit (Builtin DUnitTerm) = pure ([], [])
maybeGetPatternSubst (PVar n) e = pure ([(unBindName n, e)], [])
maybeGetPatternSubst _ _ = Nothing


-- TODO: maybe this should account for cases where you have different
-- patterns (e.g., (x, y) and z---then the 'z' should normalise to
-- '(x, y)') (2020-03-04)
-- | Try and map the variables of one pattern to the variables of another.
maybeGetPatternUnificationSubst :: Pattern -> Pattern -> Maybe [(Name, Expr)]
maybeGetPatternUnificationSubst (PVar n) (PVar m) =
  pure . pure $ (unBindName n, Var (unBindName m))
maybeGetPatternUnificationSubst (PPair l1 r1) (PPair l2 r2) =
  maybeGetPatternUnificationSubst l1 l2 <> maybeGetPatternUnificationSubst r1 r2
maybeGetPatternUnificationSubst _ _ = Nothing


-- | Synthesise a type for a term, guided by a pattern it should match.
synthTypePatGuided :: Pattern -> Expr -> CM Type
synthTypePatGuided p e = do
  ty <- checkOrInferType (patToImplTy p) e
  patGuideTyNames p ty
  where
    -- | Build up a type with implicits for the expression.
    patToImplTy :: Pattern -> Expr
    patToImplTy (PAt _ p) = patToImplTy p
    patToImplTy (PPair (PVar n) r) =
      ProductTy (mkAbs (unBindName n) Implicit (patToImplTy r))
    patToImplTy PUnit = Builtin DUnitTy
    patToImplTy _ = Implicit

    -- | Try and unify pattern variables with bound variables in the type.
    patGuideTyNames :: Pattern -> Expr -> CM Expr
    patGuideTyNames (PPair (PVar x) r) (ProductTy ab) = do
      let xv = unBindName x
      ae <- patGuideTyNames r =<< substitute (absVar ab, Var xv) (absExpr ab)
      pure $ ProductTy (mkAbs xv (absTy ab) ae)
    patGuideTyNames (PAt _ p) t = patGuideTyNames p t
    -- don't know how to guide the types beyond this point, so we just give them back
    patGuideTyNames _ t = pure t


-- | 'withActivePattern e pat act' takes an expression,
-- | an introduction form produced from a pattern match on the
-- | expression, and an action, then runs the action with variables
-- | rebound as appropriate for equality checking.
withActivePattern :: Expr -> Expr -> CM a -> CM a
withActivePattern e intro act = do
  e' <- normalise e
  case (e', intro) of
    -- when the expression was a variable, just replace uses of it inside
    -- the body
    -- TODO: make sure we don't overwrite vars that are in the pattern (2020-03-10)
    (Var v, _) -> withValuedVariable v intro act
    -- we don't know how to refine the value-scope based on the pattern and
    -- expression, so we just continue as-is
    _ -> act

-}


---------------------
----- Inference -----
---------------------


-- | Infer a type for the expression, and its underlying term.
inferExpr :: Expr -> CM (Term, Type)
inferExpr e = do
  traceM $ "inferExpr: inferring a type and term for expression: " <> pprintShow e
  res@(term, typ) <- withLocalCheckingOf e $ inferExpr_ e
  traceM $ "inferExpr: inferred a term '" <> pprintShow term <> "' and type '" <> pprintShow typ <> "' for expression '" <> pprintShow e <> "'"
  pure res


inferExpr_ :: Expr -> CM (Term, Type)
inferExpr_ (Var x) = do
  ty <- lookupType' x
  mval <- maybeLookupValue x
  let val = maybe (I.App (I.Var x) []) id mval
  pure (val, ty)
inferExpr_ e = notImplemented $ "inferExpr_: TODO, inference for expression: " <> pprintShow e


--------------------
----- Builtins -----
--------------------


getBuiltinType :: BuiltinTerm -> Type
getBuiltinType e =
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

    -- (_+_) : (l1 l2 : Level) -> Type l1 -> Type l2 -> Type (lmax l1 l2)
    DCoproduct -> builtinType coproductBin

    -- inl : (l1 l2 : Level) (a : Type l1) (b : Type l2) -> a -> a + b
    Inl -> builtinType inlTerm

    -- inr : (l1 l2 : Level) (a : Type l1) (b : Type l2) -> b -> a + b
    Inr -> builtinType inrTerm

    -- Nat : Type 0
    DNat -> builtinType natTy

    -- zero : Nat
    DNZero -> builtinType dnzero

    -- succ : Nat -> Nat
    DNSucc -> builtinType dnsucc

    -- Unit : Type 0
    DUnitTy -> builtinType unitTy

    -- unit : Unit
    DUnitTerm -> builtinType unitTerm

    -- Empty : Type 0
    DEmptyTy -> builtinType emptyTy

    -- Id : (l : Level) (a : Type l) -> a -> a -> Type l
    IdTy -> builtinType idTy

    -- refl : (l : Level) (a : Type l) (x : a) -> Id l a x x
    DRefl -> builtinType reflTerm


-------------------
----- Helpers -----
-------------------


universeOrNotAType :: Type -> CM Type
universeOrNotAType t =
  case un t of
    Universe{} -> pure t
    _ -> notAType


theUniverseWeLiveIn :: Type -> Level
theUniverseWeLiveIn = prevLevel . level



class Normalise m t where
  normalise :: t -> m t


instance (Monad m, Normalise m a) => Normalise m [a] where
  normalise = mapM normalise


instance (Applicative m, Functor m, Normalise m a) => Normalise m (Maybe a) where
  normalise = maybe (pure Nothing) (fmap Just . normalise)


instance Normalise CM Term where
  normalise (TypeTerm t) = TypeTerm <$> normalise t
  normalise (Level l) = Level <$> normalise l
  normalise (I.App (I.Var n) xs) = do
    -- mval <- maybeLookupValue n
    mty  <- lookupType' n
    resTy <- substArgs mty xs
    case un resTy of
      -- typing should guarantee 'xs' is empty here
      Universe l -> do
        l' <- normalise l
        xs <- normalise xs
        pure . TypeTerm $ mkType (TyApp (TyVar n) xs) l'
      _ -> error "here"
      -- t@Pi{} -> do
      --   resTy <- substArgs t xs
      --   case un resTy of
      --     Universe l -> do
      --       l' <- normalise l
      --       pure . TypeTerm $ mkType (TyApp (TyVar n) []) l'
      --     _ -> error "here"
    -- case mval of
    --   Nothing -> I.App (I.Var n) <$> mapM normalise xs
    --   Just val ->
    where substArgs :: Type -> [Term] -> CM Type
          substArgs t xs =
            case (un t, xs) of
              (Universe{}, []) -> normalise t
              (Pi arg resTy, x:xs) -> do
                resTy' <- substitute (un (un arg), x) resTy
                substArgs resTy' xs
              _ -> error $ "substArgs: bad call: '" <> pprintShow t <> "' with arguments '" <> show (fmap pprintParened xs) <> "'"
  normalise t = notImplemented $ "normalising term: " <> pprintShow t


instance Normalise CM LevelAtom where
  normalise (LTerm t) = LTerm <$> normalise t


instance Normalise CM Level where
  normalise l@Concrete{} = pure l
  normalise (Plus n t) = do
    t' <- normalise t
    case t' of
      (LTerm (Level (Concrete m))) -> pure (Concrete (n + m))
      _ -> pure (Plus n t')
  normalise l = notImplemented $ "normalising level: " <> pprintShow l


instance Normalise CM TypeTerm where
  normalise (Universe l) = Universe <$> normalise l
  normalise (TyApp (TyVar n) xs) = do
    mval <- maybeLookupValue n
    case mval of
      Nothing -> TyApp (TyVar n) <$> normalise xs
      Just (TypeTerm val) -> un <$> substArgs val xs
      -- Just (TypeTerm val) -> fmap un . normalise =<< substArgs val xs
      Just v -> error $ "got value: " <> pprintShow v
                       {-
    mty  <- lookupType' n
    resTy <- substArgs mty xs
    case un resTy of
      -- typing should guarantee 'xs' is empty here
      Universe _l -> do
        xs <- normalise xs
        pure $ (TyApp (TyVar n) xs)
      _ -> notImplemented $ "normalising type: " <> pprintShow t
      -}

  -- TODO: ROUGH PLAN (2020-03-15)
  -- we want to be able to tell if something is an application of the builtin
  -- 'Type', then we convert this to a universe
  -- might be easier if we make 'Type' a token, so you can't shadow this--then we
  -- don't need to parse it as a variable.
    where substArgs :: Type -> [Term] -> CM Type
          substArgs t xs =
            case (un t, xs) of
              (Universe{}, []) -> normalise t
              (Pi arg resTy, x:xs) -> do
                resTy' <- substituteAndNormalise (un (un arg), x) resTy
                substArgs resTy' xs
              -- as this came from a value lookup, we know it is already in normal
              -- form, thus we cannot reduce
              (TyApp (TyVar v) xs, []) -> do
                xs' <- normalise xs
                pure $ mkType (TyApp (TyVar v) xs') (level t)
              (TyApp (TyVar v) xs, ys) -> do
                xs <- normalise xs
                ys <- normalise ys
                pure $ mkType (TyApp (TyVar v) (xs ++ ys)) (level t)
                -- pure $ mkType (TyApp (TyVar v) xs) (level t)
              -- TyApp (TyVar
              _ -> error $ "substArgs: bad call: '" <> pprintShow t <> "' with arguments '" <> show (fmap pprintParened xs) <> "'"
  normalise t = notImplemented $ "normalising TypeTerm: " <> pprintShow t


instance Normalise CM Type where
  normalise t = mkType <$> normalise (un t) <*> normalise (level t)
  {-
  normalise t = do
    l <- normalise (level t)
    t' <-
      case un t of
        (Universe l) -> Universe <$> normalise l
        (TyApp (TyVar n) xs) -> do
          mval <- maybeLookupValue n
          case mval of
            Nothing -> TyApp (TyVar n) <$> normalise xs
            Just (TypeTerm val) -> un <$> substArgs val xs
            -- Just (TypeTerm val) -> fmap un . normalise =<< substArgs val xs
            Just _ -> error ":("
                             {-
          mty  <- lookupType' n
          resTy <- substArgs mty xs
          case un resTy of
            -- typing should guarantee 'xs' is empty here
            Universe _l -> do
              xs <- normalise xs
              pure $ (TyApp (TyVar n) xs)
            _ -> notImplemented $ "normalising type: " <> pprintShow t
            -}
        _ -> notImplemented $ "normalising type: " <> pprintShow t
    pure $ mkType t' l
    where substArgs :: Type -> [Term] -> CM Type
          substArgs t xs =
            case (un t, xs) of
              (Universe{}, []) -> normalise t
              (Pi arg resTy, x:xs) -> do
                resTy' <- substitute (un (un arg), x) resTy
                substArgs resTy' xs
              (TyApp (TyVar v) xs, ys) ->
              _ -> error $ "substArgs: bad call: '" <> pprintShow t <> "' with arguments '" <> show (fmap pprintParened xs) <> "'"
                   -}


substituteAndNormalise :: (Monad m, Normalise m t, Substitutable m s t) => s -> t -> m t
substituteAndNormalise s t = substitute s t >>= normalise
