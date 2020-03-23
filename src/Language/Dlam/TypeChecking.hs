{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Dlam.TypeChecking
  ( checkExpr
  , checkAST
  ) where


import Control.Monad (when)

import Language.Dlam.Builtins
import Language.Dlam.Syntax.Abstract hiding (nameFromString)
import Language.Dlam.Syntax.Common.Language (HasType)
import Language.Dlam.Syntax.Internal hiding (Var, App, Lam)
import qualified Language.Dlam.Syntax.Internal as I
import Language.Dlam.TypeChecking.Monad
import Language.Dlam.Util.Pretty (Pretty, pprintShow)
import Language.Dlam.Util.Peekaboo


-- | Require that the term is a valid type (of unknown sort).
checkTermIsType :: Term -> CM Type
checkTermIsType (TypeTerm t) = pure t
checkTermIsType _ = notAType


-- | Require that the expression is a valid type (of unknown sort).
checkExprIsType :: Expr -> CM Type
checkExprIsType e =
  debugBlock "checkExprIsType"
    ("checking that '" <> pprintShow e <> "' is a type expression")
    (\res -> "found a type representation '" <> pprintShow res <> "' for expression '" <> pprintShow e <> "'")
    (withLocalCheckingOf e $ checkExprIsType_ e)


checkExprIsType_ :: Expr -> CM Type
checkExprIsType_ (Var x) = do
  ty <- typeOfThing x
  l <- case un ty of
         Universe l -> pure l
         _ -> notAType
  pure $ mkTyVar (nameForType x) l
checkExprIsType_ (Def x) = do
  ty <- typeOfThing x
  l <- case un ty of
         Universe l -> pure l
         _ -> notAType
  maybe (pure $ mkTyDef x l []) checkTermIsType =<< maybeLookupValue x
checkExprIsType_ (App f e) = do
  (fTerm, fTy) <- inferExprForApp f
  (appres, _) <- applyPartialToExpr fTerm e fTy
  case appres of
    TypeTerm t -> pure t
    _ -> notAType
checkExprIsType_ (FunTy ab) = do
  (x, absTy, absExpr) <- openAbs ab
  argTy <- checkExprIsType absTy
  -- TODO: improve support for gradings here (2020-03-17)
  arg' <- buildArg x thatMagicalGrading argTy
  ty <- withArgBoundForType arg' $ checkExprIsType absExpr
  pure $ mkType (mkPi' arg' ty) (nextLevel (Max (level argTy) (level ty)))
checkExprIsType_ _e = notAType


-- | Try and register the name with the given type
registerTypeForName :: AName -> Type -> CM ()
registerTypeForName n t = setType n t


-- | Type-check a declaration.
checkDeclaration :: Declaration -> CM ()
checkDeclaration ts@(TypeSig n t) = do
  ty <- debugBlock "checkDeclaration"
    ("checking signature: " <> pprintShow ts)
    (\ty -> "found type representation '" <> pprintShow ty <> "' for signature '" <> pprintShow ts <> "'")
    -- make sure that the type is actually a type
    (checkExprIsType t)

  registerTypeForName n ty
  where


checkDeclaration eqn@(FunEqn (FLHSName v) (FRHSAssign e)) = do
  (val, ty) <- debugBlock "checkDeclaration"
    ("checking equation: " <> pprintShow eqn)
    (\(val, ty) -> "found term '" <> pprintShow val <> "' and type '" <> pprintShow ty <> "' for equation '" <> pprintShow eqn <> "'")
    (do
      -- try and get a prescribed type for the equation,
      -- treating it as an implicit if no type is given
      t <- maybeLookupType v
      case t of
        -- if we don't have a type (from a signature), try and infer one as well
        Nothing -> inferExpr e
        Just ty -> (,) <$> checkExpr e ty <*> pure ty)

  -- assign the appopriate equation and normalised/inferred type for the name
  setValue v val
  setType v ty


-- | Attempt to infer the types of each definition in the AST, failing if a type
-- | mismatch is found.
checkAST :: AST -> CM ()
checkAST (AST ds) = mapM_ checkDeclaration ds


-- | Are the terms equal in the current context?
termsAreEqual :: Term -> Term -> CM Bool
-- TODO: support remaining cases (2020-03-14)
termsAreEqual (Level l1) (Level l2) = levelsAreEqual l1 l2
termsAreEqual (I.App app1) (I.App app2) =
  let x = un app1
      y = un app2
      xs = appliedArgs app1
      ys = appliedArgs app2
  in (&&) <$> pure (length xs == length ys && x == y)
          <*> (and <$> (mapM (uncurry termsAreEqual) (zip xs ys)))
termsAreEqual (TypeTerm t1) (TypeTerm t2) = typesAreEqual t1 t2
termsAreEqual t1 t2 = notImplemented $ "termsAreEqual: TODO: equality of terms '" <> pprintShow t1 <> "' and '" <> pprintShow t2 <> "'"


-- | Are the levels equal in the current context?
levelTermsAreEqual :: LevelTerm -> LevelTerm -> CM Bool
levelTermsAreEqual (LApp app1) (LApp app2) =
  let x = un app1
      y = un app2
      xs = appliedArgs app1
      ys = appliedArgs app2
  in (&&) <$> pure (length xs == length ys && x == y)
          <*> (and <$> (mapM (uncurry termsAreEqual) (zip xs ys)))


-- | Are the levels equal in the current context?
levelsAreEqual :: Level -> Level -> CM Bool
levelsAreEqual (Concrete n) (Concrete m) = pure $ n == m
levelsAreEqual (Plus n t1) (Plus m t2) =
  (&&) <$> pure (n == m) <*> levelTermsAreEqual t1 t2
-- TODO: support remaining cases (2020-03-14)
levelsAreEqual l1 l2 = notImplemented $ "levelsAreEqual: TODO: equality of levels '" <> pprintShow l1 <> "' and '" <> pprintShow l2 <> "'"


-- | Are the types equal in the current context?
typesAreEqual :: Type -> Type -> CM Bool
typesAreEqual t1 t2 = do
  -- TODO: figure out whether we should actually care whether the levels are equal (2020-03-15)
  -- _levEq <- levelsAreEqual (level t1) (level t2)
  case (un t1, un t2) of
    -- TODO: add proper equality here (2020-03-14)
    (TyApp app1, TyApp app2) ->
      let x = un app1
          y = un app2
          xs = appliedArgs app1
          ys = appliedArgs app2
      in (&&) <$> pure (length xs == length ys && x == y) <*> (and <$> (mapM (uncurry termsAreEqual) (zip xs ys)))
    (Universe l1, Universe l2) -> levelsAreEqual l1 l2
    (Pi pi1, Pi pi2) -> lunbind2 pi1 pi2 $ \unbound ->
      case unbound of
        Nothing -> pure False
        Just (arg1, t1, arg2, t2) ->
          (&&) <$> typesAreEqual (typeOf arg1) (typeOf arg2)
               <*> withArgBound arg1 (typesAreEqual t1 t2)
    -- for any other combination, we assume they are not equal
    (_, _) -> pure False


-- | 'ensureEqualTypes tyExpected tyActual' checks that 'tyExpected'
-- | and 'tyActual' represent the same type, and fails if they differ.
ensureEqualTypes :: Type -> Type -> CM ()
ensureEqualTypes tyExpected tyActual = do
  tyE <- normalise tyExpected
  tyA <- normalise tyActual
  debug $ "ensureEqualTypes: checking equality of expected type '" <> pprintShow tyExpected <> "' and actual type '" <> pprintShow tyActual <> "' which respectively normalise to '" <> pprintShow tyE <> "' and '" <> pprintShow tyA <> "'"
  typesEqual <- typesAreEqual tyE tyA
  -- typesEqual <- typesAreEqual tyExpected tyActual
  when (not typesEqual) (tyMismatch tyExpected tyActual)


-- | Check the expression against the given type, and
-- | if it is well-typed, yield the underlying term.
checkExpr :: Expr -> Type -> CM Term
checkExpr e t =
  debugBlock "checkExpr"
    ("checking expression '" <> pprintShow e <> "' against type '" <> pprintShow t <> "'")
    (\res -> "found term '" <> pprintShow res <> "' for expression '" <> pprintShow e <> "'")
    (withLocalCheckingOf e $ checkExpr_ e t)


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
  tA <- typeOfThing x
  debug $ "checkExpr_: got type '" <> pprintShow tA <> "' for variable '" <> pprintShow x <> "'"
  -- TODO: add back grading (2020-03-21)
  -- kplus1 <- lookupFVSubjectRemaining x
  -- k <- maybe (usedTooManyTimes x) pure $ I.decrementGrade kplus1

  -- G |- A : Type l
  -- ensured by the fact that tA is a type from context

  -- x @ (k, n) : A in G
  -- G |- x : A
  -- setSubjectRemaining x k
  ensureEqualTypes t tA
  freeVarToTermVar x tA
checkExpr_ (Def x) t = do
  -- x @ (k+1, n) : A in G
  tA <- typeOfThing x
  debug $ "checkExpr_: got type '" <> pprintShow tA <> "' for def '" <> pprintShow x <> "'"
  -- TODO: add back grading (2020-03-21)
  -- kplus1 <- lookupFVSubjectRemaining x
  -- k <- maybe (usedTooManyTimes x) pure $ I.decrementGrade kplus1

  -- G |- A : Type l
  -- ensured by the fact that tA is a type from context

  -- x @ (k, n) : A in G
  -- G |- x : A
  -- setSubjectRemaining x k
  ensureEqualTypes t tA
  val <- maybeLookupValue x
  case val of
    Nothing -> pure $
      case un tA of
        -- this is a partial application
        Pi{} -> I.PartialApp (partiallyApplied (DefPartial x) [])
        -- if this is a universe then we construct a type
        Universe l -> TypeTerm (mkTyDef x l [])
        -- if it's not a Pi, then it must be fully applied
        _      -> I.App (fullyApplied (I.AppDef x) [])
    Just r -> pure r

-------------------------------
----- Dependent Functions -----
-------------------------------

{-
   G |- A : Type l1
   G, x : A |- B : Type l2
   ------------------------------------- :: FunTy
   G |- (x : A) -> B : Type (lmax l1 l2)
-}
checkExpr_ (FunTy ab) t = do
  -- G |- A : Type l1
  (x, absTy, absExpr) <- openAbs ab
  tA <- checkExprIsType absTy

  -- G, x : A |- B : Type l2
  let -- TODO: add proper support for grades (2020-03-16)
  arg <- buildArg x thatMagicalGrading tA
  tB <- withArgBoundForType arg $ checkExprIsType absExpr

  -- G |- (x : A) -> B : Type (lmax l1 l2)
  let lmaxl1l2 = Max (level tA) (level tB)
  ensureEqualTypes t (mkUnivTy lmaxl1l2)
  pure . TypeTerm $ mkType (mkPi' arg tB) lmaxl1l2

{-
--------------------------------------------
-- Abstraction expression, with wild type --
--------------------------------------------
checkOrInferType' Implicit expr@(Lam ab) = do
  rTy <- withAbsBinding ab $ checkOrInferType mkImplicit absExpr
  checkOrInferType (FunTy (mkAbs' (isHidden ab) (absVar ab) (grading ab) absTy rTy)) expr
-}
{-
   G, x : A |- e : B
   --------------------------------- :: Lam
   G |- \(x : A) -> e : (x : A) -> B
-}
checkExpr_ (Lam ab) t = do
  -- TODO: check grading (2020-03-14)
  (tyArg, gr, tA, tB) <- case un t of
    (Pi pi) -> lunbind pi $ \(arg, resTy) ->
      pure (arg, I.grading arg, typeOf arg, resTy)
    _ -> expectedInferredTypeForm "function" t

  (x, absTy, absExpr) <- openAbs ab
  tA <- case absTy of
              Implicit -> pure tA
              lta -> checkExprIsType lta

  lamArg <- buildArg x gr tA

  -- replace occurrences of the pi-bound variable with the
  -- lambda-bound variable in the result type (specific to the lambda)
  xvar <- freeVarToTermVar (translate x) tA
  tB <- withArgBound lamArg $ substituteAndNormalise (argVar tyArg, xvar) tB

  -- G, x : A |- e : B
  e <- withArgBound lamArg (checkExpr absExpr tB)

  -- G |- \x -> e : (x : A) -> B
  ensureEqualTypes t (mkFunTy' lamArg tB)
  pure $ mkLam' lamArg e


{-
   G |- t1 : (x : A) -> B
   G |- t2 : A
   ---------------------- :: App
   G |- t1 t2 : [t2/x]B
-}
checkExpr_ (App e1 e2) t = do

  -- G |- t1 : (x : A) -> B
  (e1Term, e1Ty) <- inferExprForApp e1

  -- G |- t1 t2 : [t2/x]B
  (t1t2, t2forXinB) <- applyPartialToExpr e1Term e2 e1Ty
  ensureEqualTypes t t2forXinB
  pure t1t2

----------------
-- Coproducts --
----------------

{-
   G |- A : Type l1
   G |- B : Type l2
   ------------------------------ :: Coproduct
   G |- A + B : Type (lmax l1 l2)
-}
checkExpr_ (Coproduct tA tB) t = do
  -- G |- A : Type l1
  tA <- checkExprIsType tA

  -- G |- B : Type l2
  tB <- checkExprIsType tB

  -- G |- (x : A) -> B : Type (lmax l1 l2)
  let lmaxl1l2 = Max (level tA) (level tB)
  ensureEqualTypes t (mkUnivTy lmaxl1l2)

  pure $ TypeTerm $ mkCoproductTy tA tB

{-
   G, z : A + B |- C : Type l
   G, x : A |- c : [inl x/z]C
   G, y : B |- d : [inr y/z]C
   G |- e : A + B
   ------------------------------------------------------ :: CoproductCase
   G |- case z@e of (Inl x -> c; Inr y -> d) : C : [e/z]C
-}
checkExpr_ (CoproductCase (z, tC) (x, c) (y, d) e) t = do
  -- G |- e : A + B
  (e, te, tA, tB) <- inferCoproductTy e

  -- G, z : A + B |- C : Type l
  zv <- renderNameForType z te
  let copAB = mkCoproductTy tA tB
  tC <- withVarTypeBound z copAB $ checkExprIsType tC

  -- G, x : A |- c : [inl x/z]C
  xvar <- freeVarToTermVar x tA
  let inlX = mkInlTerm tA tB xvar
  inlxforzinC <- substitute (zv, inlX) tC
  c <- withVarTypeBound x tA $ withActivePattern e inlX $ checkExpr c inlxforzinC

  -- G, y : B |- d : [inr y/z]C
  yvar <- freeVarToTermVar y tB
  let inrY = mkInrTerm tA tB yvar
  inryforzinC <- substitute (zv, inrY) tC
  d <- withVarTypeBound y tB $ withActivePattern e inrY $ checkExpr d inryforzinC

  -- G |- case z@e of (Inl x -> c; Inr y -> d) : C : [e/z]C
  eforzinC <- substitute (zv, e) tC
  ensureEqualTypes t eforzinC

  xarg <- buildArg x thatMagicalGrading tA
  yarg <- buildArg y thatMagicalGrading tB
  zarg <- buildArg z thatMagicalGrading copAB

  -- now we essentially build an instance of the eliminator
  -- (axiomatic) by converting free variables to lambda-bound
  -- arguments
  fmap fst $ applyThing elimCoproduct
               [ Level (level tA), Level (level tB), Level (level tC)
               , TypeTerm tA, TypeTerm tB, mkLam' zarg (TypeTerm tC)
               , e
               , mkLam' xarg c
               , mkLam' yarg d
               ]

  where inferCoproductTy :: Expr -> CM (Term, Type, Type, Type)
        inferCoproductTy e = withLocalCheckingOf e $ do
          (e, ty) <- inferExpr e
          (tA, tB) <-
            case un ty of
              (TyApp app) ->
                if un app == AppTyCon (getTyCon tcCoproduct)
                then case appliedArgs app of
                       [TypeTerm tA, TypeTerm tB] -> pure (tA, tB)
                       _ -> error "ill-formed coproduct"
                else expectedInferredTypeForm "coproduct" ty
              _ -> expectedInferredTypeForm "coproduct" ty
          pure (e, ty, tA, tB)

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
checkExpr_ (NatCase (x, tC) cz (w, y, cs) n) t = do
  xv <- renderNameForType x natTy
  -- G, x : Nat |- C : Type l
  tC <- withVarTypeBound x natTy $ checkExprIsType tC

  -- G |- cz : [zero/x]C
  zeroforxinC <- substitute (xv, dcZeroBody) tC
  cz <- checkExpr cz zeroforxinC

  -- G, w : Nat, y : [w/x]C |- cs : [succ w/x]C
  wvar <- freeVarToTermVar w natTy
  (succw, _) <- applyThing dcSucc [wvar]
  succwforxinC <- substitute (xv, succw) tC
  wforxinC <- substitute (xv, wvar) tC
  cs <- withVarTypeBound y wforxinC
       $ withVarTypeBound w natTy
       $ checkExpr cs succwforxinC

  -- G |- n : Nat
  n <- checkExpr n natTy

  -- G |- case x@n of (Zero -> cz; Succ w@y -> cs) : C : [n/x]C
  nforxinC <- substitute (xv, n) tC
  ensureEqualTypes t nforxinC

  xarg <- buildArg x thatMagicalGrading natTy
  warg <- buildArg x thatMagicalGrading natTy
  yarg <- buildArg y thatMagicalGrading wforxinC

  -- now we essentially build an instance of the eliminator
  -- (axiomatic) by converting free variables to lambda-bound
  -- arguments
  fmap fst $ applyThing elimNat
               [ Level (level tC)
               , mkLam' xarg (TypeTerm tC)
               , cz
               , mkLam' warg (mkLam' yarg cs)
               , n
               ]

-----------
-- Empty --
-----------

{-
   G, x : Empty |- C : Type l
   G |- a : Empty
   ------------------------------ :: EmptyElim
   G |- let x@() = a : C : [a/x]C
-}
checkExpr_ (EmptyElim (x, tC) a) t = do
  xv <- renderNameForType x emptyTy

  -- G, x : Empty |- C : Type l
  tC <- withVarTypeBound x emptyTy $ checkExprIsType tC

  -- G |- a : Empty
  a <- checkExpr a emptyTy

  -- G |- let x@() = a : C : [a/x]C
  aforxinC <- substitute (xv, a) tC
  ensureEqualTypes t aforxinC

  xarg <- buildArg x thatMagicalGrading emptyTy

  -- now we essentially build an instance of the eliminator
  -- (axiomatic) by converting free variables to lambda-bound
  -- arguments
  fmap fst $ applyThing elimEmpty
               [ Level (level tC)
               , mkLam' xarg (TypeTerm tC)
               , a
               ]

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
  ensureEqualTypes t levelTy
  pure (Level $ Concrete l)
checkExpr_ e t = notImplemented $ "checkExpr_: I don't yet know how to check whether the type of the expression '" <> pprintShow e <> "' matches expected type '" <> pprintShow t <> "'"


---------------------
----- Inference -----
---------------------


-- | Infer a type for the expression, and its underlying term.
inferExpr :: Expr -> CM (Term, Type)
inferExpr e =
  debugBlock "inferExpr"
    ("inferring a type and term for expression: " <> pprintShow e)
    (\(term, typ) -> "inferred a term '" <> pprintShow term <> "' and type '" <> pprintShow typ <> "' for expression '" <> pprintShow e <> "'")
    (withLocalCheckingOf e $ inferExpr_ e)


inferExpr_ :: Expr -> CM (Term, Type)
inferExpr_ (Var x) = do
  ty <- typeOfThing x
  v <- freeVarToTermVar x ty
  pure (v, ty)
inferExpr_ (Def x) = do
  ty <- typeOfThing x
  mval <- maybeLookupValue x
  let val = maybe (mkUnboundDef x ty) id mval
  pure (val, ty)
{-
   G |- t1 : (x : A) -> B
   G |- t2 : A
   ---------------------- :: App
   G |- t1 t2 : [t2/x]B
-}
inferExpr_ (App e1 e2) = do
  -- G |- t1 : (x : A) -> B
  (e1Term, e1Ty) <- inferExprForApp e1

  -- G |- t1 t2 : [t2/x]B
  (t1t2, t2forXinB) <- applyPartialToExpr e1Term e2 e1Ty
  pure (t1t2, t2forXinB)

{-
   G, x : A |- e : B
   --------------------------------- :: Lam
   G |- \(x : A) -> e : (x : A) -> B
-}
inferExpr_ (Lam ab) = do
  -- TODO: handle the grading on the binder (2020-03-18)
  (x, absTy, absExpr) <- openAbs ab
  tA <- checkExprIsType absTy

  -- G, x : A |- e : B
  (e, tB) <- withVarTypeBound x tA $ inferExpr absExpr

  -- G |- \(x : A) -> e : (x : A) -> B
  lamArg <- buildArg x thatMagicalGrading tA
  pure (mkLam' lamArg e, mkFunTy' lamArg tB)

inferExpr_ e = notImplemented $ "inferExpr_: TODO, inference for expression: " <> pprintShow e


-- | Infer a type for the expression, and its underlying term.
-- | The resulting term and type are those of something applicable.
inferExprForApp :: Expr -> CM (TermThatCanBeApplied, TypeOfTermsThatCanBeApplied)
inferExprForApp e =
  debugBlock "inferExprForApp"
    ("inferring a type and term for expression: " <> pprintShow e)
    (\(term, typ) -> "inferred a term '" <> pprintShow term <> "' and type '" <> pprintShow typ <> "' for expression '" <> pprintShow e <> "'")
    (withLocalCheckingOf e $ inferExprForApp_ e)


inferExprForApp_ :: Expr -> CM (TermThatCanBeApplied, TypeOfTermsThatCanBeApplied)
inferExprForApp_ e = do
  (term, ty) <- inferExpr e
  case (term, un ty) of
    (PartialTerm p, TTForApp t) -> pure (p, mkType' t (level ty))
    _ -> expectedInferredTypeForm "function" ty


-------------------
----- Helpers -----
-------------------


openAbs :: Abstraction -> CM (FVName, Expr, Expr)
openAbs ab = lunbind ab $ \(absArg, absExpr) ->
  pure (translate $ argName absArg, argTy absArg, absExpr)


-- | Execute the action with the binder active (for subject checking).
withArgBound :: Arg -> CM a -> CM a
withArgBound arg act =
  let x = freeVarName $ argVar arg
  in withVarBound x (I.grading arg) (typeOf arg) act


-- | Execute the action with the binder active (for subject-type checking).
withArgBoundForType :: Arg -> CM a -> CM a
withArgBoundForType arg act =
  let x = freeVarName $ argVar arg
      g = I.grading arg
      stgrade = I.subjectTypeGrade g
  -- bind the subject-type grade to the subject grade since we are
  -- checking the remainder of the type (probably!?)
  in withVarBound x (I.mkGrading stgrade thatMagicalGrade) (typeOf arg) act


class Normalise m t where
  normalise :: t -> m t


instance (Monad m, Normalise m a) => Normalise m [a] where
  normalise = mapM normalise


instance (Applicative m, Functor m, Normalise m a) => Normalise m (Maybe a) where
  normalise = maybe (pure Nothing) (fmap Just . normalise)


instance Normalise CM TermThatCanBeApplied where
  normalise (IsPartialApp p) = IsPartialApp . partiallyApplied (un p) <$> normalise (appliedArgs p)
  normalise (IsLam lam) = lunbind lam $ \(arg, body) -> do
    let xold = argVar arg
        xoldFV = (\(AnyName n) -> translate n) (freeVarName xold)
    g <- normalise (I.grading arg)
    argTy <- normalise (typeOf arg)
    arg' <- buildArg xoldFV g argTy
    newSort <- vsortForType argTy
    body' <- normalise =<< reSort xold newSort body
    pure $ IsLam (bind arg' body')


instance Normalise CM TermThatCannotBeApplied where
  normalise (IsTypeTerm t) = IsTypeTerm <$> normalise t
  normalise (IsLevel l) = IsLevel <$> normalise l
  normalise (IsApp app) = do
    let n = un app
        xs = appliedArgs app
    xs <- normalise xs
    pure $ IsApp (fullyApplied n xs)


instance Normalise CM Term where
  normalise (FullTerm t) = FullTerm <$> normalise t
  normalise (PartialTerm t) = PartialTerm <$> normalise t


instance Normalise CM LevelTerm where
  normalise (LApp app) = LApp . fullyApplied (un app) <$> mapM normalise (appliedArgs app)


instance Normalise CM Level where
  normalise l@Concrete{} = pure l
  normalise (Plus n t) = do
    t' <- normalise t
    pure (Plus n t')
  normalise (Max l1 l2) = do
    l1 <- normalise l1
    l2 <- normalise l2
    pure $ case (l1, l2) of
             (Concrete n, Concrete m) -> Concrete (max n m)
             _ -> Max l1 l2


instance Normalise CM TypeTermOfTermsThatCanBeApplied where
  normalise (IsPi pi) = lunbind pi $ \(arg, t) -> do
    let xold = argVar arg
        xoldFV = (\(AnyName n) -> translate n) (freeVarName xold)
    g <- normalise (I.grading arg)
    argTy <- normalise (typeOf arg)
    arg' <- buildArg xoldFV g argTy
    newSort <- vsortForType argTy
    t' <- normalise =<< reSort xold newSort t
    pure $ IsPi (bind arg' t')


instance Normalise CM TypeTerm where
  normalise (Universe l) = Universe <$> normalise l
  -- Type variables are free, and thus cannot reduce through application.
  -- Type constructors are constants, and thus also cannot reduce.
  -- TODO: perhaps check we have correct number of arguments  (2020-03-16)
  normalise (TyApp app) = TyApp . fullyApplied (un app) <$> normalise (appliedArgs app)
  normalise (TTForApp t) = TTForApp <$> normalise t


instance Normalise CM I.Grading where
  -- grades are simple nats at the moment, so no normalisation (2020-03-15, GD)
  normalise g = pure g


instance Normalise CM Type where
  normalise t = mkType <$> normalise (un t) <*> normalise (level t)


substituteAndNormalise :: (Normalise CM t, Subst Level t, Subst Type t, Subst Term t, Pretty t) => (FreeVar, Term) -> t -> CM t
substituteAndNormalise (n, s) t = normalise =<< substitute (n, s) t


doTermSubst :: (Subst Level t, Subst Type t, Subst Term t) => (FreeVar, Term) -> t -> CM t
doTermSubst (n, b) t =
  case (fvToSortedName n, b) of
    (SortedName (VISLevel,  n), Level l)     -> pure $ subst n l t
    (SortedName (VISType{}, n), TypeTerm ty) -> pure $ subst n ty t
    (SortedName (VISTerm,   n), _)           -> pure $ subst n b t
    _ -> hitABug "wrong sort for name"


substitute :: (Subst Level t, Subst Type t, Pretty t, Subst Term t) => (FreeVar, Term) -> t -> CM t
substitute (n, s) t =
  debugBlock "substitute"
    ("substituting '" <> pprintShow s <> "' for '" <> pprintShow n <> "' in '" <> pprintShow t <> "'")
    (\res -> "substituted to get '" <> pprintShow res <> "'")
    (doTermSubst (n, s) t)


--------------------------
----- Free Variables -----
--------------------------


-- | Try and replace all occurrences of the variable with a variable of the given sort.
reSort :: (Pretty t, Subst Term t) => FreeVar -> VSort -> t -> CM t
reSort fv vsort t =
  debugBlock "reSort"
    ("re-sorting variable '" <> pprintShow fv <> "' to sort '" <> pprintShow vsort <> "' in '" <> pprintShow t <> "'")
    (\res -> "resorted to '" <> pprintShow res <> "'")
    $
  let vn = fvToSortedName fv in
  case (vn, vsort) of
    -- re-sorting a Term to a Level
    (SortedName (VISTerm, n), VLevel) -> pure $ subst n (Level $ mkLevelVar (translate n)) t
    -- re-sorting a Term to a Type
    (SortedName (VISTerm, n), VType l) -> pure $ subst n (TypeTerm $ mkTypeVar (translate n) l) t
    (SortedName (o, _), n)
      -- the sort wouldn't change, so keep it as is
      | toVSort o == n -> pure t
      -- otherwise we aren't allowed to perform this re-sorting, so
      -- there must be a bug in the implementation
      | otherwise -> hitABug $ "tried to re-sort variable '" <> pprintShow fv <> "' of sort '" <> pprintShow (toVSort o) <> "'"


-- | The sort variables of the given type should belong to.
vsortForType :: Type -> CM VSort
vsortForType ty =
  case un ty of
    -- TODO: perhaps add a sort for variables that can be applied (2020-03-23, GD)
    Universe l -> pure (VType l)
    _    -> do
      isLevTy <- typeIsLevelType ty
      pure $ if isLevTy then VLevel else VTerm


------------------------
----- Applications -----
------------------------


-- | Try and apply the term-like thing to the given arguments.
applyThing :: (ToTerm f, HasType f Type) => f -> [Term] -> CM (Term, Type)
applyThing f = applyMany (toTerm f) (typeOf f)


-- | @applyPartial app arg resTy@ resolves a partial application
-- | (with expected type @resTy@) by applying the argument. The result
-- | is either yet another partial application, a fully-applied term, or
-- | a type.
applyPartial :: TermThatCanBeApplied -> Term -> TypeOfTermsThatCanBeApplied -> CM (Term, Type)
applyPartial l@(IsLam lam) arg lamTy = do
  let (IsPi pi) = un lamTy
  lunbind2 lam pi $ \unbound -> do
    (larg, body, piArg, resTy) <- maybe (hitABug $ "binding structure of '" <> pprintShow l <> "' and '" <> pprintShow lamTy <> "' differed.") pure $ unbound
    body <- substituteAndNormalise (argVar larg, arg) body
    resTy <- substituteAndNormalise (argVar piArg, arg) resTy
    -- we now check to see if we have produced an application which
    -- appears to be fully-applied, but is actually partial (in which
    -- case we need to say it is partial). An example of when this
    -- could occur is if you have a function 'id : a -> a', then do
    -- the application 'id id', which would itself have type 'a -> a'.
    let body' = case (body, un resTy) of
                  (I.App app, Pi{}) ->
                    let papp = case un app of
                                 I.Var v    -> VarPartial v
                                 ConData dc -> DConPartial dc
                                 AppDef d   -> DefPartial d
                    in PartialApp (partiallyApplied papp (appliedArgs app))
                  _ -> body
    pure (body', resTy)
applyPartial (IsPartialApp pa) arg ty =
  let (IsPi pi) = un ty in lunbind pi $ \(piArg, resTy) -> do
  let newArgs = appliedArgs pa <> [arg]
  resTy <- substituteAndNormalise (argVar piArg, arg) resTy
  let resTerm =
        case un resTy of
          -- if the result is a Pi, then this is still partial---it
          -- requires more arguments to become fully applied
          Pi{} -> PartialApp (partiallyApplied (un pa) newArgs)
          -- if the result is a universe, we've just produced a type
          Universe l ->
            let thingApplied =
                  case un pa of
                    VarPartial v -> AppTyVar (termVarToTyVar v)
                    TyConPartial c -> AppTyCon c
                    DefPartial d -> AppTyDef d
                    DConPartial{} -> error "I completed a data constructor application, but produced a type."

            in TypeTerm (mkType (TyApp (fullyApplied thingApplied newArgs)) l)
          -- wasn't a universe, but is fully applied, so it's a term application
          _ -> I.App (fullyApplied (case un pa of
                                      VarPartial v -> I.Var v
                                      DConPartial dc -> ConData dc
                                      DefPartial d -> AppDef d
                                      TyConPartial{} -> error "I completed a type application and produced something that wasn't a type."
                                   ) newArgs)
  pure (resTerm, resTy)


applyPartialToTerm :: TermThatCanBeApplied -> Term -> TypeOfTermsThatCanBeApplied -> CM (Term, Type)
applyPartialToTerm f e ty =
  debugBlock "applyPartialToTerm"
    ("applying fun '" <> pprintShow f <> "' to argument '" <> pprintShow e <> "' with function type '" <> pprintShow ty <> "'")
    (\(term, ty) -> "result of the application was '" <> pprintShow term <> "' of type '" <> pprintShow ty <> "'")
    (applyPartial f e ty)


applyPartialToExpr :: TermThatCanBeApplied -> Expr -> TypeOfTermsThatCanBeApplied -> CM (Term, Type)
applyPartialToExpr f e ty = do
  -- G |- f : (x : A) -> B
  piArgTy <- let (IsPi pi) = un ty in lunbind pi (\(piArg, _) -> pure $ typeOf piArg)
  -- G |- e : A
  e <- checkExpr e piArgTy
  -- G |- f e : [e/x]B
  applyPartialToTerm f e ty


-- | Try and apply a term to zero or more arguments.
applyMany :: Term -> Type -> [Term] -> CM (Term, Type)
applyMany f ty [] = pure (f, ty)
applyMany f ty (arg:args) =
  case (f, un ty) of
    (PartialTerm app, TTForApp pi) -> do
      (newf, newty) <- applyPartial app arg (mkType' pi (level ty))
      applyMany newf newty args
    (_, _) -> expectedInferredTypeForm "function" ty


-- | Render an Abstract free variable as a Term, using the given type to guide
-- | the conversion.
freeVarToTermVar :: FVName -> Type -> CM Term
freeVarToTermVar n ty =
  case un ty of
    -- this is a partial application
    Pi{} -> pure $ I.PartialApp (partiallyApplied (VarPartial (translate n)) [])
    -- if this is a universe then we construct a type
    Universe l -> pure $ TypeTerm (mkTyVar (translate n) l)
    -- otherwise we check to see if it is a level, and if not, we just
    -- produce a fully-applied variable
    _    -> do
      isLevTy <- typeIsLevelType ty
      pure $ if isLevTy then Level (mkLevelVar (translate n)) else mkVar (translate n)


-- TODO: make sure this gives back a type def when appropriate (2020-03-21)
mkUnboundDef :: AName -> Type -> Term
mkUnboundDef n ty =
  case un ty of
    Pi{} -> PartialApp (partiallyApplied (DefPartial n) [])
    _    -> mkTermDef n []


-- | Is the given type the type of levels?
typeIsLevelType :: Type -> CM Bool
typeIsLevelType = typesAreEqual levelTy


-- | Build an argument, where the sort of the bound name is guided by the given type.
renderNameForType :: FVName -> Type -> CM FreeVar
renderNameForType n argTy = do
  vs <- vsortForType argTy
  case vs of
    VLevel   -> pure $ mkFreeVar VISLevel    (translate n :: Name Level)
    VTerm    -> pure $ mkFreeVar VISTerm     (translate n :: Name Term)
    VType l  -> pure $ mkFreeVar (VISType l) (translate n :: Name Type)


-- | Build an argument, where the sort of the bound name is guided by the given type.
buildArg :: FVName -> I.Grading -> Type -> CM Arg
buildArg n g argTy = do
  ntobind <- renderNameForType n argTy
  pure $ mkArgAN ntobind g argTy


class InScope a where
  typeOfThing :: a -> CM Type


instance InScope Appable where
  typeOfThing (I.Var v) = typeOfThing v
  typeOfThing (ConData d) = typeOfThing d
  typeOfThing (AppDef d) = typeOfThing d


instance InScope DCon where
  typeOfThing = typeOfThing . getName


instance InScope AName where
  typeOfThing = lookupType


instance InScope (Name a) where
  typeOfThing = lookupFVType


--------------------
----- Patterns -----
--------------------


-- | 'withActivePattern e pat act' takes an expression,
-- | an introduction form produced from a pattern match on the
-- | expression, and an action, then runs the action with variables
-- | rebound as appropriate for equality checking.
withActivePattern :: Term -> Term -> CM a -> CM a
withActivePattern e intro _act = notImplemented $ "withActivePattern: TODO (called with term '" <> pprintShow e <> "' and pattern term '" <> pprintShow intro <> "')"
