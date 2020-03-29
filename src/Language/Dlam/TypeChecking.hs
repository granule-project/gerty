{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Dlam.TypeChecking
  ( checkExpr
  , checkAST
  ) where


import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe (MaybeT(..), runMaybeT)
import qualified Data.Map as M

import Language.Dlam.Builtins
import Language.Dlam.Syntax.Abstract hiding (nameFromString)
import Language.Dlam.Syntax.Common.Language (HasType)
import Language.Dlam.Syntax.Internal hiding (Var, App, Lam)
import qualified Language.Dlam.Syntax.Internal as I
import Language.Dlam.TypeChecking.Monad
import Language.Dlam.Util.Pretty (Pretty(..), pprintShow, parens, text, int, beside)
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
  pure $ mkType (mkPi' arg' ty) (nextLevel (max2 (level argTy) (level ty)))

{-
   G |- A : Type l1
   G, x : A |- B : Type l2
   ------------------------------------- :: ProductTy
   G |- (x :: A) * B : Type (lmax l1 l2)
-}
checkExprIsType_ (ProductTy ab) = do
  (x, absTy, absExpr) <- openAbs ab

  -- G |- A : Type l1
  tA <- checkExprIsType absTy

  -- TODO: improve support for gradings here (2020-03-24, GD)
  arg' <- buildArg x thatMagicalGrading tA

  -- G, x : A |- B : Type l2
  tB <- withArgBoundForType arg' $ checkExprIsType absExpr


  -- G |- (x :: A) * B : Type (lmax l1 l2)
  mkProductTy arg' tB

{-
   G |- A : Type l1
   G |- B : Type l2
   ------------------------------ :: Coproduct
   G |- A + B : Type (lmax l1 l2)
-}
checkExprIsType_ (Coproduct tA tB) = do
  -- G |- A : Type l1
  tA <- checkExprIsType tA

  -- G |- B : Type l2
  tB <- checkExprIsType tB

  -- G |- A + B : Type (lmax l1 l2)
  pure $ mkCoproductTy tA tB

checkExprIsType_ (Implicit i) = do
  l <- genLevelMeta
  registerMeta i IsImplicit (VISType l)
  pure (mkTypeMeta i l)

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
  ty <- ensureEqualTypes' t tA
  freeVarToTermVar x ty
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
  tA <- ensureEqualTypes' t tA
  val <- maybeLookupValue x
  case val of
    Nothing -> pure $
      case un tA of
        -- this is a partial application
        Pi{} -> mkUnappliedPartialDef x
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
  -- TODO: add proper support for grades (2020-03-16)
  arg <- buildArg x thatMagicalGrading tA
  tB <- withArgBoundForType arg $ checkExprIsType absExpr

  -- G |- (x : A) -> B : Type (lmax l1 l2)
  let lmaxl1l2 = max2 (level tA) (level tB)
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
  (tyArg, gr, ttA, tB) <- case un t of
    (Pi pi) -> lunbind pi $ \(arg, resTy) ->
      pure (arg, I.grading arg, typeOf arg, resTy)
    _ -> expectedInferredTypeForm "function" t

  (x, absTy, absExpr) <- openAbs ab
  tA <- checkExprIsType absTy
  -- TODO: I've had to put this check here to make sure that the meta
  -- gets solved as early as possible, to make sure that the variable
  -- sorts get normalised properly (2020-03-26)
  tA <- ensureEqualTypes' ttA tA

  lamArg <- buildArg x gr tA

  -- replace occurrences of the pi-bound variable with the
  -- lambda-bound variable in the result type (specific to the lambda)
  xvar <- freeVarToTermVar (translate x) tA
  tB <- withArgBound lamArg $ substitute (argVar tyArg, xvar) tB

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

--------------
-- Products --
--------------

checkExpr_ e@ProductTy{} t = do
  -- products are types, so we should be able to determine a type for this
  prodAB <- checkExprIsType e
  -- we just need to make sure that we are expecting a type of the right level
  ensureEqualTypes t (mkUnivTy (level prodAB))
  pure . TypeTerm $ prodAB

{-
   G |- t1 : A
   G |- t2 : [t1/x]B
   G, x : A |- B : Type l
   --------------------------- :: Pair
   G |- (t1, t2) : (x : A) * B
-}
checkExpr_ (Pair e1 e2) t = do
  -- TODO: add support for checking grades (2020-03-25)
  withOpenProductTy t $ \(arg, tB) -> do
    let x = argVar arg
        tA = typeOf arg

    -- G |- t1 : A
    t1 <- checkExpr e1 tA

    -- G, x : A |- B : Type l
    -- we get this from the withOpenProductTy (x is (potentially) free in tB)

    -- G |- t2 : [t1/x]B
    t1forXinB <- substitute (x, t1) tB
    t2 <- checkExpr e2 t1forXinB

    -- G |- (t1, t2) : (x : A) * B
    mkPair (arg, tB) t1 t2

----------------
-- Coproducts --
----------------

checkExpr_ e@Coproduct{} t = do
  -- coproducts are types, so we should be able to determine a type for this
  copAB <- checkExprIsType e
  -- we just need to make sure that we are expecting a type of the right level
  ensureEqualTypes t (mkUnivTy (level copAB))
  pure . TypeTerm $ copAB

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
              (TyApp (Application app)) ->
                if un app == AppTyCon (getTyCon tcCoproduct)
                then case appliedArgs app of
                       [Level _, Level _, TypeTerm tA, TypeTerm tB] -> pure (tA, tB)
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

--------------------
-- Let Eliminator --
--------------------

{-
   G, tass(pat) |- C : Type l
   G, sass(pats) |- e2 : [Intro(T, sass(pat))/z]C
   G |- e1 : T
   ---------------------------------------------- :: Let
   G |- let z@pat = e1 in e2 : [e1/z]C
-}
checkExpr_ (Let (LetPatBound p e1) e2) t = do

  -- G |- t1 : T
  -- the type we are going to try and eliminate
  (t1, toElimTy) <- synthTypePatGuided p e1

  -- gather some information about the constructor
  (svars, tvars) <- patternVarsForType p toElimTy

  -- TODO: support cases when e2 isn't a Sig (but normalises to one,
  -- when it is well-typed) (2020-03-04)
  (e2, tC) <-
    case e2 of
      (Sig e2 tC) -> do
        -- G, tass(pat) |- C : Type l
        tC <- withBinders tvars $ checkExprIsType tC
        pure (e2, tC)
      -- if we don't have an explicit type for e2, just assume it
      -- is t for now (2020-03-04)
      _ -> pure (e2, t)

  -- TODO: generalise the 'z' to arbitrary type vars---make sure the
  -- introConstructed gets substituted in for the vars
  -- correctly (2020-03-04)
  z <- patTyVar p toElimTy

  -- G, sass(pat) |- t2 : [Intro(T, sass...)/z]C

  -- build the general element
  con <- findConstructorForType toElimTy
  introConstructed <- applyCon con svars

  introForzinC <- maybe (pure tC) (\z -> substitute (z, introConstructed) tC) z
  t2 <- withBinders svars $ withActivePattern t1 introConstructed
        $ checkExpr e2 introForzinC

  t1forzinC <- maybe (pure tC) (\z -> substitute (z, t1) tC) z
  ensureEqualTypes t t1forzinC
  pure t2

  where
        withBinders :: [(PatVar, Type)] -> CM a -> CM a
        withBinders [] m = m
        withBinders (b:bs) m = uncurry withPatVarBound b $ withBinders bs m

        -- TODO (maybe?): support arbitrarily nested typing patterns (e.g.,
        -- (x@(y, z), a)) (2020-03-04)
        -- | Get the typing variable of a pattern.
        patTyVar :: Pattern -> Type -> CM (Maybe PatVar)
        patTyVar (PAt b _) ty = Just <$> renderNameForType b ty
        patTyVar _ _ = pure Nothing

        -- TODO: support non-builtin constructors (2020-03-25)
        applyCon :: BuiltinDCon -> [(PatVar, Type)] -> CM Term
        applyCon d args = do
          args <- mapM (uncurry freeVarToTerm) args
          fmap fst $ applyThing d args

        -- TODO: for now we're just going to hardcode certain
        -- constructors to minimise the overhead of getting the new
        -- type checker up and running. When support for user-defined
        -- records is added, this will need to be
        -- changed. (2020-03-25, GD)
        findConstructorForType :: Type -> CM BuiltinDCon
        findConstructorForType ty = do
          isUnit <- runEquality typesAreEqual ty unitTy
          if isUnit then pure $ dcUnit
          else notImplemented $ "I don't yet know how to form a constructor of type '" <> pprintShow ty <> "'"

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
  pure (Level $ singleLevel (Concrete l))

---------------
-- Implicits --
---------------

checkExpr_ (Implicit i) t = do
  v <- vsortForType t
  it <- case v of
          VType l -> registerMeta i IsImplicit (VISType l) >> (pure . TypeTerm $ mkTypeMeta i l)
          VLevel  -> registerMeta i IsImplicit VISLevel >> (pure . Level $ mkLevelMeta i)
          VTerm   -> registerMeta i IsImplicit VISTerm >> (pure $ mkTermMeta i)
  pure it


-------------------------
-- Unimplemented Cases --
-------------------------

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


-- | Try and open the type as a product type, and execute the action with the binder
-- | active, passing the (now free) argument and dependent type to the action.
withOpenProductTy :: Type -> ((Arg, Type) -> CM a) -> CM a
withOpenProductTy ty act =
  case un ty of
    TyApp (Application app) ->
      case (un app, appliedArgs app) of
        (AppTyCon con, [_, _, _, I.Lam lam])
          | getName con == getName tcProduct -> lunbind lam $ \(arg, tB) ->
              case tB of
                TypeTerm tB -> act (arg, tB)
                _ -> malformedProduct
          | otherwise -> malformedProduct
        _ -> notAProduct
    _ -> notAProduct
  where malformedProduct = hitABug "malformed product type"
        notAProduct = expectedInferredTypeForm "product" ty


mkProductTy :: Arg -> Type -> CM Type
mkProductTy xtA tB = do
  let tA = typeOf xtA
  -- G |- (x :: A) * B : Type (lmax l1 l2)
  t <- fmap fst $ applyThing tcProduct
                  [ Level (level tA), Level (level tB)
                  , TypeTerm tA, mkLam' xtA (TypeTerm tB)
                  ]
  case t of
    TypeTerm t -> pure t
    _ -> hitABug "builtin product is broken"


mkPair :: (Arg, Type) -> Term -> Term -> CM Term
mkPair (arg, tB) t1 t2 =
  let tA = typeOf arg
  in fmap fst $ applyThing dcPair [ Level (level tA), Level (level tB)
                                  , TypeTerm tA, mkLam' arg (TypeTerm tB)
                                  , t1, t2]


openAbs :: Abstraction -> CM (FVName, Expr, Expr)
openAbs ab = lunbind ab $ \(absArg, absExpr) ->
  pure (translate $ argName absArg, argTy absArg, absExpr)


-- | Execute the action with the binder active (for subject checking).
withArgBound :: (TCDebug m, CMEnv m) => Arg -> m a -> m a
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


instance Normalise CM (Final t a) where
  normalise (FinalVar x) = pure $ FinalVar x
  normalise (Application app) = do
    let n = un app
        xs = appliedArgs app
    xs <- normalise xs
    pure $ mkFinalApp n xs
  normalise (MetaApp app) = do
    let n = un app
        xs = appliedArgs app
    xs <- normalise xs
    pure $ mkFinalMeta (metaId n) xs


instance Normalise CM TermThatCannotBeApplied where
  normalise (IsTypeTerm t) = IsTypeTerm <$> normalise t
  normalise (IsLevel l) = IsLevel <$> normalise l
  normalise (IsApp app) = IsApp <$> normalise app


instance Normalise CM Term where
  normalise (TermMeta m) = normaliseMetaVar VISTerm m
  normalise (FullTerm t) = FullTerm <$> normalise t
  normalise (PartialTerm t) = PartialTerm <$> normalise t


instance Normalise CM LevelTerm where
  normalise (LApp app) = LApp <$> normalise app


instance Normalise CM Level where
  normalise (LevelMeta m) = normaliseMetaVar VISLevel m
  normalise l@Concrete{} = pure l
  normalise (LTerm t) = LTerm <$> normalise t
  normalise (Plus n t) = do
    t' <- normalise t
    pure $ case t' of
             (Concrete m) -> Concrete (m + n)
             (Plus m l)   -> Plus (m + n) l
             _ -> Plus n t'
  normalise (Max l1 l2) = do
    l1 <- normalise l1
    l2 <- normalise l2
    areEq <- runEquality' levelsAreEqual l1 l2
    case areEq of
      Just l -> pure l
      Nothing -> pure $
        case (l1, l2) of
          (Concrete 0, _) -> l2
          (_, Concrete 0) -> l1
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
  normalise (TyApp app) = TyApp <$> normalise app
  normalise (TTForApp t) = TTForApp <$> normalise t


instance Normalise CM I.Grading where
  -- grades are simple nats at the moment, so no normalisation (2020-03-15, GD)
  normalise g = pure g


instance Normalise CM Type where
  normalise (TypeMeta m l) = normaliseMetaVar (VISType l) m
  normalise t = mkType <$> normalise (un t) <*> normalise (level t)


doTermSubst :: (SubstAll t) => (FreeVar, Term) -> t -> CM t
doTermSubst (n, b) t =
  case (fvToSortedName n, b) of
    (SortedName (VISLevel,  n), Level l)     -> pure $ subst n l t
    (SortedName (VISType{}, n), TypeTerm ty) -> pure $ subst n ty t
    (SortedName (VISTerm,   n), _)           -> pure $ subst n b t
    _ -> hitABug "wrong sort for name"


substitute :: (Normalise CM t, SubstAll t, Pretty t) => (FreeVar, Term) -> t -> CM t
substitute (n, s) t =
  debugBlock "substitute"
    ("substituting '" <> pprintShow s <> "' for '" <> pprintShow n <> "' in '" <> pprintShow t <> "'")
    (\res -> "substituted to get '" <> pprintShow res <> "'")
    (normalise =<< doTermSubst (n, s) t)


normaliseMetaVar :: ISSort t -> MetaId -> CM t
normaliseMetaVar s i = do
  met <- maybeGetMetaSolution s i
  pure $ case met of
           Nothing -> case s of
                        VISLevel  -> mkLevelMeta i
                        VISTerm   -> mkTermMeta  i
                        VISType l -> mkTypeMeta  i l
           Just r -> r


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
    body <- substitute (argVar larg, arg) body
    resTy <- substitute (argVar piArg, arg) resTy
    -- we now check to see if we have produced an application which
    -- appears to be fully-applied, but is actually partial (in which
    -- case we need to say it is partial). An example of when this
    -- could occur is if you have a function 'id : a -> a', then do
    -- the application 'id id', which would itself have type 'a -> a'.
    let body' = case (body, un resTy) of
                  (I.App app, Pi{}) ->
                    mkPartialApp (toPartialTerm (un app)) (appliedArgs app)
                  _ -> body
    pure (body', resTy)
applyPartial (IsPartialApp pa) arg ty =
  let (IsPi pi) = un ty in lunbind pi $ \(piArg, resTy) -> do
  let newArgs = appliedArgs pa <> [arg]
  resTy <- substitute (argVar piArg, arg) resTy
  let resTerm =
        case un resTy of
          -- if the result is a Pi, then this is still partial---it
          -- requires more arguments to become fully applied
          Pi{} -> PartialApp (partiallyApplied (un pa) newArgs)
          -- if the result is a universe, we've just produced a type
          Universe l ->
            let finalApp =
                  mkFinalApp (case un pa of
                    VarPartial v -> AppTyVar v
                    TyConPartial c -> AppTyCon c
                    DefPartial d -> AppTyDef d
                    DConPartial{} -> error "I completed a data constructor application, but produced a type.") newArgs

            in TypeTerm (mkType (TyApp finalApp) l)
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
    Pi{} -> pure $ mkUnappliedPartialVar (translate n)
    -- if this is a universe then we construct a type
    Universe l -> pure $ TypeTerm (mkTyVar (translate n) l)
    -- otherwise we check to see if it is a level, and if not, we just
    -- produce a fully-applied variable
    _    -> do
      isLevTy <- typeIsLevelType ty
      pure $ if isLevTy then Level (mkLevelVar (translate n)) else mkVar (translate n)


freeVarToTerm :: FreeVar -> Type -> CM Term
freeVarToTerm fv ty =
  case (fvToSortedName fv, un ty) of
    (SortedName (VISType{}, n), Universe l) -> pure $ TypeTerm $ mkTyVar n l
    (SortedName (VISLevel, n), _) -> pure $ Level $ mkLevelVar n
    (SortedName (VISTerm, n), TTForApp{}) -> pure $ mkUnappliedPartialVar n
    (SortedName (VISTerm, n), _) -> pure $ mkVar n
    _ -> hitABug $ "bad conversion of free variable '" <> pprintShow fv <> "' to term, with type '" <> pprintShow ty <> "'"


-- TODO: make sure this gives back a type def when appropriate (2020-03-21)
mkUnboundDef :: AName -> Type -> Term
mkUnboundDef n ty =
  case un ty of
    Pi{} -> mkUnappliedPartialDef n
    _    -> mkTermDef n []


-- | Is the given type the type of levels?
typeIsLevelType :: Type -> CM Bool
typeIsLevelType = runEquality typesAreEqual levelTy


-- | Build an argument, where the sort of the bound name is guided by the given type.
renderNameForType :: FVName -> Type -> CM FreeVar
renderNameForType n argTy = do
  vs <- vsortForType argTy
  case vs of
    VLevel   -> pure $ mkFreeVar VISLevel    (translate n :: Name Level)
    VTerm    -> pure $ mkFreeVar VISTerm     (translate n :: Name Term)
    VType l  -> pure $ mkFreeVar (VISType l) (translate n :: Name Type)


type SubstAll a = (Subst Term a, Subst Level a, Subst Type a)


-- | Open two things bound with arguments, making sure the argument
-- | names align.
-- |
-- | This executes the action with the argument variable in scope.
-- |
-- | Executes the action with 'Nothing' if the arguments are of
-- | different sorts or types.
lopenArg2 :: (Alpha a, Normalise CM a, SubstAll a, Pretty a) => Bind Arg a -> Bind Arg a -> (((Arg, a, a) -> Solver b) -> Solver b)
lopenArg2 bound1 bound2 act = lunbind2 bound1 bound2 $ \unbound ->
  case unbound of
    Nothing -> fail "arguments had wrong sorts or names"
    Just (arg1, b1, arg2, b2) -> do
      -- TODO: also add a check for grades (2020-03-24)
      ty <- areEqual (typeOf arg1) (typeOf arg2)
      let x1 = argVar arg1
          x2 = argVar arg2
      -- substitute in to make sure names are the same
      arg1v <- lift $ freeVarToTermVar (((\(AnyName n) -> translate n) (freeVarName x1))) ty
      b2 <- lift $ substitute (x2, arg1v) b2
      let newArg = mkArgAN x1 (I.grading arg1) ty
      withArgBound newArg $ act (newArg, b1, b2)


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


type PatVar = FreeVar


-- TODO: support grades for pattern variables (2020-03-25)
withPatVarBound :: PatVar -> Type -> CM a -> CM a
withPatVarBound n = withVarBound n thatMagicalGrading


-- | Compare a pattern against a type, and attempt to build a mapping
-- | from subject binders and subject type binders to their
-- | respective types.
patternVarsForType :: Pattern -> Type -> CM ([(FreeVar, Type)], [(FreeVar, Type)])
patternVarsForType (PAt n p) t = do
  fv <- renderNameForType n t
  (([], [(fv, t)]) <>) <$> patternVarsForType p t
patternVarsForType PUnit ty = ensureEqualTypes ty unitTy >> pure ([], [])
patternVarsForType p t = patternMismatch p t
-- | Synthesise a term and type for an expression, guided by a pattern it should match.
synthTypePatGuided :: Pattern -> Expr -> CM (Term, Type)
synthTypePatGuided p e = do
  ty <- patToImplTy p
  e <- checkExpr e ty
  pure (e, ty)
  where
    -- | Build up a type with implicits for the expression.
    patToImplTy :: Pattern -> CM Type
    patToImplTy (PAt _ p) = patToImplTy p
    patToImplTy (PPair (PVar n) r) = do
      -- we generate a new meta to be solved later
      tyImpl <- genPatMetaForTy
      n <- renderNameForType n tyImpl
      tyr <- patToImplTy r
      mkProductTy (mkArgAN n thatMagicalGrading tyImpl) tyr
    patToImplTy PUnit = pure unitTy
    patToImplTy (PVar _) = genPatMetaForTy
    patToImplTy p = notImplemented $ "patToImplTy: I don't yet know how to generate a type for pattern '" <> pprintShow p <> "'"


-- | 'withActivePattern e pat act' takes a term,
-- | an introduction form produced from a pattern match on the
-- | term, and an action, then runs the action with variables
-- | rebound as appropriate for equality checking.
withActivePattern :: Term -> Term -> CM a -> CM a
withActivePattern _ _ = id


--------------------------
----- Meta Variables -----
--------------------------


-- | A checker that can gracefully fail.
type Solver a = MaybeT CM a


-- | A function that compares two things for equality, producing a
-- | solution context and the common term if they are equal.
type EqFun a = a -> a -> Solver a


-- | Currently just fails.
notEqual :: (Pretty t) => t -> t -> Solver a
notEqual t1 t2 =
  let msg = "equality failed when comparing '" <> pprintShow t1 <> "' and '" <> pprintShow t2 <> "'"
  in debug msg >> fail msg


-- | Execute the solver, restoring appropriate state information when the solver fails.
withLocalSolving :: Solver a -> CM (Maybe a)
withLocalSolving sol = do
  metas <- getMetas
  res <- runMaybeT sol
  maybe (setMetas metas >> pure Nothing) (pure . Just) $ res


alternatively :: Solver a -> Solver a -> Solver a
alternatively s1 s2 = MaybeT $ do
  maybe (withLocalSolving s2) (pure . Just) =<< withLocalSolving s1


-- | Check if the two things are equal by the given equality test. If the things are
-- | equal, then update the current solution context, if they aren't, then don't touch
-- | the current context.
runEquality :: (Normalise CM a, Pretty a) => EqFun a -> a -> a -> CM Bool
runEquality f t1 t2 = maybe False (const True) <$> runEquality' f t1 t2


runEquality' :: (Normalise CM a, Pretty a) => EqFun a -> a -> a -> CM (Maybe a)
runEquality' f t1 t2 = do
  debugBlock "runEquality'"
    ("checking equality of '" <> pprintShow t1 <> "' and '" <> pprintShow t2 <> "'")
    (maybe "were not equal" (\r -> "were equal with common '" <> pprintShow r <> "'")) $ do
    t1 <- normalise t1
    t2 <- normalise t2
    withLocalSolving (f t1 t2)


class Inj a t where
  inj :: a -> t


instance Inj LevelTerm Level where
  inj = mkTLevel


instance Inj a a where
  inj = id


-- | Try and solve the meta and yield the solution.
solveMeta :: (Pretty a, Inj a t) => MetaId -> (I.ISSort t, a) -> Solver a
solveMeta i (s, t) = do
  debug $ "solving meta '" <> pprintShow i <> "' with solution '" <> pprintShow t <> "'"
  mt <- getMetaType i
  metas <- getMetas
  -- TODO: maybe have 'mergeSolution' yield the new solution (2020-03-26)
  setMetas =<< mergeSolution i (mt, mkMetaSolution (s, inj t)) metas
  pure t
  where mergeSolution :: MetaId -> (MetaType, MetaSolution) -> MetaContext -> Solver MetaContext
        mergeSolution i (mt, mi) mc = do
          s <- getMetaInfo i
          case (mi, metaState s) of
            (MetaSolution (VISTerm, t1), MetaSolved (MetaSolution (VISTerm, t2))) -> do
              debug $ "found existing solution: " <> pprintShow t2
              t <- termsAreEqual t1 t2
              pure (M.insert i (mkSolvedMeta mt (MetaSolution (VISTerm, t))) mc)
            (MetaSolution (VISLevel, l1), MetaSolved (MetaSolution (VISLevel, l2))) -> do
              debug $ "found existing solution: " <> pprintShow l2
              l <- levelsAreEqual l1 l2
              pure (M.insert i (mkSolvedMeta mt (MetaSolution (VISLevel, l))) mc)
            (MetaSolution (VISType l1, t1), MetaSolved (MetaSolution (VISType l2, t2))) -> do
              debug $ "found existing solution: " <> pprintShow t2
              l <- levelsAreEqual l1 l2
              t <- typesAreEqual t1 t2
              pure (M.insert i (mkSolvedMeta mt (MetaSolution (VISType l, t))) mc)
            (_, MetaSolved _) -> fail "wrong sorts"
            (_, MetaUnsolved _) -> pure (M.insert i (mkSolvedMeta mt mi) mc)


genLevelMeta :: CM Level
genLevelMeta = do
  i <- getFreshMetaId
  registerMeta i IsMeta VISLevel
  pure $ mkLevelMeta i


genPatMetaForTy :: CM Type
genPatMetaForTy = genTypeMeta


genTypeMeta :: CM Type
genTypeMeta = do
  l <- genLevelMeta
  i <- getFreshMetaId
  registerMeta i IsMeta (VISType l)
  pure $ mkTypeMeta i l


-----------------------------------
----- Equality and comparison -----
-----------------------------------


class TCEq a where
  areEqual :: EqFun a


liftBoolEq :: (Pretty a, Eq a) => EqFun a
liftBoolEq t1 t2 = if t1 == t2 then pure t1 else notEqual t1 t2


instance TCEq (Name a) where
  areEqual = liftBoolEq


instance TCEq Appable where
  areEqual = liftBoolEq


instance TCEq LAppable where
  areEqual = liftBoolEq


instance TCEq TyAppable where
  areEqual = liftBoolEq


instance (TCEq a) => TCEq (FullyApplied a) where
  areEqual = fullyAppliedAreEqual


instance TCEq Level where
  areEqual = levelsAreEqual


instance TCEq Term where
  areEqual = termsAreEqual


instance TCEq Type where
  areEqual = typesAreEqual


-- | For pretty-printing of lengths.
newtype Length = Length Int
  deriving (Eq)


instance TCEq Length where
  areEqual = liftBoolEq


instance Pretty Length where
  pprint (Length i) = text "length" `beside` parens (int i)


instance (TCEq a) => TCEq [a] where
  areEqual xs ys = areEqual (Length (length xs)) (Length (length ys)) >>
    mapM (uncurry areEqual) (zip xs ys)


fullyAppliedAreEqual :: (TCEq a) => EqFun (FullyApplied a)
fullyAppliedAreEqual app1 app2 = do
  z <- areEqual (un app1) (un app2)
  zs <- mapM (uncurry areEqual) (zip (appliedArgs app1) (appliedArgs app2))
  pure $ fullyApplied z zs


-- | Are the terms equal in the current context?
termsAreEqual :: EqFun Term
termsAreEqual (Level l1) (Level l2) = Level <$> areEqual l1 l2
termsAreEqual (FullTerm (IsApp app)) t = finalEquality VISTerm app t
termsAreEqual t (FullTerm (IsApp app)) = finalEquality VISTerm app t
termsAreEqual (TypeTerm t1) (TypeTerm t2) = TypeTerm <$> areEqual t1 t2
termsAreEqual (I.Lam lam1) (I.Lam lam2) =
  lopenArg2 lam1 lam2 $ \(arg, body1, body2) -> do
    bod <- areEqual body1 body2
    pure (mkLam' arg bod)
termsAreEqual t1 t2 = notEqual t1 t2


-- | Are the levels equal in the current context?
levelsAreEqual :: EqFun Level
levelsAreEqual (Concrete n) (Concrete m) =
  if n == m then pure (Concrete n) else notEqual (Concrete n) (Concrete m)
levelsAreEqual (LTerm (LApp t1)) l2 = finalEquality VISLevel t1 l2
levelsAreEqual l1 (LTerm (LApp t2)) = finalEquality VISLevel t2 l1
levelsAreEqual (Plus n l1) (Plus m l2) =
  if n == m then do
   l <- levelsAreEqual l1 l2
   pure (Plus n l)
  else notEqual (Concrete n) (Concrete m)
levelsAreEqual (Max l1 l2) (Max l1' l2') =
  maxsEq l1 l2 l1' l2' `alternatively` maxsEq l1 l2' l2 l1'
  where maxsEq l1 l2 l1' l2' = do
          l1 <- levelsAreEqual l1 l1'
          l2 <- levelsAreEqual l2 l2'
          pure (Max l1 l2)
levelsAreEqual l1 l2 = notEqual l1 l2


-- | Are the types equal in the current context?
typesAreEqual :: EqFun Type
typesAreEqual t1 t2 = do
  l <- areEqual (level t1) (level t2)
  t <- case (un t1, un t2) of
    (TyApp t1, _) -> un <$> finalEquality (VISType l) t1 t2
    (_, TyApp t2) -> un <$> finalEquality (VISType l) t2 t1
    (Universe l1, Universe l2) -> Universe <$> areEqual l1 l2
    (Pi pi1, Pi pi2) -> lopenArg2 pi1 pi2 $ \(arg, piT1, piT2) ->
      mkPi' arg <$> areEqual piT1 piT2
    (p1, p2) -> notEqual p1 p2
  pure (mkType t l)


finalEquality :: (ToPartialTerm a, Pretty t, HasFinal t a, TCEq t, TCEq a) => ISSort t -> Final t a -> t -> Solver t
finalEquality s f t =
  case (f, toFinal t) of
    (MetaApp app, Nothing) -> case (un app, appliedArgs app) of
                                (m, []) -> solveMeta (metaId m) (s, t)
                                _ -> notEqual (fromFinal s f) t
    (MetaApp app1, Just (MetaApp app2)) -> do
      let m1 = un app1; m2 = un app2
          m1args = appliedArgs app1; m2args = appliedArgs app2
      args <- areEqual m1args m2args
      case args of
        -- no arguments, so we can do a full normalisation of the metas
        [] -> metasAreEqual s (metaId m1) (metaId m2)
        -- had some arguments, so at best we can link each component of the application
        _  -> do
          m <- metaVarsAreEqual s m1 m2
          pure . fromFinal s $ mkFinalMeta (metaId m) args
    (Application app1, Just (Application app2)) -> fromFinal s . Application <$> areEqual app1 app2
    (FinalVar v1, Just (FinalVar v2)) -> fromFinal s . FinalVar <$> areEqual v1 v2
    (MetaApp app1, Just (Application app2)) -> checkMetaWithApp app1 app2
    (Application app1, Just (MetaApp app2)) -> checkMetaWithApp app2 app1
    (MetaApp app, Just (FinalVar v)) -> do
      case (un app, appliedArgs app) of
        (m, []) -> solveMeta (metaId m) (s, fromFinal s (FinalVar v))
        _ -> notEqual (fromFinal s f) t
    (FinalVar v, Just (MetaApp app)) -> do
      case (un app, appliedArgs app) of
        (m, []) -> solveMeta (metaId m) (s, fromFinal s (FinalVar v))
        _ -> notEqual (fromFinal s f) t
    _ -> notEqual (fromFinal s f) t
  where
    checkMetaWithApp app1 app2 = do
      let m = un app1; f = un app2
          margs = appliedArgs app1; fargs = appliedArgs app2
      args <- areEqual margs fargs
      case args of
        -- this was a fully-applied application, so we can solve the meta directly
        [] -> solveMeta (metaId m) (s, fromFinal s (mkFinalApp f args))
        -- we had some arguments, so the meta would have to normalise
        -- to something partial
        _  -> do
          -- we can give the meta the solution of the (unapplied) head
          -- of the application
          _ <- solveMeta (metaId m) (VISTerm, mkPartialApp (toPartialTerm f) [])
          pure (fromFinal s (mkFinalApp f args))


metasAreEqual :: (TCEq t, Pretty t) => ISSort t -> MetaId -> MetaId -> Solver t
metasAreEqual s i1 i2 =
  -- if this represents the same meta ID, then we don't want to bind as this would
  -- cause lookups to point metas to themselves
  if i1 == i2 then lift $ normaliseMetaVar s i1
  -- if the IDs are not equal, we either have:
  else do
    val1 <- maybeGetMetaSolution s i1
    val2 <- maybeGetMetaSolution s i2
    case (val1, val2) of
      -- 1. no solutions for either, so we can safely map one to the other
      (Nothing, Nothing) -> solveMeta i1 (s, mkMetaForSort s i2)
      -- 2. solution for one or the other, so we can directly map the unknown
      (Just v1, Nothing) -> solveMeta i2 (s, v1)
      (Nothing, Just v2) -> solveMeta i1 (s, v2)
      -- 3. solutions for both, in which case we can compare the solutions
      (Just v1, Just v2) -> areEqual v1 v2


-- usually you'll want to use 'metasAreEqual', but when the meta is
-- applied to something, then we are expecting the application to be
-- in normal form, which means we can only give back a meta variable.
metaVarsAreEqual :: (Pretty t, TCEq t) => ISSort t -> EqFun MetaVar
metaVarsAreEqual s m1 m2 = do
  let i1 = metaId m1; i2 = metaId m2
  -- if this represents the same meta ID, then we don't want to bind as this would
  -- cause lookups to point metas to themselves
  if i1 == i2 then pure $ mkMetaVar i1
  -- if the IDs are not equal, we either have:
  else do
    val1 <- maybeGetMetaSolution s i1
    val2 <- maybeGetMetaSolution s i2
    case (val1, val2) of
      -- 1. no solutions for either, so we can safely map one to the other
      (Nothing, Nothing) -> solveMeta i1 (s, mkMetaForSort s i2) >> pure m2
      -- 2. solution for one or the other, so we can directly map the unknown
      (Just v1, Nothing) -> solveMeta i2 (s, v1) >> pure m2
      (Nothing, Just v2) -> solveMeta i1 (s, v2) >> pure m1
      -- 3. solutions for both, in which case we can compare the solutions
      (Just v1, Just v2) -> areEqual v1 v2 >> pure m1


ensureEqualTypes' :: Type -> Type -> CM Type
ensureEqualTypes' tyExpected tyActual =
  debugBlock "ensureEqualTypes'"
    ("checking equality of expected type '" <> pprintShow tyExpected <> "' and actual type '" <> pprintShow tyActual <> "'")
    (\res -> "types were equal with common type '" <> pprintShow res <> "'") $ do
  maybe (tyMismatch tyExpected tyActual) pure =<< runEquality' typesAreEqual tyExpected tyActual


-- | 'ensureEqualTypes tyExpected tyActual' checks that 'tyExpected'
-- | and 'tyActual' represent the same type, and fails if they differ.
ensureEqualTypes :: Type -> Type -> CM ()
ensureEqualTypes t1 t2 = ensureEqualTypes' t1 t2 >> pure ()
