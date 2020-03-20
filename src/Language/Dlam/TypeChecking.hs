{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Dlam.TypeChecking
  ( checkExpr
  , checkAST
  ) where


import Control.Monad (when)

import Language.Dlam.Builtins2
import Language.Dlam.Syntax.Abstract
import Language.Dlam.Syntax.Internal hiding (Var, App, Lam)
import qualified Language.Dlam.Syntax.Internal as I
import Language.Dlam.TypeChecking.Monad
import Language.Dlam.Util.Pretty (pprintShow, pprintParened)
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
checkExprIsType_ (Builtin e) = universeOrNotAType (getBuiltinType e)
checkExprIsType_ (Var x) = do
  ty <- typeOfThing x
  l <- case un ty of
         Universe l -> pure l
         _ -> notAType
  maybe (pure $ mkTyVar (aname2Name x) l) checkTermIsType =<< maybeLookupValue x
checkExprIsType_ (App f e) = do
  (fTerm, fTy) <- inferExprForApp f
  case un fTy of
    IsPi pi -> do
      (arg, resTy) <- unbind pi

      -- make sure the argument matches the required argument type
      let argTy = typeOf arg
      e <- checkExpr e argTy

      -- now do the application, and see if we get a type back
      resTy <- substituteAndNormalise (argVar arg, e) resTy
      appres <- applyPartialToTerm fTerm e resTy

      case appres of
        TypeTerm t -> pure t
        _ -> notAType
checkExprIsType_ (FunTy ab) = do
  let x = absVar ab
  argTy <- checkExprIsType (absTy ab)
  -- TODO: improve support for gradings here (2020-03-17)
  let arg' = mkArg (aname2Name x) thatMagicalGrading argTy
  ty <- withArgBoundForType arg' $ checkExprIsType (absExpr ab)
  pure $ mkType (mkPi' arg' ty) (nextLevel (Max (level argTy) (level ty)))
checkExprIsType_ _e = notAType


-- | Try and register the name with the given type
registerTypeForName :: AName -> Type -> CM ()
registerTypeForName n t = setType' n t


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
  setValue' v val
  setType' v ty


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
    (TyApp app1, TyApp app2) ->
      let x = un app1
          y = un app2
          xs = appliedArgs app1
          ys = appliedArgs app2
      in (&&) <$> pure (length xs == length ys && x == y) <*> (and <$> (mapM (uncurry termsAreEqual) (zip xs ys)))
    (Universe l1, Universe l2) -> levelsAreEqual l1 l2
    (Pi pi1, Pi pi2) -> do
      (arg1, t1) <- unbind pi1
      -- TODO: see if Unbound.LocallyNameless offers a good way to
      -- rebind the variable (2020-03-20)
      (arg2, t2) <- unbind pi2

      let x = argVar arg1
          y = argVar arg2
      t2s <- substitute (y, mkVar x) t2
      (&&) <$> typesAreEqual (typeOf arg1) (typeOf arg2)
           <*> withArgBound arg1 (typesAreEqual t1 t2s)
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
  when (not typesEqual) (tyMismatch' tyExpected tyActual)


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

  -- x @ (k, n) : A in G
  -- G |- x : A
  setSubjectRemaining' x k
  ensureEqualTypes t tA
  val <- maybeLookupValue x
  let xt = aname2Name x
      xv = aname2Name x
  case val of
    Nothing -> pure $
      case un tA of
        -- this is a partial application
        Pi{} -> I.PartialApp (partiallyApplied (VarPartial xv) [])
        -- if this is a universe then we construct a type
        Universe l -> TypeTerm (mkTyVar xt l)
        -- if it's not a Pi, then it must be fully applied
        _      -> I.App (fullyApplied (I.Var xv) [])
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
  tA <- checkExprIsType (absTy ab)

  -- G, x : A |- B : Type l2
  let x = absVar ab
      -- TODO: add proper support for grades (2020-03-16)
      arg = mkArg (aname2Name x) thatMagicalGrading tA
  tB <- withArgBoundForType arg $ checkExprIsType (absExpr ab)

  -- G |- (x : A) -> B : Type (lmax l1 l2)
  let lmaxl1l2 = Max (level tA) (level tB)
  ensureEqualTypes t (mkUnivTy lmaxl1l2)
  pure . TypeTerm $ mkType (mkPi' arg tB) lmaxl1l2

{-
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
checkExpr_ (Lam ab) t = do
  -- TODO: check grading (2020-03-14)
  (tyArg, gr, tA, tB) <- case un t of
    (Pi pi) -> do
      (arg, resTy) <- unbind pi
      pure (arg, I.grading arg, typeOf arg, resTy)
    _ -> expectedInferredTypeForm' "function" t

  tA <- case (absTy ab) of
              Implicit -> pure tA
              lta -> checkExprIsType lta

  let x = aname2Name $ absVar ab
      lamArg = mkArg x gr tA

  -- replace occurrences of the pi-bound variable with the
  -- lambda-bound variable in the result type (specific to the lambda)
  tB <- withArgBound lamArg $ substituteAndNormalise (argVar tyArg, mkVar x) tB

  -- G, x : A |- e : B
  e <- withArgBound lamArg (checkExpr (absExpr ab) tB)

  -- G |- \x -> e : (x : A) -> B
  ensureEqualTypes t (mkFunTy x tA tB)
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

  (x, tA, tB) <-
    case un e1Ty of
      IsPi pi -> fmap (\(arg, resTy) -> (argVar arg, typeOf arg, resTy)) (unbind pi)

  -- G |- t2 : A
  e2Term <- checkExpr e2 tA

  -- G |- t1 t2 : [t2/x]B
  t2forXinB <- substituteAndNormalise (x, e2Term) tB
  ensureEqualTypes t t2forXinB
  applyPartialToTerm e1Term e2Term tB

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
  let xv = aname2Name x
      yv = aname2Name y
      zv = aname2Name z
  -- G |- e : A + B
  (e, tA, tB) <- inferCoproductTy e

  -- G, z : A + B |- C : Type l
  let copAB = mkCoproductTy tA tB
  tC <- withTypedVariable' z copAB $ checkExprIsType tC

  -- G, x : A |- c : [inl x/z]C
  let inlX = mkInlTerm tA tB (mkVar xv)
  inlxforzinC <- substitute (zv, inlX) tC
  c <- withTypedVariable' x tA $ withActivePattern e inlX $ checkExpr c inlxforzinC

  -- G, y : B |- d : [inr y/z]C
  let inrY = mkInrTerm tA tB (mkVar yv)
  inryforzinC <- substitute (zv, inrY) tC
  d <- withTypedVariable' y tB $ withActivePattern e inrY $ checkExpr d inryforzinC

  -- G |- case z@e of (Inl x -> c; Inr y -> d) : C : [e/z]C
  eforzinC <- substitute (zv, e) tC
  ensureEqualTypes t eforzinC

  -- now we essentially build an instance of the eliminator
  -- (axiomatic) by converting free variables to lambda-bound
  -- arguments
  pure $ I.App (fullyApplied elimCoproductForApp
     [ Level (level tA), Level (level tB), Level (level tC)
     , TypeTerm tA, TypeTerm tB, mkLam zv copAB (TypeTerm tC)
     , e
     , mkLam xv tA c
     , mkLam yv tB d
     ])

  where inferCoproductTy :: Expr -> CM (Term, Type, Type)
        inferCoproductTy e = withLocalCheckingOf e $ do
          (e, ty) <- inferExpr e
          (tA, tB) <-
            case un ty of
              (TyApp app) ->
                if un app == AppTyCon tcCoproduct
                then case appliedArgs app of
                       [TypeTerm tA, TypeTerm tB] -> pure (tA, tB)
                       _ -> error "ill-formed coproduct"
                else expectedInferredTypeForm' "coproduct" ty
              _ -> expectedInferredTypeForm' "coproduct" ty
          pure (e, tA, tB)

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
  let wv = aname2Name w
      xv = aname2Name x
      yv = aname2Name y
  -- G, x : Nat |- C : Type l
  tC <- withTypedVariable' x natTy $ checkExprIsType tC

  -- G |- cz : [zero/x]C
  zeroforxinC <- substitute (xv, bodyForBuiltin DNZero) tC
  cz <- checkExpr cz zeroforxinC

  -- G, w : Nat, y : [w/x]C |- cs : [succ w/x]C
  succw <- applyPartialToTerm succForApp (mkVar wv) natTy
  succwforxinC <- substitute (xv, succw) tC
  wforxinC <- substitute (xv, mkVar wv) tC
  cs <- withTypedVariable' y wforxinC
       $ withTypedVariable' w natTy
       $ checkExpr cs succwforxinC

  -- G |- n : Nat
  n <- checkExpr n natTy

  -- G |- case x@n of (Zero -> cz; Succ w@y -> cs) : C : [n/x]C
  nforxinC <- substitute (xv, n) tC
  ensureEqualTypes t nforxinC

  -- now we essentially build an instance of the eliminator
  -- (axiomatic) by converting free variables to lambda-bound
  -- arguments
  pure $ I.App (fullyApplied elimNatForApp
     [ Level (level tC)
     , mkLam xv natTy (TypeTerm tC)
     , cz
     , mkLam wv natTy (mkLam yv wforxinC cs)
     , n])

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
  let xv = aname2Name x
  -- G, x : Empty |- C : Type l
  tC <- withTypedVariable' x emptyTy $ checkExprIsType tC

  -- G |- a : Empty
  a <- checkExpr a emptyTy

  -- G |- let x@() = a : C : [a/x]C
  aforxinC <- substitute (xv, a) tC
  ensureEqualTypes t aforxinC

  -- now we essentially build an instance of the eliminator
  -- (axiomatic) by converting free variables to lambda-bound
  -- arguments
  pure $ I.App (fullyApplied elimEmptyForApp
     [ Level (level tC)
     , mkLam xv emptyTy (TypeTerm tC)
     , a])

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
inferExpr_ EType =
  let l = nameFromString "l"
      lv = mkLevelVar l
      succl = nextLevel lv
      larg = mkArg l thatMagicalGrading levelTy
  in pure (mkLam' larg (TypeTerm (mkType (Universe lv) succl))
          , mkFunTy l levelTy (mkUnivTy succl))
inferExpr_ (Var x) = do
  ty <- typeOfThing x
  mval <- maybeLookupValue x
  let val = maybe (mkVar' x ty) id mval
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

  (x, tA, tB) <-
    case un e1Ty of
      IsPi pi -> fmap (\(arg, resTy) -> (argVar arg, typeOf arg, resTy)) (unbind pi)

  -- G |- t2 : A
  e2Term <- checkExpr e2 tA

  -- G |- t1 t2 : [t2/x]B
  t2forXinB <- substituteAndNormalise (x, e2Term) tB

  term <- applyPartialToTerm e1Term e2Term tB
  pure (term, t2forXinB)

{-
   G, x : A |- e : B
   --------------------------------- :: Lam
   G |- \(x : A) -> e : (x : A) -> B
-}
inferExpr_ (Lam ab) = do
  -- TODO: handle the grading on the binder (2020-03-18)
  let x = absVar ab
      xv = aname2Name x
  tA <- checkExprIsType (absTy ab)

  -- G, x : A |- e : B
  (e, tB) <- withTypedVariable' x tA $ inferExpr (absExpr ab)

  -- G |- \(x : A) -> e : (x : A) -> B
  pure (mkLam xv tA e, mkFunTy xv tA tB)

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
    _ -> expectedInferredTypeForm' "function" ty


--------------------
----- Builtins -----
--------------------


getBuiltinType :: BuiltinTerm -> Type
getBuiltinType e = typeForBuiltin e


-------------------
----- Helpers -----
-------------------


universeOrNotAType :: Type -> CM Type
universeOrNotAType t =
  case un t of
    Universe{} -> pure t
    _ -> notAType


-- | Execute the action with the binder active (for subject checking).
withArgBound :: Arg -> CM a -> CM a
withArgBound arg act =
  let x = argVar arg
  in withVarBound x (I.grading arg) (typeOf arg) act


-- | Execute the action with the binder active (for subject-type checking).
withArgBoundForType :: Arg -> CM a -> CM a
withArgBoundForType arg act =
  let x = argVar arg
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
  normalise (IsLam lam) = do
    (arg, body) <- unbind lam
    let x = argVar arg
    g <- normalise (I.grading arg)
    argTy <- normalise (typeOf arg)
    let arg' = mkArg x g argTy
    body' <- withArgBound arg' $ normalise body
    pure $ IsLam (bind arg' body')


instance Normalise CM TermThatCannotBeApplied where
  normalise (IsTypeTerm t) = IsTypeTerm <$> normalise t
  normalise (IsLevel l) = IsLevel <$> normalise l
  normalise ap@(IsApp app) = do
    let n = un app
        xs = appliedArgs app
    mty <- typeOfThing n
    xs <- normalise xs
    resTy <- substArgs mty xs
    case un resTy of
      -- typing should guarantee 'xs' is empty here
      Universe l -> do
        l' <- normalise l
        case n of
          I.Var n -> pure . IsTypeTerm $ mkType (TyApp (fullyApplied (AppTyVar (termVarToTyVar n)) xs)) l'
          I.ConData{} -> notImplemented $ "I don't yet know how to normalise the data constructor application '" <> pprintShow ap <> "'"
          I.AppDef{} -> notImplemented $ "I don't yet know how to normalise the axiomatic application '" <> pprintShow ap <> "'"
      -- we are already fully-applied (with a constant constructor or a free variable),
      -- so all we can do is reduce the arguments
      _ -> pure . IsApp $ fullyApplied (un app) xs


instance Normalise CM Term where
  normalise (FullTerm t) = FullTerm <$> normalise t
  normalise (PartialTerm t) = PartialTerm <$> normalise t


instance Normalise CM LevelAtom where
  normalise (LTerm t) = LTerm <$> normalise t


instance Normalise CM Level where
  normalise l@Concrete{} = pure l
  normalise (Plus n t) = do
    t' <- normalise t
    case t' of
      (LTerm (Level (Concrete m))) -> pure (Concrete (n + m))
      _ -> pure (Plus n t')
  normalise (Max l1 l2) = do
    l1 <- normalise l1
    l2 <- normalise l2
    pure $ case (l1, l2) of
             (Concrete n, Concrete m) -> Concrete (max n m)
             _ -> Max l1 l2


instance Normalise CM TypeTermOfTermsThatCanBeApplied where
  normalise (IsPi pi) = do
    (arg, t) <- unbind pi
    let x = argVar arg
    g <- normalise (I.grading arg)
    argTy <- normalise (typeOf arg)
    let arg' = mkArg x g argTy
    t' <- withArgBoundForType arg' $ normalise t
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


substituteAndNormalise :: (Normalise m t, Subst b t) => (Name b, b) -> t -> m t
substituteAndNormalise (n, s) t = normalise (subst n s t)


substitute :: (Monad m, Subst b t) => (Name b, b) -> t -> m t
substitute (n, s) t = pure $ subst n s t


substArgs :: Type -> [Term] -> CM Type
substArgs t xs =
  case (un t, xs) of
    (Universe{}, []) -> pure t
    (Pi pi, []) -> fmap (\(arg, resTy) -> mkType (mkPi' arg resTy) (level t)) (unbind pi)
    (Pi pi, x:xs) -> do
      (arg, resTy) <- unbind pi
      let v = argVar arg
      resTy' <- substituteAndNormalise (v, x) resTy
      substArgs resTy' xs
    -- types are fully applied, so the (additional) arguments must be empty
    (TyApp app, []) ->
      pure $ mkType (TyApp (fullyApplied (un app) (appliedArgs app))) (level t)
    _ -> error $ "substArgs: bad call: '" <> pprintShow t <> "' with arguments '" <> show (fmap pprintParened xs) <> "'"


------------------------
----- Applications -----
------------------------


-- | @applyPartial app arg resTy@ resolves a partial application
-- | (with expected type @resTy@) by applying the argument. The result
-- | is either yet another partial application, a fully-applied term, or
-- | a type.
applyPartial :: TermThatCanBeApplied -> Term -> Type -> CM Term
applyPartial (IsLam lam) arg _ =
  (\(larg, body) -> substituteAndNormalise (argVar larg, arg) body) =<< unbind lam
applyPartial (IsPartialApp pa) arg resTy = pure $
  let newArgs = appliedArgs pa <> [arg] in
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


applyPartialToTerm :: TermThatCanBeApplied -> Term -> Type -> CM Term
applyPartialToTerm = applyPartial


mkVar' :: AName -> Type -> Term
mkVar' n ty =
  case un ty of
    Pi{} -> PartialApp (partiallyApplied (VarPartial (aname2Name n)) [])
    _    -> mkVar $ aname2Name n


class InScope a where
  typeOfThing :: a -> CM Type


instance InScope Appable where
  typeOfThing (I.Var v) = lookupFVType v
  typeOfThing (ConData d) = typeOfThing d
  typeOfThing (AppDef d) = typeOfThing d


instance InScope DCon where
  typeOfThing = typeOfThing . getName


instance InScope AName where
  typeOfThing = lookupType'


--------------------
----- Patterns -----
--------------------


-- | 'withActivePattern e pat act' takes an expression,
-- | an introduction form produced from a pattern match on the
-- | expression, and an action, then runs the action with variables
-- | rebound as appropriate for equality checking.
withActivePattern :: Term -> Term -> CM a -> CM a
withActivePattern e intro _act = notImplemented $ "withActivePattern: TODO (called with term '" <> pprintShow e <> "' and pattern term '" <> pprintShow intro <> "')"
