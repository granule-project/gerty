{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Dlam.TypeChecking
  ( checkExpr
  , checkAST
  ) where


import Control.Monad (when)

import Language.Dlam.Builtins2
import Language.Dlam.Substitution (Substitutable(substitute))
import Language.Dlam.Syntax.Abstract
import Language.Dlam.Syntax.Internal hiding (Var, App, Lam)
import qualified Language.Dlam.Syntax.Internal as I
import Language.Dlam.TypeChecking.Monad
import Language.Dlam.Util.Pretty (pprintShow, pprintParened)
import Language.Dlam.Util.Peekaboo


-- | Require that the term is a valid type (of unknown sort).
checkTermIsType :: Term -> CM Type
checkTermIsType (TypeTerm t) = pure t
checkTermIsType (I.App app) = do
  case un app of
    I.Var v -> do
      l <- fmap theUniverseWeLiveIn (lookupType' v >>= universeOrNotAType)
      pure $ mkTyVar v l
    ConData _ -> notImplemented "checkTermIsType: can't yet deal with data constructors"
    AppDef _ -> notImplemented "checkTermIsType: can't yet deal with axioms"
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
  l <- fmap theUniverseWeLiveIn (lookupType' x >>= universeOrNotAType)
  maybe (pure $ mkTyVar x l) checkTermIsType =<< maybeLookupValue x
checkExprIsType_ (App f e) = do
  (fTerm, fTy) <- inferExprForApp f
  case un fTy of
    IsPi arg resTy -> do

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
  let arg' = mkArg x thatMagicalGrading argTy
  ty <- withArgBoundForType arg' $ checkExprIsType (absExpr ab)
  pure $ mkType (Pi arg' ty) (nextLevel (Max (level argTy) (level ty)))
checkExprIsType_ _e = notAType


-- | Try and register the name with the given type
registerTypeForName :: Name -> Type -> CM ()
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
    (Pi arg1 t1, Pi arg2 t2) -> do
      let x = un (un arg1)
          y = un (un arg2)
      t2s <- substitute (y, mkVar x) t2
      (&&) <$> typesAreEqual (typeOf arg1) (typeOf arg2)
           <*> withArgBound arg1 (typesAreEqual t1 t2s)
    _ -> notImplemented $ "typesAreEqual: TODO: equality of types '" <> pprintShow t1 <> "' and '" <> pprintShow t2 <> "'"
    -- (_, _) -> pure False


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
  tA <- lookupType' x
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
  case val of
    Nothing -> pure $
      case un tA of
        -- this is a partial application
        Pi _ _ -> I.PartialApp (partiallyApplied (VarPartial x) [])
        -- if this is a universe then we construct a type
        Universe l -> TypeTerm (mkTyVar x l)
        -- if it's not a Pi, then it must be fully applied
        _      -> I.App (fullyApplied (I.Var x) [])
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
      arg = mkArg x thatMagicalGrading tA
  tB <- withArgBoundForType arg $ checkExprIsType (absExpr ab)

  -- G |- (x : A) -> B : Type (lmax l1 l2)
  let lmaxl1l2 = Max (level tA) (level tB)
  ensureEqualTypes t (mkUnivTy lmaxl1l2)
  pure . TypeTerm $ mkType (Pi arg tB) lmaxl1l2

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
checkExpr_ (Lam abE) t = do
  (tyArg, gr, tA, resTy) <- case un t of
    (Pi arg resTy) -> pure (arg, I.grading arg, typeOf arg, resTy)
    _ -> expectedInferredTypeForm' "function" t

  let x = absVar  abE
      e = absExpr abE

  -- G, x : A |- e : B

  -- make sure that we are considering the name
  -- coming from the abstraction, rather than the type
  let tB = resTy
      arg' = mkArg x gr tA

  e' <- withArgBoundForType tyArg $ withArgBound arg' (checkExpr e tB)

  -- G |- \x -> e : (x : A) -> B
  -- TODO: check grading (2020-03-14)
  pure (I.Lam arg' e')


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
      IsPi arg resTy -> pure (argVar arg, typeOf arg, resTy)

  -- G |- t2 : A
  e2Term <- checkExpr e2 tA
  -- _e2Ty <- checkOrInferType tA e2

  -- G |- t1 t2 : [t2/x]B
  t2forXinB <- substituteAndNormalise (x, e2Term) tB
  ensureEqualTypes t t2forXinB
  applyPartialToTerm e1Term e2Term tB

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
  -- G, x : Nat |- C : Type l
  tC <- withTypedVariable' x natTy $ checkExprIsType tC

  -- G |- cz : [zero/x]C
  zeroforxinC <- substitute (x, bodyForBuiltin DNZero) tC
  cz <- checkExpr cz zeroforxinC

  -- G, w : Nat, y : [w/x]C |- cs : [succ w/x]C
  succw <- applyPartialToTerm succForApp (mkVar w) natTy
  succwforxinC <- substitute (x, succw) tC
  wforxinC <- substitute (x, mkVar w) tC
  cs <- withTypedVariable' y wforxinC
       $ withTypedVariable' w natTy
       $ checkExpr cs succwforxinC

  -- G |- n : Nat
  n <- checkExpr n natTy

  -- G |- case x@n of (Zero -> cz; Succ w@y -> cs) : C : [n/x]C
  nforxinC <- substitute (x, n) tC
  ensureEqualTypes t nforxinC

  -- now we essentially build an instance of the eliminator
  -- (axiomatic) by converting free variables to lambda-bound
  -- arguments
  pure $ I.App (fullyApplied elimNatForApp
     [ Level (level tC)
     , I.Lam (mkArg' x natTy) (TypeTerm tC)
     , cz
     , I.Lam (mkArg' w natTy) (I.Lam (mkArg' y wforxinC) cs)
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
  -- G, x : Empty |- C : Type l
  tC <- withTypedVariable' x emptyTy $ checkExprIsType tC

  -- G |- a : Empty
  a <- checkExpr a emptyTy

  -- G |- let x@() = a : C : [a/x]C
  aforxinC <- substitute (x, a) tC
  ensureEqualTypes t aforxinC

  -- now we essentially build an instance of the eliminator
  -- (axiomatic) by converting free variables to lambda-bound
  -- arguments
  pure $ I.App (fullyApplied elimEmptyForApp
     [ Level (level tC)
     , I.Lam (mkArg' x emptyTy) (TypeTerm tC)
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
checkExpr_ _ _ = error "checkExpr_: TODO"


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
  let l = mkIdent "l"
      larg = mkArg l thatMagicalGrading levelTy
  in pure (I.Lam larg (TypeTerm (mkType (Universe (mkLevelVar l)) (nextLevel (mkLevelVar l))))
          , mkFunTy l levelTy (mkUnivTy (nextLevel (mkLevelVar l))))
inferExpr_ (Var x) = do
  ty <- lookupType' x
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
      IsPi arg resTy -> pure (argVar arg, typeOf arg, resTy)

  -- G |- t2 : A
  e2Term <- checkExpr e2 tA

  -- G |- t1 t2 : [t2/x]B
  t2forXinB <- substituteAndNormalise (x, e2Term) tB

  term <- applyPartialToTerm e1Term e2Term tB
  pure (term, t2forXinB)
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


theUniverseWeLiveIn :: Type -> Level
theUniverseWeLiveIn = prevLevel . level


-- | Execute the action with the binder active (for subject checking).
withArgBound :: Arg -> CM a -> CM a
withArgBound arg act =
  let x = argVar arg
  in withGradedVariable' x (I.grading arg) $ withTypedVariable' x (typeOf arg) act


-- | Execute the action with the binder active (for subject-type checking).
withArgBoundForType :: Arg -> CM a -> CM a
withArgBoundForType arg act =
  let x = argVar arg
      g = I.grading arg
      stgrade = I.subjectTypeGrade g
  -- bind the subject-type grade to the subject grade since we are
  -- checking the remainder of the type (probably!?)
  in withGradedVariable' x (I.mkGrading stgrade thatMagicalGrade) $ withTypedVariable' x (typeOf arg) act


class Normalise m t where
  normalise :: t -> m t


instance (Monad m, Normalise m a) => Normalise m [a] where
  normalise = mapM normalise


instance (Applicative m, Functor m, Normalise m a) => Normalise m (Maybe a) where
  normalise = maybe (pure Nothing) (fmap Just . normalise)


instance Normalise CM TermThatCanBeApplied where
  normalise (IsPartialApp p) = IsPartialApp . partiallyApplied (un p) <$> normalise (appliedArgs p)
  normalise (IsLam arg body) = do
    let x = un (un arg)
    g <- normalise (I.grading arg)
    argTy <- normalise (typeOf arg)
    let arg' = mkArg x g argTy
    body' <- withArgBound arg' $ normalise body
    pure $ IsLam arg' body'


instance Normalise CM TermThatCannotBeApplied where
  normalise (IsTypeTerm t) = IsTypeTerm <$> normalise t
  normalise (IsLevel l) = IsLevel <$> normalise l
  normalise ap@(IsApp app) = do
    let n = un app
        xs = appliedArgs app
    mty <- lookupType' (name n)
    resTy <- substArgs mty xs
    case un resTy of
      -- typing should guarantee 'xs' is empty here
      Universe l -> do
        l' <- normalise l
        xs <- normalise xs
        case n of
          I.Var n -> pure . IsTypeTerm $ mkType (TyApp (fullyApplied (AppTyVar n) xs)) l'
          I.ConData{} -> notImplemented $ "I don't yet know how to normalise the data constructor application '" <> pprintShow ap <> "'"
          I.AppDef{} -> notImplemented $ "I don't yet know how to normalise the axiomatic application '" <> pprintShow ap <> "'"
      -- we are already fully-applied (with a constant constructor or a free variable),
      -- so all we can do is reduce the arguments
      _ -> IsApp . fullyApplied (un app) <$> normalise xs


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
  normalise (IsPi arg t) = do
    let x = argVar arg
    g <- normalise (I.grading arg)
    argTy <- normalise (typeOf arg)
    let arg' = mkArg x g argTy
    t' <- withArgBoundForType arg' $ normalise t
    pure $ IsPi arg' t'


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


substituteAndNormalise :: (Monad m, Normalise m t, Substitutable m s t) => s -> t -> m t
substituteAndNormalise s t = substitute s t >>= normalise


substArgs :: Type -> [Term] -> CM Type
substArgs t xs =
  case (un t, xs) of
    (Universe{}, []) -> normalise t
    (Pi arg resTy, []) -> pure $ mkType (Pi arg resTy) (level t)
    (Pi arg resTy, x:xs) -> do
      let v = argVar arg
      resTy' <- substituteAndNormalise (v, x) resTy
      xs' <- mapM (substitute (v, x)) xs
      substArgs resTy' xs'
    -- types are fully applied, so the (additional) arguments must be empty
    (TyApp app, []) -> do
      mkType . TyApp . fullyApplied (un app) <$> normalise (appliedArgs app) <*> pure (level t)
    _ -> error $ "substArgs: bad call: '" <> pprintShow t <> "' with arguments '" <> show (fmap pprintParened xs) <> "'"


------------------------
----- Applications -----
------------------------


-- | @applyPartial app arg resTy@ resolves a partial application
-- | (with expected type @resTy@) by applying the argument. The result
-- | is either yet another partial application, a fully-applied term, or
-- | a type.
applyPartial :: TermThatCanBeApplied -> Term -> Type -> CM Term
applyPartial (IsLam larg body) arg _ = substituteAndNormalise (argVar larg, arg) body
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
              VarPartial v -> AppTyVar v
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


mkVar' :: Name -> Type -> Term
mkVar' n ty =
  case un ty of
    Pi{} -> PartialApp (partiallyApplied (VarPartial n) [])
    _    -> mkVar n
