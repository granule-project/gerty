{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Dlam.TypeChecking
  ( checkExpr
  , checkAST
  ) where


import Control.Monad (when)

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
  -- debug $ "levelTy': " <> pprintShow levelTy'
  t <- checkExpr l levelTy'
  case t of
    Level l' -> pure l'
    -- we determined that the expression is a level, but does not represent
    -- a level literal, so it must be a level-like term
    term -> pure (Plus 0 (LTerm term))


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
  debug $ "checkExprIsType: checking that '" <> pprintShow e <> "' is a type expression"
  res <- withLocalCheckingOf e $ checkExprIsType_ e
  debug $ "checkExprIsType: found a type representation '" <> pprintShow res <> "' for expression '" <> pprintShow e <> "'"
  pure res


checkExprIsType_ :: Expr -> CM Type
checkExprIsType_ (Builtin e) = universeOrNotAType (getBuiltinType e)
checkExprIsType_ (Var x) = do
  l <- fmap theUniverseWeLiveIn (lookupType' x >>= universeOrNotAType)
  maybe (pure $ mkType (I.TyApp (I.TyVar x) []) l) checkTermIsType =<< maybeLookupValue x
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
  debug $ "checkDeclaration: checking signature: " <> pprintShow ts
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
  debug $ "checkDeclaration: checking equation: " <> pprintShow eqn

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
  typesEqual <- typesAreEqual tyE tyA
  -- typesEqual <- typesAreEqual tyExpected tyActual
  when (not typesEqual) (tyMismatch' tyExpected tyActual)


-- | Check the expression against the given type, and
-- | if it is well-typed, yield the underlying term.
checkExpr :: Expr -> Type -> CM Term
checkExpr e t = do
  debug $ "checkExpr_: checking expression '" <> pprintShow e <> "' against type '" <> pprintShow t <> "'"
  res <- withLocalCheckingOf e $ checkExpr_ e t
  debug $ "checkExpr: found term '" <> pprintShow res <> "' for expression '" <> pprintShow e <> "'"
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
  -- debug $ "checkExpr_: got type '" <> pprintShow tA <> "' for variable '" <> pprintShow x <> "'"
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
  lmaxl1l2 <- normalise $ Max (level tA) (level tB)
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


---------------------
----- Inference -----
---------------------


-- | Infer a type for the expression, and its underlying term.
inferExpr :: Expr -> CM (Term, Type)
inferExpr e = do
  debug $ "inferExpr: inferring a type and term for expression: " <> pprintShow e
  res@(term, typ) <- withLocalCheckingOf e $ inferExpr_ e
  debug $ "inferExpr: inferred a term '" <> pprintShow term <> "' and type '" <> pprintShow typ <> "' for expression '" <> pprintShow e <> "'"
  pure res


inferExpr_ :: Expr -> CM (Term, Type)
inferExpr_ EType =
  let l = mkIdent "l"
  in pure (I.Lam (l `typedWith` levelTy' `gradedWith` thatMagicalGrading) (TypeTerm (mkType (Universe (mkLevelVar l)) (nextLevel (mkLevelVar l))))
          , mkFunTy l levelTy' (mkUnivTy (lsucApp (mkVar l))))
inferExpr_ (Var x) = do
  ty <- lookupType' x
  mval <- maybeLookupValue x
  let val = maybe (I.App (I.Var x) []) id mval
  pure (val, ty)
{-
   G |- t1 : (x : A) -> B
   G |- t2 : A
   ---------------------- :: App
   G |- t1 t2 : [t2/x]B
-}
inferExpr_ (App e1 e2) = do
  -- G |- t1 : (x : A) -> B
  (e1Term, e1Ty) <- inferExpr e1

  (x, tA, tB) <-
    case un e1Ty of
      Pi arg resTy -> pure (un (un arg), typeOf arg, resTy)
      _ -> expectedInferredTypeForm' "function" e1Ty

  -- G |- t2 : A
  e2Term <- checkExpr e2 tA

  -- G |- t1 t2 : [t2/x]B
  t2forXinB <- substituteAndNormalise (x, e2Term) tB

  term <- case e1Term of
            (I.App f xs) -> pure $ I.App f (xs ++ [e2Term])
            (I.Lam arg body) -> substituteAndNormalise (un (un arg), e2Term) body
            (TypeTerm t) ->
              case un t of
                (TyApp f xs) -> pure . TypeTerm $ mkType (TyApp f (xs ++ [e2Term])) (level t)
                _ -> notImplemented "inferExpr_: hit a supposedly impossible clause"
            _ -> notImplemented "inferExpr_: hit a supposedly impossible clause"
  pure (term, t2forXinB)
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
      _ -> I.App (I.Var n) <$> normalise xs
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
              (TyApp (TyVar v) xs, []) -> do
                xs' <- normalise xs
                pure $ mkType (TyApp (TyVar v) xs') (level t)
              (Pi arg resTy, []) -> pure $ mkType (Pi arg resTy) (level t)
              (Pi arg resTy, x:xs) -> do
                resTy' <- substitute (un (un arg), x) resTy
                substArgs resTy' xs
              _ -> error $ "substArgs: bad call: '" <> pprintShow t <> "' with arguments '" <> show (fmap pprintParened xs) <> "'"
  normalise (I.Lam arg body) = do
    let x = un (un arg)
    g <- normalise (I.grading arg)
    argTy <- normalise (typeOf arg)
    body' <- withTypedVariable' x argTy $ normalise body
    pure $ I.Lam (x `typedWith` argTy `gradedWith` g) body'


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
              (Pi arg resTy, []) -> pure $ mkType (Pi arg resTy) (level t)
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
  normalise (Pi arg t) = do
    let x = un (un arg)
    g <- normalise (I.grading arg)
    argTy <- normalise (typeOf arg)
    t' <- withTypedVariable' x argTy $ normalise t
    pure $ Pi (x `typedWith` argTy `gradedWith` g) t'


instance Normalise CM I.Grading where
  -- grades are simple nats at the moment, so no normalisation (2020-03-15, GD)
  normalise g = pure g


instance Normalise CM Type where
  normalise t = mkType <$> normalise (un t) <*> normalise (level t)


substituteAndNormalise :: (Monad m, Normalise m t, Substitutable m s t) => s -> t -> m t
substituteAndNormalise s t = substitute s t >>= normalise
