{-# LANGUAGE ViewPatterns #-}

module Language.Dlam.Types
  ( doASTInference
  ) where

--import Control.Monad.IO.Class (liftIO)
import Control.Monad.Extra (ifM)
import Control.Monad (unless, zipWithM)
import Data.Either (partitionEithers)
import Data.List (sort)
import qualified Data.Set as Set

import Language.Dlam.Substitution (Substitutable(substitute))
import Language.Dlam.Syntax.Abstract
import Language.Dlam.Syntax.Common
import qualified Language.Dlam.Syntax.Concrete as C
import Language.Dlam.Syntax.Free (freeVars)
import Language.Dlam.Syntax.Internal
import Language.Dlam.TypeChecking.Monad
import Language.Dlam.Util.Pretty hiding ((<>), isEmpty)
import qualified Language.Dlam.Scoping.Monad as SE

import Language.Dlam.TypeChecking.Predicates
import Language.Dlam.TypeChecking.Constraints (SolverResult(..))

-------------------------
----- Normalisation -----
-------------------------


-- | Execute the action with the binder from the abstraction active
-- | (for checking the body of the abstraction in a subject context).
withAbsBinding :: Abstraction -> CM a -> CM a
withAbsBinding ab act =
  let x = absVar ab
  -- TODO: do we need to account for the grading of the abstraction
  -- here? if so, how (2020-06-13)
  -- in withGradedVariable x (grading ab) $ withTypedVariable x (absTy ab) act
  in withTypedVariable x (absTy ab) act


-- | Normalise an abstraction via a series of reductions.
normaliseAbs :: Abstraction -> CM Abstraction
normaliseAbs ab = do
  t <- normalise (absTy ab)
  g <- mkGrading <$> normaliseGrade (subjectGrade ab) <*> normaliseGrade (subjectTypeGrade ab)
  e <- withAbsBinding ab (normalise (absExpr ab))
  pure (mkAbs' (isHidden ab) (absVar ab) g t e)


-- | Indicate that the expresion is now in an irreducible normal form.
finalNormalForm :: Expr -> CM Expr
finalNormalForm = pure


-- | Normalise the expression via a series of reductions.
normalise :: Expr -> CM Expr
normalise e@Implicit{} = finalNormalForm e
normalise UnitTy = finalNormalForm UnitTy
normalise Unit = finalNormalForm Unit
normalise NatTy = finalNormalForm NatTy
normalise NZero = finalNormalForm NZero
normalise (Def x) = do
  val <- lookupValue x
  case val of
    Nothing -> finalNormalForm $ Def x
    Just e -> normalise e
-- odd... surely variables could never actually have a value? I'm
-- guessing this is something to do with the 'withExprNormalisingTo'
-- infrastructure? (GD: 2020-06-12)
normalise (Var x) = do
  val <- lookupValue x
  case val of
    Nothing -> finalNormalForm $ Var x
    Just e -> normalise e
normalise (FunTy ab) = finalNormalForm =<< FunTy <$> normaliseAbs ab
normalise (Lam ab) = finalNormalForm =<< Lam <$> normaliseAbs ab
normalise (ProductTy ab) = finalNormalForm =<< ProductTy <$> normaliseAbs ab
normalise (BoxTy (g1, g2) e) = do
  g1 <- normaliseGrade g1
  g2 <- normaliseGrade g2
  e <- normalise e
  finalNormalForm $ BoxTy (g1, g2) e
normalise (Box e) = finalNormalForm =<< Box <$> normalise e
normalise (App e1 e2) = do
  e1' <- normalise e1
  e2' <- normalise e2
  case e1' of
    ------------------------
    -- Lambda abstraction --
    ------------------------

    -- (\x -> e) e' ----> [e'/x] e
    (Lam ab) -> substitute (absVar ab, e2') (absExpr ab) >>= normalise

    ------------------------
    -- Other applications --
    ------------------------

    _ -> finalNormalForm $ App e1' e2'
normalise (Pair e1 e2) = finalNormalForm =<< Pair <$> normalise e1 <*> normalise e2

normalise (Case e Nothing binds) = do
  e <- normalise e
  binds <- mapM (normaliseCaseBind e) binds
  case partitionEithers binds of
    ((match:_), _) -> finalNormalForm match
    (_, nomatches) -> finalNormalForm $ Case e Nothing nomatches
normalise (Sig e t) = Sig <$> normalise e <*> normalise t
-- TODO: Improve normalisation for levels/universes (metas?) (2020-06-13)
normalise (Universe l) = finalNormalForm $ Universe l
normalise e = notImplemented $ "normalise does not yet support '" <> pprint e <> "'"


normaliseCaseBind :: Expr -> CaseBinding -> CM (Either Expr CaseBinding)
normaliseCaseBind e (CasePatBound p m) = do
  case maybeGetPatternSubst p e of
    Nothing -> normalise m >>= pure . Right . CasePatBound p
    -- TODO: perform the subject-type substitution only in the type (2020-03-04)
    -- a.k.a . the pattern matched
    Just (ssubst, tsubst) -> fmap Left $ normalise =<< substitute tsubst =<< substitute ssubst m


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
    -- Implicits always match.
    --
    -- TODO: here we want to tell the solver to make the expressions
    -- equal, like we do with gradeEq (2020-06-26)
    (Implicit{}, _) -> pure True
    (_, Implicit{}) -> pure True
    (Universe l1, Universe l2) -> levelsAreEqual l1 l2
    (UnitTy, UnitTy) -> pure True
    (Unit, Unit) -> pure True
    (NatTy, NatTy) -> pure True
    (NZero, NZero) -> pure True
    (NSucc, NSucc) -> pure True
    (Pair e1 e2, Pair e1' e2') -> (&&) <$> equalExprs e1 e1' <*> equalExprs e2 e2'
    (BoxTy (g1, g2) e, BoxTy (g1', g2') e') -> do
      g1sOK <- gradeEq g1 g1'
      g2sOK <- gradeEq g2 g2'
      esOK <- equalExprs e e'
      pure $ g1sOK && g2sOK && esOK

    (Case e1 Nothing binds1, Case e2 Nothing binds2) -> do
      esOK <- equalExprs e1 e2
      -- TODO: need to make sure that this equality is stable, i.e.,
      -- that the cases are in the correct order (2020-06-24)
      let sizesOK = length binds1 == length binds2
      -- TODO: check whether this is optimised by the size (do we
      -- check if the binds are equal if sizes aren't?) (2020-06-24)
      bindsOK <- fmap (sizesOK &&) $ fmap and $ zipWithM equalBinds binds1 binds2
      pure $ esOK && bindsOK

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
          g1sOK <- gradeEq (subjectGrade ab1) (subjectGrade ab2)
          g2sOK <- gradeEq (subjectTypeGrade ab1) (subjectTypeGrade ab2)
          e2s <- substitute (absVar ab2, Var (absVar ab1)) (absExpr ab2)
          fmap ((g1sOK &&) . (g2sOK &&)) $
            (&&) <$> equalExprs (absTy ab1) (absTy ab2)
                 <*> withAbsBinding ab1 (equalExprs (absExpr ab1) e2s)


equalBinds :: CaseBinding -> CaseBinding -> CM Bool
equalBinds (CasePatBound p1 e1) (CasePatBound p2 e2) = do
    case maybeGetPatternUnificationSubst p1 p2 of
      Nothing -> pure False
      Just subst -> do
        -- check that e1 and e2 are equal under the pattern substitution
        (`equalExprs` e1) =<< substitute subst e2


-- | 'ensureEqualTypes tyExpected tyActual' checks that 'tyExpected' and 'tyActual'
-- | represent the same type (under normalisation), and fails if they differ.
ensureEqualTypes :: Type -> Type -> CM Type
ensureEqualTypes tyExpected tyActual = do
  typesEqual <- equalExprs tyActual tyExpected
  if typesEqual then pure tyActual
  else do
    debug $ "Checking that expected type" <+> quoted tyExpected <+> "is equal to actual type" <+> quoted tyActual
    tyMismatchAt "ensure" tyExpected tyActual


-- | Try and register the name with the given type
registerTypeForName :: Name -> Type -> CM ()
registerTypeForName n t = do
  setType n t


-- | Attempt to infer the types of a definition, and check this against the declared
-- | type, if any.
doDeclarationInference :: Declaration -> CM Declaration
doDeclarationInference (TypeSig n t) =
  withCheckingOfTopLevel n $ do
  -- this just assumes the type is okay, as we need the definition
  -- available to resolve e.g., type-level usage from boxes. Hopefully
  -- equation inference checks that the type is actually okay.
  registerTypeForName n =<< normalise t
  pure (TypeSig n t)

doDeclarationInference (FunEqn (FLHSName v) (FRHSAssign e)) =
  withCheckingOfTopLevel v $ do
  -- try and get a prescribed type for the equation,
  -- treating it as an implicit if no type is given
  t <- debugBlock "FUN EQN INFERENCE" ("finding signature for " <> pprint v) (\t -> maybe "no sig found" (("found sig: "<>) . pprint) t)
       (lookupType v)
  -- TODO: refactor this to just call checkOrInferTypeNew (2020-06-28)
  exprTy <- case t of
              Nothing -> inferExpr e emptyInContext >>= normalise . snd
              Just ty -> checkOrInferTypeNew ty e

  -- assign the appopriate equation and normalised/inferred type for the name
  setValue v e
  registerTypeForName v exprTy
  -- reset stack, so that predicates from previous equations don't
  -- bleed into the wrong scope
  resetPredicateStack
  pure (FunEqn (FLHSName v) (FRHSAssign e))


-- | Attempt to infer the types of each definition in the AST, failing if a type
-- | mismatch is found.
doASTInference :: AST -> CM AST
doASTInference (AST ds) = do
  debug $ "LENGTH" <+> (pprint $ length ds)
  fmap AST $ mapM doDeclarationInference ds


----------------------------------------------------------------------------
-- Dominic work here on a bidirectional additive-grading algorithm


-- | Require that the first grade is approximated by the second.
gradeLEq :: Grade -> Grade -> CM Bool
gradeLEq r1 r2 = do
  ifM shouldUseSMT
    -- SMT based equality
    (do
      r1 <- normaliseGrade r1 >>= existentiallyQuantifyGradeImplicits
      r2 <- normaliseGrade r2 >>= existentiallyQuantifyGradeImplicits
      ty <- requireSameTypedGrades r1 r2
      case (grade r1, grade r2) of
        --(GEnc i, GEnc j) | i == j -> pure True
        (r1, r2) -> do
          -- Go to the SMT solver
          -- NOTE THIS IS JUST EQUALITY FOR NOW
          let c = Eq r1 r2 ty
          debug $ "Adding smt constraint:" <+> pprint c
          addConstraint c
          -- Say yes for now
          return True)

      -- NOTE THIS IS ONLY EQUALITY AT THE MOMENT!
      (do
          r1' <- normaliseGrade r1
          r2' <- normaliseGrade r2
          _ty <- requireSameTypedGrades r1 r2
          return $ grade r1' == grade r2')

-- Asks whether two grades are equal, but does not
-- remember this constraint in the global predicate
-- since it could be false (which is fine)
questioningGradeEq :: Grade -> Grade -> CM Bool
questioningGradeEq g1 g2 =
  -- If we can do a syntactic equality then great
  if g1 == g2 then
    return True
  -- Otherwise we got the SMT solver now
  else do
    -- Do this as a local check, i.e., if this
    -- returns false then rollback the state
    localCheck $ gradeEqBase True g1 g2

-- NOTE: this expects that 'normaliseGrade' is rendering e.g.,
-- additions in a canonical form.
gradeEq :: Grade -> Grade -> CM Bool
gradeEq = gradeEqBase False

-- The boolean parameter triggers whether we force ask
-- the smt solver to prove equality now
gradeEqBase :: Bool -> Grade -> Grade -> CM Bool
gradeEqBase forceSMT r1 r2 = do
  ifM shouldUseSMT
  -- SMT based equality
    (do
      r1' <- normaliseGrade r1 >>= existentiallyQuantifyGradeImplicits
      r2' <- normaliseGrade r2 >>= existentiallyQuantifyGradeImplicits
      ty <- requireSameTypedGrades r1 r2
      case (grade r1', grade r2') of
        --(GEnc i, GEnc j) | i == j -> pure True
        (_, _) -> do
          -- Go to the SMT solver
          debug $ "Adding smt equality: " <> (pprint r1') <> " = " <> (pprint r2')
          addConstraint (Eq (grade r1') (grade r2') ty)
          if forceSMT
            then isTheoremValidBool
            else
              -- Say true, but we don't know yet...!
              return True)
    (do
      r1' <- normaliseGrade r1
      r2' <- normaliseGrade r2
      _ty <- requireSameTypedGrades r1 r2
      return $ grade r1' == grade r2')

contextGradeAdd :: Ctxt Grade -> Ctxt Grade -> CM (Ctxt Grade)
contextGradeAdd = cZipWithM gradeAdd

contextGradeMult :: Grade -> Ctxt Grade -> CM (Ctxt Grade)
contextGradeMult = cMapM . gradeMult

-- First argument is usually the expected, and second is the actual
contextGradeEq :: Ctxt Grade -> Ctxt Grade -> CM (Either [(Name, (Grade, Grade))] ())
contextGradeEq c d = do
  eqs <- cZipWithM (\g1 g2 -> gradeEq g1 g2 >>= \t -> pure $ if t then Right () else Left (g1, g2)) c d
  pure $ foldr (\(n, g) x -> either (\gs -> x <> (Left [(n, gs)])) (const x) g) (Right ()) $ contextToList eqs

-- DAO: may want to make this an interface so we can try
--      different implementations. For now its just specialised
newtype Ctxt a = Ctxt { unContext :: [(Name, a)] } -- M.Map Name a
  deriving (Eq, Show)


emptyContext :: Ctxt a
emptyContext = Ctxt []


extend :: Ctxt a -> Name -> a -> Ctxt a
extend (Ctxt ctxt) n t = Ctxt (ctxt ++ [(n, t)])


unextend :: Ctxt a -> (Ctxt a, (Name, a))
unextend (Ctxt []) = error "bad call to unextend with empty context"
unextend (Ctxt xs) = (Ctxt (init xs), last xs)


emptyInContext :: InContext
emptyInContext = InContext emptyContext emptyContext


data InContext =
  InContext {
     types           :: Ctxt Type
   , contextGradesIn :: Ctxt (Ctxt Grade)
  }
  deriving (Eq, Show)

data OutContext =
  OutContext {
    subjectGradesOut :: Ctxt Grade
  , typeGradesOut    :: Ctxt Grade
}
 deriving (Eq, Show)


-- | Zip over two contexts.
--
-- TODO: ensure that contexts of different sizes are rejected (2020-06-20)
cZipWithM :: (a -> b -> CM c) -> Ctxt a -> Ctxt b -> CM (Ctxt c)
cZipWithM f (Ctxt c) (Ctxt d) =
  Ctxt <$> zipWithM (\(n1, v1) (n2, v2) ->
    if n1 == n2 then f v1 v2 >>= \v -> pure (n1, v)
    else internalBug "context grade addition on contexts of different shapes")
    c d


-- | Map a function over a context.
cMap :: (a -> b) -> Ctxt a -> Ctxt b
cMap f (Ctxt c) = Ctxt $ map (\(n, v) -> (n, f v)) c


-- | Map a function over a context.
cMapM :: (a -> CM b) -> Ctxt a -> CM (Ctxt b)
cMapM f (Ctxt c) = Ctxt <$> mapM (\(n, v) -> f v >>= \r -> pure (n, r)) c


cAnyWithKey :: ((Name, v) -> Bool) -> Ctxt v -> Bool
cAnyWithKey f = any f . contextToList


contextToList :: Ctxt a -> [(Name, a)]
contextToList = unContext


-- TODO: ensure this doesn't allow repeated names (2020-06-20)
cappend :: Ctxt a -> Ctxt a -> Ctxt a
cappend (Ctxt c) (Ctxt d) = Ctxt (c <> d)


instance (Pretty a) => Pretty (Ctxt a) where
  pprint = pprintList . fmap pprintPair . unContext


instance Pretty InContext where
  -- TODO: print types too (2020-06-20)
  pprint (InContext { types = _tys, contextGradesIn = (Ctxt gs) }) =
    pprintList (fmap (\(id, x) -> pprintPair (pprint id, pprint x)) gs)


-- | A zeroed OutContext that matches the shape of the InContext, for
-- | when typing constants.
zeroedOutContextForInContext :: InContext -> OutContext
zeroedOutContextForInContext inCtx =
  OutContext { subjectGradesOut = zeroesMatchingShape (types inCtx)
             , typeGradesOut = zeroesMatchingShape (types inCtx) }


freshGradeVecMatchingShape :: Ctxt Grade -> CM (Ctxt Grade)
freshGradeVecMatchingShape = cMapM (newExistentialGrade . gradeTy)


lookupAndCutoutIn :: Name -> InContext -> Maybe (InContext, (Type, Ctxt Grade), InContext)
lookupAndCutoutIn n context = do
  (typesL, t, typesR)         <- lookupAndCutout1 n (types context)
  (cGradesL, delta, cGradesR) <- lookupAndCutout1 n (contextGradesIn context)
  return $ (InContext typesL cGradesL, (t, delta), InContext typesR cGradesR)

lookupAndCutout1 :: Name -> Ctxt a -> Maybe (Ctxt a, a, Ctxt a)
lookupAndCutout1 _ (Ctxt []) = Nothing
lookupAndCutout1 v (Ctxt ((v', x) : ctxt))
  | v == v' = Just (emptyContext, x, Ctxt ctxt)
  | otherwise = do
    (Ctxt ctxtL, y, ctxtR) <- lookupAndCutout1 v (Ctxt ctxt)
    Just (Ctxt ((v', x) : ctxtL), y, ctxtR)

-- Monoid of disjoint contexts
instance Monoid OutContext where
  mempty = OutContext emptyContext emptyContext

isEmpty :: OutContext -> Bool
isEmpty ctxt = ctxt == mempty

instance Semigroup OutContext where
  c1 <> c2 =
      OutContext (subjectGradesOut c1 `disjUnion` subjectGradesOut c2)
                 (typeGradesOut c1 `disjUnion` typeGradesOut c2)
   where
     disjUnion c@(Ctxt m1) d@(Ctxt m2) | disjoint c d = Ctxt (m1 <> m2)
     disjUnion _  _  | otherwise = error $ "Non disjoint contexts"

     disjoint m1 m2 = not $ cAnyWithKey (\(v, _) -> hasVar v m2) m1

     hasVar v m = cAnyWithKey (\(v', _) -> v' == v) m


zeroesMatchingShape :: Ctxt a -> Ctxt Grade
zeroesMatchingShape = cMap (const gradeZero)

-- Top level
checkOrInferTypeNew :: Type -> Expr -> CM Type
checkOrInferTypeNew ty expr = do
  newConjunct
  (outContext, t) <- checkExpr expr (Just ty) emptyInContext
  -- TODO: ensure that any existentially-bound implicits that don't
  -- have an exact value after resolution cause the program to fail
  -- (2020-06-27)
  if isEmpty outContext
    then do
      -- Time to check that any theorems hold
      proverResult <- isTheoremValid
      case proverResult of
        QED                  -> pure t
        NotValid msg         -> solverNotValid msg
        Timeout              -> solverTimeout
        OtherSolverError msg -> solverError msg
        SolverProofError msg -> solverError msg

    else internalBug "Binders are left!"


-- TODO: ensure incoming types are normalised (2020-06-28)
checkExpr :: Expr -> Maybe Type -> InContext -> CM (OutContext, Type)
checkExpr e t c = withLocalCheckingOf e t $
  debugBlock "checkExpr"
    (maybe ("inferring a type for expression" <+> quoted e) (\t -> "checking expression" <+> quoted e <+> "against type" <+> quoted t) t)
    (\(_, ty) -> maybe ("inferred a type" <+> quoted ty <+> "for expression" <+> quoted e)
                       (\_ -> "checked OK for" <+> quoted e) t) (checkExpr' e t c)


checkExpr' :: Expr -> Maybe Type -> InContext -> CM (OutContext, Type)


---------------------
----- Variables -----
---------------------


{-
  (M1 | g | gZ) @ G1 |- A : Type l
  ----------------------------------------------------------- :: Var
  ((M1, g, M2) | gZ,1,gZ | g,0,gZ) @ (G1, x : A, G2) |- x : A
-}
checkExpr' (Var x) Nothing ctxt = do
  debug $ "Infer for var" <+> pprint x <+> "in context" <+> pprint ctxt
  --
  case lookupAndCutoutIn x ctxt of
    -- this should be prevented by the scope checker (encountering a
    -- free variable that isn't in scope)
    Nothing -> scoperError $ SE.unknownNameErr (C.Unqualified $ nameConcrete x)
    Just (ctxtL, (ty, g'), ctxtR) -> do

      -- Check that this type is indeed a Type
      debug $ "Infer for var (type)" <+> pprint ctxtL
      (g, _) <- checkExprIsType ty ctxtL

      debug $ "Context grade eq var" <+> pprint x <+> "with" <+> pprint g' <+> "and" <+> pprint g
      --  Check context grades for `x` match what was calculated in typing
      eq <- contextGradeEq g' g

      case eq of
        Left mismatches ->
          gradeMismatchAt "var" Context mismatches
        Right () -> do
          return $ (OutContext
                    { subjectGradesOut = extend (zeroesMatchingShape (types ctxtL)) x gradeOne
                                        `cappend` (zeroesMatchingShape (types ctxtR))

                    , typeGradesOut    = extend g x gradeZero
                                        `cappend` (zeroesMatchingShape (types ctxtR)) }, ty)


----------------------------
----- Typing Universes -----
----------------------------


{-
  ------------------------- :: Type
  0G |- Type l : Type (l+1)
-}
checkExpr' (Universe l) Nothing ctxt =
  pure (zeroedOutContextForInContext ctxt, mkUnivTy (levelSucc l))


------------------------------------------------------------
----- Definitions (names standing for constant values) -----
------------------------------------------------------------


{-
  f : A in scope (aka . |- f : A)
  ------------------------------- :: Def
  0G |- f : A
-}
checkExpr' (Def n) Nothing ctxt = do
  tA <- lookupType n >>= maybe (scoperError $ SE.unknownNameErr (C.Unqualified $ nameConcrete n)) pure
  pure (zeroedOutContextForInContext ctxt, tA)


---------------------
----- Functions -----
---------------------


{-
  (M | g1 | gZ) @ G |- A : Type l1
  (M,g1 | g2,r1 | gZ) @ G, x : A |- B : Type l2

  r1 <= r2
  ----------------------------------------------------------------- :: Pi
  (M | g1 + g2 | gZ) @ G |- (x : (s, r2) A) -> B : Type (lmax l1 l2)
-}
checkExpr' (FunTy pi) Nothing ctxt = do
  let x = absVar pi
      tA = absTy pi
      tB = absExpr pi
      r2 = subjectTypeGrade pi

  -- Infer type of parameter A
  debug $ "Infer for pi type (infer for param type)"
  (g1, l1) <- checkExprIsType tA ctxt

  -- Infer type of function type body B
  debug $ "Infer for pi type (infer for body type)"
  (g2r, l2) <- checkExprIsType tB (extendInputContext ctxt x tA g1)

  let (g2, (_, r1)) = unextend g2r

  -- (ii) Check binder grade specification matches usage `r`
  eq <- gradeLEq r1 r2
  unless eq (gradeMismatchAt' "function type" SubjectType (absVar pi) r1 r2)

  lmaxl1l2 <- levelMax l1 l2
  g1plusG2 <- contextGradeAdd g1 g2
  pure ( OutContext { subjectGradesOut = g1plusG2
                    , typeGradesOut = zeroesMatchingShape (types ctxt) }
       , mkUnivTy lmaxl1l2)


{-
  (M | g1 | gZ) @ G |- A : Type l
  (M,g1 | g2,s2 | g3,r2) @ G, x : A |- t : B

  s1 <= s2
  r1 <= r2
  --------------------------------------------------------- :: Fun
  (M | g2 | g1 + g3) @ G |- \x -> t : (x : (s1, r1) A) -> B
-}
checkExpr' (Lam lam) t ctxt = do
  let tALam = absTy lam
      xLam = absVar lam
      (sLam, rLam) = (subjectGrade lam, subjectTypeGrade lam)

  -- (M | g1 | gZ) @ G |- A : Type l
  (lamBody, x, tA, tB, s1, r1) <-
    case t of
      -- no type specified, take as much information from the
      -- abstraction as possible
      Nothing -> pure (absExpr lam, xLam, tALam, Nothing, sLam, rLam)
      -- function type specified, so we check that components are
      -- equal, and use the result type from the Pi
      Just (FunTy pi) -> do
        let (sPi, rPi) = (subjectGrade pi, subjectTypeGrade pi)
            tAPi = absTy pi
            x = absVar pi

        -- ensure components of the lambda and Pi match up (argument type, grades)
        tA <- ensureEqualTypes tALam tAPi
        sBinder <- verifyGradesEqButUseOtherIfImplicit "pi binder" Subject x sLam sPi
        rBinder <- verifyGradesEqButUseOtherIfImplicit "pi binder" SubjectType x rLam rPi

        -- substitute the Pi var for the Lam var in the Lam body,
        -- to make sure that variable lookups try and find the
        -- right variable
        lamBody <- substitute (xLam, Var x) (absExpr lam)

        pure (lamBody, x, tA, Just $ absExpr pi, sBinder, rBinder)
      Just t -> expectedInferredTypeForm "function" t

  -- (M | g1 | gZ) @ G |- A : Type l
  (g1, _) <- checkExprIsType tA ctxt

  -- (M,g1 | g2,s | g3,r) @ G, x : A |- t : B
  (OutContext { subjectGradesOut = g2s, typeGradesOut = g3r }, tB) <-
    checkExpr lamBody tB (extendInputContext ctxt x tA g1)

  -- Check calculated grades against binder
  let (g2, (_, s2)) = unextend g2s
      (g3, (_, r2)) = unextend g3r
  -- s1 <= s2
  -- r1 <= r2
  eqS <- gradeLEq s1 s2
  unless eqS (gradeMismatchAt' "function" Subject (absVar lam) s1 s2)

  eqR <- gradeLEq r1 r2
  unless eqR (gradeMismatchAt' "function" SubjectType (absVar lam) r1 r2)

  g1plusG3 <- contextGradeAdd g1 g3

  -- (M | g2 | g1 + g3) @ G |- \x -> t : (x : [s, r] A) -o B
  pure ( OutContext { subjectGradesOut = g2, typeGradesOut = g1plusG3 }
       , FunTy (mkAbsGr x tA s1 r1 tB) )


{-
  (M,g1 | g3,r | gZ) @ G, x : A |- B : Type l
  (M | g2 | g1 + g3) @ G |- t1 : (x : (s, r) A) -o B
  (M | g4 | g1) @ G |- t2 : A
  ------------------------------------------------------ :: App
  (M | g2 + s * g4 | g3 + r * g4) @ G |- t1 t2 : [t2/x]B
-}
-- TODO: update this to allow a specified type (2020-06-28)
checkExpr' (App t1 t2) Nothing ctxt = do
  -- Infer left of application
  debug $ "App infer for t1 = " <> pprint t1

  -- (M | g2 | g1 + g3) @ G |- t1 : (x : (s, r) A) -o B
  (outCtxtFun@(OutContext g2 g1plusG3), funTy) <- inferExpr t1 ctxt
  funTy <- normalise funTy

  -- Need to infer types for `funTy` to see how the context
  -- is used to form `A` and `B`
  case funTy of
    -- (x :(s, r) A -o B)
    (FunTy pi) -> do
      let s   = subjectGrade pi
          r   = subjectTypeGrade pi
          tA = absTy pi
          tB = absExpr pi

      -- (M | g4 | g1) @ G |- t2 : A
      (OutContext g4 g1, tA) <- checkExpr t2 (Just tA) ctxt
      debug $ "ok A : " <> pprint tA

      -- (M,g1 | g3,r | gZ) @ G, x : A |- B : Type l
      debug $ "App infer for tyB = " <> pprint tB
      (g3r, _) <- checkExprIsType tB (extendInputContext ctxt (absVar pi) tA g1)
      let (g3, (_, rInferred)) = unextend g3r

      eq <- gradeEq rInferred r
      unless eq (gradeMismatchAt' "function type" SubjectType (absVar pi) r rInferred)

      debug "Context grade eq app 1"
      debug $ "sigma1 =" <+> pprint g1
      debug $ "sigma3 =" <+> pprint g3
      debug $ "type grades out cxtFun" <+> pprint (typeGradesOut outCtxtFun)

      g1plusG3Calculated <- contextGradeAdd g1 g3
      eq' <- contextGradeEq g1plusG3 g1plusG3Calculated

      case eq' of
        Right() -> do
          -- (M | g2 + s * g4 | g3 + r * g4) @ G |- t1 t2 : [t2/x]B
          sTimesG4 <- contextGradeMult s g4
          g2PlusSTimesG4 <- contextGradeAdd g2 sTimesG4
          rTimesG4 <- contextGradeMult r g4
          g3PlusRTimesG4 <- contextGradeAdd g3 rTimesG4

          t2forXinB <-
            ifM isOptimising
            {- then -} (do
              -- optimise here when 0 use
              noTypeUse <- questioningGradeEq r gradeZero
              if noTypeUse
                then do
                  debug $ "Optimised: no subst of " <> pprint t2 <> " for " <> pprint (absVar pi) <> " in " <> pprint tB
                  return tB
                else substitute (absVar pi, t2) tB)
              {- else -} (substitute (absVar pi, t2) tB)


          pure ( OutContext { subjectGradesOut = g2PlusSTimesG4
                            , typeGradesOut = g3PlusRTimesG4 }
               , t2forXinB)
        Left mismatches ->
          gradeMismatchAt "application function" Context mismatches
    _ -> expectedInferredTypeForm "function (type of app left)" funTy


-------------------
----- Tensors -----
-------------------


{-
  (M | g1 | gZ) @ G |- A : Type l1
  (M,g1 | g2,r | gZ) @ G, x : A |- B : Type l2
  ---------------------------------------------------------- :: Ten
  (M | g1 + g2 | gZ) @ G |- (x : r A) * B : Type (lmax l1 l2)
-}
checkExpr' (ProductTy ten) Nothing ctxt = do
  let x = absVar ten
      tA = absTy ten
      tB = absExpr ten
      r  = subjectTypeGrade ten

  -- (M | g1 | gZ) @ G |- A : Type l1
  (g1, l1) <- checkExprIsType tA ctxt

  -- (M,g1 | g2,r | gZ) @ G, x : A |- B : Type l2
  (g2r, l2) <- checkExprIsType tB (extendInputContext ctxt x tA g1)

  let (g2, (_, rInferred)) = unextend g2r

  -- (ii) Check binder grade specification matches usage `r`
  _ <- verifyGradesEq "ten type binder" Subject x r rInferred

  lmaxl1l2 <- levelMax l1 l2
  g1plusG2 <- contextGradeAdd g1 g2

  pure ( OutContext { subjectGradesOut = g1plusG2
                    , typeGradesOut = zeroesMatchingShape (types ctxt) }
       , mkUnivTy lmaxl1l2)


{-
  (M,g1 | g3,r | gZ) @ G, x : A |- B : Type l
  (M | g2 | g1) @ G |- t1 : A
  (M | g4 | g3 + r * g2) @ G |- t2 : [t1/x]B
  ----------------------------------------------------------- :: Pair
  (M | g2 + g4 | g1 + g3) @ G |- (t1, t2) : (x : (0,r) A) * B
-}
checkExpr' (Pair t1 t2) (Just ty) ctxt = do
  case ty of
    (ProductTy prod) -> do
      let x  = absVar prod
          tA = absTy prod
          tB = absExpr prod
          r  = subjectTypeGrade prod

      -- (M | g2 | g1) @ G |- t1 : A
      (OutContext { subjectGradesOut = g2, typeGradesOut = g1 }, tA')
        <- inferExpr t1 ctxt

      tA <- ensureEqualTypes tA tA'

      -- (M | g4 | g3 + r * g2) @ G |- t2 : [t1/x]B
      (OutContext { subjectGradesOut = g4, typeGradesOut = g3plusRtimesG2 }, t1forXinB)
        <- inferExpr t2 ctxt

      t1forXinB' <- substitute (x, t1) tB
      _ <- ensureEqualTypes t1forXinB t1forXinB'

      -- (M,g1 | g3,r | gZ) @ G, x : A |- B : Type l

      (g3r, _) <- checkExprIsType tB (extendInputContext ctxt x tA g1)

      let (g3, (_, r')) = unextend g3r

      rtimesG2 <- contextGradeMult r g2
      g3plusRtimesG2Calc <- contextGradeAdd g3 rtimesG2

      _ <- verifyGradeVecEq "?" g3plusRtimesG2 g3plusRtimesG2Calc
      r <- verifyGradesEq "pair type" Subject x r r'

      g2plusG4 <- contextGradeAdd g2 g4
      g1plusG3 <- contextGradeAdd g1 g3

      -- (M | g2 + g4 | g1 + g3) @ G |- (t1, t2) : (x : (0,r) A) * B
      pure (OutContext { subjectGradesOut = g2plusG4, typeGradesOut = g1plusG3 },
           ProductTy (mkAbsGr x tA gradeZero r tB))
    _ -> expectedInferredTypeForm "product" ty


{-
  (M | g1 | gZ) @ G |- A : Type l1
  (M | g2,r | gZ) @ G, x : A |- B : Type l2
  (M | g3 | g1 + g2) @ G |- t1 : (x : (0,r) A) * B
  (M,(g1 + g2) | g5,q | gZ) @ G, z : (x : (0,r) A) * B |- C : Type l3
  (M,g1,(g2,r) | g4,s,s | g5,q,q) @ G, x : A, y : B |- t2 : [(x,y)/z]C
  ---------------------------------------------------------------------------------- :: TenCut
  (M | g4 + s * g3 | g5 + q * g3) @ G |- case t1 as z in C of (x, y) -> t2 : [t1/z]C
-}
checkExpr' (Case t1 tp [CasePatBound (PPair (PVar x') (PVar y')) t2]) t1ForZinC ctxt = do
  let (x, y) = (unBindName x', unBindName y')
  -- (M | g3 | g1 + g2) @ G |- t1 : (x : (0,r) A) * B
  (OutContext { subjectGradesOut = g3, typeGradesOut = g1plusG2 }, pairTy)
    <- inferExpr t1 ctxt
  case pairTy of
    ProductTy ten -> do
      let x' = absVar ten
          tA = absTy ten
          r  = subjectTypeGrade ten
          tB = absExpr ten

      -- (M | g1 | gZ) @ G |- A : Type l1
      (g1, _) <- checkExprIsType tA ctxt

      -- (M | g2,r | gZ) @ G, x : A |- B : Type l2
      tB <- substitute [(x', Var x)] tB
      (g2r, _) <- checkExprIsType tB (extendInputContext ctxt x tA g1)

      let (g2Comp, (_, rComp)) = unextend g2r

      _ <- verifyGradesEq "typing of second component of pair" Subject x r rComp

      g1plusG2Comp <- contextGradeAdd g1 g2Comp
      g1plusG2 <- verifyGradeVecEq "todo" g1plusG2 g1plusG2Comp

      -- (M,g1,(g2,r) | g4,s,s | g5,q,q) @ G, x : A, y : B |- t2 : [(x,y)/z]C
      (OutContext { subjectGradesOut = g4ss, typeGradesOut = g5qq }, xyForZinC)
        <- case tp of
             -- in the non-dependent case, we need [(x,y)/z]C = [t1/z]C = C
             Nothing -> checkExpr t2 t1ForZinC (extendInputContext (extendInputContext ctxt x tA g1) y tB g2r)
             Just (PVar z, tC) -> do
               xyForZinC <- substitute (unBindName z, Pair (Var x) (Var y)) tC
               (out, xyForZinC) <- checkExpr t2 (Just xyForZinC) (extendInputContext (extendInputContext ctxt x tA g1) y tB g2r)
               pure (out, xyForZinC)
             Just (p, _) -> patternMismatch p t1

      (g5, q, z, tC) <-
        case tp of
          -- non-dependent elimination
          --
          -- but as the rules don't actually have a non-dependent
          -- elimination, we pretend there is a fresh variable "z" in
          -- C that is used with grade 0. Then we obtain the actual
          -- value of C from the typing of t2 ([(x,y)/z]C = C).
          Nothing -> do
            z <- getFreshName "z"
            let tC = xyForZinC
            -- (M,(g1 + g2) | g5,q | gZ) @ G, z : (x : (0,r) A) * B |- C : Type l3
            (g5q, _) <- checkExprIsType tC (extendInputContext ctxt z pairTy g1plusG2)
            -- in this case we require that q is zero
            let (g5, (_, q)) = unextend g5q
            q <- verifyGradesEq "formation of product elim type (C)" Subject x q gradeZero
            pure (g5, q, z, tC)
          Just (PVar z', tC) -> do
            let z = unBindName z'
            -- (M,(g1 + g2) | g5,q | gZ) @ G, z : (x : (0,r) A) * B |- C : Type l3
            (g5q, _) <- checkExprIsType tC (extendInputContext ctxt z pairTy g1plusG2)
            let (g5, (_, q)) = unextend g5q
            pure (g5, q, z, tC)
          Just (p, _) -> patternMismatch p t1

      xyForZinCCalc <- substitute (z, Pair (Var x) (Var y)) tC
      _ <- ensureEqualTypes xyForZinC xyForZinCCalc

      let (g4s, (_, sV1)) = unextend g4ss
          (g4, (_, sV2))  = unextend g4s
          (g5qV2, (_, qV2)) = unextend g5qq
          (g5', (_, qV3)) = unextend g5qV2

      -- check that things that should be equal are equal
      s <- verifyGradesEq "usage of components of a pair must be the same" Subject x sV1 sV2
      q <- verifyGradesEq "formation of product elim type (C)" Subject x q qV2
      q <- verifyGradesEq "formation of product elim type (C)" Subject x q qV3
      g5 <- verifyGradeVecEq "pair elim" g5 g5'

      sTimesG3 <- contextGradeMult s g3
      g4plusStimesG3 <- contextGradeAdd g4 sTimesG3
      qTimesG3 <- contextGradeMult q g3
      g5plusQtimesG3 <- contextGradeAdd g5 qTimesG3

      t1ForZinCComp <- substitute [(z, t1)] tC
      t1ForZinC <- maybe (pure t1ForZinCComp) (ensureEqualTypes t1ForZinCComp) t1ForZinC

      -- (M | g4 + s * g3 | g5 + r' * g3) @ G |- let (x, y) = t1 in t2 : [t1/z]C
      pure ( OutContext { subjectGradesOut = g4plusStimesG3, typeGradesOut = g5plusQtimesG3 }
           , t1ForZinC )
    _ -> expectedInferredTypeForm "tensor" pairTy


---------------------------
----- Graded Modality -----
---------------------------


{-
  (M, g, gZ) @ G |- A : Type l
  --------------------------------------- :: Box
  (M, g, gZ) @ G |- Box (s, r) A : Type l
-}
checkExpr' (BoxTy _ t) Nothing ctxt = do
  -- (M, g, gZ) @ G |- A : Type l
  (g, l) <- checkExprIsType t ctxt
  -- (M, g, gZ) @ G |- Box (s, r) A : Type l
  pure (OutContext { subjectGradesOut = g, typeGradesOut = zeroesMatchingShape (types ctxt) }, mkUnivTy l)


{-
  (M | g1 | g2) @ G |- t : A
  ---------------------------------------------------- :: BoxI
  (M | s * g1 | g2 + r * g1) @ G |- [t] : Box (s, r) A
-}
checkExpr' (Box t) (Just ty) ctxt = do
  case ty of
    (BoxTy (s, r) tA) -> do
      -- (M | g1 | g2) @ G |- t : A
      (OutContext { subjectGradesOut = g1, typeGradesOut = g2 }, tA)
        <- checkExpr t (Just tA) ctxt

      sTimesG1 <- contextGradeMult s g1
      rTimesG1 <- contextGradeMult r g1
      g2PlusRTimesG1 <- contextGradeAdd g2 rTimesG1

      -- (M | s * g1 | g2 + r * g1) @ G |- [t] : Box (s, r) A
      pure $ ( OutContext { subjectGradesOut = sTimesG1, typeGradesOut = g2PlusRTimesG1 }
             , BoxTy (s, r) tA )
    _ -> expectedInferredTypeForm "graded modal" ty


{-
  (M | g5 | gZ) @ G |- A : Type l1
  (M | g1 | g2)  @ G |- t1 : Box (s, r) A
  (M,g5 | g4,r1 | gZ) @ G, z : A |- B : Type l2
  (M,g5 | g3,s | g4,(r1 + r2)) @ G, x : A |- t2 : [x/z]B
  exists g6 such that g2 = g6 + g5
  exists r2 such that r = r1 + r2
  -------------------------------------------------------------------------------------- :: BoxE
  (M | g1 + g3 | g6 + g4) @ G |- case t1 split z in C of [x] -> t2 : case t1 of [z] -> B
-}
-- TODO: currently just using 'as' for 'split', separate these! (GD: 2020-06-24)
checkExpr' (Case t1 tp [CasePatBound (PBox (PVar x')) t2]) caseTy ctxt = do
  let x = unBindName x'
  -- (M | g1 | g2) @ G |- t1 : Box (s, r) A
  (OutContext { subjectGradesOut = g1, typeGradesOut = g2 }, boxTy)
    <- inferExpr t1 ctxt
  case boxTy of
    BoxTy (s, r) tA -> do
      -- (M | g5 | gZ) @ G |- A : Type l
      (g5, _) <- checkExprIsType tA ctxt

      -- exists r2 such that r = r1 + r2
      r2 <- newExistentialGrade (gradeTy r)

      (z, g3, g4, r1plusR2, xForZinB) <- do
        let mx = extendInputContext ctxt x tA g5
        -- (M,g5 | g3,s | g4,(r1+r2)) @ G, x : A |- t2 : [x/z]B
        (OutContext { subjectGradesOut = g3s, typeGradesOut = g4R1plusR2 }, xForZinB)
          <- case tp of
               Nothing -> checkExpr t2 caseTy mx
               Just (PVar z', tB) -> do
                 xForZinB <- substitute (unBindName z', Var x) tB
                 (out, _) <- checkExpr t2 (Just tB) mx
                 pure (out, xForZinB)
               Just (p, _) -> patternMismatch p t1
        z <- getFreshName "z"
        let (g3, (_, sComp)) = unextend g3s
            (g4, (_, r1plusR2)) = unextend g4R1plusR2
        _ <- verifyGradesEq "typing of body" Subject x s sComp
        r <- verifyGradesEq "typing of type" SubjectType x r r1plusR2
        pure (z, g3, g4, r, xForZinB)

      (g4', r1, finTy) <-
        case tp of
          -- non-dependent elimination
          --
          -- but as the rules don't actually have a non-dependent
          -- elimination, we pretend there is a fresh variable "z" in
          -- B that is used with grade 0. Then we obtain the actual
          -- value of B from the typing of t2.
          Nothing -> do
            tB <- substitute (x, Var z) xForZinB
            -- (M,g5 | g4,r1 | gZ) @ G, z : A |- B : Type l2
            (g4r1, _) <- checkExprIsType tB (extendInputContext ctxt z tA g5)
            -- in this case we require that r1 is zero
            let (g4, (_, r1)) = unextend g4r1
            r1 <- verifyGradesEq "box case type" Subject x r1 gradeZero
            let finTy = tB
            pure (g4, r1, finTy)
          Just (PVar z', tB) -> do
            let z = unBindName z'
            -- (M,g5 | g4,r1 | gZ) @ G, z : A |- B : Type l2
            (g4r1, _) <- checkExprIsType tB (extendInputContext ctxt z tA g5)
            let (g4, (_, r1)) = unextend g4r1
            -- TODO: this check (for freeVars) should probably be
            -- handled by equality (2020-06-24)
            let finTy = if z `Set.member` freeVars tB then Case t1 Nothing [CasePatBound (PBox (PVar (BindName z))) tB] else tB
            pure (g4, r1, finTy)
          Just (p, _) -> patternMismatch p t1

      r1plusR2Comp <- gradeAdd r1 r2
      _ <- verifyGradesEq "combined type-level use" SubjectType x r1plusR2 r1plusR2Comp

      g4 <- verifyGradeVecEq "?" g4 g4'

      -- exists g6 such that g2 = g6 + g5
      g6 <- freshGradeVecMatchingShape g5
      g5plusG6 <- contextGradeAdd g5 g6
      _ <- verifyGradeVecEq "?" g2 g5plusG6

      g1plusG3 <- contextGradeAdd g1 g3
      g6plusG4 <- contextGradeAdd g6 g4

      finTy <- maybe (pure finTy) (ensureEqualTypes finTy) caseTy

      -- (M | g1 + g3 | g6 + g4) @ G |- let [x] = t1 in t2 : let [x] = t1 in B
      pure ( OutContext { subjectGradesOut = g1plusG3, typeGradesOut = g6plusG4 }
           , finTy)
    _ -> expectedInferredTypeForm "graded modal" boxTy


----------------
----- Unit -----
----------------


{-
  ------------------- :: UnitTy
  0G |- Unit : Type 0
-}
checkExpr' UnitTy Nothing ctxt =
  pure (zeroedOutContextForInContext ctxt, mkUnivTy levelZero)


{-
  ----------------- :: Unit
  0G |- unit : Unit
-}
checkExpr' Unit Nothing ctxt =
  pure (zeroedOutContextForInContext ctxt, UnitTy)


{-
  (M | g1 | gZ) @ G |- t1 : Unit
  (M,gZ | g3,s | gZ) @ G, z : Unit |- C : Type l
  (M | g2 | g3) @ G |- t2 : [*/z]C
  ----------------------------------------------------------------------- :: UnitE
  (M | g1 + g2 | g3 + s * g1) G |- case t1 as z in C of * -> t2 : [t1/z]C
-}
checkExpr' (Case t1 tp [CasePatBound PUnit t2]) t1ForZinC ctxt = do
  -- (M | g1 | gZ) @ G |- t1 : Unit
  (OutContext { subjectGradesOut = g1, typeGradesOut = gZ' }, unitTy)
    <- inferExpr t1 ctxt
  gZ <- verifyGradeVecEq "unit elim" gZ' (zeroesMatchingShape (types ctxt))
  case unitTy of
    UnitTy -> do
      -- (M | g2 | g3) @ G |- t2 : [*/z]C
      (OutContext { subjectGradesOut = g2, typeGradesOut = g3 }, starForZinC)
        <- case tp of
             -- in the non-dependent case, we need [*/z]C = [t1/z]C = C
             Nothing -> checkExpr t2 t1ForZinC ctxt
             Just (PVar z, tC) -> do
               starForZinC <- substitute (unBindName z, Unit) tC
               checkExpr t2 (Just starForZinC) ctxt
             Just (p, _) -> patternMismatch p t1

      (g3Comp, s, z, tC) <-
        case tp of
          -- non-dependent elimination
          --
          -- but as the rules don't actually have a non-dependent
          -- elimination, we pretend there is a fresh variable "z" in
          -- C that is used with grade 0. Then we obtain the actual
          -- value of C from the typing of t2 ([*/z]C = C).
          Nothing -> do
            z <- getFreshName "z"
            let tC = starForZinC
            -- (M,gZ | g3,s | gZ) @ G, z : Unit |- C : Type l
            (g3s, _) <- checkExprIsType tC (extendInputContext ctxt z UnitTy gZ)
            -- in this case we require that s is zero
            let (g3, (_, s)) = unextend g3s
            s <- verifyGradesEq "formation of product elim type (C)" Subject z s gradeZero
            pure (g3, s, z, tC)
          Just (PVar z', tC) -> do
            let z = unBindName z'
            -- (M,gZ | g3,s | gZ) @ G, z : Unit |- C : Type l
            (g3s, _) <- checkExprIsType tC (extendInputContext ctxt z UnitTy gZ)
            let (g3, (_, s)) = unextend g3s
            pure (g3, s, z, tC)
          Just (p, _) -> patternMismatch p t1

      starForZinCCalc <- substitute (z, Unit) tC
      _ <- ensureEqualTypes starForZinC starForZinCCalc

      g3 <- verifyGradeVecEq "unit elim" g3 g3Comp

      sTimesG1 <- contextGradeMult s g1
      g1plusG2 <- contextGradeAdd g1 g2
      g3plusStimesG1 <- contextGradeAdd g3 sTimesG1

      t1forZinC <- substitute (z, t1) tC

      -- (M | g1 + g2 | g3 + s * g1) G |- case t1 as z in C of * -> t2 : [t1/x]C
      pure ( OutContext { subjectGradesOut = g1plusG2, typeGradesOut = g3plusStimesG1 }
           , t1forZinC)
    _ -> expectedInferredTypeForm "Unit" unitTy


---------------------------
----- Natural numbers -----
---------------------------


{-
  ------------------ :: NatTy
  0G |- Nat : Type 0
-}
checkExpr' NatTy Nothing ctxt =
  -- TODO: ensure that NatTy can inhabit any level (2020-07-01)
  pure (zeroedOutContextForInContext ctxt, mkUnivTy levelZero)


{-
  ---------------- :: zero
  0G |- zero : Nat
-}
checkExpr' NZero Nothing ctxt =
  pure (zeroedOutContextForInContext ctxt, NatTy)


{-
  -------------------------------------- :: succ
  0G |- succ : (k : [.1, .0] Nat) -> Nat
-}
checkExpr' NSucc Nothing ctxt =
  pure (zeroedOutContextForInContext ctxt, FunTy (mkAbsGr ignoreVar NatTy gradeOne gradeZero NatTy))


-----------------------------
----- Fallthrough cases -----
-----------------------------


-- no type passed, and none of the cases provided inference for the
-- term, so we cannot infer a type for the expression
checkExpr' _ Nothing _ = cannotSynthTypeForExpr


-- a type was passed, but none of the cases provided a way to compare
-- the types (this usually arises from type constructors), so we
-- instead infer a type and then compare Switch over to synth case
checkExpr' e (Just t) ctxt = do
  debug $ "Check fall through for " <> pprint e
  --
  (ctxt', t') <- inferExpr e ctxt
  t <- ensureEqualTypes t t'
  pure (ctxt', t)


-- | Try and infer a type for the given expression.
inferExpr :: Expr -> InContext -> CM (OutContext, Type)
inferExpr e = checkExpr e Nothing


--------------------
----- Patterns -----
--------------------


-- | Try and map components of a term to names in a pattern.
maybeGetPatternSubst :: Pattern -> Expr -> Maybe ([(Name, Expr)], [(Name, Expr)])
maybeGetPatternSubst (PPair p1 p2) (Pair l r) =
  maybeGetPatternSubst p1 l <> maybeGetPatternSubst p2 r
-- maybeGetPatternSubst PUnit (Builtin DUnitTerm) = pure []
maybeGetPatternSubst (PVar n) e = pure ([(unBindName n, e)], [])
maybeGetPatternSubst (PBox p) (Box b) = maybeGetPatternSubst p b
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
maybeGetPatternUnificationSubst (PBox p1) (PBox p2) = maybeGetPatternUnificationSubst p1 p2
maybeGetPatternUnificationSubst _ _ = Nothing


-------------------
----- Helpers -----
-------------------


mkUnivTy :: Level -> Expr
mkUnivTy = Universe


-- | Check that an expression is a type, and return the subject grades
-- | and level it was formed as.
--
-- TODO: perhaps allow specifying which level to infer the type at (2020-06-18)
--
-- TODO: perhaps allow grades in the subject type where r <= 0 (2020-06-18)
checkExprIsType :: Expr -> InContext -> CM (Ctxt Grade, Level)
checkExprIsType e ctxt = do
  (OutContext { subjectGradesOut = g, typeGradesOut = gZ }, typel) <- inferExpr e ctxt
  case typel of
    (Universe l) -> do
      _ <- allZeroes gZ
      pure (g, l)
    _ -> expectedInferredTypeForm "universe" typel
  where
    -- | Ensure the grade vector contains only zeroes (or refinements of zero).
    allZeroes :: Ctxt Grade -> CM (Ctxt Grade)
    allZeroes ctxt = verifyGradeVecEq "" ctxt (zeroesMatchingShape ctxt)


extendInputContext :: InContext -> Name -> Type -> Ctxt Grade -> InContext
extendInputContext ctxt x tA m =
  InContext { types = extend (types ctxt) x tA
            , contextGradesIn = extend (contextGradesIn ctxt) x m }


-- | Verify that two grades are equal, and return a suitably equivalent grade.
verifyGradesEq :: Doc -> Stage -> Name -> Grade -> Grade -> CM Grade
verifyGradesEq desc st n s r = do
  gEq <- gradeEq s r
  if gEq then pure s else gradeMismatchAt' desc st n s r


-- | Like verifyGradesEq, but if one of the grades is an implicit,
-- | then just use the other (for binding positions).
verifyGradesEqButUseOtherIfImplicit :: Doc -> Stage -> Name -> Grade -> Grade -> CM Grade
verifyGradesEqButUseOtherIfImplicit _ _ _ s (Grade{grade=GExpr Implicit{}}) = pure s
verifyGradesEqButUseOtherIfImplicit _ _ _ (Grade{grade=GExpr Implicit{}}) r = pure r
verifyGradesEqButUseOtherIfImplicit desc st n s r = verifyGradesEq desc st n s r


-- | Verify that two grade vectors are equal, and return a suitably
-- | equivalent grade vector.
verifyGradeVecEq :: Doc -> Ctxt Grade -> Ctxt Grade -> CM (Ctxt Grade)
verifyGradeVecEq desc g1 g2 =
  contextGradeEq g1 g2 >>= \t ->
    case t of
      Right() -> pure g1
      Left mismatches ->
        gradeMismatchAt desc Context mismatches


------------------
----- Levels -----
------------------


levelMax :: Level -> Level -> CM Level
levelMax (LMax ls) (LMax ls') = pure $ levelMax' (ls ++ ls')


levelSucc :: Level -> Level
levelSucc (LMax xs) = LMax $ fmap lsucc xs
  where lsucc (LitLevel n) = LitLevel (succ n)
        lsucc (LPlus n  m) = LPlus (succ n) m


-- mostly from https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Substitute.html#levelMax
levelMax' :: [PlusLevel] -> Level
levelMax' as0 = LMax $ ns ++ sort bs
  where
    as = Prelude.concatMap expand as0
    -- ns is empty or a singleton
    ns = case [ n | LitLevel n <- as, n > 0 ] of
      []  -> []
      ns  -> [ LitLevel n | let n = Prelude.maximum ns, n > greatestB ]
    bs = subsume [ b | b@LPlus{} <- as ]
    greatestB | null bs   = 0
              | otherwise = Prelude.maximum [ n | LPlus n _ <- bs ]

    expand l@LitLevel{} = [l]
    expand (LPlus n l) = map (plus n) $ expand0 $ [LPlus 0 l]

    expand0 [] = [LitLevel 0]
    expand0 as = as

    plus n (LitLevel m) = LitLevel (n + m)
    plus n (LPlus m l)      = LPlus (n + m) l

    subsume (LitLevel{} : _) = error "Impossible"
    subsume [] = []
    subsume (LPlus n a : bs)
      | not $ null ns = subsume bs
      | otherwise     = LPlus n a : subsume [ b | b@(LPlus _ a') <- bs, a /= a' ]
      where
        ns = [ m | LPlus m a'  <- bs, a == a', m > n ]


-- | Test whether two levels are equal.
levelsAreEqual :: Level -> Level -> CM Bool
levelsAreEqual (LMax l1) (LMax l2) = lEqual (levelMax' l1) (levelMax' l2)
  where lEqual (LMax []) (LMax []) = pure True
        lEqual (LMax (x:xs)) (LMax (y:ys)) = (&&) <$> lEqual' x y <*> lEqual (LMax xs) (LMax ys)
        lEqual _ _ = pure False
        -- TODO: support checking against meta solutions/instantiations (2020-06-13)
        lEqual' (LitLevel n) (LitLevel m) = pure (n == m)
        lEqual' (LPlus m1 l1) (LPlus m2 l2) = pure $ (m1 == m2) && (l1 == l2)
        lEqual' _ _ = pure False


------------------
----- Grades -----
------------------


gradeAdd :: Grade -> Grade -> CM Grade
gradeAdd g1 g2 = do
  ty <- requireSameTypedGrades g1 g2
  normaliseGrade (Grade { grade = GPlus (grade g1) (grade g2), gradeTy = ty })

gradeAdd':: Grade' -> Grade' -> GradeSpec -> CM Grade
gradeAdd' g1 g2 ty =
  normaliseGrade (Grade { grade = GPlus g1 g2, gradeTy = ty })


-- TODO: perhaps optimise more here (distribute addition/scaling?), or
-- perhaps do this somewhere else in a simplification function
-- (2020-06-13)
gradeMult :: Grade -> Grade -> CM Grade
gradeMult g1 g2 = do
  ty <- requireSameTypedGrades g1 g2
  normaliseGrade (Grade { grade = GTimes (grade g1) (grade g2), gradeTy = ty })

gradeMult' :: Grade' -> Grade' -> GradeSpec -> CM Grade
gradeMult' g1 g2 ty =
  normaliseGrade (Grade { grade = GTimes g1 g2, gradeTy = ty })


-- TODO: do normalisation according to whatever type the grade belongs
-- to (2020-06-13)
--
-- TODO: perform some simplification here (distribute
-- addition/scaling, perhaps?) (2020-06-13)
--
-- TODO: require that the grade type is actually a grade specification
-- (semiring) (2020-06-21)
normaliseGrade :: Grade -> CM Grade
normaliseGrade g@Grade{grade=GEnc{}} = pure g
normaliseGrade Grade{grade=GSig g s, gradeTy=s'} = do
  -- TODO: have ensureEqualTypes (and friends) return a normalised
  -- type to use (2020-06-21)
  eqTys <- gradeTypesAreEqual s s'
  unless eqTys (gradeTyMismatch s s')
  normaliseGrade (mkGrade g s)
normaliseGrade Grade{grade=GPlus g1 g2, gradeTy=ty} = do
  g1' <- normaliseGrade (mkGrade g1 ty)
  g2' <- normaliseGrade (mkGrade g2 ty)
  _ <- requireSameTypedGrades g1' g2'
  case (g1', g2') of
    (Grade{grade=GZero}, r) -> pure r
    (s, Grade{grade=GZero}) -> pure s

    -- inf + r = inf
    (s@Grade{grade=GInf}, _) -> pure s
    -- s + inf = inf
    (_, r@Grade{grade=GInf}) -> pure r

    (g3, Grade{grade=GPlus g4 g5}) -> do
      l <- gradeAdd' (grade g3) g4 ty
      gradeAdd' (grade l) g5 ty
    _ -> pure Grade{grade=GPlus (grade g1') (grade g2'), gradeTy=ty}
normaliseGrade Grade{grade=GTimes g1 g2, gradeTy=ty} = do
  g1' <- normaliseGrade (mkGrade g1 ty)
  g2' <- normaliseGrade (mkGrade g2 ty)
  _ <- requireSameTypedGrades g1' g2'
  case (g1', g2') of
    (s@Grade{grade=GZero}, _) -> pure s
    (_, r@Grade{grade=GZero}) -> pure r
    (Grade{grade=GOne}, r) -> pure r
    (s, Grade{grade=GOne}) -> pure s

    -- (s/=0) * inf = inf
    (_, r@Grade{grade=GInf}) -> pure r
    -- inf * (r/=0) = inf
    (s@Grade{grade=GInf}, _) -> pure s

    (s1, Grade{grade=GTimes s2 s3}) -> do
      l <- gradeMult' (grade s1) s2 ty
      gradeMult' (grade l) s3 ty
    _ -> pure Grade{grade=GTimes (grade g1') (grade g2'), gradeTy=ty}
-- TODO: Allow using the ordering according to whatever type the grade
-- is of (2020-06-13)
normaliseGrade Grade{grade=GLub g1 g2, gradeTy=ty} = do
  g1' <- normaliseGrade (mkGrade g1 ty)
  g2' <- normaliseGrade (mkGrade g2 ty)
  ty <- requireSameTypedGrades g1' g2'
  case (grade g1', grade g2', ty) of
    -- forall r. r <= inf
    (GInf, _, _) -> pure gradeInf { gradeTy = ty }
    (_, GInf, _) -> pure gradeInf { gradeTy = ty }
    -- Irrelevant <= Private
    (GEnc 0, GEnc 1, PrivacyLevel) -> pure $ mkGrade (GEnc 1) PrivacyLevel
    -- Private <= Public
    (GEnc 1, GEnc 2, PrivacyLevel) -> pure $ mkGrade (GEnc 2) PrivacyLevel
    -- Irrelevant <= Public
    (GEnc 0, GEnc 2, PrivacyLevel) -> pure $ mkGrade (GEnc 2) PrivacyLevel
    _ -> do
      gEq <- gradeEq g1' g2'
      pure $ if gEq then g1' else Grade{grade=GLub (grade g1') (grade g2'), gradeTy=ty}
normaliseGrade Grade{grade=GExpr g,gradeTy=ty} =
  normalise g >>= \g -> pure Grade{grade=GExpr g, gradeTy=ty}


gradeTypesAreEqual :: GradeSpec -> GradeSpec -> CM Bool
gradeTypesAreEqual PrivacyLevel PrivacyLevel = pure True
-- for now, just treating implicits as equal to any grade types (GD: 2020-06-20)
--
-- TODO: implement unification of implicits (2020-06-21)
gradeTypesAreEqual GSImplicit _ = pure True
gradeTypesAreEqual _ GSImplicit = pure True
gradeTypesAreEqual e1@PrivacyLevel e2 =
  notImplemented $ "Equality of grade types on" <+> quoted e1 <+> "and" <+> quoted e2
gradeTypesAreEqual e1@GSExpr{} e2 =
  notImplemented $ "Equality of grade types on" <+> quoted e1 <+> "and" <+> quoted e2
gradeTypesAreEqual (Extended s1) (Extended s2) =
  gradeTypesAreEqual s1 s2
gradeTypesAreEqual (Interval s1) (Interval s2) =
  gradeTypesAreEqual s1 s2
gradeTypesAreEqual s1 s2 = return (s1 == s2)



requireSameTypedGrades :: Grade -> Grade -> CM GradeSpec
requireSameTypedGrades Grade{gradeTy=s1} Grade{gradeTy=s2} = do
  eqTys <- gradeTypesAreEqual s1 s2
  if eqTys then pure s1 else gradeTyMismatch s1 s2


-- | Generate a new, existentially bound, implicit grade.
newExistentialGrade :: GradeSpec -> CM Grade
newExistentialGrade gty = do
  i <- getFreshMetaId
  existentiallyBindGradeImplicit i gty
  pure (Grade (GExpr (mkImplicit i)) gty)


-- TODO: set up a class for folding over expressions and grades (2020-06-27)
existentiallyQuantifyGradeImplicits :: Grade -> CM Grade
existentiallyQuantifyGradeImplicits p@(Grade{grade=g,gradeTy=ty}) = do
  case g of
    GExpr e -> existentiallyQuantifyExprImplicitsAsGrades e ty
               >>= \e -> pure p { grade = GExpr e }
    GEnc{} -> pure p
    GPlus l r -> do
      l <- existentiallyQuantifyGradeImplicits (mkGrade l ty)
      r <- existentiallyQuantifyGradeImplicits (mkGrade r ty)
      pure p { grade = GPlus (grade l) (grade r) }
    GTimes l r -> do
      l <- existentiallyQuantifyGradeImplicits (mkGrade l ty)
      r <- existentiallyQuantifyGradeImplicits (mkGrade r ty)
      pure p { grade = GTimes (grade l) (grade r) }
    GLub l r -> do
      l <- existentiallyQuantifyGradeImplicits (mkGrade l ty)
      r <- existentiallyQuantifyGradeImplicits (mkGrade r ty)
      pure p { grade = GLub (grade l) (grade r) }
    GSig s t -> do
      -- TODO: make sure that t and ty are the same (2020-06-27)
      existentiallyQuantifyGradeImplicits (mkGrade s t)


existentiallyQuantifyExprImplicitsAsGrades :: Expr -> GradeSpec -> CM Expr
existentiallyQuantifyExprImplicitsAsGrades e@(Implicit i) gty =
  existentiallyBindGradeImplicit i gty >> pure e
existentiallyQuantifyExprImplicitsAsGrades e _ = pure e


existentiallyBindGradeImplicit :: MetaId -> GradeSpec -> CM ()
existentiallyBindGradeImplicit i gty = do
  let n = implicitToName i
  debug $ "existentially binding (grade):" <+> quoted i
  gty <- if gty == GSImplicit
         then debug "no grade type specified, defaulting to Extended ExactUsage" >> pure (Extended ExactUsage)
         else pure gty
  existential n gty
