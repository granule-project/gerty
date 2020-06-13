{-# LANGUAGE ViewPatterns #-}

module Language.Dlam.Types
  ( doASTInference
  ) where

import Control.Monad (unless, zipWithM)
import Data.List (sort)

import Language.Dlam.Substitution (Substitutable(substitute))
import Language.Dlam.Syntax.Abstract
import Language.Dlam.Syntax.Common
import qualified Language.Dlam.Syntax.Common.Language as Com
import qualified Language.Dlam.Syntax.Concrete as C
import Language.Dlam.Syntax.Internal
import Language.Dlam.TypeChecking.Monad
import Language.Dlam.Util.Pretty (pprintShow)
import qualified Language.Dlam.Scoping.Monad as SE

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
normalise Implicit = finalNormalForm Implicit
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

normalise (Let (LetPatBound p e1) e2) = do
  e1' <- normalise e1
  case maybeGetPatternSubst p e1' of
    Nothing -> normalise e2 >>= finalNormalForm . Let (LetPatBound p e1')
    -- TODO: perform the subject-type substitution only in the type (2020-03-04)
    Just (ssubst, tsubst) -> normalise =<< substitute tsubst =<< substitute ssubst e2
normalise (Sig e t) = Sig <$> normalise e <*> normalise t
-- TODO: Improve normalisation for levels/universes (metas?) (2020-06-13)
normalise (Universe l) = finalNormalForm $ Universe l
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
    -- Implicits always match.
    (Implicit, _) -> pure True
    (_, Implicit) -> pure True
    (Universe l1, Universe l2) -> levelsAreEqual l1 l2

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


-- | Try and register the name with the given type
registerTypeForName :: Name -> Type -> CM ()
registerTypeForName n t = do
  setType n t


-- | Attempt to infer the types of a definition, and check this against the declared
-- | type, if any.
doDeclarationInference :: Declaration -> CM Declaration
doDeclarationInference (TypeSig n t) = do
  debug $ "here is a signature for " ++ show n
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
  t <- debugBlock "FUN EQN INFERENCE" ("finding signature for " <> pprintShow v) (\t -> maybe "no sig found" (("found sig: "<>) . pprintShow) t)
       (lookupType v)
  exprTy <- case t of
              Nothing -> do
                _ <- inferExpr e emptyInContext
                return $ mkImplicit
              Just ty -> do
                checkOrInferTypeNew ty e
                return ty

  -- assign the appopriate equation and normalised/inferred type for the name
  setValue v e
  setType v exprTy
  pure (FunEqn (FLHSName v) (FRHSAssign e))


-- | Attempt to infer the types of each definition in the AST, failing if a type
-- | mismatch is found.
doASTInference :: AST -> CM AST
doASTInference (AST ds) = do
  debug $ "LENGTH " ++ (show $ length ds)
  fmap AST $ mapM doDeclarationInference ds


-- | Infer a level for the given type.
inferUniverseLevel :: Type -> CM Level
inferUniverseLevel e = withLocalCheckingOf e $ do
  (_, u) <- inferExpr e emptyInContext
  norm <- normalise u
  case norm of
    (Universe l) -> pure l
    _        -> expectedInferredTypeForm "universe" norm


----------------------------------------------------------------------------
-- Dominic work here on a bidirectional additive-grading algorithm

gradeEq :: Grade -> Grade -> CM Bool
gradeEq r1 r2 = do
  r1' <- normaliseGrade r1
  r2' <- normaliseGrade r2
  return (r1' == r2')

contextGradeAdd :: Ctxt Grade -> Ctxt Grade -> CM (Ctxt Grade)
contextGradeAdd sigma1 sigma2 =
  if and (zipWith (\(id, _) (id', _) -> ident id == ident id') sigma1 sigma2)
    then zipWithM (\(id, g1) (_id', g2) -> gradeAdd g1 g2 >>= \r -> pure (id, r)) sigma1 sigma2
    else error "Internal error: context graded add on contexts of different shape"

contextGradeMult :: Grade -> Ctxt Grade -> CM (Ctxt Grade)
contextGradeMult r sigma =
  mapM (\(id, g) -> gradeMult r g >>= \s -> pure (id, s)) sigma

-- First argument is usually the expected, and second is the actual
contextGradeEq :: Ctxt Grade -> Ctxt Grade -> CM (Either (Name, (Grade, Grade)) ())
contextGradeEq [] [] = return $ Right ()

contextGradeEq ((id, g1):ctxt) ((id', g2):ctxt') | ident id == ident id' = do
  eq <- gradeEq g1 g2
  if eq
    then contextGradeEq ctxt ctxt'
    else return $ Left (id, (g1, g2))

contextGradeEq _ _ =
  error "Internal error: context graded equality on contexts of different shape"

-- DAO: may want to make this an interface so we can try
--      different implementations. For now its just specialised
type Ctxt a = [(Name, a)] -- M.Map Name a

extend :: Ctxt a -> Name -> a -> Ctxt a
extend ctxt n t = ctxt ++ [(n, t)]

unextend :: Ctxt a -> (Ctxt a, (Name, a))
unextend [] = error "bad call to unextend with empty context"
unextend [(n, t)] = ([], (n, t))
unextend (x : xs) = (x : xs', end)
  where
    (xs', end) = unextend xs

emptyInContext :: InContext
emptyInContext = InContext [] []

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

debugContextGrades :: InContext -> String
debugContextGrades ctxt =
  show (map (\(id, x) -> (ident id, map (ident . fst) x)) (contextGradesIn ctxt))

-- | A zeroed OutContext that matches the shape of the InContext, for
-- | when typing constants.
zeroedOutContextForInContext :: InContext -> OutContext
zeroedOutContextForInContext inCtx =
  OutContext { subjectGradesOut = zeroesMatchingShape (types inCtx)
             , typeGradesOut = zeroesMatchingShape (types inCtx) }

lookupAndCutoutIn :: Name -> InContext -> Maybe (InContext, (Type, Ctxt Grade), InContext)
lookupAndCutoutIn n context = do
  (typesL, t, typesR)         <- lookupAndCutout1 n (types context)
  (cGradesL, delta, cGradesR) <- lookupAndCutout1 n (contextGradesIn context)
  return $ (InContext typesL cGradesL, (t, delta), InContext typesR cGradesR)

lookupAndCutout1 :: Name -> Ctxt a -> Maybe (Ctxt a, a, Ctxt a)
lookupAndCutout1 _ [] = Nothing
lookupAndCutout1 v ((v', x) : ctxt) | ident v == ident v' =
  Just (mempty, x, ctxt)
lookupAndCutout1 v ((v', x) : ctxt) | otherwise = do
  (ctxtL, y, ctxtR) <- lookupAndCutout1 v ctxt
  Just ((v', x) : ctxtL, y, ctxtR)

-- Monoid of disjoint contexts
instance Monoid OutContext where
  mempty = OutContext [] []

isEmpty :: OutContext -> Bool
isEmpty ctxt = ctxt == mempty

instance Semigroup OutContext where
  c1 <> c2 =
      OutContext (subjectGradesOut c1 `disjUnion` subjectGradesOut c2)
                 (typeGradesOut c1 `disjUnion` typeGradesOut c2)
   where
     disjUnion m1 m2 | disjoint m1 m2 = m1 ++ m2
     disjUnion _  _  | otherwise = error $ "Non disjoint contexts"

     disjoint m1 m2 = not $ any (\(v, _) -> hasVar v m2) m1

     hasVar v m = foldr (\(v', _) r -> v' == v || r) False m


allZeroes :: Ctxt Grade -> CM Bool
allZeroes ctxt = mapM normaliseAndCheck ctxt >>= (return . and)
  where
    normaliseAndCheck (id, grade) = do
      grade' <- normaliseGrade grade
      if gradeIsZero grade'
        then return True
        else
          gradeMismatchAt "Type judgment" SubjectType id gradeZero grade'

zeroesMatchingShape :: Ctxt a -> Ctxt Grade
zeroesMatchingShape = map (\(id, _) -> (id, gradeZero))

-- Auxiliary function that examines an output context to check it has
-- 0 subject type use and that its type is of the form `Type l`
exprIsTypeAndSubjectTypeGradesZero :: OutContext -> Type -> CM (Maybe Level)
exprIsTypeAndSubjectTypeGradesZero ctxt ty = do
  isZeroed <- allZeroes (typeGradesOut ctxt)
  case ty of
    (Universe l) | isZeroed -> pure (Just l)
    _ -> pure Nothing


-- Top level
checkOrInferTypeNew :: Type -> Expr -> CM ()
checkOrInferTypeNew ty expr = do
  outContext <- checkExpr expr ty emptyInContext
  if isEmpty outContext
    then return ()
    else error "Binders are left!"

checkExpr :: Expr -> Type -> InContext -> CM OutContext
checkExpr e t c =
  debugBlock "checkExpr"
    ("checking expression '" <> pprintShow e <> "' against type '" <> pprintShow t <> "'")
    (\_ -> "checked OK for '" <> pprintShow e <> "'") (checkExpr' e t c)

{-

(Delta | sigma1 | 0) . G |- A : Type l
(Delta, sigma1 | sigma2, s | sigma3, r) . G, x : A |- t : B
----------------------------------------------------------------------- abs
(Delta | sigma2 | sigma1 + sigma3) . G |- \x . t : (x :(r, s) A -o B )

-}

checkExpr' :: Expr -> Type -> InContext -> CM OutContext
checkExpr' (Lam lam) t ctxt = do
  case t of
    -- (x : A) -> B
    FunTy pi -> do
      (outCtxtParam, paramTy) <- inferExpr (absTy pi) ctxt

      -- (i) Subject type grades are all zero and inferred type is `Type l`
      hasLevel <- exprIsTypeAndSubjectTypeGradesZero outCtxtParam paramTy
      case hasLevel of
        Just _ -> do
          -- Check body of the lambda
          let sigma1 = subjectGradesOut outCtxtParam

          outctxtBody <- do
             debug $ "Check body binding `" <> pprintShow (absVar pi) <> "` in scope"
             checkExpr (absExpr lam) (absExpr pi)
                     (InContext
                        { types = extend (types ctxt) (absVar pi) (absTy pi)
                        , contextGradesIn = extend (contextGradesIn ctxt) (absVar pi) sigma1 })

          -- Check calculated grades against binder
          let (sigma2, (_, s)) = unextend (subjectGradesOut outctxtBody)
          let (sigma3, (_, r)) = unextend (typeGradesOut outctxtBody)
          eq1 <- gradeEq s (subjectGrade pi)
          if eq1
            then do
              eq2 <- gradeEq r (subjectTypeGrade pi)
              if eq2
                then do
                  tgo <- contextGradeAdd sigma1 sigma3
                  pure $ OutContext { subjectGradesOut = sigma2, typeGradesOut = tgo }
                else gradeMismatchAt "pi binder" SubjectType (absVar pi) (subjectTypeGrade pi) r
            else gradeMismatchAt "pi binder" Subject (absVar pi) (subjectGrade pi) s

        _ -> tyMismatchAtType "abs" paramTy

    _ -> tyMismatchAt "abs" (FunTy (mkAbs (mkIdent "?") Hole Hole)) t

-- Switch over to synth case
checkExpr' e t ctxt = do
  debug $ "Check fall through for " <> pprintShow e
  --
  (ctxt', t') <- inferExpr e ctxt
  eq <- equalExprs t t'
  if eq
    then return ctxt'
    else tyMismatch t t'

-- | Try and infer a type for the given expression.
inferExpr :: Expr -> InContext -> CM (OutContext, Type)
inferExpr e c = withLocalCheckingOf e $
  debugBlock "inferExpr" ("inferring a type for expression '" <> pprintShow e <> "'")
             (\(_, t) -> "inferred a type '" <> pprintShow t <> "'")
             (inferExpr' e c)

{-

Declarative:

(D | sigma | 0) . G1 |- A : Type
---------------------------------------------------------------------- var
((D1, sigma, D2) | 0, 1, 0 | sigma, 0, 0) . (G1, x : A, G2) |- x : A

-}

inferExpr' :: Expr -> InContext -> CM (OutContext, Type)
inferExpr' (Var x) ctxt = do
  debug $ "Infer for var " <> pprintShow x <> " in context " <> debugContextGrades ctxt
  --
  case lookupAndCutoutIn x ctxt of
    -- this should be prevented by the scope checker (encountering a
    -- free variable that isn't in scope)
    Nothing -> scoperError $ SE.unknownNameErr (C.Unqualified $ nameConcrete x)
    Just (ctxtL, (ty, sigma'), ctxtR) -> do

      -- Check that this type is indeed a Type
      debug $ "Infer for var (type) " <> debugContextGrades ctxtL
      (outCtxt, typeType) <- inferExpr ty ctxtL

      -- Two checks:
      --  (i) Context grades for `x` match what was calculated in typing
      let sigma = subjectGradesOut outCtxt
      debug $ "Context grade eq var " <> pprintShow x <> " with " <> show sigma' <> " and " <> show sigma
      eq <- contextGradeEq sigma' sigma

      case eq of
        Left (mismatchVar, (expected, actual)) ->
          gradeMismatchAt "var" Context mismatchVar expected actual
        Right () -> do

          --  (ii) Subject type grades are all zero and inferred type is `Type l`
          hasLevel <- exprIsTypeAndSubjectTypeGradesZero outCtxt typeType
          case hasLevel of
            Just _ ->
              -- Success
              return $ (OutContext
                        { subjectGradesOut = extend (zeroesMatchingShape (types ctxtL)) x gradeOne
                                            <> (zeroesMatchingShape (types ctxtR))

                        , typeGradesOut    = extend sigma x gradeZero
                                            <> (zeroesMatchingShape (types ctxtR)) }, ty)

            _ -> tyMismatchAtType "var" typeType

{-

(D         | sigma1    | 0) . G        |- A : Type l1
(D, sigma1 | sigma2, r | 0) . G, x : A |- B : Type l2
---------------------------------------------------------------------- -o
(D | sigma1 + sigma2   | 0)  . G |- (x :(s, r) A -o B) : Type (l1 u l2)
)

-}

-- (x :(s, r) A -o B)
inferExpr' (FunTy pi) ctxt = do
  debug $ "Infer for pi type " <> pprintShow (FunTy pi)
  -- Infer type of parameter A
  debug $ "Infer for pi type (infer for param type)"
  (ctxtA, typeA) <- inferExpr (absTy pi) ctxt

  --  (i) Subject type grades are all zero inferred type is `Type l1`
  hasLevel <- exprIsTypeAndSubjectTypeGradesZero ctxtA typeA
  case hasLevel of
    Just l1 -> do

      let sigma1 = subjectGradesOut ctxtA

      -- Infer type of function type body B
      debug $ "Infer for pi type (infer for body type)"
      (ctxtB, typeB) <- inferExpr (absExpr pi)
                 (InContext { types = extend (types ctxt) (absVar pi) (absTy pi)
                            , contextGradesIn = extend (contextGradesIn ctxt) (absVar pi) sigma1 })

      -- (i) Subject type grades are all zero and inferred type is `Type l2`
      hasLevel' <- exprIsTypeAndSubjectTypeGradesZero ctxtB typeB
      case hasLevel' of
        Just l2 -> do

          let (sigma2, (_, rInferred)) = unextend (subjectGradesOut ctxtB)

          -- (ii) Check binder grade specification matches usage `r`
          eq <- gradeEq rInferred (subjectTypeGrade pi)
          if eq
            then do
              lmaxl1l2 <- levelMax l1 l2
              sgo <- contextGradeAdd sigma1 sigma2
              pure ( OutContext { subjectGradesOut = sgo
                                , typeGradesOut = zeroesMatchingShape (types ctxt) }
                   , mkUnivTy lmaxl1l2)
  -- Errors
            else gradeMismatchAt "pi type binder" Subject (absVar pi) (subjectTypeGrade pi) rInferred
        _ -> tyMismatchAtType "LHS of -o" typeB
    _ -> tyMismatchAtType "RHS of -o" typeA

{-

-}

----

{-

(M | g2 | g1 + g3) @ G |- t1 : (x : (s, r) A) -o B
(M | g4 | g1) @ G |- t2 : A
------------------------------------------------------ :: App
(M | g2 + s * g4 | g3 + r * g4) @ G |- t1 t2 : [t2/x]B

-}

inferExpr' (App t1 t2) ctxt = do
  -- Infer left of application
  debug $ "App infer for t1 = " <> pprintShow t1

  -- (M | g2 | g1 + g3) @ G |- t1 : (x : (s, r) A) -o B
  (outCtxtFun@(OutContext g2 g1plusG3), funTy) <- inferExpr t1 ctxt

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
      (OutContext g4 g1, tA') <- inferExpr t2 ctxt
      tA <- ensureEqualTypes tA' tA
      debug $ "ok A : " <> pprintShow tA

      -- (M,g1 | g3,r | gZ) @ G, x : A |- B : Type l
      debug $ "App infer for tyB = " <> pprintShow tB
      let gammaX = extend (types ctxt) (absVar pi) tA
          mG1 = extend (contextGradesIn ctxt) (absVar pi) g1
      (outCtxtB@(OutContext _g3R _gZ), tBUniv) <-
        inferExpr tB (InContext { types = gammaX, contextGradesIn = mG1 })

      debug $ "Ok B : " <> pprintShow tBUniv

      _ <- maybe (tyMismatchAtType "kind of function app return" tBUniv) (\_ -> pure ())
             <$> exprIsTypeAndSubjectTypeGradesZero outCtxtB tBUniv
      let (g3, (_, rInferred)) = unextend (subjectGradesOut outCtxtB)

      eq <- gradeEq rInferred r
      unless eq (gradeMismatchAt "function type" SubjectType (absVar pi) r rInferred)

      debug "Context grade eq app 1"
      debug $ "sigma1 = " ++ show (map (\(id,t) -> (ident id, t)) g1)
      debug $ "sigma3 = " ++ show (map (\(id,t) -> (ident id, t)) g3)
      debug $ "type grades out cxtFun " ++ show ((map (\(id,t) -> (ident id, t)) $ typeGradesOut outCtxtFun))

      g1plusG3Calculated <- contextGradeAdd g1 g3
      eq' <- contextGradeEq g1plusG3 g1plusG3Calculated

      case eq' of
        Right() -> do
          -- (M | g2 + s * g4 | g3 + r * g4) @ G |- t1 t2 : [t2/x]B
          sTimesG4 <- contextGradeMult s g4
          g2PlusSTimesG4 <- contextGradeAdd g2 sTimesG4
          rTimesG4 <- contextGradeMult r g4
          g3PlusRTimesG4 <- contextGradeAdd g3 rTimesG4

          t2forXinB <- substitute (absVar pi, t2) tB

          pure ( OutContext { subjectGradesOut = g2PlusSTimesG4
                            , typeGradesOut = g3PlusRTimesG4 }
               , t2forXinB)
        Left (mismatchVar, (expected, actual)) ->
          gradeMismatchAt "application function" Context mismatchVar expected actual
    _ -> tyMismatchAt "type of app left" (FunTy (mkAbs (mkIdent "?") Hole Hole)) funTy

inferExpr' (Def n) ctxt = do
  tA <- lookupType n >>= maybe (scoperError $ SE.unknownNameErr (C.Unqualified $ nameConcrete n)) pure
  pure (zeroedOutContextForInContext ctxt, tA)

inferExpr' (Universe l) ctxt =
  pure (zeroedOutContextForInContext ctxt, mkUnivTy (levelSucc l))

inferExpr' _ _ = do
  cannotSynthTypeForExpr


--------------------
----- Patterns -----
--------------------


-- | Try and map components of a term to names in a pattern.
maybeGetPatternSubst :: Pattern -> Expr -> Maybe ([(Name, Expr)], [(Name, Expr)])
maybeGetPatternSubst (PPair p1 p2) (Pair l r) =
  maybeGetPatternSubst p1 l <> maybeGetPatternSubst p2 r
-- maybeGetPatternSubst PUnit (Builtin DUnitTerm) = pure []
maybeGetPatternSubst (PAt n p) e =
  (([], [(unBindName n, e)]) <>) <$> maybeGetPatternSubst p e
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


-------------------
----- Helpers -----
-------------------


tyMismatchAtType :: String -> Type -> CM a
tyMismatchAtType s t = tyMismatchAt s (univMeta (MetaId (-1)))  t


mkUnivTy :: Level -> Expr
mkUnivTy = Universe


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


gradeZero, gradeOne :: Grade
--gradeZero = Builtin DNZero
--gradeOne  = App (Builtin DNSucc) gradeZero
gradeZero = Com.GZero
gradeOne = Com.GOne


gradeAdd :: Grade -> Grade -> CM Grade
gradeAdd g1 g2 = normaliseGrade (Com.GPlus g1 g2)


-- TODO: perhaps optimise more here (distribute addition/scaling?), or
-- perhaps do this somewhere else in a simplification function
-- (2020-06-13)
gradeMult :: Grade -> Grade -> CM Grade
gradeMult g1 g2 = normaliseGrade (Com.GTimes g1 g2)


gradeIsZero :: Grade -> Bool
gradeIsZero Com.GZero = True
gradeIsZero _ = False


-- TODO: do normalisation according to whatever type the grade belongs
-- to (2020-06-13)
--
-- TODO: perform some simplification here (distribute
-- addition/scaling, perhaps?) (2020-06-13)
normaliseGrade :: Grade -> CM Grade
normaliseGrade Com.GZero = pure Com.GZero
normaliseGrade Com.GOne = pure Com.GOne
normaliseGrade (Com.GPlus g1 g2) = do
  g1' <- normaliseGrade g1
  g2' <- normaliseGrade g2
  case (g1', g2') of
    (Com.GZero, r) -> pure r
    (s, Com.GZero) -> pure s
    _ -> pure (Com.GPlus g1' g2')
normaliseGrade (Com.GTimes g1 g2) = do
  g1' <- normaliseGrade g1
  g2' <- normaliseGrade g2
  case (g1', g2') of
    (Com.GZero, _) -> pure Com.GZero
    (_, Com.GZero) -> pure Com.GZero
    (Com.GOne, r) -> pure r
    (s, Com.GOne) -> pure s
    _ -> pure (Com.GTimes g1' g2')
-- TODO: Allow using the ordering according to whatever type the grade
-- is of (2020-06-13)
normaliseGrade (Com.GLub g1 g2) = do
  g1' <- normaliseGrade g1
  g2' <- normaliseGrade g2
  gEq <- gradeEq g1' g2'
  pure $ if gEq then g1' else Com.GLub g1' g2'
normaliseGrade Com.GImplicit = pure Com.GImplicit
