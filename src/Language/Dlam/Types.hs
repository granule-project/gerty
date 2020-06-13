{-# LANGUAGE ViewPatterns #-}

module Language.Dlam.Types
  ( doASTInference
  ) where

import Language.Dlam.Builtins
import Language.Dlam.Substitution
  ( Substitutable(substitute)
  , freshen
  )
import Language.Dlam.Syntax.Abstract
import Language.Dlam.Syntax.Common
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
-- VALUE: LitLevel
-- TODO: maybe add better normalisation for levels (e.g., vars and metas) (2020-06-13)
normalise (LevelExpr l) = finalNormalForm $ LevelExpr l
-- lzero ---> 0
normalise (Builtin LZero) = finalNormalForm . LevelExpr $ LitLevel 0
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
-- TODO: Improve normalisation for levels/universes (metas, variables?) (2020-06-13)
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
    (LevelExpr l1, LevelExpr l2) -> levelsAreEqual l1 l2

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


-- | Test whether two levels are equal.
levelsAreEqual :: Level -> Level -> CM Bool
levelsAreEqual (LitLevel n) (LitLevel m) = pure $ n == m
levelsAreEqual l1 l2 = notImplemented $ "levelsAreEqual on levels '" <> pprintShow l1 <> "' and '" <> pprintShow l2 <> "'"


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
                _ <- checkOrInferType mkImplicit e
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

----------------------------------------------------------------------------
-- Dominic work here on a bidirectional additive-grading algorithm

gradeEq :: Grade -> Grade -> CM Bool
gradeEq r1 r2 = do
  r1' <- normalise r1
  r2' <- normalise r2
  return (r1' == r2')

contextGradeAdd :: Ctxt Grade -> Ctxt Grade -> Ctxt Grade
contextGradeAdd sigma1 sigma2 =
  if and (zipWith (\(id, _) (id', _) -> ident id == ident id') sigma1 sigma2)
    then zipWith (\(id, g1) (_id', g2) -> (id, gradeAdd g1 g2)) sigma1 sigma2
    else error "Internal error: context graded add on contexts of different shape"

contextGradeMult :: Grade -> Ctxt Grade -> Ctxt Grade
contextGradeMult r sigma =
  map (\(id, g) -> (id, gradeMult r g)) sigma

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
      grade' <- normalise grade
      if gradeIsZero grade'
        then return True
        else
          gradeMismatchAt "Type judgment" SubjectType id gradeZero grade'

zeroesMatchingShape :: Ctxt a -> Ctxt Grade
zeroesMatchingShape = map (\(id, _) -> (id, gradeZero))

-- Auxiliary function that exmaines an output context to check it
-- has 0 subject type use and that its type is of the form `Type l`
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
                then return $ OutContext {
                               subjectGradesOut = sigma2
                             , typeGradesOut    = contextGradeAdd sigma1 sigma3
                              }
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
inferExpr' (LevelExpr i) ctxt = do
  debug $ "Infer for a literal level " <> show i
  pure (zeroedOutContextForInContext ctxt, Def $ mkIdent "Level")

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
              return (OutContext { subjectGradesOut = contextGradeAdd sigma1 sigma2
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

(D         | sigma1    | 0) . G        |- A : Type l1
(D, sigma1 | sigma3, r | 0) . G, x : A |- B : Type l2
(D | sigma2 | sigma1 + sigma3) . G |- t1 : (x :(s, r) A -o B)
(D | sigma4 | sigma1)          . G |- t2 : A
----------------------------------------------------------------------------- -o
(D | sigma2 + s * sigma4 | sigma3 + r * sigma4) . G |- t1 t2 : [t2/x] B

-}

inferExpr' e@(App t1 t2) ctxt = do
  debug $ "Infer for application " <> pprintShow e

  -- Infer left of application
  debug $ "App infer for t1 = " <> pprintShow t1
  (outCtxtFun, funTy) <- inferExpr t1 ctxt

  let sigma2 = subjectGradesOut outCtxtFun

  -- Need to infer types for `funTy` to see how the context
  -- is used to form `A` and `B`
  case funTy of
    -- (x :(s, r) A -o B)
    (FunTy pi) -> do
      let r   = subjectTypeGrade pi
      let s   = subjectGrade pi
      let tyA = absTy pi
      let tyB = absExpr pi

      -- Infer the type of the A
      debug $ "App infer for tyA = " <> pprintShow tyA
      (outCtxtA, typeOfA) <- inferExpr tyA ctxt
      debug $ "ok A : " <> pprintShow typeOfA

      hasLevel <- exprIsTypeAndSubjectTypeGradesZero outCtxtA typeOfA
      case hasLevel of
        Nothing -> tyMismatchAtType "kind of function arg" typeOfA
        Just _ -> do
          let sigma1 = subjectGradesOut outCtxtA

          -- Infer the type of the B in the context with `x`
          debug $ "App infer for tyB = " <> pprintShow tyB
          (outCtxtB, typeOfB) <-
             inferExpr tyB
               InContext {
                 types = extend (types ctxt) (absVar pi) tyA
               , contextGradesIn = extend (contextGradesIn ctxt) (absVar pi) sigma1
               }
          debug $ "Ok B : " <> pprintShow typeOfB

          hasLevel' <- exprIsTypeAndSubjectTypeGradesZero outCtxtB typeOfB
          case hasLevel' of
            Nothing -> tyMismatchAtType "kind of function app return" typeOfB
            Just _ -> do
              let (sigma3, (_, rInferred)) = unextend (subjectGradesOut outCtxtB)

              eq <- gradeEq rInferred r
              if eq then do
                debug "Context grade eq app 1"
                debug $ "sigma1 = " ++ show (map (\(id,t) -> (ident id, t)) sigma1)
                debug $ "sigma3 = " ++ show (map (\(id,t) -> (ident id, t)) sigma3)
                debug $ "type grades out cxtFun " ++ show ((map (\(id,t) -> (ident id, t)) $ typeGradesOut outCtxtFun))
                eq' <- contextGradeEq (contextGradeAdd sigma1 sigma3) (typeGradesOut outCtxtFun)
                case eq' of
                  Right() -> do
                    -- Check argument `t2` and its usage
                    outCtxtArg <- checkExpr t2 tyA ctxt
                    debug "Context grade eq app 2"
                    eq2 <- contextGradeEq sigma1 (typeGradesOut outCtxtArg)

                    case eq2 of
                      Right() -> do
                        let sigma4 = subjectGradesOut outCtxtArg
                        tyB' <- substitute (absVar pi, tyA) tyB

                        return (OutContext
                          { subjectGradesOut =
                                contextGradeAdd sigma2 (contextGradeMult s sigma4)
                          , typeGradesOut =
                                contextGradeAdd sigma3 (contextGradeMult r sigma4)
                            }
                          , tyB')
                      Left (mismatchVar, (expected, actual)) ->
                        gradeMismatchAt "application argument" Context mismatchVar expected actual
                  Left (mismatchVar, (expected, actual)) ->
                    gradeMismatchAt "application function" Context mismatchVar expected actual
              else
                gradeMismatchAt "function type" SubjectType (absVar pi) r rInferred

    _ -> tyMismatchAt "type of app left" (FunTy (mkAbs (mkIdent "?") Hole Hole)) funTy

inferExpr' (Def n) ctxt = do
  tA <- lookupType n >>= maybe (scoperError $ SE.unknownNameErr (C.Unqualified $ nameConcrete n)) pure
  pure (zeroedOutContextForInContext ctxt, tA)

inferExpr' (Universe (LitLevel l)) ctxt =
  pure (zeroedOutContextForInContext ctxt, mkUnivTy (LitLevel (l + 1)))

inferExpr' _ _ = do
  cannotSynthTypeForExpr

-----------------------------------------------
-- OLD STUFF FROM HERE

-- | 'checkOrInferType ty ex' checks that the type of 'ex' matches 'ty', or infers
-- | it 'ty' is a wild. Evaluates to the calculated type.
checkOrInferType :: Type -> Expr -> CM Expr
checkOrInferType t e = withLocalCheckingOf e $ checkOrInferType' t e


checkOrInferType' :: Type -> Expr -> CM Expr
--------------
-- Builtins --
--------------
checkOrInferType' t (Builtin e) =
  -- here we simply check that the expected type
  -- matches the type defined for the builtin
  ensureEqualTypes t $
    case e of
      -- lzero : Level
      LZero -> builtinType lzero

      -- lsuc : Level -> Level
      LSuc  -> builtinType lsuc

      -- Level : Type 0
      LevelTy -> builtinType levelTy

      -- lmax : Level -> Level -> Level
      LMax -> builtinType lmax

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
----------------------
-- Level expression --
----------------------
checkOrInferType' t LevelExpr{} = ensureEqualTypes t (builtinBody levelTy)
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
checkOrInferType' t (Var x) = do
  -- x @ (k+1, n) : A in G
  -- TODO: remove this possible failure---the scope checker should prevent this (2020-03-05)
  tA <- lookupType x >>= maybe (scoperError $ SE.unknownNameErr (C.Unqualified $ nameConcrete x)) pure
  kplus1 <- lookupSubjectRemaining x
  k <- case kplus1 of
         -- as the scope checker ensures that all local variables are
         -- in scope, the only way something could not be assigned
         -- here is if it is a top-level definition, in which case we
         -- treat its usage as implicit
         -- TODO: assign implicit grades to top-level definitions (2020-03-12)
         Nothing -> pure Implicit
         Just kplus1 -> do
           -- just normalise for now, and assume it is well-typed (2020-03-11, GD)
           kplus1 <- normalise kplus1
           maybe (usedTooManyTimes x) pure =<< decrementGrade kplus1

  -- G |- A : Type l
  _l <- inferUniverseLevel tA
  tA <- normalise tA

  -- x @ (k, n) : A in G
  -- G |- x : A
  setSubjectRemaining x k
  ensureEqualTypes t tA

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
  lmaxl1l2 <- levelMax l1 l2
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
  lmaxl1l2 <- levelMax l1 l2
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
  lmaxl1l2 <- levelMax l1 l2
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
  let inlX = inlTermApp (LevelExpr l1) (LevelExpr l2) tA tB (Var x)
  e' <- normalise e
  inlxforzinC <- substitute (z, inlX) tC
  _ <- withTypedVariable x tA $ withActivePattern e' inlX
       $ checkOrInferType inlxforzinC c

  -- G, y : B |- d : [inr y/z]C
  let inrY = inrTermApp (LevelExpr l1) (LevelExpr l2) tA tB (Var y)
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
    substitute (x, Var z) =<< substitute (y, Var z) =<< substitute (p, reflTermApp (LevelExpr l1) tA (Var z)) tC
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
synthType e =
  checkOrInferType mkImplicit e


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


-------------------
----- Helpers -----
-------------------


tyMismatchAtType :: String -> Type -> CM a
tyMismatchAtType s t = tyMismatchAt s (mkUnivTy LInfer) t


------------------
----- Levels -----
------------------


levelMax :: Level -> Level -> CM Level
levelMax (LitLevel l1) (LitLevel l2) = pure $ LitLevel (max l1 l2)
levelMax l1 l2 = notImplemented $ "levelMax on '" <> pprintShow l1 <> "' and '" <> pprintShow l2 <> "'"
