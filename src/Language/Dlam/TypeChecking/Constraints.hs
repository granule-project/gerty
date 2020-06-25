{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- Deals with compilation of grades into symbolic representations of SBV.
   Heavily based on Granule by Vilem Liepelt and Dominic Orchard -}

module Language.Dlam.TypeChecking.Constraints
  (provePredicate, Quantifier(..), SolverResult(..)) where

--import Data.Foldable (foldrM)
import Data.SBV hiding (kindOf, name, symbolic, Interval)
import Control.Monad (liftM2)

import Language.Dlam.Util.Pretty
import Language.Dlam.TypeChecking.Predicates

import Language.Dlam.TypeChecking.Constraints.SymbolicGrades
import qualified Language.Dlam.TypeChecking.Constraints.SNatX as SNatX
import Language.Dlam.Syntax.Abstract

type Ctxt a = [(Name, a)]

data Quantifier = ForallQ | InstanceQ

data SolverResult
  = QED
  | NotValid Doc
  -- | NotValidTrivial [Constraint]
  | Timeout
  | SolverProofError Doc
  | OtherSolverError Doc

provePredicate :: Pred -> IO SolverResult
provePredicate predicate
  | isTrivial predicate = do
      return QED
  | otherwise = do
      let sbvTheorem = compileToSBV predicate
      -- Prove -----------
      ThmResult thmRes <- proveWith defaultSMTCfg $ do --  -- proveWith cvc4 {verbose=True}
        case 10000 of
          n | n <= 0 -> return ()
          n -> setTimeOut n
        sbvTheorem
      ------------------
      return $ case thmRes of
        -- we're good: the negation of the theorem is unsatisfiable
        Unsatisfiable {}    -> QED
        ProofError _ msgs _ -> SolverProofError $ vcat (fmap pprint msgs)
        Unknown _ UnknownTimeOut -> Timeout
        Unknown _ reason  -> OtherSolverError $ text (show reason)
        _ ->
          case getModelAssignment thmRes of
            -- Main 'Falsifiable' result
            Right (False, assg :: [ Integer ] ) ->
                  -- Show fatal error, with prover result
                  {-
                  negated <- liftIO . sat $ sbvSatTheorem
                  print $ show $ getModelDictionary negated
                  case (getModelAssignment negated) of
                    Right (_, assg :: [Integer]) -> do
                      print $ show assg
                    Left msg -> print $ show msg
                  -}
                   NotValid $ "is" <+> pprint (show (ThmResult thmRes)) <+> "assignment" <+> pprint (show assg)
            Right (True, _) -> NotValid "returned probable model."
            Left str -> OtherSolverError (pprint str)


-- | Compile constraint into an SBV symbolic bool, along with a list of
-- | constraints which are trivially unequal (if such things exist) (e.g., things like 1=0).
compileToSBV :: Pred -> Symbolic SBool
compileToSBV predicate = buildTheorem' [] predicate

  where

    -- Build the theorem, doing local creation of universal variables
    -- when needed (see Impl case)
    buildTheorem' :: Ctxt SGrade -> Pred -> Symbolic SBool
    buildTheorem' solverVars (Conj ps) = do
      ps' <- mapM (buildTheorem' solverVars) ps
      return $ sAnd ps'

    buildTheorem' solverVars (Disj ps) = do
      ps' <- mapM (buildTheorem' solverVars) ps
      return $ sOr ps'

    buildTheorem' solverVars (Impl p1 p2) = do
        p1' <- buildTheorem' solverVars p1
        p2' <- buildTheorem' solverVars p2
        return $ p1' .=> p2'

    buildTheorem' solverVars (Neg p) = do
        p' <- buildTheorem' solverVars p
        return $ sNot p'

    buildTheorem' solverVars (Exists v t p) =
       freshCVarScoped compileQuantScoped (ident v) t InstanceQ
            (\(varPred, solverVar) -> do
              pred' <- buildTheorem' ((v, solverVar) : solverVars) p
              return (varPred .&& pred'))

    buildTheorem' solverVars (Forall v t p) =
        freshCVarScoped compileQuantScoped (ident v) t ForallQ
            (\(varPred, solverVar) -> do
              pred' <- buildTheorem' ((v, solverVar) : solverVars) p
              return (varPred .=> pred'))

    buildTheorem' solverVars (Con cons) =
      compile solverVars cons

freshCVarScoped ::
    (forall a . QuantifiableScoped a => Quantifier -> String -> (SBV a -> Symbolic SBool) -> Symbolic SBool)
  -> String
  -> GradeSpec
  -> Quantifier
  -> ((SBool, SGrade) -> Symbolic SBool)
  -> Symbolic SBool
freshCVarScoped quant name (Interval t) q k =

  freshCVarScoped quant (name ++ ".lower") t q
   (\(predLb, solverVarLb) ->
      freshCVarScoped quant (name ++ ".upper") t q
       (\(predUb, solverVarUb) -> do
          -- Respect the meaning of intervals
          lessEq <- symGradeLessEq solverVarLb solverVarUb
          k ( predLb .&& predUb .&& lessEq
            , SInterval solverVarLb solverVarUb )
          ))

freshCVarScoped quant name PrivacyLevel q k =
  quant q name (\solverVar ->
    k (solverVar .== literal 1
                  .|| solverVar .== literal 2
                  .|| solverVar .== literal 0
                    , SLevel solverVar))

freshCVarScoped quant name ExactUsage q k =
  quant q name (\solverVar -> k (solverVar .>= 0, SNat solverVar))

freshCVarScoped quant name (Extended ExactUsage) q k =
   quant q name (\solverVar ->
    k (SNatX.representationConstraint solverVar
     , SExtNat (SNatX.SNatX solverVar)))

freshCVarScoped _ _ t _ _ =
  solverError $ "Trying to make a fresh solver variable for a grade of type: "
      ++ show t ++ " but I don't know how."

-- | What is the SBV representation of a quantifier
compileQuantScoped :: QuantifiableScoped a => Quantifier -> String -> (SBV a -> Symbolic SBool) -> Symbolic SBool
compileQuantScoped ForallQ = universalScoped
compileQuantScoped _ = existentialScoped

-- | Represents symbolic values which can be quantified over inside the solver
-- | Mostly this just overrides to SBV's in-built quantification, but sometimes
-- | we want some custom things to happen when we quantify
class QuantifiableScoped a where
  universalScoped :: String -> (SBV a -> Symbolic SBool) -> Symbolic SBool
  existentialScoped :: String -> (SBV a -> Symbolic SBool) -> Symbolic SBool

instance QuantifiableScoped Integer where
  universalScoped v = forAll [v]
  existentialScoped v = forSome [v]

instance QuantifiableScoped Float where
  universalScoped v = forAll [v]
  existentialScoped v = forSome [v]

-- Compile a constraint into a symbolic bool (SBV predicate)
compile :: Ctxt SGrade -> Constraint -> Symbolic SBool

compile vars (Eq c1 c2 t) =
  bindM2And' eqConstraint (compileCoeffect c1 t vars) (compileCoeffect c2 t vars)

-- Assumes that c3 is already existentially bound
compile vars (Lub c1 c2 c3@(GExpr (Var v)) t) =

  case t of
    {-
    -- An alternate procedure for computing least-upper bounds
    -- I was experimenting with this to see if it could speed up solving.
    -- For largely symbolic constraints, it doesn't seem to make much difference.

    -- Use the join when `extendedNat` is involved
    (isInterval -> Just t') | t' == extendedNat -> do
      (s1, p1) <- compileCoeffect c1 t vars
      (s2, p2) <- compileCoeffect c2 t vars
      (s3, p3) <- compileCoeffect c3 t vars
      lub   <- s1 `symGradeJoin` s2
      eq    <- s3 `symGradeEq` lub
      return (p1 .&& p2 .&& p3 .&& eq) -}

    _ -> do
      (s1, p1) <- compileCoeffect c1 t vars
      (s2, p2) <- compileCoeffect c2 t vars
      (s3, p3) <- compileCoeffect c3 t vars
      -- s3 is an upper bound
      pa1 <- approximatedByOrEqualConstraint s1 s3
      pb1 <- approximatedByOrEqualConstraint s2 s3
      --- and it is the least such upper bound
      pc <- freshCVarScoped compileQuantScoped (ident v ++ ".up") t ForallQ
              (\(py, y) -> do
                pc1 <- approximatedByOrEqualConstraint s1 y
                pc2 <- approximatedByOrEqualConstraint s2 y
                pc3 <- approximatedByOrEqualConstraint s3 y
                return ((py .&& pc1 .&& pc2) .=> pc3))
      return (p1 .&& p2 .&& p3 .&& pa1 .&& pb1 .&& pc)

compile vars (ApproximatedBy c1 c2 t) =
  bindM2And' approximatedByOrEqualConstraint (compileCoeffect c1 t vars) (compileCoeffect c2 t vars)

compile _vars c = error $ "Internal bug: cannot compile " ++ show c

-- | Compile a grade term into its symbolic representation
-- | (along with any additional predicates)
compileCoeffect :: Grade' -> GradeSpec -> Ctxt SGrade -> Symbolic (SGrade, SBool)

compileCoeffect (GSig g gspec) _ ctxt = compileCoeffect g gspec ctxt

compileCoeffect (GEnc i) PrivacyLevel _ =
  return (SLevel . fromInteger . toInteger $ i, sTrue)

compileCoeffect (GEnc i) ExactUsage _ =
  return (SNat  . fromInteger . toInteger $ i, sTrue)

-- An implicit has gotten through so resolve it to just Nat
compileCoeffect (GEnc i) GSImplicit _ | i == 0 || i == 1 =
  return (SNat  . fromInteger . toInteger $ i, sTrue)

compileCoeffect (GEnc i) (Extended ExactUsage) _ =
  return (SExtNat . fromInteger . toInteger $ i, sTrue)

compileCoeffect (GEnc i) (Interval gspec) vars =
  liftM2And SInterval
        (compileCoeffect (GEnc i) gspec vars)
        (compileCoeffect (GEnc i) gspec vars)

compileCoeffect (GExpr (Var v)) _ vars =
   case lookup v vars of
    Just cvar -> return (cvar, sTrue)
    _ -> solverError $ "Looking up a variable '" ++ show v ++ "' in " ++ show vars

compileCoeffect (GLub n m) k vars =
  bindM2And symGradeJoin (compileCoeffect n k vars) (compileCoeffect m k vars)

compileCoeffect (GPlus n m) k vars =
  bindM2And symGradePlus (compileCoeffect n k vars) (compileCoeffect m k vars)

compileCoeffect (GTimes n m) k vars =
  bindM2And symGradeTimes (compileCoeffect n k vars) (compileCoeffect m k vars)

compileCoeffect (GExpr (App (App (Var (ident -> "Interval")) lb) ub)) (Interval t) vars = do
  (lower, p1) <- compileCoeffect (GExpr lb) t vars
  (upper, p2) <- compileCoeffect (GExpr ub) t vars
  intervalConstraint <- symGradeLessEq lower upper
  return $ (SInterval lower upper, p1 .&& p2 .&& intervalConstraint)

-- Turns a natural number into its representation using 0 and 1 +
compileCoeffect (GEnc i) t vars | i >= 2 =
  compileCoeffect (injection i) t vars
    where
      injection 0 = GEnc 0
      injection 1 = GEnc 1
      injection i | i > 1 = GPlus (GEnc 1) (injection (i-1))
      injection i = error $ "Cannot interpreter integer " ++ show i ++ " for " ++ pprintShow t

compileCoeffect grade ty _ =
   solverError $ "Can't compile a grade: " ++ pprintShow grade ++ " {" ++ (show grade) ++ "}"
        ++ " of ty " ++ pprintShow ty

-- | Generate equality constraints for two symbolic grades
eqConstraint :: SGrade -> SGrade -> Symbolic SBool
eqConstraint (SNat n) (SNat m)     = return $ n .== m
eqConstraint (SLevel l) (SLevel k) = return $ l .== k
eqConstraint (SExtNat x) (SExtNat y) = return $ x .== y
eqConstraint SPoint SPoint           = return sTrue

eqConstraint (SInterval lb1 ub1) (SInterval lb2 ub2) =
  liftM2 (.&&) (eqConstraint lb1 lb2) (eqConstraint ub1 ub2)

eqConstraint x y =
  solverError $ "Kind error trying to generate equality " ++ show x ++ " = " ++ show y

-- | Generate less-than-equal constraints for two symbolic grades
approximatedByOrEqualConstraint :: SGrade -> SGrade -> Symbolic SBool
approximatedByOrEqualConstraint (SNat n) (SNat m)      = return $ n .== m
approximatedByOrEqualConstraint SPoint SPoint          = return $ sTrue
approximatedByOrEqualConstraint (SExtNat x) (SExtNat y) = return $ x .== y

approximatedByOrEqualConstraint (SLevel l) (SLevel k) =
    -- Private <= Public
  return
    $ ite (l .== literal 0) sTrue
      $ ite (l .== literal 1) sTrue
        $ ite (k .== literal 2) sTrue sFalse

-- Perform approximation when nat-like grades are involved
-- e.g. [2..3] <= [0..10]  iff (0 <= 2 and 3 <= 10)
approximatedByOrEqualConstraint (SInterval lb1 ub1) (SInterval lb2 ub2)
    | natLike lb1 || natLike lb2 || natLike ub1 || natLike ub2 =
  liftM2 (.&&) (symGradeLessEq lb2 lb1) (symGradeLessEq ub1 ub2)

-- if intervals are not nat-like then use the notion of approximation
-- given here
approximatedByOrEqualConstraint (SInterval lb1 ub1) (SInterval lb2 ub2) =
  liftM2 (.&&) (approximatedByOrEqualConstraint lb2 lb1)
                (approximatedByOrEqualConstraint ub1 ub2)

approximatedByOrEqualConstraint x y =
  solverError $ "Error trying to generate " ++ show x ++ " <= " ++ show y

-- Useful combinators here
-- Generalises `bindM2` to functions which return also a symbolic grades
-- which should be combined via .&&
bindM2And :: Monad m => (t1 -> t2 -> m b) -> m (t1, SBool) -> m (t2, SBool) -> m (b, SBool)
bindM2And k ma mb = do
  (a, p) <- ma
  (b, q) <- mb
  c <- k a b
  return (c, p .&& q)

bindM2And' :: Monad m => (t1 -> t2 -> m SBool) -> m (t1, SBool) -> m (t2, SBool) -> m SBool
bindM2And' k ma mb = do
  (a, p) <- ma
  (b, q) <- mb
  c <- k a b
  return (p .&& q .&& c)

liftM2And :: Monad m => (t1 -> t2 -> b) -> m (t1, SBool) -> m (t2, SBool) -> m (b, SBool)
liftM2And k = bindM2And (\a b -> return (k a b))