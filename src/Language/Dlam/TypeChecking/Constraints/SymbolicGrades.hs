{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE FlexibleContexts #-}

{- Provides a symbolic representation of grades (coeffects, effects, indices)
   in order for a solver to use.
-}
module Language.Dlam.TypeChecking.Constraints.SymbolicGrades
  (
  -- * IOSolver
    IOSolver
  , runIOSolver
  , solverError
  , Symbolic

  -- * Grades
  , SGrade(..)
  , match
  , natLike
  , symGradeLess
  , symGradeGreater
  , symGradeLessEq
  , symGradeGreaterEq
  , symGradeMeet
  , symGradeJoin
  , symGradePlus
  , symGradeTimes
  )
  where


import Control.Monad (liftM2)
import Control.Monad.Except (ExceptT, MonadError, throwError, runExceptT)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.SBV hiding (kindOf, name, symbolic, Symbolic)
import GHC.Generics (Generic)


import Language.Dlam.TypeChecking.Constraints.SNatX
import Language.Dlam.TypeChecking.Monad.Exception (SolverError, solverError')
import Language.Dlam.Util.Pretty (Doc, pprint, pprintShow, quoted, (<+>))


type IOSolver = ExceptT SolverError IO
type Symbolic = SymbolicT IOSolver


solverError :: (MonadError SolverError m) => Doc -> m a
solverError = throwError . solverError'


runIOSolver :: (MonadIO m) => IOSolver a -> m (Either SolverError a)
runIOSolver = liftIO . runExceptT


-- Symbolic grades, for coeffects and indices
data SGrade =
       SNat      SInteger
     | SLevel    SInteger
     | SecLevel  SInteger
     | SExtNat   { sExtNat :: SNatX }
     | SInterval { sLowerBound :: SGrade, sUpperBound :: SGrade }
     -- Single point coeffect (not exposed at the moment)
     | SPoint
    deriving (Show, Generic)

-- Work out if two symbolic grades are of the same type
match :: SGrade -> SGrade -> Bool
match (SNat _) (SNat _) = True
match (SLevel _) (SLevel _) = True
match (SecLevel _) (SecLevel _) = True
match (SExtNat _) (SExtNat _) = True
match (SInterval s1 s2) (SInterval t1 t2) = match s1 t1 && match s2 t2
match SPoint SPoint = True
match _ _ = False

natLike :: SGrade -> Bool
natLike (SNat _) = True
natLike (SExtNat _) = True
natLike _ = False

instance Mergeable SGrade where
  symbolicMerge s sb (SNat n) (SNat n') = SNat (symbolicMerge s sb n n')
  symbolicMerge s sb (SLevel n) (SLevel n') = SLevel (symbolicMerge s sb n n')
  symbolicMerge s sb (SecLevel n) (SecLevel n') = SecLevel (symbolicMerge s sb n n')
  symbolicMerge s sb (SExtNat n) (SExtNat n') = SExtNat (symbolicMerge s sb n n')
  symbolicMerge s sb (SInterval lb1 ub1) (SInterval lb2 ub2) =
    SInterval (symbolicMerge s sb lb1 lb2) (symbolicMerge s sb ub1 ub2)
  symbolicMerge _s _sb SPoint SPoint = SPoint

  symbolicMerge _ _ s t = error . pprintShow $ cannotDo "symbolicMerge" s t

symGradeLess :: SGrade -> SGrade -> Symbolic SBool
symGradeLess (SInterval lb1 ub1) (SInterval lb2 ub2) =
  liftM2 (.&&) (symGradeLess lb2 lb1) (symGradeLess ub1 ub2)

symGradeLess (SNat n) (SNat n')     = return $ n .< n'
symGradeLess (SLevel n) (SLevel n') = return $ n .< n'
symGradeLess (SecLevel n) (SecLevel n') = return $ n .< n'
symGradeLess (SExtNat n) (SExtNat n') = return $ n .< n'
symGradeLess SPoint SPoint            = return sTrue
symGradeLess s t = solverError $ cannotDo ".<" s t

symGradeGreater :: SGrade -> SGrade -> Symbolic SBool
symGradeGreater x y = symGradeLess y x

symGradeLessEq :: SGrade -> SGrade -> Symbolic SBool
symGradeLessEq x y = lazyOrSymbolicM (symGradeEq x y) (symGradeLess x y)

symGradeGreaterEq :: SGrade -> SGrade -> Symbolic SBool
symGradeGreaterEq x y = lazyOrSymbolicM (symGradeEq x y) (symGradeGreater x y)

-- A short-circuiting disjunction for effectful computations that
-- produce symoblic bools (a kind of expanded `iteLazy` for Symbolic monad)
lazyOrSymbolicM :: Symbolic SBool -> Symbolic SBool -> Symbolic SBool
lazyOrSymbolicM m1 m2 = m1 >>= \b1 ->
  case unliteral b1 of
    Just True -> return sTrue
    _         -> m2 >>= \b2 -> return $ symbolicMerge False b1 sTrue b2

symGradeEq :: SGrade -> SGrade -> Symbolic SBool
symGradeEq (SInterval lb1 ub1) (SInterval lb2 ub2) =
  liftM2 (.&&) (symGradeEq lb2 lb1) (symGradeEq ub1 ub2)

symGradeEq (SNat n) (SNat n')     = return $ n .== n'
symGradeEq (SLevel n) (SLevel n') = return $ n .== n'
symGradeEq (SecLevel n) (SecLevel n') = return $ n .== n'
symGradeEq (SExtNat n) (SExtNat n') = return $ n .== n'
symGradeEq SPoint SPoint          = return $ sTrue
symGradeEq s t = solverError $ cannotDo ".==" s t

-- | Meet operation on symbolic grades
symGradeMeet :: SGrade -> SGrade -> Symbolic SGrade
symGradeMeet (SNat n1) (SNat n2)     = return $ SNat $ n1 `smin` n2
symGradeMeet (SLevel s) (SLevel t)   = return $ SLevel $ s `smin` t
symGradeMeet (SecLevel s) (SecLevel t)   = return $ SecLevel $ s `smin` t
symGradeMeet (SExtNat x) (SExtNat y) = return $ SExtNat $
  ite (isInf x) y (ite (isInf y) x (SNatX (xVal x `smin` xVal y)))
symGradeMeet (SInterval lb1 ub1) (SInterval lb2 ub2) =
  liftM2 SInterval (lb1 `symGradeJoin` lb2) (ub1 `symGradeMeet` ub2)
symGradeMeet SPoint SPoint = return SPoint
symGradeMeet s t = solverError $ cannotDo "meet" s t

-- | Join operation on symbolic grades
symGradeJoin :: SGrade -> SGrade -> Symbolic SGrade
symGradeJoin (SNat n1) (SNat n2) = return $ SNat (n1 `smax` n2)
symGradeJoin (SLevel s) (SLevel t) = return $ SLevel $ s `smax` t
symGradeJoin (SecLevel s) (SecLevel t) = return $ SecLevel $ s `smax` t
symGradeJoin (SExtNat x) (SExtNat y) = return $ SExtNat $
  ite (isInf x .|| isInf y) inf (SNatX (xVal x `smax` xVal y))
symGradeJoin (SInterval lb1 ub1) (SInterval lb2 ub2) =
   liftM2 SInterval (lb1 `symGradeMeet` lb2) (ub1 `symGradeJoin` ub2)
symGradeJoin SPoint SPoint = return SPoint
symGradeJoin s t = solverError $ cannotDo "join" s t

-- | Plus operation on symbolic grades
symGradePlus :: SGrade -> SGrade -> Symbolic SGrade
symGradePlus (SNat n1) (SNat n2) = return $ SNat (n1 + n2)
symGradePlus (SLevel lev1) (SLevel lev2) = return $ SLevel $ lev1 `smax` lev2
symGradePlus (SecLevel lev1) (SecLevel lev2) = return $ SecLevel $ lev1 `smax` lev2
symGradePlus (SExtNat x) (SExtNat y) = return $ SExtNat (x + y)
symGradePlus (SInterval lb1 ub1) (SInterval lb2 ub2) =
    liftM2 SInterval (lb1 `symGradePlus` lb2) (ub1 `symGradePlus` ub2)
symGradePlus SPoint SPoint = return $ SPoint
symGradePlus s t = solverError $ cannotDo "plus" s t

-- | Times operation on symbolic grades
symGradeTimes :: SGrade -> SGrade -> Symbolic SGrade
symGradeTimes (SNat n1) (SNat n2) = return $ SNat (n1 * n2)
-- these would be ill-kinded multiplications (GD: 2020-07-01)
-- symGradeTimes (SNat n1) (SExtNat (SNatX n2)) = return $ SExtNat $ SNatX (n1 * n2)
-- symGradeTimes (SExtNat (SNatX n1)) (SNat n2) = return $ SExtNat $ SNatX (n1 * n2)
symGradeTimes (SLevel lev1) (SLevel lev2) = return $
    ite (lev1 .== literal 0)
        (SLevel $ literal 0)
      $ ite (lev2 .== literal 0)
            (SLevel $ literal 0)
            (SLevel $ lev1 `smax` lev2)
symGradeTimes (SecLevel lev1) (SecLevel lev2) = return $
    ite (lev1 .== literal 0) (SecLevel $ literal 0) (SecLevel lev2)
symGradeTimes (SExtNat x) (SExtNat y) = return $ SExtNat (x * y)

symGradeTimes (SInterval lb1 ub1) (SInterval lb2 ub2) =
    liftM2 SInterval (comb symGradeMeet) (comb symGradeJoin)
     where
      comb f = do
        lb1lb2 <- lb1 `symGradeTimes` lb2
        lb1ub2 <- lb1 `symGradeTimes` ub2
        ub1lb2 <- ub1 `symGradeTimes` lb2
        ub1ub2 <- ub1 `symGradeTimes` ub2
        a <- lb1lb2 `f` lb1ub2
        b <- a `f` ub1lb2
        b `f` ub1ub2

symGradeTimes SPoint SPoint = return SPoint
symGradeTimes s t = solverError $ cannotDo "times" s t

cannotDo :: Doc -> SGrade -> SGrade -> Doc
cannotDo op s t =
  "Cannot perform symbolic operation"
      <+> quoted op <+> "on"
      <+> pprint (show s) <+> "and"
      <+> pprint (show t)
