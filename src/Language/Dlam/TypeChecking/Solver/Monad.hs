module Language.Dlam.TypeChecking.Solver.Monad
  ( SoMState
  , startSoMState
  , HasSolver(..)

  -- * Predicates
  , getPredicateStack
  , resetPredicateStack
  , addConstraint
  , existential
  , universal
  , concludeImplication
  , newConjunct
  ) where


import Control.Monad (unless)

import Language.Dlam.Syntax.Abstract
import Language.Dlam.TypeChecking.Predicates (Constraint, Pred(..))
import Language.Dlam.Util.Pretty hiding ((<>))


data SoMState = MkSoMState { predicateStack :: [Pred] }


startSoMState :: SoMState
startSoMState = MkSoMState { predicateStack = [] }


class (Monad m) => HasSolver m where
  getSolverState :: m SoMState
  modifySolverState :: (SoMState -> SoMState) -> m ()


getPredicateStack :: (HasSolver m) => m [Pred]
getPredicateStack = predicateStack <$> getSolverState


setPredicateStack :: (HasSolver m) => [Pred] -> m ()
setPredicateStack s = modifySolverState (\st -> st { predicateStack = s })

modifyPredicateStack :: (HasSolver m) => ([Pred] -> [Pred]) -> m ()
modifyPredicateStack f = getPredicateStack >>= setPredicateStack . f


resetPredicateStack :: (HasSolver m) => m ()
resetPredicateStack = setPredicateStack []


-- Add a constraint to the predicate stack
addConstraint :: (HasSolver m) => Constraint -> m ()
addConstraint c = do
  stack <- getPredicateStack
  unless (Conj [Con c] `elem` stack) $
    setPredicateStack
      (case stack of
         (p : stack) -> conjunctPred (Con c) p : stack
         stack -> Conj [Con c] : stack)


newConjunct :: (HasSolver m) => m ()
newConjunct =
  modifySolverState (\st -> st { predicateStack = Conj [] : predicateStack st })


concludeImplication :: (HasSolver m) => m ()
concludeImplication = modifyPredicateStack (\stack ->
  case stack of
    (p' : p : stack) -> conjunctPredStack (Impl p p') stack
    _ -> error "Predicate: not enough conjunctions on the stack")


-- Introduce a conjunction onto the the top of the predicate stack
conjunctPredStack :: Pred -> [Pred] -> [Pred]
conjunctPredStack p (p' : stack) = conjunctPred p p' : stack
conjunctPredStack p [] = [Conj [p]]


-- Introduce a conjunction (under the scope of binders)
conjunctPred :: Pred -> Pred -> Pred
conjunctPred p (Conj ps) = Conj (p : ps)
conjunctPred p (Forall var k ps) = Forall var k (conjunctPred p ps)
conjunctPred p (Exists var k ps) = Exists var k (conjunctPred p ps)
conjunctPred _ p = error $ "Cannot append a predicate to " <> pprintShow p


existential :: (HasSolver m) => Name -> GradeSpec -> m ()
existential var k = modifyPredicateStack (\stack ->
  case stack of
    (p : stack) -> Exists var k p : stack
    [] -> [Exists var k (Conj [])])


universal :: (HasSolver m) => Name -> GradeSpec -> m ()
universal var k = modifyPredicateStack (\stack ->
  case stack of
    (p : stack) -> Forall var k p : stack
    [] -> [Forall var k (Conj [])])
