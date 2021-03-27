module Language.Gerty.TypeChecking.Monad.Solver
  (
  -- * Predicate
    isTheoremValid
  , isTheoremValidBool
  ) where


import Language.Gerty.TypeChecking.Constraints
import Language.Gerty.TypeChecking.Constraints.SymbolicGrades (runIOSolver)
import Language.Gerty.TypeChecking.Monad.Base
import Language.Gerty.TypeChecking.Predicates
import Language.Gerty.Util.Pretty (hang, pprint)

------------------------------
----- Predicate building -----
------------------------------


isTheoremValid :: CM SolverResult
isTheoremValid = do
  ps <- getPredicateStack
  shouldSimplify <- shouldSimplifySMT
  let thm = if shouldSimplify then simplifyPred (Conj (reverse ps))
            else Conj (reverse ps)
  debug $ hang "Asking SMT solver if the following is valid:" 1 (pprint thm)
  sRes <- runIOSolver (provePredicate thm)
  either throwCM pure sRes


isTheoremValidBool :: CM Bool
isTheoremValidBool = do
  result <- isTheoremValid
  case result of
    QED -> return True
    _   -> return False
