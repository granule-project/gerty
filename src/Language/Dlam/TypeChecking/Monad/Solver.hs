module Language.Dlam.TypeChecking.Monad.Solver
  (
  -- * Predicate
    isTheoremValid
  , isTheoremValidBool
  ) where


import Control.Monad.IO.Class (liftIO)


import Language.Dlam.TypeChecking.Constraints
import Language.Dlam.TypeChecking.Monad.Base
import Language.Dlam.TypeChecking.Predicates
import Language.Dlam.Util.Pretty (pprint)


------------------------------
----- Predicate building -----
------------------------------


isTheoremValid :: CM SolverResult
isTheoremValid = do
  ps <- getPredicateStack
  let thm = Conj (reverse ps)
  debug $ "Asking SMT solver if the following is valid: " <> pprint thm
  liftIO $ provePredicate thm


isTheoremValidBool :: CM Bool
isTheoremValidBool = do
  result <- isTheoremValid
  case result of
    QED -> return True
    _   -> return False
