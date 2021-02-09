module Language.Dlam.TypeChecking.Monad.Exception
  ( TCError(..)
  , SolverError
  , solverError'
  ) where

import Language.Dlam.Syntax.Abstract
import Language.Dlam.Syntax.Parser.Monad (ParseError)

import qualified Language.Dlam.Scoping.Monad.Exception as SE
import Language.Dlam.TypeChecking.Monad.Grading (Stage(..))

import Language.Dlam.Util.Pretty hiding ((<>))


data TCError
  ---------------------------
  -- Implementation Errors --
  ---------------------------

  = NotImplemented Doc

  | InternalBug Doc

  ------------------
  -- Scope Errors --
  ------------------

  | ScoperError SE.SCError

  ------------------
  -- Synth Errors --
  ------------------

  | CannotSynthTypeForExpr

  | CannotSynthExprForType Expr

  -----------------
  -- Type Errors --
  -----------------

  | TypeMismatch Expr Expr

  | ExpectedInferredTypeForm Doc Expr

  --------------------
  -- Pattern Errors --
  --------------------

  | PatternMismatch Pattern Expr

  --------------------
  -- Grading Errors --
  --------------------

  | GradeMismatch Stage [(Name, (Grade, Grade))]

  | GradeTypeMismatch GradeSpec GradeSpec

  | SolverNotValid Doc

  | SolverError Doc

  | SolverTimeout

  ------------------
  -- Parse Errors --
  ------------------

  | ParseError ParseError


-- for now, this is just an alias for a type-checker error, but we can
-- separate this out if desired (2020-06-26)
type SolverError = TCError


instance Pretty TCError where
  pprint (NotImplemented e) = e
  pprint CannotSynthTypeForExpr = "I couldn't synthesise a type for the expression."
  pprint (CannotSynthExprForType t) =
    "I was asked to try and synthesise a term of type" <+> quoted t <+> parens ("internal rep:" <+> pprint t) <+> "but I wasn't able to do so."
  pprint (TypeMismatch tyExpected tyActual) =
    "Expected type" <+> quoted tyExpected <+> "but got" <+> quoted tyActual
  pprint (GradeTypeMismatch tyExpected tyActual) =
    "Expected (grade) type" <+> quoted tyExpected <+> "but got" <+> quoted tyActual
  pprint (GradeMismatch stage mismatches) =
    hang ("At" <+> pprint stage <+> "stage got the following mismatched grades:") 1
    (vcat $ fmap (\(v, (e, a)) -> "For" <+> quoted v <+> "expected" <+> pprint e <+> "but got" <+> pprint a) mismatches)
  pprint (SolverError msg)    = msg
  pprint (SolverNotValid msg) = msg
  pprint SolverTimeout = "Solver timeout"
  pprint (ExpectedInferredTypeForm descr t) =
    "I was expecting the expression to have a" <+> descr <+>
                        "type, but instead I found its type to be" <+> quoted t
  pprint (PatternMismatch p t) =
    "The pattern" <+> quoted p <+> "is not valid for type" <+> quoted t

  pprint (ParseError e) = pprint e
  pprint (ScoperError e) = pprint e
  pprint (InternalBug e) = "Internal error:" <+> e


solverError' :: Doc -> SolverError
solverError' = SolverError
