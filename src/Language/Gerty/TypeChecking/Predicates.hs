{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}

module Language.Gerty.TypeChecking.Predicates where

import Language.Gerty.Syntax.Abstract
import Language.Gerty.Util.Pretty

import Prelude hiding ((<>))

{-

This module provides the representation of theorems (predicates)
inside the type checker.

-}

import GHC.Generics (Generic)

-- Represents a predicate generated by the type checking algorithm
data Pred where
    Conj   :: [Pred] -> Pred
    Disj   :: [Pred] -> Pred
    Impl   :: Pred -> Pred -> Pred
    Con    :: Constraint -> Pred
    Neg    :: Pred -> Pred
    Forall :: Name -> GradeSpec -> Pred -> Pred
    Exists :: Name -> GradeSpec -> Pred -> Pred
    deriving (Show, Eq)

-- Represent constraints generated by the type checking algorithm
data Constraint =
    Eq             Grade' Grade' GradeSpec
  | ApproximatedBy Grade' Grade' GradeSpec

  deriving (Show, Eq, Generic)

instance Pretty Constraint where
  pprint (Eq c1 c2 _) =
      "(" <> pprint c1 <> " = " <> pprint c2 <> ")" -- @" <> show s

  pprint (ApproximatedBy c1 c2 k) =
      case k of
        -- Nat is discrete
        ExactUsage -> "(" <> pprint c1 <> " = " <> pprint c2 <> ")"
        _ -> "(" <> pprint c1 <> " ≤ " <> pprint c2 <> ")" -- <> " @ " <> pprintShow k

-- Fold operation on a predicate
predFold ::
     ([a] -> a)
  -> ([a] -> a)
  -> (a -> a -> a)
  -> (Constraint -> a)
  -> (a -> a)
  -> (Name -> GradeSpec -> a -> a)
  -> (Name -> GradeSpec -> a -> a)
  -> Pred
  -> a
predFold c d i a n fa e (Conj ps)   = c (map (predFold c d i a n fa e) ps)
predFold c d i a n fa e (Disj ps)   = d (map (predFold c d i a n fa e) ps)
predFold c d i a n fa e (Impl p p') = i (predFold c d i a n fa e p) (predFold c d i a n fa e p')
predFold _ _ _ a _  _ _ (Con cons)  = a cons
predFold c d i a n fa e (Neg p) = n (predFold c d i a n fa e p)
predFold c d i a n fa e (Forall x t p) = fa x t (predFold c d i a n fa e p)
predFold c d i a n fa e (Exists x t p) = e x t (predFold c d i a n fa e p)

instance Pretty Pred where
  pprint =
    predFold
     (cat . (punctuate " ∧ "))
     (cat . (punctuate " ∨ "))
     (\p q -> "(" <> p <> " -> " <> q <> ")")
     pprint
     (\p -> "¬(" <> p <> ")")
     (\x t p -> "∀ " <> pprint x <> " : " <> pprint t <> " . " $$ p)
     (\x t p -> "∃ " <> pprint x <> " : " <> pprint t <> " . " $$ p)

-- | Whether the predicate is empty, i.e. contains no constraints
isTrivial :: Pred -> Bool
isTrivial = predFold and or (\_lhs rhs -> rhs) (const False) id (\_ _ p -> p) (\_ _ p -> p)
