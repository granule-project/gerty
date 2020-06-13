module Language.Dlam.Syntax.Free
  ( Free(..)
  ) where


import qualified Data.Set as Set

import qualified Language.Dlam.Syntax.Abstract as A


class Free t where
  freeVars  :: t -> Set.Set A.Name


instance (Free a, Free b) => Free (a, b) where
  freeVars (x, y) = freeVars x `Set.union` freeVars y


freeVarsAbs :: A.Abstraction -> Set.Set A.Name
freeVarsAbs ab = Set.delete (A.absVar ab) (freeVars (A.absExpr ab))


instance Free A.Expr where
  freeVars (A.FunTy ab)                    = freeVarsAbs ab
  freeVars (A.Lam ab)                      = freeVarsAbs ab
  freeVars (A.ProductTy ab)                = freeVarsAbs ab
  freeVars (A.App e1 e2)                   = freeVars (e1, e2)
  freeVars (A.Pair e1 e2)                  = freeVars (e1, e2)
  freeVars (A.NatCase (x, tC) cz (w, y, cs) _n) =
    (Set.delete x (freeVars tC)) `Set.union` (freeVars cz) `Set.union` (Set.delete w $ Set.delete y $ freeVars cs)
  freeVars (A.Var var)                     = Set.singleton var
  freeVars (A.Def _)                       = Set.empty
  freeVars (A.Sig e _)                     = freeVars e
  freeVars (A.EmptyElim (x, tC) a)         = Set.delete x $ freeVars (tC, a)
  freeVars (A.Universe l)                  = freeVars l
  freeVars A.Hole                          = Set.empty
  freeVars A.Implicit                      = Set.empty
  freeVars A.Builtin{}                     = Set.empty
  freeVars (A.Let pb e) = Set.difference (freeVars e) (boundVars pb)
    where boundVars (A.LetPatBound p _) =
            Set.map A.unBindName $ A.boundSubjectVars p <> A.boundTypingVars p


instance Free A.Level where
  freeVars A.LInfer{} = Set.empty
  freeVars A.LitLevel{} = Set.empty
