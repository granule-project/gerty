module Language.Dlam.Syntax.Free
  ( Free(..)
  ) where


import qualified Data.Set as Set

import qualified Language.Dlam.Syntax.Abstract as A


class Free t where
  freeVars  :: t -> Set.Set A.Name


instance (Free a, Free b) => Free (a, b) where
  freeVars (x, y) = freeVars x `Set.union` freeVars y


-- TODO: when support for first-class grades is added, ensure we check
-- grades for free variables (2020-06-20)
freeVarsAbs :: A.Abstraction -> Set.Set A.Name
freeVarsAbs ab = Set.delete (A.absVar ab) (freeVars (A.absExpr ab))


instance Free A.Expr where
  freeVars (A.FunTy ab)                    = freeVarsAbs ab
  -- TODO: when suporting first-class grades, ensure we check the
  -- grading here for free variables (2020-06-21)
  freeVars (A.BoxTy _ e)                   = freeVars e
  freeVars (A.Box e)                       = freeVars e
  freeVars (A.Lam ab)                      = freeVarsAbs ab
  freeVars (A.ProductTy ab)                = freeVarsAbs ab
  freeVars (A.App e1 e2)                   = freeVars (e1, e2)
  freeVars (A.Pair e1 e2)                  = freeVars (e1, e2)
  freeVars (A.Var var)                     = Set.singleton var
  freeVars (A.Def _)                       = Set.empty
  freeVars (A.Sig e _)                     = freeVars e
  freeVars (A.Universe l)                  = freeVars l
  freeVars A.Hole                          = Set.empty
  freeVars A.Implicit                      = Set.empty
  freeVars A.UnitTy                        = Set.empty
  freeVars A.Unit                          = Set.empty
  freeVars A.NatTy                         = Set.empty
  freeVars A.NZero                         = Set.empty
  freeVars A.NSucc                         = Set.empty
  freeVars (A.Case e pt binds) =
    freeVars e `Set.union`
      maybe Set.empty (\(p, t) -> withDiff t p) pt `Set.union`
      (Set.unions (fmap (\(A.CasePatBound p b) -> withDiff b p) binds))
    where withDiff e p = Set.difference (freeVars e)
            (Set.map A.unBindName $ A.boundSubjectVars p <> A.boundTypingVars p)


instance Free A.Level where
  -- NOTE: if we add support for level variables, this will need updating (2020-06-13)
  freeVars _ = Set.empty
