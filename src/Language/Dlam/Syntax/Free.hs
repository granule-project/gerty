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
  freeVars (A.Abs ab)                      = freeVarsAbs ab
  freeVars (A.ProductTy ab)                = freeVarsAbs ab
  freeVars (A.App e1 e2)                   = freeVars (e1, e2)
  freeVars (A.Pair e1 e2)                  = freeVars (e1, e2)
  freeVars (A.Coproduct t1 t2) = freeVars (t1, t2)
  freeVars (A.CoproductCase (_z, _tC) (x, c) (y, d) _e) =
    Set.delete x (Set.delete y (freeVars (c, d)))
  freeVars (A.NatCase (x, tC) cz (w, y, cs) _n) =
    (Set.delete x (freeVars tC)) `Set.union` (freeVars cz) `Set.union` (Set.delete w $ Set.delete y $ freeVars cs)
  freeVars (A.Var var)                     = Set.singleton var
  freeVars (A.Sig e _)                     = freeVars e
  freeVars (A.PairElim (z, tC) (x, y, g) p) =
    Set.delete z (Set.delete x (Set.delete y (freeVars (g, (p, tC)))))
  freeVars (A.RewriteExpr (x, y, p, tC) (z, c) a b p') =
    (Set.delete x (Set.delete y (Set.delete p (freeVars tC)))) `Set.union` (Set.delete z (freeVars c)) `Set.union` (freeVars (a, (b, p')))
  freeVars (A.UnitElim (x, tC) c a)        = Set.delete x $ freeVars (tC, (c, a))
  freeVars (A.EmptyElim (x, tC) a)         = Set.delete x $ freeVars (tC, a)
  freeVars A.Hole                          = Set.empty
  freeVars A.Implicit                      = Set.empty
  freeVars A.LitLevel{}                    = Set.empty
  freeVars A.Builtin{}                     = Set.empty
