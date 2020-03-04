module Language.Dlam.Syntax.Free
  ( Free(..)
  ) where


import qualified Data.Set as Set

import qualified Language.Dlam.Syntax.Concrete as C


class Free t where
  freeVars  :: t -> Set.Set C.Name


instance (Free a, Free b) => Free (a, b) where
  freeVars (x, y) = freeVars x `Set.union` freeVars y


freeVarsAbs :: C.Abstraction -> Set.Set C.Name
freeVarsAbs ab = Set.delete (C.absVar ab) (freeVars (C.absExpr ab))


instance Free C.Expr where
  freeVars (C.FunTy ab)                    = freeVarsAbs ab
  freeVars (C.Abs ab)                      = freeVarsAbs ab
  freeVars (C.ProductTy ab)                = freeVarsAbs ab
  freeVars (C.App e1 e2)                   = freeVars (e1, e2)
  freeVars (C.Pair e1 e2)                  = freeVars (e1, e2)
  freeVars (C.Coproduct t1 t2) = freeVars (t1, t2)
  freeVars (C.CoproductCase (_z, _tC) (x, c) (y, d) _e) =
    Set.delete x (Set.delete y (freeVars (c, d)))
  freeVars (C.NatCase (x, tC) cz (w, y, cs) _n) =
    (Set.delete x (freeVars tC)) `Set.union` (freeVars cz) `Set.union` (Set.delete w $ Set.delete y $ freeVars cs)
  freeVars (C.Var var)                     = Set.singleton var
  freeVars (C.Sig e _)                     = freeVars e
  freeVars (C.PairElim (z, tC) (x, y, g) p) =
    Set.delete z (Set.delete x (Set.delete y (freeVars (g, (p, tC)))))
  freeVars (C.RewriteExpr (x, y, p, tC) (z, c) a b p') =
    (Set.delete x (Set.delete y (Set.delete p (freeVars tC)))) `Set.union` (Set.delete z (freeVars c)) `Set.union` (freeVars (a, (b, p')))
  freeVars (C.UnitElim (x, tC) c a)        = Set.delete x $ freeVars (tC, (c, a))
  freeVars (C.EmptyElim (x, tC) a)         = Set.delete x $ freeVars (tC, a)
  freeVars C.Hole                          = Set.empty
  freeVars C.Implicit                      = Set.empty
  freeVars C.LitLevel{}                    = Set.empty
  freeVars C.Builtin{}                     = Set.empty
