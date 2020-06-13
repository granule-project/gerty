{-# LANGUAGE ViewPatterns #-}
module Language.Dlam.Builtins
  (

  -- * Collected builtins
    builtins
  , builtinsTypes
  , builtinsValues

  -- * Grades
  , gradeZero
  , gradeOne
  , gradeAdd
  , gradeMult
  , gradeIsZero

  -- * Builtin definitions

  , Builtin
  , builtinName
  , builtinBody
  , builtinType

  -- ** Type Universes
  , mkUnivTy

  -- ** Natural numbers
  , natTy
  , dnzero
  , dnsucc
  , dnsuccApp

  -- ** Unit
  , unitTy
  , unitTerm
  ) where


import qualified Data.Map as M

import Language.Dlam.Syntax.Abstract
import Language.Dlam.Util.Pretty (pprintShow)


-- | The list of builtins.
builtins :: [Builtin]
builtins =
   [ natTy, dnzero, dnsucc
   , unitTerm, unitTy
   ]


builtinsTypes :: M.Map Name Expr
builtinsTypes = M.fromList
  (fmap (\bin -> (builtinName bin, builtinType bin)) builtins)


builtinsValues :: M.Map Name Expr
builtinsValues = M.fromList
  (fmap (\bin -> (builtinName bin, builtinBody bin)) builtins)


-------------------------------
----- Builtin definitions -----
-------------------------------


newtype Builtin = MkBuiltin (Name, BuiltinTerm, Expr)

mkBuiltin :: BuiltinTerm -> Expr -> Builtin
mkBuiltin exprRef ty = MkBuiltin (mkIdent (pprintShow exprRef), exprRef, ty)

-- | Syntactic name of a builtin term.
builtinName :: Builtin -> Name
builtinName (MkBuiltin (n, _, _)) = n

-- | Body for a builtin term (essentially an Agda postulate).
builtinBody :: Builtin -> Expr
builtinBody (MkBuiltin (_, e, _)) = Builtin e

-- | The type of a builtin term.
builtinType :: Builtin -> Expr
builtinType (MkBuiltin (_, _, t)) = t


mkFunTy :: Name -> Expr -> Expr -> Expr
mkFunTy n t e = FunTy $ mkAbs n t e

typeZero, natTy' :: Expr
typeZero = mkUnivTy (LitLevel 0)

mkApp :: Expr -> Expr -> Expr
mkApp = App

unitTy, unitTerm,
 natTy, dnzero, dnsucc :: Builtin

unitTy = mkBuiltin DUnitTy typeZero

unitTerm = mkBuiltin DUnitTerm (builtinBody unitTy)

natTy = mkBuiltin DNat typeZero
natTy' = builtinBody natTy
dnzero = mkBuiltin DNZero natTy'
dnsucc = mkBuiltin DNSucc (mkFunTy ignoreVar natTy' natTy')


mkUnivTy :: Level -> Expr
mkUnivTy = Universe

dnsuccApp :: Expr -> Expr
dnsuccApp = mkApp (builtinBody dnsucc)


------------------
----- Grades -----
------------------


gradeZero, gradeOne :: Grade
--gradeZero = Builtin DNZero
--gradeOne  = App (Builtin DNSucc) gradeZero
gradeZero = Def (mkIdent "zero")
gradeOne = App (Def (mkIdent "succ")) gradeZero


gradeAdd :: Grade -> Grade -> Grade
gradeAdd x y | gradeIsZero x = y
gradeAdd (App (Def (ident -> "succ")) x) y =
  App (Def (mkIdent "succ")) (gradeAdd x y)
--gradeAdd (App (Builtin DNSucc) x) y =
--  App (Builtin DNSucc) (gradeAdd x y)
-- Cannot apply induction
gradeAdd x y =
 App (App (Def (mkIdent "+r")) x) y


gradeMult :: Grade -> Grade -> Grade
gradeMult x _ | gradeIsZero x = gradeZero
gradeMult (App (Def (ident -> "succ")) x) y =
  gradeAdd y (gradeMult x y)
-- gradeMult (App (Builtin DNSucc) x) y =
--   gradeAdd y (gradeMult x y)
-- Cannot apply induction
gradeMult x y =
 App (App (Def (mkIdent "*r")) x) y


gradeIsZero :: Grade -> Bool
gradeIsZero (Def (ident -> "zero")) = True
gradeIsZero (Builtin DNZero) = True
gradeIsZero _ = False
