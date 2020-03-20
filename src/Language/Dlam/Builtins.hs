module Language.Dlam.Builtins
  (

  -- * Collected builtins
    builtins
  , builtinsTypes
  , builtinsValues

  -- * Builtin definitions

  , Builtin
  , builtinName
  , builtinBody
  , builtinType

  -- ** Levels
  , levelTy
  , levelTy'
  , lzero
  , lsuc
  , lsucApp
  , lmax
  , lmaxApp

  -- ** Type Universes
  , mkUnivTy

  -- ** Coproducts
  , inlTerm
  , inlTermApp
  , inrTerm
  , inrTermApp

  -- ** Natural numbers
  , natTy
  , dnzero
  , dnsucc
  , dnsuccApp

  -- ** Unit
  , unitTy
  , unitTerm

  -- ** Empty type
  , emptyTy

  -- ** Identity
  , idTy
  , idTyApp
  , reflTerm
  , reflTermApp
  ) where


import qualified Data.Map as M

import Language.Dlam.Syntax.Abstract
import Language.Dlam.Util.Pretty (pprintShow)


-- | The list of builtins.
builtins :: [Builtin]
builtins =
   [ levelTy, lzero, lsuc, lmax
   , inlTerm, inrTerm
   , natTy, dnzero, dnsucc
   , unitTerm, unitTy
   , idTy, reflTerm
   , emptyTy
   ]


builtinsTypes :: M.Map AName Expr
builtinsTypes = M.fromList
  (fmap (\bin -> (builtinName bin, builtinType bin)) builtins)


builtinsValues :: M.Map AName Expr
builtinsValues = M.fromList
  (fmap (\bin -> (builtinName bin, builtinBody bin)) builtins)


-------------------------------
----- Builtin definitions -----
-------------------------------


newtype Builtin = MkBuiltin (AName, BuiltinTerm, Expr)

mkBuiltin :: BuiltinTerm -> Expr -> Builtin
mkBuiltin exprRef ty = MkBuiltin (mkIdent (pprintShow exprRef), exprRef, ty)

-- | Syntactic name of a builtin term.
builtinName :: Builtin -> AName
builtinName (MkBuiltin (n, _, _)) = n

-- | Body for a builtin term (essentially an Agda postulate).
builtinBody :: Builtin -> Expr
builtinBody (MkBuiltin (_, e, _)) = Builtin e

-- | The type of a builtin term.
builtinType :: Builtin -> Expr
builtinType (MkBuiltin (_, _, t)) = t


mkFunTy :: AName -> Expr -> Expr -> Expr
mkFunTy n t e = FunTy $ mkAbs n t e

typeZero, levelTy', natTy' :: Expr
typeZero = mkUnivTy (LitLevel 0)

mkApp :: Expr -> Expr -> Expr
mkApp = App

levelTy' = builtinBody levelTy

levelTy, lzero, lsuc, lmax,
 inlTerm, inrTerm,
 unitTy, unitTerm,
 idTy, reflTerm,
 natTy, dnzero, dnsucc,
 emptyTy :: Builtin

levelTy = mkBuiltin LevelTy typeZero
lzero = mkBuiltin LZero levelTy'
lsuc = mkBuiltin LSuc (mkFunTy ignoreVar levelTy' levelTy')
lmax = mkBuiltin LMax (mkFunTy ignoreVar levelTy' (mkFunTy ignoreVar levelTy' levelTy'))
inlTerm = mkBuiltin Inl inlTermTY
  where
    inlTermTY =
      let l1 = mkIdent "l1"; l1v = Var l1
          l2 = mkIdent "l2"; l2v = Var l2
          a = mkIdent "a"; av = Var a
          b = mkIdent "b"; bv = Var b
      in mkFunTy l1 levelTy'
          (mkFunTy l2 levelTy'
           (mkFunTy a (mkUnivTy l1v)
            (mkFunTy b (mkUnivTy l2v)
             (mkFunTy ignoreVar av (Coproduct av bv)))))
inrTerm = mkBuiltin Inr inrTermTY
  where
    inrTermTY =
      let l1 = mkIdent "l1"; l1v = Var l1
          l2 = mkIdent "l2"; l2v = Var l2
          a = mkIdent "a"; av = Var a
          b = mkIdent "b"; bv = Var b
      in mkFunTy l1 levelTy'
          (mkFunTy l2 levelTy'
           (mkFunTy a (mkUnivTy l1v)
            (mkFunTy b (mkUnivTy l2v)
             (mkFunTy ignoreVar bv (Coproduct av bv)))))

unitTy = mkBuiltin DUnitTy typeZero

unitTerm = mkBuiltin DUnitTerm (builtinBody unitTy)

idTy = mkBuiltin IdTy idTyTY
  where
    idTyTY :: Expr
    idTyTY =
      let l = mkIdent "l"
          lv = Var l
          a = mkIdent "a"
          av = Var a
      in mkFunTy l levelTy' (mkFunTy a (mkUnivTy lv) (mkFunTy ignoreVar av (mkFunTy ignoreVar av (mkUnivTy lv))))

reflTerm = mkBuiltin DRefl reflTermTY
  where
    reflTermTY :: Expr
    reflTermTY =
      let l = mkIdent "l"
          lv = Var l
          a = mkIdent "a"
          av = Var a
          x = mkIdent "x"
          xv = Var x
      in mkFunTy l levelTy' (mkFunTy a (mkUnivTy lv) (mkFunTy x av (idTyApp lv av xv xv)))

natTy = mkBuiltin DNat typeZero
natTy' = builtinBody natTy
dnzero = mkBuiltin DNZero natTy'
dnsucc = mkBuiltin DNSucc (mkFunTy ignoreVar natTy' natTy')
emptyTy = mkBuiltin DEmptyTy typeZero


lsucApp :: Expr -> Expr
lsucApp = mkApp (builtinBody lsuc)

lmaxApp :: Expr -> Expr -> Expr
lmaxApp l1 l2 = mkApp (mkApp (builtinBody lmax) l1) l2

mkUnivTy :: Expr -> Expr
mkUnivTy = AType

inlTermApp :: Expr -> Expr -> Expr -> Expr -> Expr -> Expr
inlTermApp l1 l2 a b v = mkApp (mkApp (mkApp (mkApp (mkApp (builtinBody inlTerm) l1) l2) a) b) v

inrTermApp :: Expr -> Expr -> Expr -> Expr -> Expr -> Expr
inrTermApp l1 l2 a b v = mkApp (mkApp (mkApp (mkApp (mkApp (builtinBody inrTerm) l1) l2) a) b) v

idTyApp :: Expr -> Expr -> Expr -> Expr -> Expr
idTyApp l t x y = mkApp (mkApp (mkApp (mkApp (builtinBody idTy) l) t) x) y

reflTermApp :: Expr -> Expr -> Expr -> Expr
reflTermApp l t x = mkApp (mkApp (mkApp (builtinBody reflTerm) l) t) x

dnsuccApp :: Expr -> Expr
dnsuccApp = mkApp (builtinBody dnsucc)
