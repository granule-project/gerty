module Language.Dlam.Builtins2
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
  , coproductBin
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

import Language.Dlam.Syntax.Abstract (Name, mkIdent, ignoreVar, BuiltinTerm(..))
import Language.Dlam.Syntax.Internal
-- import Language.Dlam.Util.Peekaboo
import Language.Dlam.Util.Pretty (pprintShow)


-- | The list of builtins.
builtins :: [Builtin]
builtins = builtinTerms <> builtinTypes


-- | The list of builtin terms.
builtinTerms :: [Builtin]
builtinTerms =
  [ lzero, lsuc, lmax
  , inlTerm, inrTerm
  , dnzero, dnsucc
  , unitTerm
  , reflTerm
  -- [ typeTy
  -- , lzero, lsuc, lmax
  -- , inlTerm, inrTerm
  -- , dnzero, dnsucc
  -- , unitTerm
  -- , idTy, reflTerm
  ]


-- | The list of builtin types.
builtinTypes :: [Builtin]
builtinTypes =
  [ levelTy
  , natTy
  , unitTy
  , emptyTy
  , idTy
  -- [ typeTy
  -- , lzero, lsuc, lmax
  -- , inlTerm, inrTerm
  -- , dnzero, dnsucc
  -- , unitTerm
  -- , idTy, reflTerm
  ]


builtinsTypes :: M.Map Name Type
builtinsTypes = M.fromList
  (fmap (\bin -> (builtinName bin, builtinType bin)) builtins)


builtinsValues :: M.Map Name Term
builtinsValues = M.fromList $
  (fmap (\bin -> (builtinName bin, builtinBody bin)) builtinTerms)
  <>
  (fmap (\bin -> (builtinName bin, builtinTypeBody bin)) builtinTypes)


-------------------------------
----- Builtin definitions -----
-------------------------------


newtype Builtin = MkBuiltin (Name, Type)

mkBuiltin :: BuiltinTerm -> Type -> Builtin
mkBuiltin exprRef ty = MkBuiltin (mkIdent (pprintShow exprRef), ty)


mkBuiltinType :: BuiltinTerm -> Level -> Builtin
mkBuiltinType exprRef l = MkBuiltin (mkIdent (pprintShow exprRef), mkUnivTy l)


-- | Syntactic name of a builtin term.
builtinName :: Builtin -> Name
builtinName (MkBuiltin (n, _)) = n

-- | Body for a builtin term (essentially an Agda postulate).
builtinBody :: Builtin -> Term
builtinBody (MkBuiltin (n, _)) = App (Var n) []

-- | Body for a builtin type (essentially an Agda postulate).
builtinTypeBody :: Builtin -> Term
builtinTypeBody (MkBuiltin (n, _)) = TypeTerm $ mkType (TyApp (TyVar n) []) (Concrete 0)

-- | The type of a builtin term.
builtinType :: Builtin -> Type
builtinType (MkBuiltin (_, t)) = t


mkFunTy :: Name -> Type -> Type -> Type
mkFunTy n t e = mkType (Pi (n `typedWith` t `gradedWith` thatMagicalGrading) e) (nextLevel $ Max (level t) (level e))

levelZero :: Level
levelZero = Concrete 0

mkTLevel :: Term -> Level
mkTLevel = Plus 0 . LTerm

mkLevelVar :: Name -> Level
mkLevelVar n = mkTLevel $ mkVar n

mkTypeVar :: Name -> Level -> Type
mkTypeVar n = mkType (TyApp (TyVar n) [])

-- mkTyVar :: Name -> Level -> Term
-- mkTyVar n l = TypeTerm $ mkTypeVar n l

mkVar :: Name -> Term
mkVar n = App (Var n) []

typeZero, levelTy', natTy', unitTy' :: Type
typeZero = mkUnivTy (Concrete 0)

levelTy' = mkTypeVar (builtinName levelTy) levelZero
unitTy' = mkTypeVar (builtinName unitTy) levelZero

levelTy, lzero, lsuc, lmax,
 coproductBin, inlTerm, inrTerm,
 unitTy, unitTerm,
 idTy, reflTerm,
 natTy, dnzero, dnsucc,
 emptyTy :: Builtin

levelTy = mkBuiltinType LevelTy levelZero
lzero = mkBuiltin LZero levelTy'
lsuc = mkBuiltin LSuc (mkFunTy ignoreVar levelTy' levelTy')
lmax = mkBuiltin LMax (mkFunTy ignoreVar levelTy' (mkFunTy ignoreVar levelTy' levelTy'))
coproductBin = mkBuiltin DCoproduct coproductTY
  where
    coproductTY =
      let l1 = mkIdent "l1"; l1v = mkLevelVar l1
          l2 = mkIdent "l2"; l2v = mkLevelVar l2
          a = mkIdent "a"
          b = mkIdent "b"
      in mkFunTy l1 levelTy'
          (mkFunTy l2 levelTy'
           (mkFunTy a (mkUnivTy l1v)
            (mkFunTy b (mkUnivTy l2v) (mkUnivTy (lmaxApp l1v l2v)))))
inlTerm = mkBuiltin Inl inlTermTY
  where
    inlTermTY =
      let l1 = mkIdent "l1"; l1v = mkLevelVar l1
          l2 = mkIdent "l2"; l2v = mkLevelVar l2
          a = mkIdent "a"; av = mkTypeVar a l1v
          b = mkIdent "b"; bv = mkTypeVar b l2v
      in mkFunTy l1 levelTy'
          (mkFunTy l2 levelTy'
           (mkFunTy a (mkUnivTy l1v)
            (mkFunTy b (mkUnivTy l2v)
             (mkFunTy ignoreVar av (mkCoproductTy av bv)))))
inrTerm = mkBuiltin Inr inrTermTY
  where
    inrTermTY =
      let l1 = mkIdent "l1"; l1v = mkLevelVar l1
          l2 = mkIdent "l2"; l2v = mkLevelVar l2
          a = mkIdent "a"; av = mkTypeVar a l1v
          b = mkIdent "b"; bv = mkTypeVar b l2v
      in mkFunTy l1 levelTy'
          (mkFunTy l2 levelTy'
           (mkFunTy a (mkUnivTy l1v)
            (mkFunTy b (mkUnivTy l2v)
             (mkFunTy ignoreVar bv (mkCoproductTy av bv)))))

unitTy = mkBuiltin DUnitTy typeZero

unitTerm = mkBuiltin DUnitTerm unitTy'

idTy = mkBuiltin IdTy idTyTY
  where
    idTyTY :: Type
    idTyTY =
      let l = mkIdent "l"
          lv = mkLevelVar l
          a = mkIdent "a"
          av = mkTypeVar a lv
      in mkFunTy l levelTy' (mkFunTy a (mkUnivTy lv) (mkFunTy ignoreVar av (mkFunTy ignoreVar av (mkUnivTy lv))))

reflTerm = mkBuiltin DRefl reflTermTY
  where
    reflTermTY :: Type
    reflTermTY =
      let l = mkIdent "l"
          lv = mkLevelVar l
          a = mkIdent "a"
          av = mkTypeVar a lv
          x = mkIdent "x"
          xv = App (Var x) []
      in mkFunTy l levelTy' (mkFunTy a (mkUnivTy lv) (mkFunTy x av (idTyApp lv av xv xv)))

natTy = mkBuiltin DNat typeZero
natTy' = mkTypeVar (builtinName natTy) levelZero
dnzero = mkBuiltin DNZero natTy'
dnsucc = mkBuiltin DNSucc (mkFunTy ignoreVar natTy' natTy')
emptyTy = mkBuiltin DEmptyTy typeZero


lsucApp :: Term -> Level
lsucApp = Plus 1 . LTerm

lmaxApp :: Level -> Level -> Level
lmaxApp = Max

mkUnivTy :: Level -> Type
mkUnivTy l = mkType (Universe l) l

inlTermApp :: Term -> Term -> Term -> Term -> Term -> Term
inlTermApp l1 l2 a b v = mkBinApp inlTerm [l1, l2, a, b, v]

inrTermApp :: Term -> Term -> Term -> Term -> Term -> Term
inrTermApp l1 l2 a b v = mkBinApp inrTerm [l1, l2, a, b, v]

idTyApp :: Level -> Type -> Term -> Term -> Type
idTyApp l t x y = mkType (mkBinTyApp idTy [Level l, TypeTerm t, x, y]) l

reflTermApp :: Term -> Term -> Term -> Term
reflTermApp l t x = mkBinApp reflTerm [l, t, x]

dnsuccApp :: Term -> Term
dnsuccApp t = mkBinApp dnsucc [t]


mkCoproductTy :: Type -> Type -> Type
mkCoproductTy l r = mkType (mkBinTyApp coproductBin [TypeTerm l, TypeTerm r]) (lmaxApp (level l) (level r))


-------------------
----- Helpers -----
-------------------


mkBinApp :: Builtin -> [Term] -> Term
mkBinApp b = App (Var (builtinName b))


mkBinTyApp :: Builtin -> [Term] -> TypeTerm
mkBinTyApp b = TyApp (TyVar (builtinName b))
