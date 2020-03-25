{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
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

  -- ** Data Constructors
  , dcPair
  , dcSucc

  -- ** Type Constructors
  , tcCoproduct
  , tcProduct

  -- ** Common types
  , levelTy
  , natTy
  , emptyTy

  -- ** Eliminators
  , elimCoproduct
  , elimEmpty
  , elimNat

  -- ** Type Universes
  , mkUnivTy

  -- * Helpers
  , dcZeroBody
  , mkLevelVar
  , mkVar
  , mkArg'
  , succTy
  , getTyCon
  , mkCoproductTy
  , mkInlTerm
  , mkInrTerm
  , ToTerm(..)
  ) where


import qualified Data.Map as M

import Language.Dlam.Syntax.Abstract (AName, mkIdent)
import Language.Dlam.Syntax.Common.Language (HasType(typeOf))
import Language.Dlam.Syntax.Internal hiding (typeOf)
import Language.Dlam.Util.Peekaboo


-- | The list of builtins.
builtins :: [Builtin]
builtins =
  builtinDataConstructors
  <>
  builtinTypeConstructors
  <>
  builtinEliminators
  <>
  builtinSpecialDefinitions
  where
    builtinDataConstructors = fmap BinDCon
      [ dcInl
      , dcInr
      , dcLmax
      , dcLsuc
      , dcLzero
      , dcPair
      , dcRefl
      , dcSucc
      , dcUnit
      , dcZero
      ]
    builtinTypeConstructors = fmap BinTyCon
      [ tcCoproduct
      , tcEmpty
      , tcId
      , tcLevel
      , tcNat
      , tcProduct
      , tcUnit
      ]
    builtinEliminators = fmap BinDef
      [ elimEmpty
      , elimNat
      ]
    builtinSpecialDefinitions = fmap BinDef
      [ defType ]


builtinsTypes :: M.Map AName Type
builtinsTypes = M.fromList
  (fmap (\bin -> (builtinName bin, builtinType bin)) builtins)


builtinsValues :: M.Map AName Term
builtinsValues = M.fromList $
  (fmap (\bin -> (builtinName bin, builtinBody bin)) builtins)


dcZeroBody :: Term
dcZeroBody = builtinBody (BinDCon dcZero)


-------------------------------
----- Builtin definitions -----
-------------------------------


-- | A builtin.
data Builtin
  -- | Builtin type constructor.
  = BinTyCon BuiltinTyCon
  -- | Builtin data constructor.
  | BinDCon BuiltinDCon
  -- | A constant (postulate).
  | BinDef BuiltinDef


newtype BuiltinDCon = BuiltinDCon (Maybe Term, DCon)


newtype BuiltinDef = BuiltinDef (AName, [Arg], Maybe Term, Type)


newtype BuiltinTyCon = BuiltinTyCon TyCon


type BuiltinName = String


mkBuiltinDef :: BuiltinName -> [Arg] -> Type -> BuiltinDef
mkBuiltinDef bn args ty = let n = mkIdent bn in BuiltinDef (n, args, Nothing, ty)


mkBuiltinDefWithBody :: BuiltinName -> [Arg] -> Term -> Type -> BuiltinDef
mkBuiltinDefWithBody bn args body ty = let n = mkIdent bn in BuiltinDef (n, args, Just body, ty)


mkBuiltinDCon :: BuiltinName -> [Arg] -> FullyApplied TyCon -> Term -> BuiltinDCon
mkBuiltinDCon bn args tyc body = let n = mkIdent bn in BuiltinDCon (Just body, mkDCon n args tyc)


mkBuiltinDConNoDef :: BuiltinName -> [Arg] -> FullyApplied TyCon -> BuiltinDCon
mkBuiltinDConNoDef bn args tyc = let n = mkIdent bn in BuiltinDCon (Nothing, mkDCon n args tyc)


mkBuiltinTyCon :: BuiltinName -> [Arg] -> Level -> BuiltinTyCon
mkBuiltinTyCon bn args l = let n = mkIdent bn in BuiltinTyCon $ mkTyCon n args (mkUnivTy l)


-- | Make a new builtin type (0-argument type constructor).
mkBuiltinType :: BuiltinName -> BuiltinTyCon
mkBuiltinType n = mkBuiltinTyCon n [] levelZero


class ToTerm a where
  toTerm :: a -> Term


instance ToTerm Builtin where
  toTerm (BinTyCon tc) = toTerm tc
  toTerm (BinDCon dc)  = toTerm dc
  toTerm (BinDef  d)   = toTerm d


instance ToTerm BuiltinTyCon where
  toTerm (BuiltinTyCon tcon) =
    if length (args tcon) > 0
    then PartialApp (partiallyApplied (TyConPartial tcon) [])
    -- TODO: not sure if this is the correct level! (2020-03-16)
    else TypeTerm $ mkType (TyApp $ mkFinalApp (AppTyCon tcon) []) (level $ conTy tcon)


instance ToTerm BuiltinDCon where
  -- no internal representation provided, this behaves like an axiom
  toTerm (BuiltinDCon (Nothing, dcon)) =
    if length (args dcon) > 0
    then PartialApp (partiallyApplied (DConPartial dcon) [])
    else App (fullyApplied (ConData dcon) [])

  -- if an internal representation is provided, then we can produce a
  -- lambda or concrete term
  toTerm (BuiltinDCon (Just inner, dcon)) =
    mkLamFromArgsAndBody (args dcon) inner
    where mkLamFromArgsAndBody :: [Arg] -> Term -> Term
          mkLamFromArgsAndBody [] body = body
          mkLamFromArgsAndBody (arg:args) body = mkLam' arg (mkLamFromArgsAndBody args body)


instance ToTerm BuiltinDef where
  -- If the 'postulate' has an associated builtin reduction, we provide it.
  toTerm (BuiltinDef (_, args, Just inner, _)) =
    mkLamFromArgsAndBody args inner
    where mkLamFromArgsAndBody :: [Arg] -> Term -> Term
          mkLamFromArgsAndBody [] body = body
          mkLamFromArgsAndBody (arg:args) body = mkLam' arg (mkLamFromArgsAndBody args body)
  -- Constant postulate, so we don't do any fancy reduction.
  toTerm (BuiltinDef (n, args, Nothing, _)) =
    if length args > 0
    then PartialApp (partiallyApplied (DefPartial n) [])
    else App (fullyApplied (AppDef n) [])


getDCon :: BuiltinDCon -> DCon
getDCon (BuiltinDCon (_, dc)) = dc


getTyCon :: BuiltinTyCon -> TyCon
getTyCon (BuiltinTyCon tc) = tc


instance HasName Builtin where
  getName (BinTyCon tc) = getName tc
  getName (BinDCon dc)  = getName dc
  getName (BinDef  d)   = getName d


instance HasName BuiltinTyCon where
  getName = getName . getTyCon


instance HasName BuiltinDCon where
  getName = getName . getDCon


instance HasName BuiltinDef where
  getName (BuiltinDef (n,_,_,_)) = n


instance HasType Builtin Type where
  typeOf (BinTyCon tc) = typeOf tc
  typeOf (BinDCon dc)  = typeOf dc
  typeOf (BinDef  d)   = typeOf d


instance HasType BuiltinTyCon Type where
  typeOf = mkTyConTy . getTyCon


instance HasType BuiltinDCon Type where
  typeOf (BuiltinDCon (_, dcon)) = mkDConTy dcon


instance HasType BuiltinDef Type where
  typeOf (BuiltinDef (_, args, _, ty)) = mkDefTy args ty


-- | Syntactic name of a builtin term.
builtinName :: Builtin -> AName
builtinName = getName


-- | Body for a builtin term (potentially a postulate).
builtinBody :: Builtin -> Term
builtinBody = toTerm


-- | The type of a builtin term.
builtinType :: Builtin -> Type
builtinType = typeOf


mkTyConTy :: TyCon -> Type
mkTyConTy con = foldr (\arg t -> mkFunTy' arg t) (conTy con) (args con)


-- TODO: make sure this is actually going to have the correct level w/
-- the arguments passed (will need to build the builtins in the monad,
-- I think) (2020-03-16)
mkDConTy :: DCon -> Type
mkDConTy con =
  let tyCon = dconTy con
      lev = level . conTy . un $ tyCon
  in foldr (\arg t -> mkFunTy' arg t) (mkType (TyApp $ fmap AppTyCon (fullyAppliedToFinal tyCon)) lev) (args con)


mkDefTy :: [Arg] -> Type -> Type
mkDefTy args ty = foldr (\arg t -> mkFunTy' arg t) ty args


levelTy, natTy, emptyTy :: Type
levelTy = mkTyAxiom tcLevel levelZero
natTy = mkTyAxiom tcNat levelZero
emptyTy = mkTyAxiom tcEmpty levelZero


mkUnivTy :: Level -> Type
mkUnivTy l = mkType (Universe l) l


mkCoproductTyForApp :: Type -> Type -> FullyApplied TyCon
mkCoproductTyForApp t1 t2 = fullyAppliedTC tcCoproduct [Level (level t1), Level (level t2), TypeTerm t1, TypeTerm t2]

mkCoproductTy :: Type -> Type -> Type
mkCoproductTy t1 t2 = mkType (TyApp (fmap AppTyCon (fullyAppliedToFinal $ mkCoproductTyForApp t1 t2))) (max2 (level t1) (level t2))


-----------------------------
----- Type Constructors -----
-----------------------------


tcCoproduct, tcEmpty, tcId, tcLevel, tcNat, tcProduct, tcUnit :: BuiltinTyCon


tcEmpty = mkBuiltinType "Empty"
tcLevel = mkBuiltinType "Level"
tcNat   = mkBuiltinType "Nat"
tcUnit  = mkBuiltinType "Unit"


tcCoproduct =
  let l1 = nameFromString "l1"; l1v = mkLevelVar l1
      l2 = nameFromString "l2"; l2v = mkLevelVar l2
      a = nameFromString "a"
      b = nameFromString "b"
  in mkBuiltinTyCon "Coproduct"
     [ mkLevelArg l1, mkLevelArg l2
     , mkTyArg a l1v, mkTyArg b l2v]
     (max2 l1v l2v)


tcId =
  let l = nameFromString "l"
      lv = mkLevelVar l
      a = nameFromString "a"
      av = mkTypeVar a lv
  in mkBuiltinTyCon "Id"
       [ mkLevelArg l, mkTyArg a lv
       , mkArgNoBind av, mkArgNoBind av]
       lv


{-
  Product : {l1 l2 : Level} (a : Type l1) -> (a -> Type l2) -> Type (lmax l1 l2)
-}
tcProduct =
  let l1 = nameFromString "l1"; l1v = mkLevelVar l1
      l2 = nameFromString "l2"; l2v = mkLevelVar l2
      a = nameFromString "a"
      av = mkTypeVar a l1v
  in mkBuiltinTyCon "Product"
     [ mkLevelArg l1, mkLevelArg l2
     , mkTyArg a l1v, mkArgNoBind (mkFunTyNoBind av (mkUnivTy l2v))]
     (max2 l1v l2v)


tcLevel', tcNat', tcUnit' :: FullyApplied TyCon
tcLevel' = fullyAppliedTC tcLevel []
tcNat' = fullyAppliedTC tcNat []
tcUnit' = fullyAppliedTC tcUnit []


--------------------------------------------------------
----- Data Constructors (with internal definition) -----
--------------------------------------------------------


dcLmax, dcLsuc, dcLzero :: BuiltinDCon


dcLzero = mkBuiltinDCon "lzero" [] tcLevel' (Level levelZero)


dcLsuc = let l = nameFromString "l" in mkBuiltinDCon "lsuc" [mkLevelArg l] tcLevel'
               (Level (nextLevel (mkLevelVar l)))


dcLmax =
  let l1 = nameFromString "l1"; l2 = nameFromString "l2" in
  mkBuiltinDCon "lmax" [mkLevelArg l1, mkLevelArg l2] tcLevel'
                  (Level (max2 (mkLevelVar l1) (mkLevelVar l2)))


------------------------------------------------------
----- Data Constructors (no internal definition) -----
------------------------------------------------------


dcInl, dcInr, dcPair, dcRefl, dcSucc, dcUnit, dcZero :: BuiltinDCon


dcInl =
  let l1 = nameFromString "l1"; l1v = mkLevelVar l1
      l2 = nameFromString "l2"; l2v = mkLevelVar l2
      a = nameFromString "a"; av = mkTypeVar a l1v
      b = nameFromString "b"; bv = mkTypeVar b l2v
  in mkBuiltinDConNoDef "inl"
       [ mkLevelArg l1, mkLevelArg l2
       , mkTyArg a l1v, mkTyArg b l2v
       , mkArgNoBind av
       ]
       (mkCoproductTyForApp av bv)


mkInlTerm :: Type -> Type -> Term -> Term
mkInlTerm tA tB a = App (fullyApplied (ConData $ getDCon dcInr) [Level (level tA), Level (level tB), TypeTerm tA, TypeTerm tB, a])


dcInr =
  let l1 = nameFromString "l1"; l1v = mkLevelVar l1
      l2 = nameFromString "l2"; l2v = mkLevelVar l2
      a = nameFromString "a"; av = mkTypeVar a l1v
      b = nameFromString "b"; bv = mkTypeVar b l2v
  in mkBuiltinDConNoDef "inr"
       [ mkLevelArg l1, mkLevelArg l2
       , mkTyArg a l1v, mkTyArg b l2v
       , mkArgNoBind bv
       ]
       (mkCoproductTyForApp av bv)


mkInrTerm :: Type -> Type -> Term -> Term
mkInrTerm tA tB b = App (fullyApplied (ConData $ getDCon dcInr) [Level (level tA), Level (level tB), TypeTerm tA, TypeTerm tB, b])


{-
  pair ::
    {l1 l2 : Level} {A : Type l1} {B : A -> Type l2}
    (x : A) -> B x -> Product A B
-}
dcPair =
  let l1 = nameFromString "l1"
      l2 = nameFromString "l2"
      l1v = mkLevelVar l1
      l2v = mkLevelVar l2
      a = nameFromString "a"
      av = mkTypeVar a l1v
      x = nameFromString "x"
      b = nameFromString "B"
      bv = mkTypeVar (nameForType b) l2v
      xv = mkVar x
      appB a = mkType (TyApp (mkFinalApp (AppTyVar b) [a])) l2v
  in mkBuiltinDConNoDef "pair"
       [ mkLevelArg l1, mkLevelArg l2
       , mkTyArg a l1v, mkArg' b (mkFunTyNoBind av (mkUnivTy l2v))
       , mkArg' x av
       , mkArgNoBind (appB xv)
       ]
       (fullyAppliedTC tcProduct [ Level l1v, Level l2v
                                 , TypeTerm av, mkLam' (mkArg' x av) (TypeTerm bv)])


dcRefl =
  let l = nameFromString "l"
      lv = mkLevelVar l
      a = nameFromString "a"
      av = mkTypeVar a lv
      x = nameFromString "x"
      xv = mkVar x
  in mkBuiltinDConNoDef "refl"
       [mkLevelArg l, mkTyArg a lv, mkArg' x av]
       (fullyAppliedTC tcId [Level lv, TypeTerm av, xv, xv])


dcZero = mkBuiltinDConNoDef "zero" [] tcNat'


dcSucc = mkBuiltinDConNoDef "succ" [mkArgNoBind natTy] tcNat'


dcUnit = mkBuiltinDConNoDef "unit" [] tcUnit'


succTy :: TypeOfTermsThatCanBeApplied
succTy = mkFunTyNoBind' natTy natTy


-----------------------
----- Eliminators -----
-----------------------

{-
  elimNat :
    (l : Level)
    (C : Nat -> Type l)
    (cz : C zero)
    (cs : (x : Nat) -> (y : C x) -> C (succ x))
    (n : Nat)
    -> C n
-}
elimNat :: BuiltinDef
elimNat =
  let (n, x, y, cz, cs) = five nameFromString ("n", "x", "y", "cz", "cs")
      l = nameFromString "l"
      tC = nameFromString "C"
      five fun (a,b,c,d,e) = (fun a, fun b, fun c, fun d, fun e)
      lv = mkLevelVar l
      xv = mkVar x
      appC a = mkType (TyApp (mkFinalApp (AppTyVar tC) [a])) lv
      succApp a = App (fullyApplied (ConData $ getDCon dcSucc) [a])
      args =
        [ mkLevelArg l
        , mkArg' (nameForTerm tC) (mkFunTyNoBind natTy (mkUnivTy lv))
        , mkArg' cz (appC (mkVar cz))
        , mkArg' cs (mkFunTy x natTy (mkFunTy y (appC xv) (appC (succApp xv))))
        , mkArg' n natTy
        ]
      ty = appC (mkVar n)
  in mkBuiltinDef "elimNat" args ty


{-
  elimEmpty :
    (l : Level)
    (C : Empty -> Type l)
    (a : Empty)
    -> C a
-}
elimEmpty :: BuiltinDef
elimEmpty =
  let l = nameFromString "l"
      a = nameFromString "a"
      tC = nameFromString "tC"
      lv = mkLevelVar l
      appC a = mkType (TyApp (mkFinalApp (AppTyVar tC) [a])) lv
      args =
        [ mkLevelArg l
        , mkArg' (nameForTerm tC) (mkFunTyNoBind emptyTy (mkUnivTy lv))
        , mkArg' a  emptyTy
        ]
      ty = appC (mkVar a)
  in mkBuiltinDef "elimEmpty" args ty


{-
  elimCoproduct :
    (l1 l2 l3 : Level)
    (a : Type l1) (b : Type l2) (C : a + b -> Type l3)
    (p : a + b)
    -> (a -> C p)
    -> (b -> C p)
    -> C p
-}
elimCoproduct :: BuiltinDef
elimCoproduct =
  let (l1, l2, l3) = three nameFromString ("l1", "l2", "l3")
      (a, b) = two nameFromString ("a", "b")
      (p, tC) = two nameFromString ("p", "C")
      three fun (a,b,c) = (fun a, fun b, fun c)
      two fun (a,b) = (fun a, fun b)
      l1v = mkLevelVar l1
      l2v = mkLevelVar l2
      l3v = mkLevelVar l3
      aty = mkTypeVar a l1v
      bty = mkTypeVar b l2v
      appC a = mkType (TyApp (mkFinalApp (AppTyVar tC) [a])) l3v
      copAB = mkCoproductTy aty bty
      pv = mkVar p
      args =
        [ mkLevelArg l1, mkLevelArg l2, mkLevelArg l3
        , mkTyArg a l1v, mkTyArg b l2v
        , mkArg' (nameForTerm tC) (mkFunTyNoBind copAB (mkUnivTy l3v))
        , mkArg' p copAB
        , mkArgNoBind (mkFunTyNoBind aty (appC pv))
        , mkArgNoBind (mkFunTyNoBind bty (appC pv))
        ]
      ty = appC pv
  in mkBuiltinDef "elimCoproduct" args ty


-------------------------------
----- Special Definitions -----
-------------------------------


defType :: BuiltinDef


{-
  Type (l : Level) : Type (lsuc l)
  Type l = Type l
-}
defType =
  let l = nameFromString "l"; lv = mkLevelVar l
  in mkBuiltinDefWithBody "Type"
     [ mkLevelArg l ]
     (TypeTerm $ mkUnivTy lv)
     (mkUnivTy (nextLevel lv))


-------------------
----- Helpers -----
-------------------


-- | Make an argument that captures a level variable.
mkLevelArg :: LVarId -> Arg
mkLevelArg n = mkArg (VISLevel, n) thatMagicalGrading levelTy


-- | Make an argument that captures a type variable.
mkTyArg :: TyVarId -> Level -> Arg
mkTyArg n l = mkArg (VISType l, n) thatMagicalGrading (mkUnivTy l)


mkTyAxiom :: BuiltinTyCon -> Level -> Type
mkTyAxiom (BuiltinTyCon tc) = mkType (TyApp (mkFinalApp (AppTyCon tc) []))


fullyAppliedTC :: BuiltinTyCon -> [Term] -> FullyApplied TyCon
fullyAppliedTC = fullyApplied . getTyCon
