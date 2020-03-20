module Language.Dlam.Builtins
  (

  -- * Collected builtins
    builtins
  , builtinsTypes
  , builtinsValues
  , bodyForBuiltin
  , typeForBuiltin

  -- * Builtin definitions

  , Builtin
  , builtinName
  , builtinBody
  , builtinType

  -- ** Type Constructors
  , tcCoproduct

  -- ** Common types
  , levelTy
  , natTy
  , emptyTy

  -- ** Type Universes
  , mkUnivTy

  -- * Helpers
  , mkLevelVar
  , mkVar
  , mkArg'
  , succForApp
  , elimNatForApp
  , elimEmptyForApp
  , elimCoproductForApp
  , mkCoproductTy
  , mkInlTerm
  , mkInrTerm
  ) where


import qualified Data.Map as M

import Language.Dlam.Syntax.Abstract (AName, mkIdent, BuiltinTerm(..))
import Language.Dlam.Syntax.Internal
import Language.Dlam.Util.Peekaboo
import Language.Dlam.Util.Pretty (pprintShow)


-- | The list of builtins.
builtins :: [Builtin]
builtins =
  builtinDataConstructors
  <>
  builtinTypeConstructors
  <>
  builtinEliminators
  where
    builtinDataConstructors = fmap BinDCon
      [ dcInl
      , dcInr
      , dcLmax
      , dcLsuc
      , dcLzero
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
      , tcUnit
      ]
    builtinEliminators = fmap BinDef
      [ elimEmpty
      , elimNat
      ]


builtinsTypes :: M.Map AName Type
builtinsTypes = M.fromList
  (fmap (\bin -> (builtinName bin, builtinType bin)) builtins)


builtinsValues :: M.Map AName Term
builtinsValues = M.fromList $
  (fmap (\bin -> (builtinName bin, builtinBody bin)) builtins)


getBuiltin :: BuiltinTerm -> Builtin
getBuiltin t =
  case t of
    -- lzero : Level
    LZero -> BinDCon dcLzero

    -- lsuc : Level -> Level
    LSuc  -> BinDCon dcLsuc

    -- Level : Type 0
    LevelTy -> BinTyCon tcLevel

    -- lmax : Level -> Level -> Level
    LMax -> BinDCon dcLmax

    -- (_+_) : (l1 l2 : Level) -> Type l1 -> Type l2 -> Type (lmax l1 l2)
    DCoproduct -> BinTyCon tcCoproduct

    -- inl : (l1 l2 : Level) (a : Type l1) (b : Type l2) -> a -> a + b
    Inl -> BinDCon dcInl

    -- inr : (l1 l2 : Level) (a : Type l1) (b : Type l2) -> b -> a + b
    Inr -> BinDCon dcInr

    -- Nat : Type 0
    DNat -> BinTyCon tcNat

    -- zero : Nat
    DNZero -> BinDCon dcZero

    -- succ : Nat -> Nat
    DNSucc -> BinDCon dcSucc

    -- Unit : Type 0
    DUnitTy -> BinTyCon tcUnit

    -- unit : Unit
    DUnitTerm -> BinDCon dcUnit

    -- Empty : Type 0
    DEmptyTy -> BinTyCon tcEmpty

    -- Id : (l : Level) (a : Type l) -> a -> a -> Type l
    IdTy -> BinTyCon tcId

    -- refl : (l : Level) (a : Type l) (x : a) -> Id l a x x
    DRefl -> BinDCon dcRefl


typeForBuiltin :: BuiltinTerm -> Type
typeForBuiltin = builtinType . getBuiltin


bodyForBuiltin :: BuiltinTerm -> Term
bodyForBuiltin = builtinBody . getBuiltin


-------------------------------
----- Builtin definitions -----
-------------------------------


-- | A builtin.
data Builtin
  -- | Builtin type constructor.
  = BinTyCon TyCon
  -- | Builtin data constructor.
  | BinDCon BuiltinDCon
  -- | A constant (postulate).
  | BinDef BuiltinDef


type BuiltinDCon = (Maybe Term, DCon)


type BuiltinDef = (AName, [Arg], Type)


mkBuiltinDef :: AName -> [Arg] -> Type -> BuiltinDef
mkBuiltinDef n args ty = (n, args, ty)


mkBuiltinDCon :: BuiltinTerm -> [Arg] -> FullyApplied TyCon -> Term -> BuiltinDCon
mkBuiltinDCon bin args tyc body =
  let n = mkIdent (pprintShow bin) in (Just body, mkDCon n args tyc)


mkBuiltinDConNoDef :: BuiltinTerm -> [Arg] -> FullyApplied TyCon -> BuiltinDCon
mkBuiltinDConNoDef bin args tyc  =
  let n = mkIdent (pprintShow bin) in (Nothing, mkDCon n args tyc)


mkBuiltinTyCon :: BuiltinTerm -> [Arg] -> Level -> TyCon
mkBuiltinTyCon bin args l =
  let n = mkIdent (pprintShow bin) in mkTyCon n args (mkUnivTy l)


-- | Make a new builtin type (0-argument type constructor).
mkBuiltinType :: BuiltinTerm -> TyCon
mkBuiltinType exprRef = mkBuiltinTyCon exprRef [] levelZero


-- | Syntactic name of a builtin term.
builtinName :: Builtin -> AName
builtinName (BinTyCon tcon) = getName tcon
builtinName (BinDCon  dcon) = getName $ snd dcon
builtinName (BinDef (n,_,_)) = n


-- | Body for a builtin term (potentially a postulate).
builtinBody :: Builtin -> Term
builtinBody (BinTyCon tcon) =
  if length (args tcon) > 0
  then PartialApp (partiallyApplied (TyConPartial tcon) [])
  -- TODO: not sure if this is the correct level! (2020-03-16)
  else TypeTerm $ mkType (TyApp $ fullyApplied (AppTyCon tcon) []) (level $ conTy tcon)
  -- else TypeTerm $ mkType (Constructed $ fullyApplied tcon []) (prevLevel $ level $ conTy tcon)

-- no internal representation provided, this behaves like an axiom
builtinBody (BinDCon (Nothing, dcon)) =
  if length (args dcon) > 0
  then PartialApp (partiallyApplied (DConPartial dcon) [])
  else App (fullyApplied (ConData dcon) [])

-- if an internal representation is provided, then we can produce a
-- lambda or concrete term
builtinBody (BinDCon (Just inner, dcon)) =
  mkLamFromArgsAndBody (args dcon) inner
  where mkLamFromArgsAndBody :: [Arg] -> Term -> Term
        mkLamFromArgsAndBody [] body = body
        mkLamFromArgsAndBody (arg:args) body = mkLam' arg (mkLamFromArgsAndBody args body)

-- Constant postulate, so we don't do any fancy reduction.
builtinBody (BinDef (n, args, _)) =
  if length args > 0
  then PartialApp (partiallyApplied (DefPartial n) [])
  else App (fullyApplied (AppDef n) [])


-- | The type of a builtin term.
builtinType :: Builtin -> Type
builtinType (BinTyCon tcon) = mkTyConTy tcon
builtinType (BinDCon (_, dcon)) = mkDConTy dcon
builtinType (BinDef (_, args, ty)) = mkDefTy args ty


mkTyConTy :: TyCon -> Type
mkTyConTy con = foldr (\arg t -> mkFunTy (argVar arg) (typeOf arg) t) (conTy con) (args con)


-- TODO: make sure this is actually going to have the correct level w/
-- the arguments passed (will need to build the builtins in the monad,
-- I think) (2020-03-16)
mkDConTy :: DCon -> Type
mkDConTy con = foldr (\arg t -> mkFunTy (argVar arg) (typeOf arg) t) (mkType (TyApp $ fmap AppTyCon (dconTy con)) (level $ conTy (un $ dconTy con))) (args con)


mkDefTy :: [Arg] -> Type -> Type
mkDefTy args ty = foldr (\arg t -> mkFunTy (argVar arg) (typeOf arg) t) ty args


levelTy, natTy, emptyTy :: Type
levelTy = mkTyAxiom tcLevel levelZero
natTy = mkTyAxiom tcNat levelZero
emptyTy = mkTyAxiom tcEmpty levelZero


mkUnivTy :: Level -> Type
mkUnivTy l = mkType (Universe l) l

mkCoproductTyForApp :: Type -> Type -> FullyApplied TyCon
mkCoproductTyForApp t1 t2 = fullyApplied tcCoproduct [Level (level t1), Level (level t2), TypeTerm t1, TypeTerm t2]

mkCoproductTy :: Type -> Type -> Type
mkCoproductTy t1 t2 = mkType (TyApp (fmap AppTyCon (mkCoproductTyForApp t1 t2))) (Max (level t1) (level t2))


-----------------------------
----- Type Constructors -----
-----------------------------


tcCoproduct, tcEmpty, tcId, tcLevel, tcNat, tcUnit :: TyCon


tcEmpty = mkBuiltinType DEmptyTy
tcLevel = mkBuiltinType LevelTy
tcNat   = mkBuiltinType DNat
tcUnit  = mkBuiltinType DUnitTy


tcCoproduct =
  let l1 = nameFromString "l1"; l1v = mkLevelVar l1
      l2 = nameFromString "l2"; l2v = mkLevelVar l2
      a = nameFromString "a"
      b = nameFromString "b"
  in mkBuiltinTyCon DCoproduct
     [ mkArg' l1 levelTy, mkArg' l2 levelTy
     , mkArg' a (mkUnivTy l1v), mkArg' b (mkUnivTy l2v)]
     (Max l1v l2v)


tcId =
  let l = nameFromString "l"
      lv = mkLevelVar l
      a = nameFromString "a"
      av = mkTypeVar a lv
  in mkBuiltinTyCon IdTy
       [ mkArg' l levelTy, mkTyArg a (mkUnivTy lv)
       , mkArgNoBind av, mkArgNoBind av]
       lv


tcLevel', tcNat', tcUnit' :: FullyApplied TyCon
tcLevel' = fullyApplied tcLevel []
tcNat' = fullyApplied tcNat []
tcUnit' = fullyApplied tcUnit []


--------------------------------------------------------
----- Data Constructors (with internal definition) -----
--------------------------------------------------------


dcLmax, dcLsuc, dcLzero :: BuiltinDCon


dcLzero = mkBuiltinDCon LZero [] tcLevel' (Level levelZero)


dcLsuc = let l = nameFromString "l" in mkBuiltinDCon LSuc [mkArg' l levelTy] tcLevel'
               (Level (nextLevel (mkLevelVar l)))


dcLmax =
  let l1 = nameFromString "l1"; l2 = nameFromString "l2" in
  mkBuiltinDCon LMax [mkArg' l1 levelTy, mkArg' l2 levelTy] tcLevel'
                  (Level (Max (mkLevelVar l1) (mkLevelVar l2)))


------------------------------------------------------
----- Data Constructors (no internal definition) -----
------------------------------------------------------


dcInl, dcInr, dcRefl, dcSucc, dcUnit, dcZero :: BuiltinDCon


dcInl =
  let l1 = nameFromString "l1"; l1v = mkLevelVar l1
      l2 = nameFromString "l2"; l2v = mkLevelVar l2
      a = nameFromString "a"; av = mkTypeVar a l1v
      b = nameFromString "b"; bv = mkTypeVar b l2v
  in mkBuiltinDConNoDef Inl
       [ mkArg' l1 levelTy, mkArg' l2 levelTy
       , mkTyArg a (mkUnivTy l1v), mkTyArg b (mkUnivTy l2v)
       , mkArgNoBind av
       ]
       (mkCoproductTyForApp av bv)


mkInlTerm :: Type -> Type -> Term -> Term
mkInlTerm tA tB a = App (fullyApplied (ConData $ snd dcInr) [Level (level tA), Level (level tB), TypeTerm tA, TypeTerm tB, a])


dcInr =
  let l1 = nameFromString "l1"; l1v = mkLevelVar l1
      l2 = nameFromString "l2"; l2v = mkLevelVar l2
      a = nameFromString "a"; av = mkTypeVar a l1v
      b = nameFromString "b"; bv = mkTypeVar b l2v
  in mkBuiltinDConNoDef Inr
       [ mkArg' l1 levelTy, mkArg' l2 levelTy
       , mkTyArg a (mkUnivTy l1v), mkTyArg b (mkUnivTy l2v)
       , mkArgNoBind bv
       ]
       (mkCoproductTyForApp av bv)


mkInrTerm :: Type -> Type -> Term -> Term
mkInrTerm tA tB b = App (fullyApplied (ConData $ snd dcInr) [Level (level tA), Level (level tB), TypeTerm tA, TypeTerm tB, b])


dcRefl =
  let l = nameFromString "l"
      lv = mkLevelVar l
      a = nameFromString "a"
      av = mkTypeVar a lv
      x = nameFromString "x"
      xv = mkVar x
  in mkBuiltinDConNoDef DRefl
       [mkArg' l levelTy, mkTyArg a (mkUnivTy lv), mkArg' x av]
       (fullyApplied tcId [Level lv, TypeTerm av, xv, xv])


dcZero = mkBuiltinDConNoDef DNZero [] tcNat'


dcSucc = mkBuiltinDConNoDef DNSucc [mkArgNoBind natTy] tcNat'


dcUnit = mkBuiltinDConNoDef DUnitTerm [] tcUnit'


succForApp :: TermThatCanBeApplied
succForApp = IsPartialApp $ partiallyApplied (DConPartial (snd dcSucc)) []


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
  let (l, n, x, y, cz, cs) = six nameFromString ("l", "n", "x", "y", "cz", "cs")
      tC = nameFromString "C"
      six fun (a,b,c,d,e,f) = (fun a, fun b, fun c, fun d, fun e, fun f)
      lv = mkLevelVar l
      xv = mkVar x
      appC a = mkType (TyApp (fullyApplied (AppTyVar tC) [a])) lv
      succApp a = App (fullyApplied (ConData $ snd dcSucc) [a])
      args =
        [ mkArg' l levelTy
        , mkTyArg tC (mkFunTyNoBind natTy (mkUnivTy lv))
        , mkArg' cz (appC (mkVar cz))
        , mkArg' cs (mkFunTy x natTy (mkFunTy y (appC xv) (appC (succApp xv))))
        , mkArg' n natTy
        ]
      ty = appC (mkVar n)
  in mkBuiltinDef (mkIdent "elimNat") args ty


elimNatForApp :: Appable
elimNatForApp = AppDef (builtinName $ (BinDef elimNat))


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
      appC a = mkType (TyApp (fullyApplied (AppTyVar tC) [a])) lv
      args =
        [ mkArg' l levelTy
        , mkTyArg tC (mkFunTyNoBind emptyTy (mkUnivTy lv))
        , mkArg' a  emptyTy
        ]
      ty = appC (mkVar a)
  in mkBuiltinDef (mkIdent "elimEmpty") args ty


elimEmptyForApp :: Appable
elimEmptyForApp = AppDef (builtinName $ (BinDef elimEmpty))


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
      (a, b, tC) = three nameFromString ("a", "b", "tC")
      p = nameFromString "p"
      three fun (a,b,c) = (fun a, fun b, fun c)
      l1v = mkLevelVar l1
      l2v = mkLevelVar l2
      l3v = mkLevelVar l3
      aty = mkTypeVar a l1v
      bty = mkTypeVar b l2v
      appC a = mkType (TyApp (fullyApplied (AppTyVar tC) [a])) l3v
      copAB = mkCoproductTy aty bty
      pv = mkVar p
      args =
        [ mkArg' l1 levelTy, mkArg' l2 levelTy, mkArg' l3 levelTy
        , mkTyArg a (mkUnivTy l1v), mkTyArg b (mkUnivTy l2v)
        , mkTyArg tC (mkFunTyNoBind copAB (mkUnivTy l3v))
        , mkArg' p copAB
        , mkArgNoBind (mkFunTyNoBind aty (appC pv))
        , mkArgNoBind (mkFunTyNoBind bty (appC pv))
        ]
      ty = appC pv
  in mkBuiltinDef (mkIdent "elimCoproduct") args ty


elimCoproductForApp :: Appable
elimCoproductForApp = AppDef (builtinName $ (BinDef elimCoproduct))
