module Language.Dlam.Builtins2
  (

  -- * Collected builtins
    builtins
  , builtinsTypes
  , builtinsValues
  , typeForBuiltin

  -- * Builtin definitions

  , Builtin
  , builtinName
  , builtinBody
  , builtinType

  -- ** Levels
  , levelTy'

  -- ** Type Universes
  , mkUnivTy

  -- * Helpers
  , mkFunTy
  , mkLevelVar
  , mkVar
  ) where


import qualified Data.Map as M

import Language.Dlam.Syntax.Abstract (Name, mkIdent, ignoreVar, BuiltinTerm(..))
import Language.Dlam.Syntax.Internal
import Language.Dlam.Util.Peekaboo
import Language.Dlam.Util.Pretty (pprintShow)


-- | The list of builtins.
builtins :: [Builtin]
builtins =
  builtinDataConstructors
  <>
  builtinTypeConstructors
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


builtinsTypes :: M.Map Name Type
builtinsTypes = M.fromList
  (fmap (\bin -> (builtinName bin, builtinType bin)) builtins)


builtinsValues :: M.Map Name Term
builtinsValues = M.fromList $
  (fmap (\bin -> (builtinName bin, builtinBody bin)) builtins)


typeForBuiltin :: BuiltinTerm -> Type
typeForBuiltin t = builtinType $
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


-------------------------------
----- Builtin definitions -----
-------------------------------


-- | A builtin.
data Builtin
  -- | Builtin type constructor.
  = BinTyCon TyCon
  -- | Builtin data constructor.
  | BinDCon BuiltinDCon


type BuiltinDCon = (Maybe Term, DCon)


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
builtinName :: Builtin -> Name
builtinName (BinTyCon tcon) = name tcon
builtinName (BinDCon  dcon) = name $ snd dcon


-- | Body for a builtin term (potentially a postulate).
builtinBody :: Builtin -> Term
builtinBody (BinTyCon tcon) =
  if length (args tcon) > 0
  then PartialApp (partiallyApplied (TyConPartial tcon) [])
  -- TODO: not sure if this is the correct level! (2020-03-16)
  else TypeTerm $ mkType (Constructed $ fullyApplied tcon []) (level $ conTy tcon)
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
        mkLamFromArgsAndBody (arg:args) body = Lam arg (mkLamFromArgsAndBody args body)


-- | The type of a builtin term.
builtinType :: Builtin -> Type
builtinType (BinTyCon tcon) = mkTyConTy tcon
builtinType (BinDCon (_, dcon)) = mkDConTy dcon


mkTyConTy :: TyCon -> Type
mkTyConTy con = foldr (\arg t -> mkFunTy (argVar arg) (typeOf arg) t) (conTy con) (args con)


-- TODO: make sure this is actually going to have the correct level w/
-- the arguments passed (will need to build the builtins in the monad,
-- I think) (2020-03-16)
mkDConTy :: DCon -> Type
mkDConTy con = foldr (\arg t -> mkFunTy (argVar arg) (typeOf arg) t) (mkType (Constructed $ dconTy con) (level $ conTy (un $ dconTy con))) (args con)


mkFunTy :: Name -> Type -> Type -> Type
mkFunTy n t e = mkType (Pi (n `typedWith` t `gradedWith` thatMagicalGrading) e) (nextLevel $ Max (level t) (level e))


levelZero :: Level
levelZero = Concrete 0


mkTLevel :: Term -> Level
mkTLevel = Plus 0 . LTerm


mkLevelVar :: Name -> Level
mkLevelVar n = mkTLevel $ mkVar n


-- | Make a new (fully-applied) type variable.
mkTypeVar :: Name -> Level -> Type
mkTypeVar n = mkType (VarApp (fullyApplied n []))


-- | Make a new (fully-applied) free variable.
mkVar :: Name -> Term
mkVar n = App (fullyApplied (Var n) [])


levelTy', natTy' :: Type
levelTy' = mkTypeVar (name tcLevel) levelZero
natTy' = mkTypeVar (name tcNat) levelZero


mkArg' :: Name -> Type -> Arg
mkArg' n t = mkArg n thatMagicalGrading t


mkUnivTy :: Level -> Type
mkUnivTy l = mkType (Universe l) l


-----------------------------
----- Type Constructors -----
-----------------------------


tcCoproduct, tcEmpty, tcId, tcLevel, tcNat, tcUnit :: TyCon


tcEmpty = mkBuiltinType DEmptyTy
tcLevel = mkBuiltinType LevelTy
tcNat   = mkBuiltinType DNat
tcUnit  = mkBuiltinType DUnitTy


tcCoproduct =
  let l1 = mkIdent "l1"; l1v = mkLevelVar l1
      l2 = mkIdent "l2"; l2v = mkLevelVar l2
      a = mkIdent "a"
      b = mkIdent "b"
  in mkBuiltinTyCon DCoproduct
     [ mkArg' l1 levelTy', mkArg' l2 levelTy'
     , mkArg' a (mkUnivTy l1v), mkArg' b (mkUnivTy l2v)]
     (Max l1v l2v)


tcId =
  let l = mkIdent "l"
      lv = mkLevelVar l
      a = mkIdent "a"
      av = mkTypeVar a lv
  in mkBuiltinTyCon IdTy
       [ mkArg' l levelTy', mkArg' a (mkUnivTy lv)
       , mkArg' ignoreVar av, mkArg' ignoreVar av]
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


dcLsuc = let l = mkIdent "l" in mkBuiltinDCon LSuc [mkArg' l levelTy'] tcLevel'
               (Level (nextLevel (mkLevelVar l)))


dcLmax =
  let l1 = mkIdent "l1"; l2 = mkIdent "l2" in
  mkBuiltinDCon LMax [mkArg' l1 levelTy', mkArg' l2 levelTy'] tcLevel'
                  (Level (Max (mkLevelVar l1) (mkLevelVar l2)))


------------------------------------------------------
----- Data Constructors (no internal definition) -----
------------------------------------------------------


dcInl, dcInr, dcRefl, dcSucc, dcUnit, dcZero :: BuiltinDCon


dcInl =
  let l1 = mkIdent "l1"; l1v = mkLevelVar l1
      l2 = mkIdent "l2"; l2v = mkLevelVar l2
      a = mkIdent "a"; av = mkTypeVar a l1v
      b = mkIdent "b"; bv = mkTypeVar b l2v
  in mkBuiltinDConNoDef Inl
       [ mkArg' l1 levelTy', mkArg' l2 levelTy'
       , mkArg' a (mkUnivTy l1v), mkArg' b (mkUnivTy l2v)
       , mkArg' ignoreVar av
       ]
       (fullyApplied tcCoproduct [TypeTerm av, TypeTerm bv])


dcInr =
  let l1 = mkIdent "l1"; l1v = mkLevelVar l1
      l2 = mkIdent "l2"; l2v = mkLevelVar l2
      a = mkIdent "a"; av = mkTypeVar a l1v
      b = mkIdent "b"; bv = mkTypeVar b l2v
  in mkBuiltinDConNoDef Inr
       [ mkArg' l1 levelTy', mkArg' l2 levelTy'
       , mkArg' a (mkUnivTy l1v), mkArg' b (mkUnivTy l2v)
       , mkArg' ignoreVar bv
       ]
       (fullyApplied tcCoproduct [TypeTerm av, TypeTerm bv])


dcRefl =
  let l = mkIdent "l"
      lv = mkLevelVar l
      a = mkIdent "a"
      av = mkTypeVar a lv
      x = mkIdent "x"
      xv = mkVar x
  in mkBuiltinDConNoDef DRefl
       [mkArg' l levelTy', mkArg' a (mkUnivTy lv), mkArg' x av]
       (fullyApplied tcId [Level lv, TypeTerm av, xv, xv])


dcZero = mkBuiltinDConNoDef DNZero [] tcNat'


dcSucc = mkBuiltinDConNoDef DNSucc [mkArg' ignoreVar natTy'] tcNat'


dcUnit = mkBuiltinDConNoDef DUnitTerm [] tcUnit'
