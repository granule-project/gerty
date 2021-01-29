{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Dlam.Syntax.Translation.ConcreteToAbstract
  ( ToAbstract(..)
  ) where


import Control.Arrow (first, second)
import Control.Monad (join)
import Control.Monad.Except (throwError)
import qualified Data.List.NonEmpty as NE


import Language.Dlam.Substitution (fresh)
import Language.Dlam.Syntax.Common
import Language.Dlam.Syntax.Common.Language (typeOf)
import qualified Language.Dlam.Syntax.Abstract as A
import qualified Language.Dlam.Syntax.Concrete as C
import Language.Dlam.Scoping.Monad
import Language.Dlam.Scoping.Scope
import Language.Dlam.Util.Pretty (pprintShow)


class ToAbstract c a where
  toAbstract :: c -> SM a


type Locals = [(C.Name, A.Name)]


-- | Generate a new, ignored name.
newIgnoredName :: SM A.Name
newIgnoredName = toAbstract C.ignoreVar


instance ToAbstract C.AST A.AST where
  toAbstract (C.AST []) = pure $ A.AST []
  toAbstract (C.AST ((C.TypeSig n e):ds)) = do
    n' <- toAbstract (mustBeNew n ISSig)
    e' <- toAbstract e
    (A.AST ds') <- toAbstract (C.AST ds)
    pure . A.AST $ (A.TypeSig n' e'):ds'
  toAbstract (C.AST ((C.FunEqn (C.FLHSName n) r):ds)) = do
    n' <- toAbstract (fdefLookingForSignature n)
    r' <- toAbstract r
    (A.AST ds') <- toAbstract (C.AST ds)
    pure . A.AST $ (A.FunEqn (A.FLHSName n') r'):ds'
  -- currently just ignoring records pending implementation (2020-03-05, GD)
  toAbstract (C.AST ((C.RecordDef _n _con _p _e _decls):ds)) = toAbstract (C.AST ds)
  toAbstract (C.AST ((C.Field _n _t):ds)) = toAbstract (C.AST ds)


instance ToAbstract C.FLHS A.FLHS where
  toAbstract (C.FLHSName n) = A.FLHSName <$> toAbstract n


instance ToAbstract C.FRHS A.FRHS where
  toAbstract (C.FRHSAssign e) = A.FRHSAssign <$> toAbstract e


instance ToAbstract C.Name A.Name where
  toAbstract n = do
    i <- fresh
    pure $ A.Name { A.nameId = i, A.nameConcrete = n }


mkMaybeOldName :: C.Name -> InScopeType -> NameClassifier -> MaybeOldName
mkMaybeOldName n c nc =
  MaybeOldName { monName = n, monHowBind = HowBind { hbBindsAs = c, hbClashesWith = nc } }


mustBeNew :: C.Name -> InScopeType -> MaybeOldName
mustBeNew n c = mkMaybeOldName n c NCAll


fdefLookingForSignature :: C.Name -> MaybeOldName
fdefLookingForSignature n = mkMaybeOldName n ISDef (AllExcept [NCT ISSig])


data MaybeOldName = MaybeOldName
  { monName :: C.Name
  , monHowBind :: HowBind
  }

instance ToAbstract MaybeOldName A.Name where
  -- we try to find an existing instance of the name, but if the name
  -- isn't in scope, then we initialise it here.
  toAbstract mon = do
    let n = monName mon
        -- let's pretend it's unqualified for now
        -- TODO: fail if they try and use an actually-qualified name here (2020-03-07)
        qn = C.Unqualified n
    rn <- maybeResolveNameCurrentScope qn
    case rn of

      -- we didn't find anything in scope, so we bind fresh
      Nothing -> do
        n' <- toAbstract n
        bindNameCurrentScope (monHowBind mon) n n'
        pure n'

      -- we found a local variable, so we can't make a new definition (yet)
      -- (currently we should always clash with locals, as
      -- this is treated as a 'top-level' definitions check)
      Just ResolvedVar{} -> throwError $ nameClash n

      -- we found something else we don't clash with, so we override!
      -- (this lets you switch a signature to a definition, for example)
      Just r -> do
        let n' = nameOf r
        bindNameCurrentScope (monHowBind mon) n n'
        pure n'


newtype OldQName = OldQName C.QName

instance ToAbstract OldQName A.Expr where
  toAbstract (OldQName n) = do
    -- this will fail if the name isn't in scope (which is exactly
    -- what we want to happen, as we are trying to look up an existing
    -- name)
    rn <- maybeResolveNameCurrentScope n
    -- TODO: add support for resolving constructors (2020-06-12)
    case rn of
      Just (ResolvedVar n) -> pure $ A.Var n
      Just rn -> pure $ A.Def (nameOf rn)
      Nothing -> case pprintShow n of
                   "Nat" -> pure A.NatTy
                   "succ" -> pure A.NSucc
                   "zero" -> pure A.NZero
                   _ -> throwError $ unknownNameErr n


instance ToAbstract C.PiBindings ([A.TypedBinding], Locals) where
  toAbstract (C.PiBindings []) = pure ([], [])
  toAbstract (C.PiBindings (arg:bs)) = do
    let i  = isHidden arg
        ns = fmap C.unBoundName $ C.bindsWhat arg
        g  = tryIt C.grading (un (C.unTB arg))
        s  :: C.Expr = typeOf arg
    ns' <- mapM toAbstract ns
    s' <- toAbstract s
    g' <- maybe newImplicitGrading toAbstract g
    let nsLocs = zip ns ns'
    (piBinds, locals) <- withLocals nsLocs $ toAbstract (C.PiBindings bs)
    pure (fmap (A.mkTypedBinding i g' s' . A.bindName) ns' <> piBinds, nsLocs <> locals)


instance ToAbstract C.LambdaArgs ([A.LambdaArg], Locals) where
  toAbstract [] = pure ([], [])
  toAbstract (arg:bs) = do
    let i = isHidden arg
        ns = fmap C.unBoundName $ C.bindsWhat arg
        g  = join $ tryIt (tryMight C.grading) (un arg)
        s :: C.Expr = idc typeOf (const C.Implicit) $ un arg
    ns' <- mapM toAbstract ns
    s' <- toAbstract s
    g' <- maybe newImplicitGrading toAbstract g
    let nsLocs = zip ns ns'
    (args, locals) <- withLocals nsLocs $ toAbstract bs
    pure (fmap (A.mkLambdaArg i g' s' . A.bindName) ns' <> args, nsLocs <> locals)


instance ToAbstract C.Grading A.Grading where
  toAbstract g = A.mkGrading <$> toAbstract (C.subjectGrade g) <*> toAbstract (C.subjectTypeGrade g)

instance ToAbstract C.Grade A.Grade' where
  toAbstract g = toAbstract g >>= (return . A.grade)

instance ToAbstract C.Grade A.Grade where
  toAbstract C.GZero = pure A.gradeZero
  toAbstract C.GOne  = pure A.gradeOne
  toAbstract C.GInf  = pure A.gradeInf
  toAbstract (C.GPlus g1 g2)  = A.mkGradePlus  <$> toAbstract g1 <*> toAbstract g2
  toAbstract (C.GTimes g1 g2) = A.mkGradeTimes <$> toAbstract g1 <*> toAbstract g2
  toAbstract (C.GLub g1 g2)   = A.mkGradeLub   <$> toAbstract g1 <*> toAbstract g2
  toAbstract (C.GExpr e@(C.Ident v))
    -- TODO: make this more robust, it's really hacky at the moment... (2020-06-21)
    | pprintShow v `elem` ["Irrelevant", "Private", "Public", "Lo", "Hi"] = do
    -- we are treating privacy levels as a form of builtin for now, so
    -- we check whether they are bound in scope already, in which case
    -- we need to just treat them as non builtin expressions
    rn <- maybeResolveNameCurrentScope v
    case rn of
      Nothing -> case pprintShow v of
                   "Irrelevant" -> pure A.gradeZero{A.gradeTy=A.PrivacyLevel}
                   "Private" -> pure A.gradeOne{A.gradeTy=A.PrivacyLevel}
                   -- public is encoded as '2'
                   "Public" -> pure A.Grade{A.grade=A.GEnc 2, A.gradeTy=A.PrivacyLevel}
                   "Hi" -> pure A.gradeZero{A.gradeTy=A.SecurityLevel}
                   "Lo" -> pure A.gradeOne{A.gradeTy=A.SecurityLevel}
                   _ -> error "impossible at toAbstract C.Grade A.Grade"
      Just _  -> do
        e' <- toAbstract e
        pure A.Grade{A.grade=A.GExpr e', A.gradeTy=A.GSImplicit}
  toAbstract (C.GExpr e) = do
    e' <- toAbstract e
    pure A.Grade{A.grade=A.GExpr e', A.gradeTy=A.GSImplicit}
  toAbstract (C.GSig g e@(C.Ident v))
    -- TODO: make this more robust, it's really hacky at the moment... (2020-06-21)
    | pprintShow v `elem` ["Privacy", "Security"] = do
    -- we are treating privacy levels as a form of builtin for now, so
    -- we check whether they are bound in scope already, in which case
    -- we need to just treat them as non builtin expressions
    rn <- maybeResolveNameCurrentScope v
    g <- toAbstract g
    case rn of
      Nothing -> case pprintShow v of
                   "Privacy" -> pure A.Grade{A.grade=A.GSig g A.PrivacyLevel,A.gradeTy=A.PrivacyLevel}
                   "Security" -> pure A.Grade{A.grade=A.GSig g A.SecurityLevel,A.gradeTy=A.SecurityLevel}
                   _ -> error "impossible at toAbstract (type) C.Grade A.Grade"
      Just _  -> do
        e' <- toAbstract e
        pure A.Grade{A.grade=A.GExpr e', A.gradeTy=A.GSImplicit}
  toAbstract (C.GSig g t) = do
    g <- toAbstract g
    t <- toAbstract t
    pure A.Grade{A.grade=A.GSig g (A.GSExpr t), A.gradeTy=A.GSImplicit}
  toAbstract (C.GParens g) = toAbstract g


instance ToAbstract C.Expr A.Expr where
  toAbstract (C.Ident v) = toAbstract (OldQName v)
  toAbstract C.UnitTy = pure A.UnitTy
  toAbstract C.Unit = pure A.Unit
  toAbstract C.UniverseNoLevel = A.univMeta <$> getFreshMetaId
  toAbstract (C.BoxTy g t) = A.BoxTy <$> toAbstract g <*> toAbstract t
  toAbstract (C.Box t) = A.Box <$> toAbstract t
  toAbstract (C.Universe l) = pure $ A.Universe (A.LMax [A.LitLevel l])
  toAbstract (C.Fun tA tB) = do
    name <- newIgnoredName
    (tA, tB) <- toAbstract (tA, tB)
    subG <- newImplicitGrade
    subTyG <- newZeroGrade
    pure . A.FunTy $ A.mkAbsGr name tA subG subTyG tB
  toAbstract (C.Pi piBinds expr) = do
    (piBinds' :: [A.TypedBinding], mySpace) <- toAbstract piBinds
    expr' <- withLocals mySpace $ toAbstract expr
    pure $ foldr (\b f -> A.FunTy (A.mkAbs' (isHidden b) (A.unBoundName . un. un . un . A.unTB $ b) (A.grading b) (typeOf b) f)) expr' piBinds'
  toAbstract (C.Lam args expr) = do
    (args' :: [A.LambdaArg], mySpace) <- toAbstract args
    expr' <- withLocals mySpace $ toAbstract expr
    pure $ foldr (\b f -> A.Lam (A.mkAbs' (isHidden b) (A.unBoundName . un. un . un . A.unTB $ b) (A.grading b) (typeOf b) f)) expr' args'
  toAbstract (C.NondepProductTy tA tB) = do
    name <- newIgnoredName
    (tA, tB) <- toAbstract (tA, tB)
    subG <- newImplicitGrade
    subTyG <- newZeroGrade
    pure $ A.ProductTy (A.mkAbsGr name tA subG subTyG tB)
  toAbstract (C.ProductTy (x, r, tA) tB) = do
    (v, r, tA) <- toAbstract (x, r, tA)
    tB <- withLocals [(x, v)] $ toAbstract tB
    pure $ A.ProductTy $ A.mkAbsGr v tA A.gradeZero r tB
  toAbstract (C.Pair l r) = A.Pair <$> toAbstract l <*> toAbstract r
  toAbstract (C.App f e) = A.App <$> toAbstract f <*> toAbstract e
  toAbstract (C.Sig e t) = A.Sig <$> toAbstract e <*> toAbstract t
  toAbstract C.Hole = newHole
  toAbstract C.Implicit = newImplicit
  toAbstract (C.Case e tp binds) = do
    e <- toAbstract e
    tp <- case tp of
            Nothing -> pure Nothing
            Just (p, t) -> do
              (A.CasePatBound p t) <- toAbstract (C.CasePatBound p t)
              pure (Just (p, t))
    binds <- mapM toAbstract (NE.toList $ NE.sort binds)
    pure $ A.Case e tp binds
  -- TODO: add special handling for brace arguments (2020-03-09)
  toAbstract (C.BraceArg e) = toAbstract (un e)
  toAbstract (C.Parens   e) = toAbstract e


instance ToAbstract C.CaseBinding A.CaseBinding where
  toAbstract (C.CasePatBound p e) = do
    (p, names) <- toAbstract p
    e <- withLocals names $ toAbstract e
    pure $ A.CasePatBound p e


instance ToAbstract C.Pattern (A.Pattern, Locals) where
  -- TODO: make sure we don't allow repeated names in patterns (2020-03-05)
  -- TODO: add support for binding the vars for the type (2020-03-05)
  toAbstract (C.PIdent n) = do
    c  <- maybeResolveMeAConstructor n
    case c of
      -- the name was a constructor, so we treat it as an empty application
      Just c' -> pure (A.PCon c' [], [])

      -- we couldn't find a constructor
      Nothing -> do
        -- we check if this is a qualified name---if it is qualified then
        -- it must be a constructor, so we fail---otherwise we bind the name
        case toUnqualifiedName n of
          Nothing -> throwError $ nonConstructorInPattern n
          Just n' -> do
            n'' <- toAbstract n'
            pure (A.PVar (A.BindName n''), [(n', n'')])
  toAbstract (C.PPair p1 p2) = do
    (p1', p1vs) <- toAbstract p1
    (p2', p2vs) <- toAbstract p2
    pure $ (A.PPair p1' p2', p1vs <> p2vs)
  toAbstract C.PUnit = pure (A.PUnit, [])
  toAbstract p@(C.PApp c args) = do
    c' <- maybeResolveMeAConstructor c
    c' <- case c' of
            Nothing -> throwError $ notAValidPattern p
            Just c' -> pure c'
    (args', binds) <- fmap (second concat) $ fmap unzip $ mapM toAbstract args
    pure $ (A.PCon c' args', binds)
  toAbstract (C.PParens p) = toAbstract p
  toAbstract (C.PBox p) = first A.PBox <$> toAbstract p


-- | Try and resolve the name as a constructor.
maybeResolveMeAConstructor :: C.QName -> SM (Maybe A.Name)
maybeResolveMeAConstructor n = do
  res <- maybeResolveNameCurrentScope n
  case res of
    Just (ResolvedCon cname) -> pure (Just cname)
    _ -> pure Nothing


-- | Only yield the name if it is unqualified.
toUnqualifiedName :: C.QName -> Maybe C.Name
toUnqualifiedName C.Qualified{} = Nothing
toUnqualifiedName (C.Unqualified n) = pure n


----------------------------
----- Helper Instances -----
----------------------------


instance (ToAbstract a a', ToAbstract b b') => ToAbstract (a, b) (a', b') where
  toAbstract (x, y) = do
    x <- toAbstract x
    y <- toAbstract y
    pure (x, y)


instance (ToAbstract a a', ToAbstract b b', ToAbstract c c') => ToAbstract (a, b, c) (a', b', c') where
  toAbstract (x, y, z) = do
    (x, (y, z)) <- toAbstract (x, (y, z))
    pure (x, y, z)


newHole :: SM A.Expr
newHole = A.mkHole <$> getFreshMetaId


newImplicit :: SM A.Expr
newImplicit = A.mkImplicit <$> getFreshMetaId


newImplicitGrading :: SM A.Grading
newImplicitGrading = A.mkGrading <$> newImplicitGrade <*> newImplicitGrade


newImplicitGrade, newZeroGrade :: SM A.Grade
newImplicitGrade = toAbstract C.implicitGrade
newZeroGrade = toAbstract C.GZero
