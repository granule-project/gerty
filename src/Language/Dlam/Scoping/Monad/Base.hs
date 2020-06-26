{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
module Language.Dlam.Scoping.Monad.Base
  (
   -- * Scope checking monad
   SM

   -- * State
  , ScoperState
  , runNewScoper
  , SCResult
  , scrLog
  , scrRes
  , getFreshNameId
  , getFreshMetaId

  -- * Environment

  -- ** Scope
  , ScopeInfo(..)
  , lookupLocalVar
  , lookupLocalQVar
  , withLocals
  -- *** Binding
  , bindNameCurrentScope
  , maybeResolveNameCurrentScope
  , resolveNameCurrentScope
  , HowBind(..)
  , NameClassifier(..)
  , pattern NCAll
  , pattern NCNone
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Map as M

import Language.Dlam.Syntax.Abstract
import qualified Language.Dlam.Syntax.Concrete as C
import Language.Dlam.Syntax.Common (NameId)
import Language.Dlam.Scoping.Monad.Exception
import Language.Dlam.Scoping.Scope


data ScoperState
  = ScoperState
    { nextNameId :: NameId
    -- ^ Unique NameId for naming.
    , scScope :: ScopeInfo
    -- ^ Information about the current scope.
    }


-- | The starting checker state.
startScoperState :: ScoperState
startScoperState =
  ScoperState { nextNameId = 0, scScope = startScopeInfo }


-- | The checker monad.
newtype SM a =
  SM { runSM :: ExceptT SCError (WriterT SCLog (ReaderT SCEnv (State ScoperState))) a }
  deriving ( Applicative, Functor, Monad
           , MonadReader SCEnv
           , MonadState ScoperState
           , MonadWriter SCLog
           , MonadError SCError)


type SCLog = String


data SCResult a
  = SCResult
    { scrLog :: SCLog
    , scrRes :: Either SCError a
    }


runScoper :: SCEnv -> ScoperState -> SM a -> SCResult a
runScoper env st p =
  let (res, log) = evalState (runReaderT (runWriterT $ (runExceptT (runSM p))) env) st
  in SCResult { scrLog = log, scrRes = res }


runNewScoper :: SM a -> SCResult a
runNewScoper = runScoper startEnv startScoperState



-- | Get a unique NameId.
getFreshNameId :: SM NameId
getFreshNameId = get >>= \s -> let c = nextNameId s in put s { nextNameId = succ c } >> pure c


-- | Get a unique MetaId.
getFreshMetaId :: SM MetaId
getFreshMetaId = mkMetaId . fromIntegral <$> getFreshNameId


-------------------------------
-- * Scope checking environment
-------------------------------


-- | Scope-checking environment.
data SCEnv = SCEnv ()


startEnv :: SCEnv
startEnv = SCEnv ()


-----------------------
-- * Scopes and Binding
-----------------------


type LocalVars = M.Map C.Name Name


data ScopeInfo = ScopeInfo
  { scopeLocals :: LocalVars
    -- ^ Local variables in scope.
    -- TODO: add support for mapping to multiple names for ambiguity
    -- situations (like Agda does) (2020-03-05)
  , scopeCurrent :: Scope
  -- ^ Current definition scope.
  }


startScopeInfo :: ScopeInfo
startScopeInfo = ScopeInfo
  { scopeLocals = M.empty
  , scopeCurrent = Scope { scopeNameSpace = mempty }
  }


onScopeInfo :: (ScopeInfo -> ScopeInfo) -> ScoperState -> ScoperState
onScopeInfo f s = s { scScope = f (scScope s) }


addLocals :: [(C.Name, Name)] -> ScoperState -> ScoperState
addLocals locals =
  onScopeInfo $ \si ->
    let oldVars = scopeLocals si
    in si { scopeLocals = oldVars <> M.fromList locals }


setLocals :: LocalVars -> ScoperState -> ScoperState
setLocals locals = onScopeInfo $ \si -> si { scopeLocals = locals }


getScopeInfo :: SM ScopeInfo
getScopeInfo = scScope <$> get


getScopeLocals :: SM LocalVars
getScopeLocals = scopeLocals <$> getScopeInfo


lookupLocalVar :: C.Name -> SM (Maybe Name)
lookupLocalVar n = M.lookup n <$> getScopeLocals


lookupLocalQVar :: C.QName -> SM (Maybe Name)
lookupLocalQVar n = (M.lookup n . M.mapKeys C.Unqualified) <$> getScopeLocals


-- | Execute the given action with the specified local variables
-- | (additionally) bound. This restores the scope after checking.
withLocals :: [(C.Name, Name)] -> SM a -> SM a
withLocals locals act = do
  oldLocals <- getScopeLocals
  modify $ addLocals locals
  res <- act
  modify (setLocals oldLocals)
  pure res


getCurrentScope :: SM Scope
getCurrentScope = scopeCurrent <$> getScopeInfo


modifyCurrentScope :: (Scope -> Scope) -> SM ()
modifyCurrentScope f = modify $ onScopeInfo (\si -> si { scopeCurrent = f (scopeCurrent si) })


-- TODO: we might want this to check locals as well? (2020-03-07)
maybeResolveNameCurrentScope' :: C.QName -> SM (Maybe InScopeName)
maybeResolveNameCurrentScope' n = lookupInScope n <$> getCurrentScope


doesNameExistInCurrentScope :: NameClassifier -> C.QName -> SM Bool
doesNameExistInCurrentScope nc n = maybe False (any (willItClash nc) . howBound) <$> maybeResolveNameCurrentScope' n


bindNameCurrentScope :: HowBind -> C.Name -> Name -> SM ()
bindNameCurrentScope hb cn an = do
  isBound <- doesNameExistInCurrentScope (hbClashesWith hb) (C.Unqualified cn)
  if isBound
  then throwError $ nameClash cn
  else modifyCurrentScope (addNameToScope (hbBindsAs hb) cn an)


data NameClassifier
  -- | Clashes with the given scope type.
  = NCT InScopeType
  -- | Clashes with all of the given classifiers.
  | NCAnd [NameClassifier]
  -- | Clashes with everything except the given classifiers.
  | AllExcept [NameClassifier]


-- | Clashes with everything.
pattern NCAll :: NameClassifier
pattern NCAll = AllExcept []


-- | Doesn't clash with anything.
pattern NCNone :: NameClassifier
pattern NCNone = NCAnd []


-- | Information for performing a binding.
data HowBind = HowBind
  { hbBindsAs :: InScopeType
  , hbClashesWith :: NameClassifier
  }


willItClash :: NameClassifier -> InScopeType -> Bool
willItClash (AllExcept ps) t = not $ any (`willItClash` t) ps
willItClash (NCAnd ps) t = any (`willItClash` t) ps
willItClash (NCT t1) t2 = t1 == t2


maybeResolveNameCurrentScope :: C.QName -> SM (Maybe ResolvedName)
maybeResolveNameCurrentScope n = do
  local <- lookupLocalQVar n
  case local of
    Just ld -> pure . Just $ ResolvedVar ld
    Nothing -> do
      ot <- lookupInScope n <$> getCurrentScope
      case ot of
        Nothing -> pure Nothing
        Just r  ->
          if (ISDef `elem` howBound r) then pure . Just $ ResolvedDef (isnName r)
          else if (ISSig `elem` howBound r) then pure . Just $ ResolvedSig (isnName r)
          else throwError . notImplemented $ "I don't yet know how to resolve " <> show r


resolveNameCurrentScope :: C.QName -> SM ResolvedName
resolveNameCurrentScope n =
  maybe (throwError $ unknownNameErr n) pure =<< maybeResolveNameCurrentScope n
