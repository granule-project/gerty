{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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

  -- * Environment

  -- ** Scope
  , ScopeInfo(..)
  , lookupLocalVar
  , withLocals
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Map as M

import Language.Dlam.Builtins
import Language.Dlam.Syntax.Abstract
import qualified Language.Dlam.Syntax.Concrete as C
import Language.Dlam.Syntax.Common (NameId)
import Language.Dlam.Scoping.Monad.Exception (SCError)


data ScoperState
  = ScoperState
    { nextNameId :: NameId
    -- ^ Unique NameId for naming.
    }


-- | The starting checker state.
startScoperState :: ScoperState
startScoperState =
  ScoperState { nextNameId = 0 }


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


-------------------------------
-- * Scope checking environment
-------------------------------


-- | Scope-checking environment.
data SCEnv = SCEnv
  { scScope :: ScopeInfo
  -- ^ Current scope information.
  }


data ScopeInfo = ScopeInfo
  { localVars :: M.Map C.Name Name }
    -- ^ Local variables in scope.
    -- TODO: add support for mapping to multiple names for ambiguity
    -- situations (like Agda does) (2020-03-05)


startScopeInfo :: ScopeInfo
startScopeInfo =
  ScopeInfo {
    localVars = M.fromList (fmap (\b -> (nameConcrete (builtinName b), builtinName b)) builtins)
  }


startEnv :: SCEnv
startEnv = SCEnv { scScope = startScopeInfo }


addLocals :: [(C.Name, Name)] -> SCEnv -> SCEnv
addLocals locals sc =
  let oldVars = localVars (scScope sc)
  in sc { scScope = (scScope sc) { localVars = oldVars <> M.fromList locals } }


lookupLocalVar :: C.Name -> SM (Maybe Name)
lookupLocalVar n = M.lookup n . localVars <$> reader scScope


-- | Execute the given action with the specified local variables
-- | (additionally) bound. This restores the scope after checking.
withLocals :: [(C.Name, Name)] -> SM a -> SM a
withLocals locals = local (addLocals locals)
