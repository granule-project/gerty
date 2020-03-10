{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Language.Dlam.TypeChecking.Monad.Base
  (
   -- * Type checker monad
   CM

   -- * State
  , CheckerState
  , runNewChecker
  , TCResult
  , tcrLog
  , tcrRes

  , getFreshNameId

  -- ** Scope
  , lookupType
  , setType
  , withTypedVariable
  , lookupValue
  , setValue

  -- * Environment
  , withLocalCheckingOf

  -- * Exceptions and error handling
  , TCErr

  -- ** Implementation errors
  , notImplemented

  -- ** Scope errors
  , scoperError

  -- ** Synthesis errors
  , cannotSynthTypeForExpr
  , cannotSynthExprForType

  -- ** Type errors
  , tyMismatch
  , expectedInferredTypeForm

  -- ** Pattern errors
  , patternMismatch

  -- ** Parse errors
  , parseError
  ) where

import Control.Exception (Exception)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Map as M

import Language.Dlam.Builtins
import qualified Language.Dlam.Scoping.Monad.Exception as SE
import Language.Dlam.Syntax.Abstract
import Language.Dlam.Syntax.Common (NameId)
import Language.Dlam.Util.Pretty (pprintShow)


data CheckerState
  = CheckerState
    { typingScope :: M.Map Name Expr
    , valueScope :: M.Map Name Expr
    , nextNameId :: NameId
    -- ^ Unique NameId for naming.
    }


-- | The starting checker state.
startCheckerState :: CheckerState
startCheckerState =
  CheckerState { typingScope = builtinsTypes
               , valueScope = builtinsValues
               , nextNameId = 0
               }


-- | The checker monad.
newtype CM a =
  CM { runCM :: ExceptT TCErr (WriterT TCLog (ReaderT TCEnv (State CheckerState))) a }
  deriving ( Applicative, Functor, Monad
           , MonadReader TCEnv
           , MonadState CheckerState
           , MonadWriter TCLog
           , MonadError TCErr)


type TCLog = String


data TCResult a
  = TCResult
    { tcrLog :: TCLog
    , tcrRes :: Either TCErr a
    }


runChecker :: TCEnv -> CheckerState -> CM a -> TCResult a
runChecker env st p =
  let (res, log) = evalState (runReaderT (runWriterT $ (runExceptT (runCM p))) env) st
  in TCResult { tcrLog = log, tcrRes = res }


runNewChecker :: CM a -> TCResult a
runNewChecker = runChecker startEnv startCheckerState



-- | Get a unique NameId.
getFreshNameId :: CM NameId
getFreshNameId = get >>= \s -> let c = nextNameId s in put s { nextNameId = succ c } >> pure c


lookupType :: Name -> CM (Maybe Expr)
lookupType n = M.lookup n . typingScope <$> get


setType :: Name -> Expr -> CM ()
setType n t = modify (\s -> s { typingScope = M.insert n t (typingScope s) })


-- | Execute the action with the given identifier bound with the given type.
withTypedVariable :: Name -> Expr -> CM a -> CM a
withTypedVariable v t p = do
  st <- get
  setType v t
  res <- p
  -- restore the typing scope
  modify (\s -> s { typingScope = typingScope st})
  pure res


lookupValue :: Name -> CM (Maybe Expr)
lookupValue n = M.lookup n . valueScope <$> get


setValue :: Name -> Expr -> CM ()
setValue n t = modify (\s -> s { valueScope = M.insert n t (valueScope s) })


------------------------------
-- * Type checking environment
------------------------------


-- | Type-checking environment.
data TCEnv = TCEnv
  { tceCurrentExpr :: Maybe Expr
  -- ^ Expression currently being checked (if any).
  }


tceSetCurrentExpr :: Expr -> TCEnv -> TCEnv
tceSetCurrentExpr e env = env { tceCurrentExpr = Just e }


startEnv :: TCEnv
startEnv = TCEnv { tceCurrentExpr = Nothing }


-- | Indicate that we are now checking the given expression when running the action.
withLocalCheckingOf :: Expr -> CM a -> CM a
withLocalCheckingOf e = local (tceSetCurrentExpr e)


-----------------------------------------
----- Exceptions and error handling -----
-----------------------------------------


data TCError
  ---------------------------
  -- Implementation Errors --
  ---------------------------

  = NotImplemented String

  ------------------
  -- Scope Errors --
  ------------------

  | ScoperError SE.SCError

  ------------------
  -- Synth Errors --
  ------------------

  | CannotSynthTypeForExpr

  | CannotSynthExprForType Expr

  -----------------
  -- Type Errors --
  -----------------

  | TypeMismatch Expr Expr

  | ExpectedInferredTypeForm String Expr

  --------------------
  -- Pattern Errors --
  --------------------

  | PatternMismatch Pattern Expr

  ------------------
  -- Parse Errors --
  ------------------

  | ParseError String




instance Show TCError where
  show (NotImplemented e) = e
  show (ScoperError e) = "The following was raised when scope-checking: " <> show e
  show CannotSynthTypeForExpr = "I couldn't synthesise a type for the expression."
  show (CannotSynthExprForType t) =
    "I was asked to try and synthesise a term of type '" <> pprintShow t <> "' but I wasn't able to do so."
  show (TypeMismatch tyExpected tyActual) =
    "Expected type '" <> pprintShow tyExpected <> "' but got '" <> pprintShow tyActual <> "'"
  show (ExpectedInferredTypeForm descr t) =
    "I was expecting the expression to have a "
    <> descr <> " type, but instead I found its type to be '"
    <> pprintShow t <> "'"
  show (PatternMismatch p t) =
    "The pattern '" <> pprintShow p <> "' is not valid for type '" <> pprintShow t <> "'"
  show (ParseError e) = e

instance Exception TCError


notImplemented :: String -> CM a
notImplemented descr = throwCM (NotImplemented descr)


-- | Indicate that an issue occurred when performing a scope analysis.
scoperError :: SE.SCError -> CM a
scoperError e = throwCM (ScoperError e)


cannotSynthTypeForExpr :: CM a
cannotSynthTypeForExpr = throwCM CannotSynthTypeForExpr


cannotSynthExprForType :: Expr -> CM a
cannotSynthExprForType t = throwCM (CannotSynthExprForType t)


-- | 'tyMismatch expr tyExpected tyActual' indicates that an expression
-- | was found to have a type that differs from expected.
tyMismatch :: Expr -> Expr -> CM a
tyMismatch tyExpected tyActual =
  throwCM (TypeMismatch tyExpected tyActual)


expectedInferredTypeForm :: String -> Expr -> CM a
expectedInferredTypeForm descr t =
  throwCM (ExpectedInferredTypeForm descr t)


patternMismatch :: Pattern -> Expr -> CM a
patternMismatch p t = throwCM (PatternMismatch p t)


parseError :: String -> CM a
parseError = throwCM . ParseError


-----------------------------------------
----- Errors and exception handling -----
-----------------------------------------


data TCErr = TCErr
  { tcErrErr :: TCError
  -- ^ The underlying error.
  , tcErrEnv :: TCEnv
  -- ^ Environment at point of the error.
  }


instance Exception TCErr


-- | Expression being checked when failure occurred.
tcErrExpr :: TCErr -> Maybe Expr
tcErrExpr = tceCurrentExpr . tcErrEnv


throwCM :: TCError -> CM a
throwCM e = do
  env <- ask
  throwError $ TCErr { tcErrErr = e, tcErrEnv = env }


instance Show TCErr where
  show e = "The following error occurred when type-checking" <> (maybe ": " (\expr -> " '" <> pprintShow expr <> "': ") (tcErrExpr e)) <> show (tcErrErr e)
