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

  -- ** Environment

  -- *** Scope
  , ScopeInfo(..)
  , lookupLocalVar
  , withLocals

  -- ** Normalisation
  , lookupNormalForm
  , withExprNormalisingTo

  -- * Exceptions and error handling
  , TCError

  -- ** Implementation errors
  , notImplemented

  -- ** Scope errors
  , unknownNameErr

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

import Language.Dlam.Syntax.Abstract
import qualified Language.Dlam.Syntax.Concrete as C
import Language.Dlam.Syntax.Common (NameId)
import Language.Dlam.Util.Pretty (pprintShow)


data CheckerState
  = CheckerState
    { typingScope :: M.Map Name Expr
    , valueScope :: M.Map Name Expr
    , normalFormEquivalences :: M.Map Expr Expr
    -- ^ If (e1, e2) is in the normalFormEquivalences map, we treat them as equivalent
    -- ^ under normalisation.
    , nextNameId :: NameId
    -- ^ Unique NameId for naming.
    }


-- | The starting checker state.
startCheckerState :: CheckerState
startCheckerState =
  CheckerState { typingScope = builtinsTypes
               , valueScope = builtinsValues
               , normalFormEquivalences = M.empty
               , nextNameId = 0
               }
  where
    builtinsTypes = M.fromList
      (fmap (\bin -> (builtinName bin, builtinType bin)) builtins)
    builtinsValues = M.fromList
      (fmap (\bin -> (builtinName bin, builtinBody bin)) builtins)


-- | The list of builtins.
builtins :: [Builtin]
builtins =
   [ typeTy
   , levelTy, lzero, lsuc, lmax
   , inlTerm, inrTerm
   , natTy, dnzero, dnsucc
   , unitTerm, unitTy
   , idTy, reflTerm
   , emptyTy
   ]


-- | The checker monad.
newtype CM a =
  CM { runCM :: ExceptT TCError (WriterT TCLog (ReaderT TCEnv (State CheckerState))) a }
  deriving ( Applicative, Functor, Monad
           , MonadReader TCEnv
           , MonadState CheckerState
           , MonadWriter TCLog
           , MonadError TCError)


type TCLog = String


data TCResult a
  = TCResult
    { tcrLog :: TCLog
    , tcrRes :: Either TCError a
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


lookupNormalForm :: Expr -> CM (Maybe Expr)
lookupNormalForm n = M.lookup n . normalFormEquivalences <$> get


addNormalFormEquivalence :: Expr -> Expr -> CM ()
addNormalFormEquivalence nf1 nf2 = modify (\s -> s { normalFormEquivalences = M.insert nf1 nf2 (normalFormEquivalences s) })


-- | 'withExprNormalisingTo e nf m' runs 'm', but causes
-- | any expressions that would usually normalise to (the normal form of)
-- | 'e' to instead normalise to 'nf'.
withExprNormalisingTo :: Expr -> Expr -> CM a -> CM a
withExprNormalisingTo e nf p = do
  st <- get
  addNormalFormEquivalence e nf
  res <- p
  -- restore the normal forms
  modify (\s -> s { normalFormEquivalences = normalFormEquivalences st})
  pure res


------------------------------
-- * Type checking environment
------------------------------

-- | Type-checking environment.
data TCEnv = TCEnv
  { tcScope :: ScopeInfo
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


startEnv :: TCEnv
startEnv = TCEnv { tcScope = startScopeInfo }


addLocals :: [(C.Name, Name)] -> TCEnv -> TCEnv
addLocals locals sc =
  let oldVars = localVars (tcScope sc)
  in sc { tcScope = (tcScope sc) { localVars = oldVars <> M.fromList locals } }


lookupLocalVar :: C.Name -> CM (Maybe Name)
lookupLocalVar n = M.lookup n . localVars <$> reader tcScope


-- | Execute the given action with the specified local variables
-- | (additionally) bound. This restores the scope after checking.
withLocals :: [(C.Name, Name)] -> CM a -> CM a
withLocals locals = local (addLocals locals)


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

  | NotInScope C.Name

  ------------------
  -- Synth Errors --
  ------------------

  | CannotSynthTypeForExpr Expr

  | CannotSynthExprForType Expr

  -----------------
  -- Type Errors --
  -----------------

  | TypeMismatch Expr Expr Expr

  | ExpectedInferredTypeForm String Expr Expr

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
  show (NotInScope n) = "Unknown identifier '" <> pprintShow n <> "'"
  show (CannotSynthTypeForExpr expr) =
    "I was asked to try and synthesise a type for '" <> pprintShow expr <> "' but I wasn't able to do so."
  show (CannotSynthExprForType t) =
    "I was asked to try and synthesise a term of type '" <> pprintShow t <> "' but I wasn't able to do so."
  show (TypeMismatch expr tyExpected tyActual) =
    "Error when checking the type of '" <> pprintShow expr <>
    "', expected '" <> pprintShow tyExpected <> "' but got '" <> pprintShow tyActual <> "'"
  show (ExpectedInferredTypeForm descr expr t) =
    "I was expecting the expression '" <> pprintShow expr
    <> "' to have a " <> descr <> " type, but instead I found its type to be '"
    <> pprintShow t <> "'"
  show (PatternMismatch p t) =
    "The pattern '" <> pprintShow p <> "' is not valid for type '" <> pprintShow t <> "'"
  show (ParseError e) = e

instance Exception TCError


notImplemented :: String -> CM a
notImplemented descr = throwError (NotImplemented descr)


-- | Indicate that an identifier is not known to be defined.
unknownNameErr :: C.Name -> CM a
unknownNameErr n = throwError (NotInScope n)


cannotSynthTypeForExpr :: Expr -> CM a
cannotSynthTypeForExpr expr = throwError (CannotSynthTypeForExpr expr)


cannotSynthExprForType :: Expr -> CM a
cannotSynthExprForType t = throwError (CannotSynthExprForType t)


-- | 'tyMismatch expr tyExpected tyActual' indicates that an expression
-- | was found to have a type that differs from expected.
tyMismatch :: Expr -> Expr -> Expr -> CM a
tyMismatch expr tyExpected tyActual =
  throwError (TypeMismatch expr tyExpected tyActual)


expectedInferredTypeForm :: String -> Expr -> Expr -> CM a
expectedInferredTypeForm descr expr t =
  throwError (ExpectedInferredTypeForm descr expr t)


patternMismatch :: Pattern -> Expr -> CM a
patternMismatch p t = throwError (PatternMismatch p t)


parseError :: String -> CM a
parseError = throwError . ParseError
