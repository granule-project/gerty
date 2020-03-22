{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Language.Dlam.TypeChecking.Monad.Base
  (
   -- * Type checker monad
   CM

   -- * Logging
  , Verbosity
  , verbositySilent
  , verbosityInfo
  , verbosityDebug
  , TCLog
  , debug
  , debugBlock
  , info
  , formatLog

   -- * State
  , CheckerState
  , runNewChecker
  , TCResult
  , tcrLog
  , tcrRes

  , getFreshNameId

  -- ** Scope
  , lookupType
  , maybeLookupType
  , setType
  , withTypedVariable
  , lookupValue
  , maybeLookupValue
  , setValue

  -- ** Grading
  , withGradedVariable
  , lookupSubjectRemaining
  , setSubjectRemaining

  -- * Environment
  , withLocalCheckingOf

  -- ** Free Variables
  , lookupFVType
  , lookupFVSubjectRemaining
  , withVarBound
  , withVarTypeBound

  -- * Exceptions and error handling
  , TCErr
  , isSyntaxErr
  , isScopingErr
  , isTypingErr

  -- ** Implementation errors
  , notImplemented
  , hitABug

  -- ** Scope errors
  , scoperError

  -- ** Synthesis errors
  , cannotSynthTypeForExpr
  , cannotSynthExprForType

  -- ** Type errors
  , tyMismatch
  , expectedInferredTypeForm
  , notAType

  -- ** Pattern errors
  , patternMismatch

  -- ** Grading errors
  , usedTooManyTimes

  -- ** Parse errors
  , parseError
  ) where

import Control.Exception (Exception)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Map as M
import qualified Data.Set as Set

import Language.Dlam.Builtins
import qualified Language.Dlam.Scoping.Monad.Exception as SE
import Language.Dlam.Syntax.Abstract
import qualified Language.Dlam.Syntax.Internal as I
import Language.Dlam.Syntax.Common (NameId(..))
import qualified Language.Dlam.Syntax.Concrete.Name as C
import Language.Dlam.Syntax.Parser.Monad (ParseError)
import Language.Dlam.Util.Pretty hiding ((<>))


data CheckerState
  = CheckerState
    { typingScope :: M.Map AName I.Type
    , valueScope :: M.Map AName I.Term
    , provisionScope :: M.Map AName I.Grading
    -- ^ Scope of provisions (how can an assumption be used---grades remaining).
    , nextNameId :: NameId
    -- ^ Unique NameId for naming.
    , debugNesting :: Int
    -- ^ Counter used to make it easier to locate debugging messages.
    }


-- | The starting checker state.
startCheckerState :: CheckerState
startCheckerState =
  CheckerState { typingScope = builtinsTypes
               , valueScope = builtinsValues
               , provisionScope = M.empty
               , nextNameId = 0
               , debugNesting = 0
               }


-- | The checker monad.
newtype CM a =
  CM { runCM :: ExceptT TCErr (WriterT TCLog (ReaderT TCEnv (State CheckerState))) a }
  deriving ( Applicative, Functor, Monad
           , MonadReader TCEnv
           , MonadState CheckerState
           , MonadWriter TCLog
           , MonadError TCErr)


-------------------
----- Logging -----
-------------------


type TCLog = [LogMessage]


data LogMessage = InfoMessage String | DebugMessage String


instance Show LogMessage where
  show (InfoMessage s) = "INFO: " <> s
  show (DebugMessage s) = "DEBUG: " <> s


messageLevel :: LogMessage -> Verbosity
messageLevel InfoMessage{} = Info
messageLevel DebugMessage{} = Debug


data Verbosity = Silent | Info | Debug
  deriving (Eq, Ord)


verbositySilent, verbosityInfo, verbosityDebug :: Verbosity
verbositySilent = Silent
verbosityInfo = Info
verbosityDebug = Debug


-- | Write some debugging information.
debug :: String -> CM ()
debug msg = do
  debugNest <- fmap debugNesting get
  let formattedMessage = if debugNest == 0 then msg else unwords [replicate debugNest '>', msg]
  tell . pure . DebugMessage $ formattedMessage


info :: String -> CM ()
info = tell . pure . InfoMessage


-- | Indicate we are entering a debug block.
debugOpen :: CM ()
debugOpen = modify (\s -> s { debugNesting = succ (debugNesting s) })


-- | Indicate we are leaving a debug block.
debugClose :: CM ()
debugClose = modify (\s -> s { debugNesting = pred (debugNesting s) })


-- | Wrap the action in some debugging messages. The final message can
-- | use the result of the action.
debugBlock :: String -> String -> (a -> String) -> CM a -> CM a
debugBlock blockDesc' open close action = do
  let blockDesc = if blockDesc' /= "" then blockDesc' <> ": " else ""
  debug (blockDesc <> open)
  debugOpen
  res <- action
  debugClose
  debug (blockDesc <> close res)
  pure res


filterLog :: Verbosity -> TCLog -> TCLog
filterLog l = filter ((<= l) . messageLevel)


formatLog :: Verbosity -> TCLog -> String
formatLog v = unlines . fmap show . filterLog v


--------------------
----- Checking -----
--------------------


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


maybeLookupType :: AName -> CM (Maybe I.Type)
maybeLookupType n = M.lookup n . typingScope <$> get


lookupType :: AName -> CM I.Type
lookupType n =
  debugBlock "lookupType'"
    ("looking up type of: " <> pprintShow n)
    (\t -> "found type '" <> pprintShow t <> "' for variable '" <> pprintShow n <> "'")
    (maybeLookupType n >>= maybe (scoperError $ SE.unknownNameErr (C.Unqualified $ nameConcrete n)) pure)


setType :: AName -> I.Type -> CM ()
setType n t = modify (\s -> s { typingScope = M.insert n t (typingScope s) })


-- | Execute the action with the given identifier bound with the given type.
withTypedVariable :: AName -> I.Type -> CM a -> CM a
withTypedVariable v t p = do
  debug $ "setting type of variable '" <> pprintShow v <> "' to '" <> pprintShow t <> "'"
  st <- get
  setType v t
  res <- p
  -- restore the typing scope
  modify (\s -> s { typingScope = typingScope st})
  debug $ "unsetting type of variable '" <> pprintShow v <> "' (previously '" <> pprintShow t <> "')"
  pure res


maybeLookupValue :: AName -> CM (Maybe I.Term)
maybeLookupValue n = M.lookup n . valueScope <$> get


lookupValue :: AName -> CM I.Term
lookupValue n =
  maybeLookupValue n >>= maybe (scoperError $ SE.unknownNameErr (C.Unqualified $ nameConcrete n)) pure


setValue :: AName -> I.Term -> CM ()
setValue n t = modify (\s -> s { valueScope = M.insert n t (valueScope s) })


-------------
-- Grading --
-------------


lookupRemaining :: AName -> CM (Maybe I.Grading)
lookupRemaining n = M.lookup n . provisionScope <$> get


lookupSubjectRemaining :: AName -> CM (Maybe I.Grade)
lookupSubjectRemaining n = fmap I.subjectGrade <$> lookupRemaining n


modifyRemaining :: AName -> (I.Grading -> I.Grading) -> CM ()
modifyRemaining n f = do
  prev <- lookupRemaining n
  case prev of
    Nothing -> pure ()
    Just prev -> setRemaining n (f prev)


setRemaining :: AName -> I.Grading -> CM ()
setRemaining n g = modify (\s -> s { provisionScope = M.insert n g (provisionScope s) })


setSubjectRemaining :: AName -> I.Grade -> CM ()
setSubjectRemaining n g = modifyRemaining n (\gs -> I.mkGrading g (I.subjectTypeGrade gs))


-- | Execute the action with the given identifier bound with the given grading.
withGradedVariable :: AName -> I.Grading -> CM a -> CM a
withGradedVariable v gr p = do
  st <- get
  setRemaining v gr
  res <- p
  -- restore the provision scope
  modify (\s -> s { provisionScope = provisionScope st})
  pure res


------------------------------
-- * Type checking environment
------------------------------


-- | Type-checking environment.
data TCEnv = TCEnv
  { tceCurrentExpr :: Maybe Expr
  -- ^ Expression currently being checked (if any).
  , tceFVContext :: FreeVarContext
  -- ^ Current context of free variables.
  , inScopeSet :: Set.Set FreeVar
  -- ^ Currently known free variables.
  }


tceSetCurrentExpr :: Expr -> TCEnv -> TCEnv
tceSetCurrentExpr e env = env { tceCurrentExpr = Just e }


startEnv :: TCEnv
startEnv = TCEnv { tceCurrentExpr = Nothing, tceFVContext = emptyContext, inScopeSet = Set.empty }


-- | Indicate that we are now checking the given expression when running the action.
withLocalCheckingOf :: Expr -> CM a -> CM a
withLocalCheckingOf e = local (tceSetCurrentExpr e)


---------------------------
-- Free Variable Context --
---------------------------


type FreeVar = AnyName


type FreeVarInfo = (I.Grading, I.Type)


newtype FreeVarContext = FVC { unFVC :: M.Map FreeVar FreeVarInfo }


fvcToList :: FreeVarContext -> [(FreeVar, FreeVarInfo)]
fvcToList = M.toList . unFVC


fvcMapOp :: (M.Map FreeVar FreeVarInfo -> a) -> FreeVarContext -> a
fvcMapOp f (FVC m) = f m


fvcMap :: (M.Map FreeVar FreeVarInfo -> M.Map FreeVar FreeVarInfo) -> FreeVarContext -> FreeVarContext
fvcMap f = fvcMapOp (FVC . f)


emptyContext :: FreeVarContext
emptyContext = FVC M.empty


instance Pretty FreeVarContext where
  pprint xs = hsep $ punctuate comma $ fmap pprintBinding (fvcToList xs)
    where pprintBinding (n, (g, t)) = pprint n <+> text "->" <+> char '{' <+> pprint g `beside` char ',' <+> pprint t <+> char '}'


tceAddInScope :: [AnyName] -> TCEnv -> TCEnv
tceAddInScope names env =
  env { inScopeSet = Set.union (Set.fromList names) (inScopeSet env) }


getInScope :: CM (Set.Set FreeVar)
getInScope = fmap inScopeSet ask


-- | Execute the action with the given free variables in scope.
withInScope :: [AnyName] -> CM a -> CM a
withInScope names = local (tceAddInScope names)


getContext :: CM FreeVarContext
getContext = fmap tceFVContext ask


tceAddBinding :: FreeVar -> FreeVarInfo -> TCEnv -> TCEnv
tceAddBinding v bod env = env { tceFVContext = fvcMap (M.insert v bod) (tceFVContext env) }


-- | Execute the action with the given free variable bound with the
-- | given grading and type.
withVarBound :: (Rep n) => I.Name n -> I.Grading -> I.Type -> CM a -> CM a
withVarBound n g ty =
  local (tceAddBinding (I.AnyName n) (g, ty))


-- | Execute the action with the given free variable bound with the
-- | given type (ignoring grading).
withVarTypeBound :: (Rep n) => I.Name n -> I.Type -> CM a -> CM a
withVarTypeBound n ty = withVarBound n I.thatMagicalGrading ty


lookupFVInfo :: (Rep n) => I.Name n -> CM FreeVarInfo
lookupFVInfo n = do
  ctx <- getContext
  maybe (hitABug $ "tried to look up the type of free variable '" <> pprintShow n <> "' but it wasn't in scope. Scope checking or type-checking is broken.\nContext was: " <> pprintShow ctx) pure . fvcMapOp (M.lookup (nameToFreeVar n)) =<< getContext
  where nameToFreeVar = I.AnyName


lookupFVType :: (Rep n) => I.Name n -> CM I.Type
lookupFVType = fmap snd . lookupFVInfo


lookupFVSubjectRemaining :: (Rep n) => I.Name n -> CM I.Grade
lookupFVSubjectRemaining = fmap (I.subjectGrade . fst) . lookupFVInfo


-----------------------------------------
----- Exceptions and error handling -----
-----------------------------------------


data TCError
  ---------------------------
  -- Implementation Errors --
  ---------------------------

  = NotImplemented String
  | ImplementationBug String

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

  | TypeMismatch I.Type I.Type

  | ExpectedInferredTypeForm String I.Type
  | NotAType

  --------------------
  -- Pattern Errors --
  --------------------

  | PatternMismatch Pattern Expr

  --------------------
  -- Grading Errors --
  --------------------

  | UsedTooManyTimes (I.Name ())

  ------------------
  -- Parse Errors --
  ------------------

  | ParseError ParseError




instance Show TCError where
  show (NotImplemented e) = e
  show (ImplementationBug e) = "[BUG]: " <> e
  show CannotSynthTypeForExpr = "I couldn't synthesise a type for the expression."
  show (CannotSynthExprForType t) =
    "I was asked to try and synthesise a term of type '" <> pprintShow t <> "' but I wasn't able to do so."
  show (TypeMismatch tyExpected tyActual) =
    "Expected type '" <> pprintShow tyExpected <> "' but got '" <> pprintShow tyActual <> "'"
  show (ExpectedInferredTypeForm descr t) =
    "I was expecting the expression to have a "
    <> descr <> " type, but instead I found its type to be '"
    <> pprintShow t <> "'"
  show NotAType = "I was expecting the expression to be a type, but it wasn't."
  show (PatternMismatch p t) =
    "The pattern '" <> pprintShow p <> "' is not valid for type '" <> pprintShow t <> "'"
  show (UsedTooManyTimes n) =
    "'" <> pprintShow n <> "' is used too many times."
  show (ParseError e) = show e
  show (ScoperError e) = show e

instance Exception TCError


notImplemented :: String -> CM a
notImplemented descr = throwCM (NotImplemented descr)


hitABug :: String -> CM a
hitABug descr = throwCM (ImplementationBug descr)


-- | Indicate that an issue occurred when performing a scope analysis.
scoperError :: SE.SCError -> CM a
scoperError e = throwCM (ScoperError e)


cannotSynthTypeForExpr :: CM a
cannotSynthTypeForExpr = throwCM CannotSynthTypeForExpr


cannotSynthExprForType :: Expr -> CM a
cannotSynthExprForType t = throwCM (CannotSynthExprForType t)


-- | 'tyMismatch expr tyExpected tyActual' indicates that an expression
-- | was found to have a type that differs from expected.
tyMismatch :: I.Type -> I.Type -> CM a
tyMismatch tyExpected tyActual =
  throwCM (TypeMismatch tyExpected tyActual)


expectedInferredTypeForm :: String -> I.Type -> CM a
expectedInferredTypeForm descr t =
  throwCM (ExpectedInferredTypeForm descr t)


notAType :: CM a
notAType = throwCM NotAType


patternMismatch :: Pattern -> Expr -> CM a
patternMismatch p t = throwCM (PatternMismatch p t)


usedTooManyTimes :: I.Name b -> CM a
usedTooManyTimes = throwCM . UsedTooManyTimes . I.translate


parseError :: ParseError -> CM a
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
  show e = "The following error occurred when " <> phaseMsg <> (maybe ": " (\expr -> " '" <> pprintShow expr <> "': ") (tcErrExpr e)) <> show (tcErrErr e)
    where phaseMsg = case errPhase e of
                       PhaseParsing -> "parsing"
                       PhaseScoping -> "scope checking"
                       PhaseTyping  -> "type-checking"


data ProgramPhase = PhaseParsing | PhaseScoping | PhaseTyping
  deriving (Show, Eq, Ord)


-- | In which phase was the error raised.
errPhase :: TCErr -> ProgramPhase
errPhase = errPhase' . tcErrErr
  where errPhase' ParseError{}  = PhaseParsing
        errPhase' ScoperError{} = PhaseScoping
        errPhase' _             = PhaseTyping


isSyntaxErr, isScopingErr, isTypingErr :: TCErr -> Bool
isSyntaxErr = isPhaseErr PhaseParsing
isScopingErr = isPhaseErr PhaseScoping
isTypingErr = isPhaseErr PhaseTyping


isPhaseErr :: ProgramPhase -> TCErr -> Bool
isPhaseErr phase err = not (isImplementationErr err) && errPhase err == phase


isImplementationErr :: TCErr -> Bool
isImplementationErr e = case tcErrErr e of NotImplemented{} -> True; _ -> False


-----------------------
----- For Unbound -----
-----------------------


instance I.LFresh CM where
  getAvoids = getInScope
  avoid = withInScope
  lfresh n = do
    let s = name2String n
    used <- getAvoids
    pure $ head (filter (\x -> not (Set.member (AnyName x) used)) (map (makeName s) [0..]))
