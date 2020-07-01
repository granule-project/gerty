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
  , runNewCheckerWithOpts
  , TCResult
  , tcrLog
  , tcrRes

  , getFreshNameId
  , getFreshName
  , getFreshMetaId

  -- ** Scope
  , lookupType
  , setType
  , withTypedVariable
  , lookupValue
  , setValue
  , withValuedVariable

  -- ** Grading
  , Stage(..)

  -- * Environment
  , withLocalCheckingOf
  , withCheckingOfTopLevel

  -- ** Options
  , TCOpts(..)
  , defaultTCOpts
  , isBenchmarking
  , isOptimising
  , shouldSimplifySMT

  -- * Predicates
  , getPredicateStack
  , resetPredicateStack
  , addConstraint
  , existential
  , universal
  , concludeImplication
  , newConjunct

  -- * Exceptions and error handling
  , TCErr
  , throwCM
  , isSyntaxErr
  , isScopingErr
  , isTypingErr
  , SolverError

  -- ** Implementation errors
  , notImplemented
  , internalBug

  -- ** Scope errors
  , scoperError

  -- ** Synthesis errors
  , cannotSynthTypeForExpr
  , cannotSynthExprForType

  -- ** Type errors
  , tyMismatch
  , tyMismatchAt
  , expectedInferredTypeForm

  -- ** Pattern errors
  , patternMismatch

  -- ** Grading errors
  , gradeMismatchAt
  , gradeMismatchAt'
  , gradeTyMismatch
  , solverNotValid
  , solverError
  , solverTimeout
  , solverError'

  -- ** Parse errors
  , parseError
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Map as M

import qualified Language.Dlam.Scoping.Monad.Exception as SE
import Language.Dlam.Syntax.Abstract
import Language.Dlam.Syntax.Common (NameId)
import qualified Language.Dlam.Syntax.Concrete as C
import Language.Dlam.Syntax.Parser.Monad (ParseError)
import Language.Dlam.Util.Pretty hiding ((<>))

import Language.Dlam.TypeChecking.Predicates

data CheckerState
  = CheckerState
    { typingScope :: M.Map Name Expr
    , valueScope :: M.Map Name Expr
    , nextNameId :: NameId
    -- ^ Unique NameId for naming.
    , debugNesting :: Int
    -- ^ Counter used to make it easier to locate debugging messages.
    , predicateStack :: [Pred]
    }


-- | The starting checker state.
startCheckerState :: CheckerState
startCheckerState =
  CheckerState { typingScope = mempty
               , valueScope = mempty
               , nextNameId = 0
               , debugNesting = 0
               , predicateStack = []
               }



-- | The checker monad.
newtype CM a =
  CM { runCM :: ExceptT TCErr (WriterT TCLog (ReaderT TCEnv (StateT CheckerState IO))) a }
  deriving ( Applicative, Functor, Monad
           , MonadReader TCEnv
           , MonadState CheckerState
           , MonadWriter TCLog
           , MonadError TCErr
           , MonadIO)

-------------------
----- Logging -----
-------------------


type TCLog = [LogMessage]


data LogMessage = InfoMessage Doc | DebugMessage Doc


instance Pretty LogMessage where
  pprint (InfoMessage s) = "INFO:" <+> s
  pprint (DebugMessage s) = "DEBUG:" <+> s


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
debug :: Doc -> CM ()
debug msg = do
  debugNest <- fmap debugNesting get
  let formattedMessage = if debugNest == 0 then msg else hsep [text $ replicate debugNest '>', msg]
  tell . pure . DebugMessage $ formattedMessage


info :: Doc -> CM ()
info = tell . pure . InfoMessage


-- | Indicate we are entering a debug block.
debugOpen :: CM ()
debugOpen = modify (\s -> s { debugNesting = succ (debugNesting s) })


-- | Indicate we are leaving a debug block.
debugClose :: CM ()
debugClose = modify (\s -> s { debugNesting = pred (debugNesting s) })


-- | Wrap the action in some debugging messages. The final message can
-- | use the result of the action.
debugBlock :: Doc -> Doc -> (a -> Doc) -> CM a -> CM a
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


formatLog :: Verbosity -> TCLog -> Doc
-- TODO: check whether this should be 'vcat' here (should be equiv to unlines) (2020-06-20)
formatLog v = foldr (\p q -> p $+$ q) empty . fmap pprint . filterLog v


--------------------
----- Checking -----
--------------------


data TCResult a
  = TCResult
    { tcrLog :: TCLog
    , tcrRes :: Either TCErr a
    }


runChecker :: TCEnv -> CheckerState -> CM a -> IO (TCResult a)
runChecker env st p = do
  (res, log) <- evalStateT (runReaderT (runWriterT $ (runExceptT (runCM p))) env) st
  return $ TCResult { tcrLog = log, tcrRes = res }


runNewChecker :: CM a -> IO (TCResult a)
runNewChecker = runChecker startEnv startCheckerState


runNewCheckerWithOpts :: TCOpts -> CM a -> IO (TCResult a)
runNewCheckerWithOpts opts =
  runChecker (startEnv { tcOpts = opts }) startCheckerState



-- | Get a unique NameId.
getFreshNameId :: CM NameId
getFreshNameId = get >>= \s -> let c = nextNameId s in put s { nextNameId = succ c } >> pure c


-- | Generate a fresh name, based on the given base name.
getFreshName :: String -> CM Name
getFreshName s = do
  n <- getFreshNameId
  pure (Name n (C.Name s))


-- | Get a unique NameId.
getFreshMetaId :: CM MetaId
getFreshMetaId = getFreshNameId >>= pure . mkMetaId . toInteger


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


-- | Execute the action with the given identifier bound with the given value.
withValuedVariable :: Name -> Expr -> CM a -> CM a
withValuedVariable v t p = do
  st <- get
  setValue v t
  res <- p
  -- restore the value scope
  modify (\s -> s { valueScope = valueScope st})
  pure res


-------------
-- Grading --
-------------

-- Different 'stages' when it comes to grading
data Stage = Subject | SubjectType | Context

instance Pretty Stage where
  pprint Subject     = text "subject"
  pprint SubjectType = text "type"
  pprint Context     = text "context"


------------------------------
-- * Type checking environment
------------------------------


-- | Type-checking environment.
data TCEnv = TCEnv
  { tceCurrentExpr :: Maybe (Expr, Maybe Expr)
  -- ^ Expression currently being checked (if any). When the type
  -- ^ is provided (second element), it means the expression was being
  -- ^ checked against that type. When the type is not provided, it
  -- ^ means a type was being inferred for the expression.
  , tceCurrentTopLevel :: Maybe Name
  -- ^ Top-level definition being checked (if any).
  , tcOpts :: TCOpts
  -- ^ Type-checking options.
  }


-- | Type-checking options.
data TCOpts = TCOpts
  { tycOptimise :: Bool
  -- ^ Whether to optimise code.
  , benchmark   :: Bool
  -- ^ Whether to run benchmarks.
  , smtSimplify :: Bool
  -- ^ Whether to simplify theorems before passing them to the SMT solver.
  }


getOpts :: CM TCOpts
getOpts = fmap tcOpts ask


isBenchmarking :: CM Bool
isBenchmarking = benchmark <$> getOpts

isOptimising :: CM Bool
isOptimising = tycOptimise <$> getOpts


shouldSimplifySMT :: CM Bool
shouldSimplifySMT = smtSimplify <$> getOpts


tceSetCurrentExpr :: (Expr, Maybe Expr) -> TCEnv -> TCEnv
tceSetCurrentExpr e env = env { tceCurrentExpr = Just e }


tceSetCurrentTopLevel :: Name -> TCEnv -> TCEnv
tceSetCurrentTopLevel n env = env { tceCurrentTopLevel = Just n }


startEnv :: TCEnv
startEnv = TCEnv { tcOpts = defaultTCOpts, tceCurrentExpr = Nothing, tceCurrentTopLevel = Nothing }


defaultTCOpts :: TCOpts
defaultTCOpts = TCOpts { benchmark = False, tycOptimise = False, smtSimplify = False }


-- | Indicate that we are now checking the given expression when running the action.
withLocalCheckingOf :: Expr -> Maybe Expr -> CM a -> CM a
withLocalCheckingOf e t = local (tceSetCurrentExpr (e, t))


-- | Indicate that we are now checking the given top-level name when running the action.
withCheckingOfTopLevel :: Name -> CM a -> CM a
withCheckingOfTopLevel n = local (tceSetCurrentTopLevel n)


-----------------------
----- Constraints -----
-----------------------


getPredicateStack :: CM [Pred]
getPredicateStack = fmap predicateStack $ get


setPredicateStack :: [Pred] -> CM ()
setPredicateStack s = modify (\st -> st { predicateStack = s })


resetPredicateStack :: CM ()
resetPredicateStack = setPredicateStack []


-- Add a constraint to the predicate stack
addConstraint :: Constraint -> CM ()
addConstraint c = do
  st <- get
  case predicateStack st of
    (p : stack) ->
      put (st { predicateStack = conjunctPred (Con c) p : stack })
    stack ->
      put (st { predicateStack = Conj [Con c] : stack })

newConjunct :: CM ()
newConjunct =
  modify (\st -> st { predicateStack = Conj [] : predicateStack st })

concludeImplication :: CM ()
concludeImplication = do
  st <- get
  case predicateStack st of
    (p' : p : stack) ->
      modify (\st -> st { predicateStack = conjunctPredStack (Impl p p') stack })
    _ -> error "Predicate: not enough conjunctions on the stack"

-- Introduce a conjunction onto the the top of the predicate stack
conjunctPredStack :: Pred -> [Pred] -> [Pred]
conjunctPredStack p (p' : stack) = conjunctPred p p' : stack
conjunctPredStack p [] = [Conj [p]]

-- Introduce a conjunction (under the scope of binders)
conjunctPred :: Pred -> Pred -> Pred
conjunctPred p (Conj ps) = Conj (p : ps)
conjunctPred p (Forall var k ps) = Forall var k (conjunctPred p ps)
conjunctPred p (Exists var k ps) = Exists var k (conjunctPred p ps)
conjunctPred _ p = error $ "Cannot append a predicate to " <> pprintShow p

existential :: Name -> GradeSpec -> CM ()
existential var k = do
  checkerState <- get
  case predicateStack checkerState of
    (p : stack) -> do
      put (checkerState { predicateStack = Exists var k p : stack })
    [] ->
      put (checkerState { predicateStack = [Exists var k (Conj [])] })

universal :: Name -> GradeSpec -> CM ()
universal var k = do
  checkerState <- get
  case predicateStack checkerState of
    (p : stack) -> do
      put (checkerState { predicateStack = Forall var k p : stack })
    [] ->
      put (checkerState { predicateStack = [Forall var k (Conj [])] })


-----------------------------------------
----- Exceptions and error handling -----
-----------------------------------------


data TCError
  ---------------------------
  -- Implementation Errors --
  ---------------------------

  = NotImplemented Doc

  | InternalBug Doc

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

  | ExpectedInferredTypeForm Doc Expr

  --------------------
  -- Pattern Errors --
  --------------------

  | PatternMismatch Pattern Expr

  --------------------
  -- Grading Errors --
  --------------------

  | GradeMismatch Stage [(Name, (Grade, Grade))]

  | GradeTypeMismatch GradeSpec GradeSpec

  | SolverNotValid Doc

  | SolverError Doc

  | SolverTimeout

  ------------------
  -- Parse Errors --
  ------------------

  | ParseError ParseError


-- for now, this is just an alias for a type-checker error, but we can
-- separate this out if desired (2020-06-26)
type SolverError = TCError


instance Pretty TCError where
  pprint (NotImplemented e) = e
  pprint CannotSynthTypeForExpr = "I couldn't synthesise a type for the expression."
  pprint (CannotSynthExprForType t) =
    "I was asked to try and synthesise a term of type" <+> quoted t <+> parens ("internal rep:" <+> pprint t) <+> "but I wasn't able to do so."
  pprint (TypeMismatch tyExpected tyActual) =
    "Expected type" <+> quoted tyExpected <+> "but got" <+> quoted tyActual
  pprint (GradeTypeMismatch tyExpected tyActual) =
    "Expected (grade) type" <+> quoted tyExpected <+> "but got" <+> quoted tyActual
  pprint (GradeMismatch stage mismatches) =
    hang ("At stage" <+> pprint stage <+> "got the following mismatched grades:") 1
    (vcat $ fmap (\(v, (e, a)) -> "For" <+> quoted v <+> "expected" <+> pprint e <+> "but got" <+> pprint a) mismatches)
  pprint (SolverError msg)    = msg
  pprint (SolverNotValid msg) = msg
  pprint SolverTimeout = "Solver timeout"
  pprint (ExpectedInferredTypeForm descr t) =
    "I was expecting the expression to have a" <+> descr <+>
                        "type, but instead I found its type to be" <+> quoted t
  pprint (PatternMismatch p t) =
    "The pattern" <+> quoted p <+> "is not valid for type" <+> quoted t

  pprint (ParseError e) = pprint e
  pprint (ScoperError e) = pprint e
  pprint (InternalBug e) = "Internal error:" <+> e


notImplemented :: Doc -> CM a
notImplemented descr = throwCM (NotImplemented descr)


internalBug :: Doc -> CM a
internalBug descr = throwCM (InternalBug descr)


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

-- | 'tyMismatch expr tyExpected tyActual' indicates that an expression
-- | was found to have a type that differs from expected.
tyMismatchAt :: Doc -> Expr -> Expr -> CM a
tyMismatchAt locale tyExpected tyActual =
  throwCMat locale (TypeMismatch tyExpected tyActual)

gradeMismatchAt :: Doc -> Stage -> [(Name, (Grade, Grade))] -> CM a
gradeMismatchAt locale stage mismatches =
  throwCMat locale (GradeMismatch stage mismatches)

gradeTyMismatch :: GradeSpec -> GradeSpec -> CM a
gradeTyMismatch ty1 ty2 =
  throwCM (GradeTypeMismatch ty1 ty2)

gradeMismatchAt' :: Doc -> Stage -> Name -> Grade -> Grade -> CM a
gradeMismatchAt' locale stage var gExpected gActual =
  throwCMat locale (GradeMismatch stage [(var, (gExpected, gActual))])

expectedInferredTypeForm :: Doc -> Expr -> CM a
expectedInferredTypeForm descr t =
  throwCM (ExpectedInferredTypeForm descr t)

solverError' :: Doc -> SolverError
solverError' = SolverError

solverError :: Doc -> CM a
solverError = throwCM . solverError'

solverNotValid :: Doc -> CM a
solverNotValid msg = throwCM (SolverNotValid msg)

solverTimeout :: CM a
solverTimeout =
  throwCM SolverTimeout

patternMismatch :: Pattern -> Expr -> CM a
patternMismatch p t = throwCM (PatternMismatch p t)


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
  , localeMessage :: Maybe Doc
  -- ^ Additional message to localise where we are
  }


-- | Expression being checked when failure occurred.
tcErrExpr :: TCErr -> Maybe Expr
tcErrExpr = fmap fst . tceCurrentExpr . tcErrEnv


-- | Type of expression being checked when failure occurred.
tcErrTy :: TCErr -> Maybe Expr
tcErrTy = join . fmap snd . tceCurrentExpr . tcErrEnv


-- | Top-level definition being checked when failure occurred.
tcErrTL :: TCErr -> Maybe Name
tcErrTL = tceCurrentTopLevel . tcErrEnv


throwCM :: TCError -> CM a
throwCM e = do
  env <- ask
  throwError $ TCErr { tcErrErr = e, tcErrEnv = env, localeMessage = Nothing }

throwCMat :: Doc -> TCError -> CM a
throwCMat msg e = do
  env <- ask
  throwError $ TCErr { tcErrErr = e, tcErrEnv = env, localeMessage = Just msg }

instance Pretty TCErr where
  pprint e = ((maybe "" (\tld -> ("During checking of top-level" <+> (quoted tld <> colon))) (tcErrTL e)) $+$ "The following error occurred when" <+> text phaseMsg)
      <> (maybe "" (\msg -> " (at " <> msg <> ")") (localeMessage e))
      <> (maybe ":" (\expr -> " " <> (quoted expr <+>
                              (maybe empty (("against a type" <+>) . quoted) (tcErrTy e))) <> ":") (tcErrExpr e)) $+$ pprint (tcErrErr e)
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
isSyntaxErr = (== PhaseParsing) . errPhase
isScopingErr = (== PhaseScoping) . errPhase
isTypingErr = (== PhaseTyping) . errPhase
