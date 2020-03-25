{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
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

  -- ** Metas
  , getMetas
  , MetaType(..)
  , registerMeta
  , solveMeta
  , getFreshMetaId

  -- ** Scope
  , lookupType
  , maybeLookupType
  , setType
  , lookupValue
  , maybeLookupValue
  , setValue
  , updateWithScopeInfo

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
import qualified Language.Dlam.Scoping.Monad.Base as SM
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
    , nextMetaId :: I.MetaId
    -- ^ Unique id for metas.
    , debugNesting :: Int
    -- ^ Counter used to make it easier to locate debugging messages.
    , metas :: MetaContext
    }


-- TODO: take the scoper state as an argument so e.g., we can set the meta id (2020-03-25)
-- | The starting checker state.
startCheckerState :: CheckerState
startCheckerState =
  CheckerState { typingScope = builtinsTypes
               , valueScope = builtinsValues
               , provisionScope = M.empty
               , nextNameId = 0
               , nextMetaId = 0
               , debugNesting = 0
               , metas = M.empty
               }


-- | Update the checker with information from a scope analysis. USE WITH CAUTION.
updateWithScopeInfo :: SM.SCResult a -> CM ()
updateWithScopeInfo = setNextMetaId . SM.nextImplicitId . SM.scrState
  where setNextMetaId :: MetaId -> CM ()
        setNextMetaId i = modify (\s -> s { nextMetaId = i })


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


maybeLookupValue :: AName -> CM (Maybe I.Term)
maybeLookupValue n = M.lookup n . valueScope <$> get


lookupValue :: AName -> CM I.Term
lookupValue n =
  maybeLookupValue n >>= maybe (scoperError $ SE.unknownNameErr (C.Unqualified $ nameConcrete n)) pure


setValue :: AName -> I.Term -> CM ()
setValue n t = modify (\s -> s { valueScope = M.insert n t (valueScope s) })


-----------
-- Metas --
-----------


type MetaId = I.MetaId


type MetaContext = M.Map MetaId MetaInfo


instance Pretty MetaContext where
  pprint xs = vcat $ fmap pprintBinding (M.toList xs)
    where pprintBinding (n, MetaInfo mt ms) =
            let mtt = brackets $ case mt of
                        IsImplicit -> text "IMPLICIT"
                        IsMeta     -> text "META"
                mst = case ms of
                        MetaUnsolved{} -> text "(wasn't able to solve)"
                        MetaSolved (I.VISType{}, _, t) -> equals <+> pprint t
                        MetaSolved (I.VISTerm, _, t) -> equals <+> pprint t
                        MetaSolved (I.VISLevel, _, t) -> equals <+> pprint t
            in mtt <+> pprint n <+> mst


data MetaType = IsImplicit | IsMeta


data MetaState = forall t. MetaSolved (I.ISSort t, t -> t -> CM Bool, t) | forall t. MetaUnsolved (I.ISSort t)


data MetaInfo = MetaInfo MetaType MetaState


getMetas :: CM MetaContext
getMetas = metas <$> get


setMetas :: MetaContext -> CM ()
setMetas impls = modify (\s -> s { metas = impls })


registerMeta :: MetaId -> MetaType -> I.ISSort t -> CM ()
registerMeta i mt s = do
  debug $ "registering meta '" <> pprintShow i <> "'"
  metas <- getMetas
  case M.lookup i metas of
    Nothing -> setMetas (M.insert i (MetaInfo mt (MetaUnsolved s)) metas)
    Just{} -> hitABug "meta already registered"


solveMeta :: (Pretty t) => MetaId -> (I.ISSort t, t -> t -> CM Bool, t) -> CM ()
solveMeta i s = do
  metas <- getMetas
  soln <- case M.lookup i metas of
            Nothing -> hitABug $ "tried to solve meta '" <> pprintShow i <> "' with solution '" <> pprintShow (thd3 s) <> "' but the meta isn't registered."
            -- TODO: check that the solutions are equal (2020-03-25)
            Just (MetaInfo mt (MetaSolved (st,eq,t1))) -> do
              areEq <- case (s, st) of
                         ((I.VISType{}, _, t2), I.VISType{}) -> eq t1 t2
                         ((I.VISLevel, _, t2), I.VISLevel) -> eq t1 t2
                         ((I.VISTerm, _, t2), I.VISTerm) -> eq t1 t2
                         (_, _) -> pure False
              if areEq then pure (MetaInfo mt (MetaSolved s)) else hitABug "meta already solved"
            Just (MetaInfo mt (MetaUnsolved r)) ->
              case (r, s) of
                -- TODO: add check that the levels are the same (2020-03-25)
                (I.VISType{}, (I.VISType l, eq, t)) -> pure $ MetaInfo mt (MetaSolved (I.VISType l, eq, t))
                (I.VISTerm, (I.VISTerm, eq, t)) -> pure $ MetaInfo mt (MetaSolved (I.VISTerm, eq, t))
                (I.VISLevel, (I.VISLevel, eq, t)) -> pure $ MetaInfo mt (MetaSolved (I.VISLevel, eq, t))
                (_, _) -> hitABug $ "tried to solve meta with incorrect sort"
  setMetas (M.insert i soln metas)
  where thd3 (_,_,c) = c


-- | Get a unique MetaId.
getFreshMetaId :: CM I.MetaId
getFreshMetaId = get >>= \s -> let c = nextMetaId s in put s { nextMetaId = succ c } >> pure c


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


newtype FreeVar = FreeVar { unFreeVar :: AnyName }
  deriving (Eq, Ord, Pretty)


class ToFreeVar a where
  toFreeVar :: a -> FreeVar


instance ToFreeVar AnyName where
  toFreeVar (AnyName n) = toFreeVar n


instance ToFreeVar (Name n) where
  toFreeVar n = FreeVar (AnyName (forgetSort n))


instance ToFreeVar I.FreeVar where
  toFreeVar n = toFreeVar (I.freeVarName n)


forgetSort :: Name a -> Name ()
forgetSort = translate


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


tceAddInScope :: [FreeVar] -> TCEnv -> TCEnv
tceAddInScope names env =
  env { inScopeSet = Set.union (Set.fromList names) (inScopeSet env) }


getInScope :: CM (Set.Set FreeVar)
getInScope = fmap inScopeSet ask


-- | Execute the action with the given free variables in scope.
withInScope :: [FreeVar] -> CM a -> CM a
withInScope names = local (tceAddInScope names)


getContext :: CM FreeVarContext
getContext = fmap tceFVContext ask


tceAddBinding :: FreeVar -> FreeVarInfo -> TCEnv -> TCEnv
tceAddBinding v bod env = env { tceFVContext = fvcMap (M.insert v bod) (tceFVContext env) }


-- | Execute the action with the given free variable bound with the
-- | given grading and type.
withVarBound :: (ToFreeVar n, Pretty n) => n -> I.Grading -> I.Type -> CM a -> CM a
withVarBound n g ty act =
  debugBlock "withVarBound"
    ("binding '" <> pprintShow n <> "' with grades '" <> pprintShow g <> "' and type '" <> pprintShow ty <> "'")
    (\_ -> "unbinding '" <> pprintShow n <> "'")
    (local (tceAddBinding (toFreeVar n) (g, ty)) act)


-- | Execute the action with the given free variable bound with the
-- | given type (ignoring grading).
withVarTypeBound :: (ToFreeVar n, Pretty n) => n -> I.Type -> CM a -> CM a
withVarTypeBound n ty = withVarBound n I.thatMagicalGrading ty


lookupFVInfo :: (ToFreeVar n, Pretty n) => n -> CM FreeVarInfo
lookupFVInfo n = do
  ctx <- getContext
  maybe (hitABug $ "tried to look up the type of free variable '" <> pprintShow n <> "' but it wasn't in scope. Scope checking or type-checking is broken.\nContext was: " <> pprintShow ctx) pure . fvcMapOp (M.lookup (toFreeVar n)) =<< getContext


lookupFVType :: I.Name n -> CM I.Type
lookupFVType = fmap snd . lookupFVInfo


lookupFVSubjectRemaining :: I.Name n -> CM I.Grade
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

  | PatternMismatch Pattern I.Type

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


patternMismatch :: Pattern -> I.Type -> CM a
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
isImplementationErr e =
  case tcErrErr e of
    NotImplemented{}    -> True
    ImplementationBug{} -> True
    _                   -> False


-----------------------
----- For Unbound -----
-----------------------


instance I.LFresh CM where
  getAvoids = Set.map unFreeVar <$> getInScope
  avoid xs = withInScope (fmap toFreeVar xs)
  lfresh n = do
    let s = name2String n
    used <- getAvoids
    pure $ head (filter (\x -> not (Set.member (AnyName x) used)) (map (makeName s) [0..]))
