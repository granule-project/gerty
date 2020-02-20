{-# LANGUAGE FlexibleContexts #-}
module Dlam.Types
  ( doNASTInference
  ) where

import Dlam.Binders (HasBinders(..))
import Dlam.Syntax
import Dlam.PrettyPrint


-------------------
----- Helpers -----
-------------------


-- | Indicate that an identifier is not known to be defined.
unknownIdentifierErr :: Identifier -> m a
unknownIdentifierErr x = error $ "unknown identifier " <> show x


------------------------------
----- AST Type Inference -----
------------------------------


-- | Check if two types are equal.
equalTypes :: (Eq e) => Expr e -> Expr e -> Bool
equalTypes = (==)


-- | Attempt to infer the types of a definition, and check this against the declared
-- | type, if any.
doNStmtInference :: (Eq e, PrettyPrint e, Show e, Monad m, HasBinders m Identifier (Maybe (Expr e)) (Expr e)) => NStmt e -> m (NStmt e)
doNStmtInference r@(Decl v (Just t) e) = do
  setBinder (mkIdent v) (Just e, t)
  exprTy <- inferType e
  if equalTypes exprTy t
  then pure r
  -- TODO: improve error system (2020-02-20)
  else error $ "for definition of '" <> v <> "', the type of '" <> pprint e <> "' was found to be '" <> pprint exprTy <> "' but the expected type was '" <> pprint t <> "'"
doNStmtInference (Decl v Nothing e) = do
  exprTy <- inferType e
  setBinder (mkIdent v) (Just e, exprTy)
  pure (Decl v (Just exprTy) e)

-- | Attempt to infer the types of each definition in the AST, failing if a type
-- | mismatch is found.
doNASTInference :: (Eq e, PrettyPrint e, Show e, Monad m, HasBinders m Identifier (Maybe (Expr e)) (Expr e)) => NAST e -> m (NAST e)
doNASTInference (NAST ds) = fmap NAST $ mapM doNStmtInference ds


inferType :: (PrettyPrint ext, Show ext, Monad m, HasBinders m Identifier (Maybe (Expr ext)) (Expr ext)) => Expr ext -> m (Expr ext)
inferType (Var x) = do
  ty <- getBinderType x
  case ty of
    -- TODO: update this to use a better error system (2020-02-19)
    Nothing -> unknownIdentifierErr x
    Just t  -> pure t
inferType (TypeTy l) = pure $ TypeTy (succ l)
inferType e = error $ "type inference not implemented for '" <> pprint e <> "' (" <> show e <> ")"
