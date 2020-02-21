{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Dlam.PrettyPrint
  ( PrettyPrint(..)
  ) where

import Data.List (intersperse)

import Dlam.Syntax

-- Pretty print terms
class PrettyPrint t where
    isLexicallyAtomic :: t -> Bool
    isLexicallyAtomic _ = False

    pprint :: t -> String

bracket_pprint :: PrettyPrint t => t -> String
bracket_pprint t | isLexicallyAtomic t = pprint t
                 | otherwise           = "(" ++ pprint t ++ ")"

-- Untyped lambda calculus
instance PrettyPrint ex => PrettyPrint (Expr ex) where
    isLexicallyAtomic (Var _) = True
    isLexicallyAtomic (Ext e) = isLexicallyAtomic e
    isLexicallyAtomic _       = False

    pprint (Abs var Nothing e)  = "\\" ++ var ++ " -> " ++ pprint e
    pprint (LitLevel n)           = show n
    pprint (Abs var (Just t) e) = "\\ (" ++ var ++ " : " ++ pprint t ++ ") -> " ++ pprint e
    pprint (FunTy ab) =
      "(" ++ absVar ab ++ " : " ++ pprint (absTy ab) ++ ") -> " ++ pprint (absExpr ab)
    pprint (App (Abs var mt e1) e2) =
      bracket_pprint (Abs var mt e1) ++ " " ++ bracket_pprint e2
    pprint (App (Sig e1 t) e2) =
      bracket_pprint (Sig e1 t) ++ " " ++ bracket_pprint e2
    pprint (App e1 e2) = pprint e1 ++ " " ++ bracket_pprint e2
    pprint (Var var) = var
    pprint (Sig e t) = bracket_pprint e ++ " : " ++ pprint t
    -- Source extensions
    pprint (Ext e) = pprint e
    -- ML
    pprint (GenLet x e1 e2) = "let " ++ x ++ " = " ++ pprint e1 ++ " in " ++ pprint e2
    pprint Wild = "_"
    pprint (Builtin s) = pprint s

instance PrettyPrint BuiltinTerm where
  pprint LZero = "lzero"
  pprint LMax  = "lmax"
  pprint LSuc  = "lsuc"
  pprint LevelTy = "Level"
  pprint TypeTy  = "Type"

instance (PrettyPrint e) => PrettyPrint (NAST e) where
  pprint (NAST sts) = concat . intersperse "\n\n" $ fmap pprint sts

instance (PrettyPrint e) => PrettyPrint (NStmt e) where
  pprint (Decl v t e) = v <> " : " <> pprint t <> "\n" <> v <> " = " <> pprint e

instance PrettyPrint () where
    pprint () = "()"

instance PrettyPrint NoExt where
  pprint _ = undefined
