{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Dlam.PrettyPrint
  ( PrettyPrint(..)
  ) where

import Data.List (intersperse)

import Language.Dlam.Syntax

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

    pprint (LitLevel n)           = show n
    pprint (Abs ab) =
      concat ["\\ (", pprint (absVar ab), " : ", pprint (absTy ab), ") -> ", pprint (absExpr ab)]
    pprint (FunTy ab) =
      concat ["(", pprint (absVar ab), " : ",
                 pprint (absTy ab), ") -> ", pprint (absExpr ab)]
    pprint (ProductTy ab) =
      concat ["(", pprint (absVar ab), " : ",
                 pprint (absTy ab), ") * ", pprint (absExpr ab)]
    pprint (App abs@(Abs _) e2) =
      bracket_pprint abs ++ " " ++ bracket_pprint e2
    pprint (App (Sig e1 t) e2) =
      bracket_pprint (Sig e1 t) ++ " " ++ bracket_pprint e2
    pprint (App e1@App{} e2) = bracket_pprint e1 ++ " " ++ bracket_pprint e2
    pprint (App e1 e2) = pprint e1 ++ " " ++ bracket_pprint e2
    pprint (Pair e1 e2) = "(" <> pprint e1 <> ", " <> pprint e2 <> ")"
    pprint (IfExpr e1 e2 e3) = "if " <> pprint e1 <> " then " <> pprint e2 <> " else " <> pprint e3
    pprint (Var var) = pprint var
    pprint (Sig e t) = bracket_pprint e ++ " : " ++ pprint t
    -- Source extensions
    pprint (Ext e) = pprint e
    -- ML
    pprint (GenLet x e1 e2) = "let " ++ pprint x ++ " = " ++ pprint e1 ++ " in " ++ pprint e2
    pprint Wild = "_"
    pprint (Builtin s) = pprint s
    pprint (PairElim x y e1 e2) = "let (" <> pprint x <> ", " <> pprint y <> ") = " <> pprint e1 <> " in " <> pprint e2

instance PrettyPrint Identifier where
  pprint (Ident v) = v
  pprint (GenIdent (v, i)) = v <> "_" <> show i
  pprint Ignore = "_"

instance PrettyPrint BuiltinTerm where
  pprint LZero = "lzero"
  pprint LMax  = "lmax"
  pprint LSuc  = "lsuc"
  pprint LevelTy = "Level"
  pprint TypeTy  = "Type"
  pprint DBool  = "Bool"
  pprint DTrue  = "true"
  pprint DFalse = "false"
  pprint DUnitTy = "Unit"
  pprint DUnitTerm = "unit"

instance (PrettyPrint e) => PrettyPrint (NAST e) where
  pprint (NAST sts) = concat . intersperse "\n\n" $ fmap pprint sts

instance (PrettyPrint e) => PrettyPrint (NStmt e) where
  pprint (Decl v t e) = v <> " : " <> pprint t <> "\n" <> v <> " = " <> pprint e

instance PrettyPrint () where
    pprint () = "()"

instance PrettyPrint NoExt where
  pprint _ = undefined