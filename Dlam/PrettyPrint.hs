{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Dlam.PrettyPrint
  ( PrettyPrint(..)
  ) where

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
    pprint TypeTy{}             = "type"
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

instance (PrettyPrint e) => PrettyPrint (AST e) where
  pprint (AST []) = ""
  pprint (AST (st : sts)) = pprint st <> "\n" <> pprint (AST sts)

instance (PrettyPrint e) => PrettyPrint (Stmt e) where
  pprint (StmtAssign v e) = v <> " = " <> pprint e
  pprint (StmtType v t) = v <> " : " <> pprint t

instance PrettyPrint () where
    pprint () = "()"

instance PrettyPrint NoExt where
  pprint _ = undefined
