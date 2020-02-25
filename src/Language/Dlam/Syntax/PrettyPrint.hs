{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Dlam.Syntax.PrettyPrint
  ( PrettyPrint(..)
  ) where

import Data.List (intersperse)

import Language.Dlam.Syntax.Syntax

-- Pretty print terms
class PrettyPrint t where
    isLexicallyAtomic :: t -> Bool
    isLexicallyAtomic _ = False

    pprint :: t -> String

bracket_pprint :: PrettyPrint t => t -> String
bracket_pprint t | isLexicallyAtomic t = pprint t
                 | otherwise           = "(" ++ pprint t ++ ")"


-- | Pretty-print an Abstraction, separating the (possibly named)
-- | binder from the expression using the given separator.
pprintAbs :: String -> Abstraction -> String
pprintAbs sep ab =
  let leftTyStr =
        case absVar ab of
          Ignore -> pprint (absTy ab)
          _      -> concat ["(", pprint (absVar ab), " : ", pprint (absTy ab), ")"]
  in concat [leftTyStr, " ", sep, " ", pprint (absExpr ab)]


-- Untyped lambda calculus
instance PrettyPrint Expr where
    isLexicallyAtomic (Var _) = True
    isLexicallyAtomic _       = False

    pprint (LitLevel n)           = show n
    pprint (Abs ab) = "\\ " <> pprintAbs "->" ab
    pprint (FunTy ab) = pprintAbs "->" ab
    pprint (ProductTy ab) = pprintAbs "*" ab
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
    -- ML
    pprint (GenLet x e1 e2) = "let " ++ pprint x ++ " = " ++ pprint e1 ++ " in " ++ pprint e2
    pprint Hole = "?"
    pprint Implicit{} = "_"
    pprint (Builtin s) = pprint s
    pprint (PairElim Ignore x y e1 e2 Implicit{}) = "let (" <> pprint x <> ", " <> pprint y <> ") = " <> pprint e1 <> " in " <> pprint e2
    pprint (PairElim z x y e1 e2 e3) = "let (" <> pprint z <> ", " <> pprint x <> ", " <> pprint y <> ") = " <> pprint e1 <> " in (" <> pprint e2 <> " : " <> pprint e3 <> ")"

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

instance PrettyPrint NAST where
  pprint (NAST sts) = concat . intersperse "\n\n" $ fmap pprint sts

instance PrettyPrint NStmt where
  pprint (Decl v Nothing e) =
    v <> " = " <> pprint e
  pprint (Decl v (Just t) e) =
    v <> " : " <> pprint t <> "\n" <> v <> " = " <> pprint e
