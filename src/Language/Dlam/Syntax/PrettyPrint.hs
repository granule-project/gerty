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
    isLexicallyAtomic LitLevel{} = True
    isLexicallyAtomic Builtin{}  = True
    isLexicallyAtomic Pair{}     = True
    isLexicallyAtomic Hole{}     = True
    isLexicallyAtomic Implicit{} = True
    isLexicallyAtomic _       = False

    pprint (LitLevel n)           = show n
    pprint (Abs ab) = "\\ " <> pprintAbs "->" ab
    pprint (FunTy ab) = pprintAbs "->" ab
    pprint (ProductTy ab) = pprintAbs "*" ab
    pprint (App abs@(Abs _) e2) =
      bracket_pprint abs ++ " " ++ bracket_pprint e2
    pprint (App (Sig e1 t) e2) =
      bracket_pprint (Sig e1 t) ++ " " ++ bracket_pprint e2
    pprint (App e1 e2) = pprint e1 ++ " " ++ bracket_pprint e2
    pprint (Pair e1 e2) = "(" <> pprint e1 <> ", " <> pprint e2 <> ")"
    pprint (IfExpr e1 e2 e3) = "if " <> pprint e1 <> " then " <> pprint e2 <> " else " <> pprint e3
    pprint (Coproduct e1 e2) = pprint e1 <> " + " <> pprint e2
    pprint (CoproductCase (z, tC) (x, c) (y, d) e) =
      "case " <> pprint z <> "@" <> bracket_pprint e <> " of ("
              <> "inl " <> pprint x <> " -> " <> pprint c <> "; "
              <> "inr " <> pprint y <> " -> " <> pprint d <> ") : " <> pprint tC
    pprint (NatCase (x, tC) cz (w, y, cs) n) =
      "case " <> pprint x <> "@" <> bracket_pprint n <> " of ("
              <> "Zero -> " <> pprint cz <> "; "
              <> "Succ " <> pprint w <> "@" <> pprint y <> " -> " <> pprint cs <> ") : " <> pprint tC
    pprint (RewriteExpr x y p tC z c a b p') =
      concat ["rewrite (", pprint x, ".", pprint y, ".", pprint p, ".", pprint tC, ", ", pprint z, ".", pprint c, ", ", pprint a, ", ", pprint b, ", ", pprint p', ")"]
    pprint (Var var) = pprint var
    pprint (Sig e t) = bracket_pprint e ++ " : " ++ pprint t
    pprint Hole = "?"
    pprint Implicit{} = "_"
    pprint (Builtin s) = pprint s
    pprint (PairElim (Ignore, Implicit{}) (x, y, g) p) = "let (" <> pprint x <> ", " <> pprint y <> ") = " <> pprint p <> " in " <> pprint g
    pprint (PairElim (z, tC) (x, y, g) p) = "let " <> pprint z <> "@(" <> pprint x <> ", " <> pprint y <> ") = " <> pprint p <> " in (" <> pprint g <> " : " <> pprint tC <> ")"

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
  pprint Inl = "inl"
  pprint Inr = "inr"
  pprint DNat = "Nat"
  pprint DNZero = "zero"
  pprint DNSucc = "succ"
  pprint DUnitTy = "Unit"
  pprint DUnitTerm = "unit"
  pprint IdTy = "Id"
  pprint DRefl = "refl"

instance PrettyPrint NAST where
  pprint (NAST sts) = concat . intersperse "\n\n" $ fmap pprint sts

instance PrettyPrint NStmt where
  pprint (Decl v Nothing e) =
    v <> " = " <> pprint e
  pprint (Decl v (Just t) e) =
    v <> " : " <> pprint t <> "\n" <> v <> " = " <> pprint e
