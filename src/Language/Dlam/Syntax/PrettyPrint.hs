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
    pprint (Coproduct e1 e2) = pprint e1 <> " + " <> pprint e2
    pprint (CoproductCase (z, tC) (x, c) (y, d) e) =
      "case " <> pprint z <> "@" <> bracket_pprint e <> " of ("
              <> "Inl " <> pprint x <> " -> " <> pprint c <> "; "
              <> "Inr " <> pprint y <> " -> " <> pprint d <> ") : " <> pprint tC
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
  pprint LZero     = pprint . builtinName $ lzero
  pprint LMax      = pprint . builtinName $ lmax
  pprint LSuc      = pprint . builtinName $ lsuc
  pprint LevelTy   = pprint . builtinName $ levelTy
  pprint TypeTy    = pprint . builtinName $ typeTy
  pprint Inl       = pprint . builtinName $ inlTerm
  pprint Inr       = pprint . builtinName $ inrTerm
  pprint DNat      = pprint . builtinName $ natTy
  pprint DNZero    = pprint . builtinName $ dnzero
  pprint DNSucc    = pprint . builtinName $ dnsucc
  pprint DUnitTy   = pprint . builtinName $ unitTy
  pprint DUnitTerm = pprint . builtinName $ unitTerm
  pprint IdTy      = pprint . builtinName $ idTy
  pprint DRefl     = pprint . builtinName $ reflTerm

instance PrettyPrint AST where
  pprint (AST decls) = concat . intersperse "\n\n" $ fmap pprint decls

instance PrettyPrint FLHS where
  pprint (FLHSName n) = pprint n

instance PrettyPrint FRHS where
  pprint (FRHSAssign e) = "= " <> pprint e

instance PrettyPrint Declaration where
  pprint (TypeSig n t) = pprint n <> " : " <> pprint t
  pprint (FunEqn lhs rhs) = pprint lhs <> " " <> pprint rhs
