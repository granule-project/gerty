{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Dlam.PrettyPrint where

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
    pprint (Abs var (Just t) e) = "\\ (" ++ var ++ " : " ++ pprint t ++ ") -> " ++ pprint e
    pprint (App (Abs var mt e1) e2) =
      bracket_pprint (Abs var mt e1) ++ " " ++ bracket_pprint e2
    pprint (App (Sig e1 t) e2) =
      bracket_pprint (Sig e1 t) ++ " " ++ bracket_pprint e2
    pprint (App e1 e2) = pprint e1 ++ " " ++ bracket_pprint e2
    pprint (Var var) = var
    pprint (Sig e t) = bracket_pprint e ++ " : " ++ pprint t
    -- Source extensions
    pprint (Ext e) = pprint e
    -- Poly
    pprint (TyAbs var e) = "/\\" ++ var ++ " -> " ++ pprint e
    pprint (TyEmbed t) = "@" ++ bracket_pprint t
    -- ML
    pprint (GenLet x e1 e2) = "let " ++ x ++ " = " ++ pprint e1 ++ " in " ++ pprint e2

instance PrettyPrint PCF where
    isLexicallyAtomic Zero    = True
    isLexicallyAtomic _       = False

    pprint Zero                   = "zero"
    pprint Succ                   = "succ"
    pprint (Fix e)                = "fix " ++ bracket_pprint e
    pprint (NatCase e e1 (x, e2)) =
      "natcase " ++ bracket_pprint e ++ " of zero => " ++
      bracket_pprint e1 ++ " | succ " ++ x ++ " => " ++ bracket_pprint e2
    pprint (Pair e1 e2)           = "<" ++ pprint e1 ++ ", " ++ pprint e2 ++ ">"
    pprint (Fst e)                = "fst " ++ bracket_pprint e
    pprint (Snd e)                = "snd " ++ bracket_pprint e
    pprint (Inl e)                = "inl " ++ bracket_pprint e
    pprint (Inr e)                = "inr " ++ bracket_pprint e
    pprint (Case e (x,e1) (y,e2)) =
      "case " ++ bracket_pprint e ++ " of inl " ++ x ++ " => " ++
      bracket_pprint e1 ++ " | inr " ++ y ++ " => " ++ bracket_pprint e2

instance PrettyPrint () where
    pprint () = "()"

instance PrettyPrint Type where
    isLexicallyAtomic NatTy = True
    isLexicallyAtomic (TyVar _) = True
    isLexicallyAtomic _     = False

    pprint NatTy = "Nat"
    pprint (FunTy Nothing tyA tyB) =
      bracket_pprint tyA ++ " -> " ++ pprint tyB
    pprint (FunTy (Just var) tyA tyB) =
      "(" ++ var ++ " : " ++ pprint tyA ++ ") -> " ++ pprint tyB
    pprint (ProdTy tyA tyB) =
      bracket_pprint tyA ++ " * " ++ bracket_pprint tyB
    pprint (SumTy tyA tyB) =
      bracket_pprint tyA ++ " + " ++ bracket_pprint tyB
    pprint (TyVar var) = var
    pprint (TypeTy l)  = "type"
    pprint (Forall var t) = "forall " ++ var ++ " . " ++ pprint t
