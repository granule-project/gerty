module Language.Dlam.Builtins
  ( builtins
  , builtinsTypes
  , builtinsValues
  ) where


import qualified Data.Map as M

import Language.Dlam.Syntax.Abstract


-- | The list of builtins.
builtins :: [Builtin]
builtins =
   [ typeTy
   , levelTy, lzero, lsuc, lmax
   , inlTerm, inrTerm
   , natTy, dnzero, dnsucc
   , unitTerm, unitTy
   , idTy, reflTerm
   , emptyTy
   ]


builtinsTypes :: M.Map Name Expr
builtinsTypes = M.fromList
  (fmap (\bin -> (builtinName bin, builtinType bin)) builtins)


builtinsValues :: M.Map Name Expr
builtinsValues = M.fromList
  (fmap (\bin -> (builtinName bin, builtinBody bin)) builtins)
