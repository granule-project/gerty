{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Language.Dlam.Util.Pretty
  ( module Text.PrettyPrint
  , Pretty(..)
  , pprintParened
  , pprintShow
  , beside
  ) where


import Data.Int
import Text.PrettyPrint
import Prelude hiding ((<>))

import Unbound.LocallyNameless (AnyName(..), Name, name2String, name2Integer)


pprintParened :: Pretty t => t -> Doc
pprintParened t = (if isLexicallyAtomic t then id else parens) $ pprint t


pprintShow :: Pretty t => t -> String
pprintShow = render . pprint


beside :: Doc -> Doc -> Doc
beside = (<>)


class Pretty a where
  -- | Does the component (not) need wrapping in delimiters to disambiguate
  -- | it from the surrounding environment?
  -- |
  -- | The default is that no components are lexically atomic.
  isLexicallyAtomic :: a -> Bool
  isLexicallyAtomic _ = False

  pprint :: a -> Doc


instance Pretty Doc where
  pprint = id


instance Pretty Int32 where
  isLexicallyAtomic _ = True
  pprint = text . show


instance Pretty String where
  pprint = text


instance Pretty AnyName where
  isLexicallyAtomic _ = True
  pprint (AnyName n) = pprint n


instance Pretty (Name a) where
  isLexicallyAtomic _ = True
  pprint n = text (name2String n) <> let i = name2Integer n in if i == 0 then empty else char '_' <> integer i


instance Pretty Int where
  isLexicallyAtomic _ = True
  pprint = int
