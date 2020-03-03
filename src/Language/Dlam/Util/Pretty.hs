module Language.Dlam.Util.Pretty
  ( module Text.PrettyPrint
  , Pretty(..)
  , pprintParened
  , pprintShow
  ) where


import Text.PrettyPrint


pprintParened :: Pretty t => t -> Doc
pprintParened t = (if isLexicallyAtomic t then id else parens) $ pprint t


pprintShow :: Pretty t => t -> String
pprintShow = render . pprint


class Pretty a where
  -- | Does the component (not) need wrapping in delimiters to disambiguate
  -- | it from the surrounding environment?
  -- |
  -- | The default is that no components are lexically atomic.
  isLexicallyAtomic :: a -> Bool
  isLexicallyAtomic _ = False

  pprint :: a -> Doc
