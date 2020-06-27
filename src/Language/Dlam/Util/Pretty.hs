{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Language.Dlam.Util.Pretty
  ( module Text.PrettyPrint.Annotated
  , Pretty(..)
  , Doc
  , pprintParened
  , pprintShow
  , pprintShowWithOpts
  , RenderOptions(..)
  , defaultRenderOptions

  -- * Helpers
  , identifier
  , pprintList
  , pprintPair
  , quoted
  , angles
  , bold
  , red
  , green
  ) where


import Data.Int
import Prelude hiding ((<>))

import Text.PrettyPrint.Annotated hiding (Doc)
import qualified Text.PrettyPrint.Annotated as P
import Text.PrettyPrint.Annotated.HughesPJ (AnnotDetails(..))


-----------------
-- Annotations --
-----------------


data Annot = AnnotIdentNum Integer


data RenderOptions = RenderOptions { showIdentNumbers :: Bool }


defaultRenderOptions :: RenderOptions
defaultRenderOptions = RenderOptions { showIdentNumbers = False }


type Doc = P.Doc Annot


---------------------
-- Pretty-printing --
---------------------


pprintParened :: Pretty t => t -> Doc
pprintParened t = (if isLexicallyAtomic t then id else parens) $ pprint t


pprintShow :: Pretty t => t -> String
pprintShow = pprintShowWithOpts defaultRenderOptions


-- | Pretty-print a value to a string, with options.
pprintShowWithOpts :: Pretty t => RenderOptions -> t -> String
pprintShowWithOpts opts =
  fullRenderAnn (mode style) (lineLength style) (ribbonsPerLine style) (printer opts) "" . pprint


printer :: RenderOptions -> AnnotDetails Annot -> String -> String
-- this is an identifier attachment
printer opts (AnnotEnd (AnnotIdentNum n)) s =
  if showIdentNumbers opts then "`" ++ show n ++ s else s
printer _opts AnnotStart s = s
printer _opts (NoAnnot t _) s = txtPrinter t s


-- | Default TextDetails printer (from https://hackage.haskell.org/package/pretty-1.1.3.6/docs/src/Text.PrettyPrint.Annotated.HughesPJ.html#txtPrinter).
txtPrinter :: TextDetails -> String -> String
txtPrinter (Chr c)   s  = c:s
txtPrinter (Str s1)  s2 = s1 ++ s2
txtPrinter (PStr s1) s2 = s1 ++ s2


class Pretty a where
  -- | Does the component (not) need wrapping in delimiters to disambiguate
  -- | it from the surrounding environment?
  -- |
  -- | The default is that no components are lexically atomic.
  isLexicallyAtomic :: a -> Bool
  isLexicallyAtomic _ = False

  pprint :: a -> Doc


instance Pretty Int32 where
  pprint = text . show


instance Pretty Int where
  pprint = text . show


instance Pretty String where
  pprint = text


instance Pretty Doc where
  pprint = id


-------------------
----- Helpers -----
-------------------


quoted :: (Pretty a) => a -> Doc
quoted = quotes . pprint


-- | Pretty-print a value inside angle brackets.
angles :: (Pretty a) => a -> Doc
angles p = char '<' <> pprint p <> char '>'


-- | Pretty-print an identifier.
identifier :: (Pretty a) => Integer -> a -> Doc
identifier gid n = annotate (AnnotIdentNum gid) (pprint n)


pprintList :: (Pretty a) => [a] -> Doc
pprintList = brackets . hsep . punctuate comma . fmap pprint


pprintPair :: (Pretty a, Pretty b) => (a, b) -> Doc
pprintPair (x, y) = parens ((pprint x <> comma) <+> pprint y)


withAnsi :: Doc -> Doc -> Doc
withAnsi ansiCode doc = ansiCode <> doc <> ansiReset


bold, red, green :: Doc -> Doc
bold  = withAnsi ansiBold
red   = withAnsi ansiRed
green = withAnsi ansiGreen


ansiReset, ansiBold, ansiRed, ansiGreen :: Doc
ansiReset = "\x1b[0m"
ansiBold  = "\x1b[1m"
ansiRed   = "\x1b[31m"
ansiGreen = "\x1b[32m"
