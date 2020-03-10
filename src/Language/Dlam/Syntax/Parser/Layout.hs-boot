module Language.Dlam.Syntax.Parser.Layout where

import Language.Dlam.Syntax.Parser.Alex
import Language.Dlam.Syntax.Parser.Tokens

offsideRule      :: LexAction Token
newLayoutContext :: LexAction Token
emptyLayout      :: LexAction Token