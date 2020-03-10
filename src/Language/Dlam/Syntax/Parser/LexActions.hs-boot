module Language.Dlam.Syntax.Parser.LexActions where

import Language.Dlam.Syntax.Literal
import Language.Dlam.Syntax.Parser.Alex
import Language.Dlam.Syntax.Parser.Monad
import Language.Dlam.Syntax.Parser.Tokens
import Language.Dlam.Syntax.Position

lexToken :: Parser Token

token :: (String -> Parser tok) -> LexAction tok

withInterval  :: ((Interval, String) -> tok) -> LexAction tok
withInterval' :: (String -> a) -> ((Interval, a) -> tok) -> LexAction tok
withLayout :: LexAction r -> LexAction r

begin     :: LexState -> LexAction Token
beginWith :: LexState -> LexAction a -> LexAction a
endWith   :: LexAction a -> LexAction a
begin_    :: LexState -> LexAction Token
end_      :: LexAction Token

keyword    :: Keyword -> LexAction Token
symbol     :: Symbol -> LexAction Token
identifier :: LexAction Token
literal    :: Read a => (Range -> a -> Literal) -> LexAction Token
literal'   :: (String -> a) -> (Range -> a -> Literal) -> LexAction Token
integer    :: String -> Integer

followedBy    :: Char -> LexPredicate
eof           :: LexPredicate
inState       :: LexState -> LexPredicate