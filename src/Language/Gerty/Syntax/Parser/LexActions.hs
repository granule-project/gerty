{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-| This module contains the building blocks used to construct the lexer.
-}
module Language.Gerty.Syntax.Parser.LexActions
    ( -- * Main function
      lexToken
      -- * Lex actions
      -- ** General actions
    , token
    , withInterval, withInterval', withInterval_
    , withLayout
    , begin, end, beginWith, endWith
    , begin_, end_
    , lexError
      -- ** Specialized actions
    , keyword, symbol, identifier, literal, literal', integer
      -- * Lex predicates
    , followedBy, eof, inState
    ) where

import Control.Arrow
import Data.Char
import Data.Maybe

import Language.Gerty.Syntax.Lexer
import Language.Gerty.Syntax.Parser.Alex
import Language.Gerty.Syntax.Parser.Monad
import Language.Gerty.Syntax.Parser.Tokens
import Language.Gerty.Syntax.Position
import Language.Gerty.Syntax.Literal

{--------------------------------------------------------------------------
    Scan functions
 --------------------------------------------------------------------------}

-- | Called at the end of a file. Returns 'TokEOF'.
returnEOF :: AlexInput -> Parser Token
returnEOF AlexInput{ lexSrcFile, lexPos } = do
  -- Andreas, 2018-12-30, issue #3480
  -- The following setLastPos leads to parse error reporting
  -- far away from the interesting position, in particular
  -- if there is a long comment before the EOF.
  -- (Such a long comment is frequent in interactive programming, as
  -- commenting out until the end of the file is a common habit.)
  -- -- setLastPos lexPos
  -- Without it, we get much more useful error locations.
  setPrevToken "<EOF>"
  return $ TokEOF $ posToInterval lexSrcFile lexPos lexPos

-- | Set the current input and lex a new token (calls 'lexToken').
skipTo :: AlexInput -> Parser Token
skipTo inp = do
  setLexInput inp
  lexToken

{-| Scan the input to find the next token. Calls
'Language.Gerty.Syntax.Parser.Lexer.alexScanUser'. This is the main lexing function
where all the work happens. The function 'Language.Gerty.Syntax.Parser.Lexer.lexer',
used by the parser is the continuation version of this function.
-}
lexToken :: Parser Token
lexToken =
    do  inp <- getLexInput
        lss <- getLexState
        flags <- getParseFlags
        case alexScanUser (lss, flags) inp (head lss) of
            AlexEOF                     -> returnEOF inp
            AlexSkip inp' _len           -> skipTo inp'
            AlexToken inp' len action   -> fmap postToken $ action inp inp' len
            AlexError i                 -> parseError $ concat
              [ "Lexical error"
              , case listToMaybe $ lexInput i of
                  Just '\t'                -> " (you may want to replace tabs with spaces)"
                  Just c | not (isPrint c) -> " (unprintable character)"
                  _ -> ""
              , ":"
              ]

postToken :: Token -> Token
postToken (TokId (r, "\x03bb")) = TokSymbol SymLambda r
postToken (TokId (r, "\x2192")) = TokSymbol SymArrow r
postToken t = t

{--------------------------------------------------------------------------
    Lex actions
 --------------------------------------------------------------------------}

-- | The most general way of parsing a token.
token :: (String -> Parser tok) -> LexAction tok
token action inp inp' len =
    do  setLexInput inp'
        setPrevToken t
        setLastPos $ lexPos inp
        action t
    where
        t = take len $ lexInput inp

-- | Parse a token from an 'Interval' and the lexed string.
withInterval :: ((Interval, String) -> tok) -> LexAction tok
withInterval f = token $ \s -> do
                   r <- getParseInterval
                   return $ f (r,s)

-- | Like 'withInterval', but applies a function to the string.
withInterval' :: (String -> a) -> ((Interval, a) -> tok) -> LexAction tok
withInterval' f t = withInterval (t . (id *** f))

-- | Return a token without looking at the lexed string.
withInterval_ :: (Interval -> r) -> LexAction r
withInterval_ f = withInterval (f . fst)


-- | Executed for layout keywords. Enters the 'Language.Gerty.Syntax.Parser.Lexer.layout'
--   state and performs the given action.
withLayout :: LexAction r -> LexAction r
withLayout a i1 i2 n =
    do  pushLexState layout
        a i1 i2 n


-- | Enter a new state without consuming any input.
begin :: LexState -> LexAction Token
begin code _ _ _ =
    do  pushLexState code
        lexToken


-- | Enter a new state throwing away the current lexeme.
begin_ :: LexState -> LexAction Token
begin_ code _ inp' _ =
    do  pushLexState code
        skipTo inp'

-- | Exit the current state throwing away the current lexeme.
end_ :: LexAction Token
end_ _ inp' _ =
    do  popLexState
        skipTo inp'


-- | Enter a new state and perform the given action.
beginWith :: LexState -> LexAction a -> LexAction a
beginWith code a inp inp' n =
    do  pushLexState code
        a inp inp' n

-- | Exit the current state and perform the given action.
endWith :: LexAction a -> LexAction a
endWith a inp inp' n =
    do  popLexState
        a inp inp' n


-- | Exit the current state without consuming any input
end :: LexAction Token
end _ _ _ =
    do  popLexState
        lexToken

-- | Parse a 'Keyword' token, triggers layout for 'layoutKeywords'.
keyword :: Keyword -> LexAction Token
keyword k = layout $ withInterval_ (TokKeyword k)
    where
        layout | k `elem` layoutKeywords  = withLayout
               | otherwise              = id


-- | Parse a 'Symbol' token.
symbol :: Symbol -> LexAction Token
symbol s = withInterval_ (TokSymbol s)


-- | Split a list into sublists. Generalisation of the prelude function
--   @words@.
--
--   > words xs == wordsBy isSpace xs
wordsBy :: (a -> Bool) -> [a] -> [[a]]
wordsBy p xs = yesP xs
    where
        yesP xs = noP (dropWhile p xs)

        noP []  = []
        noP xs  = ys : yesP zs
            where
                (ys,zs) = break p xs


-- | Parse a number.

number :: String -> Integer
number str = read $ case str of
  '0' : 'x' : _num -> str
  _               -> concat $ wordsBy ('_' ==) str

integer :: String -> Integer
integer = \case
  '-' : str -> - (number str)
  str       -> number str

-- | Parse a literal.
literal' :: (String -> a) -> (Range -> a -> Literal) -> LexAction Token
literal' read lit =
  withInterval' read (TokLiteral . uncurry lit . first getRange)

literal :: Read a => (Range -> a -> Literal) -> LexAction Token
literal = literal' read

-- | Parse an identifier. Identifiers can be qualified (see 'Name').
--   Example: @Foo.Bar.f@
identifier :: LexAction Token
identifier = qualified (either TokId TokQId)


-- | Parse a possibly qualified name.
qualified :: (Either (Interval, String) [(Interval, String)] -> a) -> LexAction a
qualified tok =
    token $ \s ->
    do  i <- getParseInterval
        case mkName i $ wordsBy (=='.') s of
            []  -> lexError "lex error on .."
            [x] -> return $ tok $ Left  x
            xs  -> return $ tok $ Right xs
    where
        -- Compute the ranges for the substrings (separated by '.') of
        -- a name. Dots are included: the intervals generated for
        -- "A.B.x" correspond to "A.", "B." and "x".
        mkName :: Interval -> [String] -> [(Interval, String)]
        mkName _ []     = []
        mkName i [x]    = [(i, x)]
        mkName i (x:xs) = (i0, x) : mkName i1 xs
            where
                p0 = iStart i
                p1 = iEnd i
                p' = movePos (movePosByString p0 x) '.'
                i0 = Interval p0 p'
                i1 = Interval p' p1


{--------------------------------------------------------------------------
    Predicates
 --------------------------------------------------------------------------}

-- | True when the given character is the next character of the input string.
followedBy :: Char -> LexPredicate
followedBy c' _ _ _ inp =
    case lexInput inp of
        []  -> False
        c:_ -> c == c'

-- | True if we are at the end of the file.
eof :: LexPredicate
eof _ _ _ inp = null $ lexInput inp

-- | True if the given state appears somewhere on the state stack
inState :: LexState -> LexPredicate
inState s (ls, _) _ _ _ = s `elem` ls
