module Language.Gerty.Syntax.Parser.Tokens
    ( Token(..)
    , Keyword(..)
    , layoutKeywords
    , Symbol(..)
    ) where

import Language.Gerty.Syntax.Literal (Literal)
import Language.Gerty.Syntax.Position

data Keyword
        = KwLet | KwIn | KwWhere
        | KwRecord | KwConstructor | KwField
        | KwRewrite
        | KwCase | KwOf | KwInl | KwInr
        | KwAs
        | KwZero | KwSucc
        | KwType
        | KwUnitTy | KwUnit
    deriving (Eq, Show)

layoutKeywords :: [Keyword]
layoutKeywords = [ KwWhere, KwField ]
--     [ KwLet, KwWhere, KwField ]

data Symbol
        = SymDot | SymSemi | SymVirtualSemi | SymBar
        | SymColon | SymArrow | SymEqual | SymLambda
        | SymUnderscore | SymQuestionMark   | SymAt
        | SymOpenParen        | SymCloseParen
        | SymOpenAngle        | SymCloseAngle
        | SymOpenBrace        | SymCloseBrace
        | SymOpenVirtualBrace | SymCloseVirtualBrace
        | SymPlus | SymStar | SymAbsurd | SymComma
        | SymOpenBracket | SymCloseBracket
        | SymEndComment -- ^ A misplaced end-comment "-}".
        | SymDotInf | SymDotPlus | SymDotStar | SymDotLub
    deriving (Eq, Show)

data Token
          -- Keywords
        = TokKeyword Keyword Interval
          -- Identifiers and operators
        | TokId         (Interval, String)
        | TokQId        [(Interval, String)]
                        -- Non-empty namespace. The intervals for
                        -- "A.B.x" correspond to "A.", "B." and "x".
          -- Literals
        | TokLiteral    Literal
        | TokNat        (Range, Integer)
          -- Special symbols
        | TokSymbol Symbol Interval
          -- Other tokens
        | TokString (Interval, String)  -- arbitrary string, used in pragmas
        | TokSetN (Interval, Integer)
        | TokPropN (Interval, Integer)
        | TokTeX (Interval, String)
        | TokMarkup (Interval, String)
        | TokComment (Interval, String)
        | TokDummy      -- Dummy token to make Happy not complain
                        -- about overlapping cases.
        | TokEOF Interval
    deriving (Eq, Show)

instance HasRange Token where
  getRange (TokKeyword _ i)    = getRange i
  getRange (TokId (i, _))      = getRange i
  getRange (TokQId iss)        = getRange (map fst iss)
  getRange (TokLiteral lit)    = getRange lit
  getRange (TokNat (i, _))     = getRange i
  getRange (TokSymbol _ i)     = getRange i
  getRange (TokString (i, _))  = getRange i
  getRange (TokSetN (i, _))    = getRange i
  getRange (TokPropN (i, _))   = getRange i
  getRange (TokTeX (i, _))     = getRange i
  getRange (TokMarkup (i, _))  = getRange i
  getRange (TokComment (i, _)) = getRange i
  getRange TokDummy            = noRange
  getRange (TokEOF i)          = getRange i
