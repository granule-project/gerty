module Language.Dlam.TypeChecking.Monad.Grading
  ( Stage(..)
  ) where


import Language.Dlam.Util.Pretty hiding ((<>))


-- | Different 'stages' when it comes to grading.
data Stage = Subject | SubjectType | Context

instance Pretty Stage where
  pprint Subject     = text "subject"
  pprint SubjectType = text "type"
  pprint Context     = text "context"
