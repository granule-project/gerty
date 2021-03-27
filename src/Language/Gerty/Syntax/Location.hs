module Language.Gerty.Syntax.Location
  (
  -- * Locations
    Location
  , locFile
  , locLine
  , locColumn

  -- * Spans
  , Span
  , mkSpan
  , spanFile
  , spanStart
  , spanEnd
  ) where


-- | A line and column position.
data Pos = Pos { posLine :: Int, posCol :: Int }
  deriving (Eq)


instance Ord Pos where
  p1 <= p2 | posLine p1 < posLine p2  = True
           | posLine p1 == posLine p2 = posCol p1 <= posCol p2
           | otherwise                = False


-- | A position in a file.
data Location = Location
  { locFile :: FilePath
  , locPos  :: Pos
  } deriving (Eq)


-- Does Haskell let you index types with strings?  I want to say:
-- Location : FilePath -> Type, to guarantee (at the type level) e.g.,
-- we can't compare locations from different files (GD: 2020-02-25)
instance Ord Location where
  l1 <= l2
    | locFile l1 /= locFile l2 =
      error "Attempted to compare locations from different files"
    | otherwise = locPos l1 <= locPos l2



-- | The line number of the given location.
locLine :: Location -> Int
locLine = posLine . locPos


-- | The column number of the given location.
locColumn :: Location -> Int
locColumn = posCol . locPos


-- | A position range in a file.
data Span = Span
  { spanStartPos :: Pos
  , spanEndPos   :: Pos
  , spanFile     :: FilePath
  }


mkSpan :: Location -> Location -> Span
mkSpan loc1 loc2
  | loc1 > loc2 =
    error "tried to make a span when the start location is after the end"
  | locFile loc1 /= locFile loc2 =
    error "tried to make a span when the start and end locations are in different files"
  | otherwise = Span { spanFile = locFile loc1
                     , spanStartPos = locPos loc1
                     , spanEndPos = locPos loc2 }


-- | The start location of a span.
spanStart :: Span -> Location
spanStart s = Location { locFile = spanFile s, locPos = spanStartPos s }


-- | The end location of a span.
spanEnd :: Span -> Location
spanEnd s = Location { locFile = spanFile s, locPos = spanEndPos s }
