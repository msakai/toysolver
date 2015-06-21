{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Text.SDPFile
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- References:
--
-- * SDPA (Semidefinite Programming Algorithm) User's Manual
--   <http://sdpa.indsys.chuo-u.ac.jp/~fujisawa/sdpa_doc.pdf>
--
-- * <http://euler.nmt.edu/~brian/sdplib/FORMAT>
--
-----------------------------------------------------------------------------
module ToySolver.Text.SDPFile
  ( -- * The problem type
    Problem (..)
  , Matrix
  , Block
  , mDim
  , nBlock
  , blockElem

    -- * Construction
  , DenseMatrix
  , DenseBlock
  , denseMatrix
  , denseBlock
  , diagBlock
  
    -- * Rendering
  , render
  , renderSparse

    -- * Parsing
  , parseDataString
  , parseDataFile
  , parseSparseDataString
  , parseSparseDataFile
  ) where

import Control.Applicative ((<*))
import Control.Monad
import Data.List (intersperse)
import Data.Ratio
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import Text.Parsec
import Text.Parsec.String

-- ---------------------------------------------------------------------------
-- problem description
-- ---------------------------------------------------------------------------

data Problem
  = Problem
  { blockStruct :: [Int]      -- ^ the block strcuture vector (bLOCKsTRUCT)
  , costs       :: [Rational] -- ^ Constant Vector
  , matrices    :: [Matrix]   -- ^ Constraint Matrices
  }
  deriving (Show, Ord, Eq)

type Matrix = [Block]

type Block = Map (Int,Int) Rational

-- | the number of primal variables (mDim)
mDim :: Problem -> Int
mDim prob = length (matrices prob) - 1

-- | the number of blocks (nBLOCK)
nBlock :: Problem -> Int
nBlock prob = length (blockStruct prob)

blockElem :: Int -> Int -> Block -> Rational
blockElem i j b = Map.findWithDefault 0 (i,j) b

-- ---------------------------------------------------------------------------
-- construction
-- ---------------------------------------------------------------------------

type DenseMatrix = [DenseBlock]

type DenseBlock = [[Rational]]

denseBlock :: DenseBlock -> Block
denseBlock xxs = Map.fromList [((i,j),x) | (i,xs) <- zip [1..] xxs, (j,x) <- zip [1..] xs, x /= 0]

denseMatrix :: DenseMatrix -> Matrix
denseMatrix = map denseBlock

diagBlock :: [Rational] -> Block
diagBlock xs = Map.fromList [((i,i),x) | (i,x) <- zip [1..] xs]

-- ---------------------------------------------------------------------------
-- parsing
-- ---------------------------------------------------------------------------

-- | Parse a SDPA format (.dat) string.
parseDataString :: SourceName -> String -> Either ParseError Problem
parseDataString = parse (pDataFile <* eof)

-- | Parse a SDPA format file (.dat).
parseDataFile :: FilePath -> IO (Either ParseError Problem)
parseDataFile = parseFromFile (pDataFile <* eof)

-- | Parse a SDPA sparse format (.dat-s) string.
parseSparseDataString :: SourceName -> String -> Either ParseError Problem
parseSparseDataString = parse (pSparseDataFile <* eof)

-- | Parse a SDPA sparse format file (.dat-s).
parseSparseDataFile :: FilePath -> IO (Either ParseError Problem)
parseSparseDataFile = parseFromFile (pSparseDataFile <* eof)

pDataFile :: Parser Problem
pDataFile = do
  _ <- many pComment
  m  <- nat_line -- mDim
  _n <- nat_line -- nBlock
  bs <- pBlockStruct -- bLOCKsTRUCT
  cs <- pCosts
  ms <- pDenseMatrices (fromIntegral m) bs
  spaces
  return $
    Problem
    { blockStruct = bs
    , costs       = cs
    , matrices    = ms
    }

pSparseDataFile :: Parser Problem
pSparseDataFile = do
  _ <- many pComment
  m  <- nat_line -- mDim
  _n <- nat_line -- nBlock
  bs <- pBlockStruct -- bLOCKsTRUCT
  cs <- pCosts
  ms <- pSparseMatrices (fromIntegral m) bs
  spaces
  return $
    Problem
    { blockStruct = bs
    , costs       = cs
    , matrices    = ms
    }

pComment :: Parser String
pComment = do
  c <- oneOf "*\""
  cs <- manyTill anyChar newline
  return (c:cs)

pBlockStruct :: Parser [Int]
pBlockStruct = do
  optional sep
  let int' = int >>= \i -> optional sep >> return i
  xs <- many int'
  _ <- manyTill anyChar newline
  return $ map fromIntegral xs 
  where
    sep = many1 (oneOf " \t(){},")

pCosts :: Parser [Rational]
pCosts = do
  let sep = many1 (oneOf " \t(){},")
      real' = real >>= \r -> optional sep >> return r
  optional sep
  cs <- many real'
  _ <- newline
  return cs

pDenseMatrices :: Int -> [Int] -> Parser [Matrix]
pDenseMatrices m bs = optional sep >> replicateM (fromIntegral m + 1) pDenceMatrix
  where
    sep = many1 (space <|> oneOf "(){},")
    real' = real >>= \r -> optional sep >> return r
    pDenceMatrix = forM bs $ \b ->
      if b >= 0
      then do
        xs <- replicateM b (replicateM b real')
        return $ denseBlock xs
      else do
        xs <- replicateM (abs b) real'
        return $ diagBlock xs

pSparseMatrices :: Int -> [Int] -> Parser [Matrix]
pSparseMatrices m bs = do
  xs <- many pLine
  let t = IntMap.unionsWith (IntMap.unionWith Map.union)
            [ IntMap.singleton matno (IntMap.singleton blkno (Map.fromList [((i,j),e),((j,i),e)]))
            | (matno,blkno,i,j,e) <- xs ]
  return $
    [ [IntMap.findWithDefault Map.empty blkno mat | blkno <- [1 .. length bs]]
    | matno <- [0..m], let mat = IntMap.findWithDefault IntMap.empty matno t
    ]

  where
    sep = many1 (oneOf " \t") >> return ()
    pLine = do
      optional sep
      matno <- nat
      sep
      blkno <- nat
      sep
      i <- nat
      sep
      j <- nat
      sep
      e <- real
      optional sep
      _ <- newline
      return (fromIntegral matno, fromIntegral blkno, fromIntegral i, fromIntegral j, e)

nat_line :: Parser Integer
nat_line = do
  spaces
  n <- nat
  _ <- manyTill anyChar newline
  return n

nat :: Parser Integer
nat = do
  ds <- many1 digit
  return $! read ds

int :: Parser Integer
int = do
  s <- option 1 sign
  n <- nat
  return $! s * n

real :: Parser Rational
real = do
  s <- option 1 sign 
  b <- (do{ x <- nat; y <- option 0 frac; return (fromInteger x + y) })
    <|> frac
  c <- option 0 e
  return (s * b*10^^c)
  where
    digits = many1 digit

    frac :: Parser Rational
    frac = do
      _ <- char '.'
      s <- digits
      return (read s % 10^(length s))

    e :: Parser Integer
    e = do
      _ <- oneOf "eE"
      f <- msum [ char '+' >> return id
                , char '-' >> return negate
                , return id
                ]
      liftM f nat

sign :: Num a => Parser a
sign = (char '+' >> return 1) <|> (char '-' >> return (-1))

-- ---------------------------------------------------------------------------
-- rendering
-- ---------------------------------------------------------------------------

render :: Problem -> ShowS
render = renderImpl False

renderSparse :: Problem -> ShowS
renderSparse = renderImpl True

renderImpl :: Bool -> Problem -> ShowS
renderImpl sparse prob =
  -- mDim
  shows (mDim prob) . showString " = mDIM\n" .

  -- nBlock
  shows (nBlock prob) . showString " = nBlock\n" .

  -- blockStruct
  showChar '(' .
    sepByS [shows i | i <- blockStruct prob] (showString ", ") .
    showChar ')' .
    showString " = bLOCKsTRUCT\n" .

  -- costs
  showChar '(' .
    sepByS [showRat c | c <- costs prob] (showString ", ") .
    showString ")\n" .

  -- matrices
  if sparse
    then concatS [renderSparseMatrix matno m | (matno, m) <- zip [0..] (matrices prob)]
    else concatS $ map renderDenseMatrix (matrices prob)

  where
    renderSparseMatrix :: Int -> Matrix -> ShowS
    renderSparseMatrix matno m =
      concatS [ shows matno . showChar ' ' .
                shows blkno . showChar ' ' .
                shows i . showChar ' ' .
                shows j . showChar ' ' .
                showRat e . showChar '\n'
              | (blkno, blk) <- zip [(1::Int)..] m, ((i,j),e) <- Map.toList blk, i <= j ]

    renderDenseMatrix :: Matrix -> ShowS
    renderDenseMatrix m = 
      showString "{\n" .
      concatS [renderDenseBlock b s . showString "\n" | (b,s) <- zip m (blockStruct prob)] .
      showString "}\n"

    renderDenseBlock :: Block -> Int -> ShowS
    renderDenseBlock b s
      | s < 0 =
          showString "  " . renderVec [blockElem i i b | i <- [1 .. abs s]]
      | otherwise = 
          showString "  { " .
          sepByS [renderRow i | i <- [1..s]] (showString ", ") .     
          showString " }"
      where
        renderRow i = renderVec [blockElem i j b | j <- [1..s]]

renderVec :: [Rational] -> ShowS
renderVec xs =
  showChar '{' .
  sepByS (map showRat xs) (showString ", ") .
  showChar '}'

showRat :: Rational -> ShowS
showRat r
  | denominator r == 1 = shows (numerator r)
  | otherwise = shows (fromRational r :: Double)

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

sepByS :: [ShowS] -> ShowS -> ShowS
sepByS xs sep = concatS $ intersperse sep xs
