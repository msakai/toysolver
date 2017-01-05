{-# LANGUAGE CPP, ConstraintKinds, FlexibleContexts, GADTs, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Text.SDPFile
-- Copyright   :  (c) Masahiro Sakai 2012,2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (CPP, ConstraintKinds, FlexibleContexts, GADTs, ScopedTypeVariables)
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
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy as BL
import Data.List (intersperse)
import Data.Scientific (Scientific)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import Text.Megaparsec
import qualified Text.Megaparsec.Lexer as Lexer
import Text.Megaparsec.Prim (MonadParsec ())

#if MIN_VERSION_megaparsec(5,0,0)
type C e s m = (MonadParsec e s m, Token s ~ Char)
#else
type C e s m = (MonadParsec s m Char)
#endif

-- ---------------------------------------------------------------------------
-- problem description
-- ---------------------------------------------------------------------------

data Problem
  = Problem
  { blockStruct :: [Int]      -- ^ the block strcuture vector (bLOCKsTRUCT)
  , costs       :: [Scientific] -- ^ Constant Vector
  , matrices    :: [Matrix]   -- ^ Constraint Matrices
  }
  deriving (Show, Ord, Eq)

type Matrix = [Block]

type Block = Map (Int,Int) Scientific

-- | the number of primal variables (mDim)
mDim :: Problem -> Int
mDim prob = length (matrices prob) - 1

-- | the number of blocks (nBLOCK)
nBlock :: Problem -> Int
nBlock prob = length (blockStruct prob)

blockElem :: Int -> Int -> Block -> Scientific
blockElem i j b = Map.findWithDefault 0 (i,j) b

-- ---------------------------------------------------------------------------
-- construction
-- ---------------------------------------------------------------------------

type DenseMatrix = [DenseBlock]

type DenseBlock = [[Scientific]]

denseBlock :: DenseBlock -> Block
denseBlock xxs = Map.fromList [((i,j),x) | (i,xs) <- zip [1..] xxs, (j,x) <- zip [1..] xs, x /= 0]

denseMatrix :: DenseMatrix -> Matrix
denseMatrix = map denseBlock

diagBlock :: [Scientific] -> Block
diagBlock xs = Map.fromList [((i,i),x) | (i,x) <- zip [1..] xs]

-- ---------------------------------------------------------------------------
-- parsing
-- ---------------------------------------------------------------------------

-- | Parse a SDPA format (.dat) string.
#if MIN_VERSION_megaparsec(5,0,0)
parseDataString :: (Stream s, Token s ~ Char) => String -> s -> Either (ParseError Char Dec) Problem
#else
parseDataString :: Stream s Char => String -> s -> Either ParseError Problem
#endif
parseDataString = parse (pDataFile <* eof)

-- | Parse a SDPA format file (.dat).
#if MIN_VERSION_megaparsec(5,0,0)
parseDataFile :: FilePath -> IO (Either (ParseError Char Dec) Problem)
#else
parseDataFile :: FilePath -> IO (Either ParseError Problem)
#endif
parseDataFile fname = do
  s <- BL.readFile fname
  return $! parse (pDataFile <* eof) fname s

-- | Parse a SDPA sparse format (.dat-s) string.
#if MIN_VERSION_megaparsec(5,0,0)
parseSparseDataString :: (Stream s, Token s ~ Char) => String -> s -> Either (ParseError Char Dec) Problem
#else
parseSparseDataString :: Stream s Char => String -> s -> Either ParseError Problem
#endif
parseSparseDataString = parse (pSparseDataFile <* eof)

-- | Parse a SDPA sparse format file (.dat-s).
#if MIN_VERSION_megaparsec(5,0,0)
parseSparseDataFile :: FilePath -> IO (Either (ParseError Char Dec) Problem)
#else
parseSparseDataFile :: FilePath -> IO (Either ParseError Problem)
#endif
parseSparseDataFile fname = do
  s <- BL.readFile fname
  return $! parse (pSparseDataFile <* eof) fname s

pDataFile :: C e s m => m Problem
pDataFile = do
  _ <- many pComment
  m  <- nat_line -- mDim
  _n <- nat_line -- nBlock
  bs <- pBlockStruct -- bLOCKsTRUCT
  cs <- pCosts
  ms <- pDenseMatrices (fromIntegral m) bs
  space
  return $
    Problem
    { blockStruct = bs
    , costs       = cs
    , matrices    = ms
    }

pSparseDataFile :: C e s m => m Problem
pSparseDataFile = do
  _ <- many pComment
  m  <- nat_line -- mDim
  _n <- nat_line -- nBlock
  bs <- pBlockStruct -- bLOCKsTRUCT
  cs <- pCosts
  ms <- pSparseMatrices (fromIntegral m) bs
  space
  return $
    Problem
    { blockStruct = bs
    , costs       = cs
    , matrices    = ms
    }

pComment :: C e s m => m String
pComment = do
  c <- oneOf "*\""
  cs <- manyTill anyChar newline
  return (c:cs)

pBlockStruct :: C e s m => m [Int]
pBlockStruct = do
  optional sep
  let int' = int >>= \i -> optional sep >> return i
  xs <- many int'
  _ <- manyTill anyChar newline
  return $ map fromIntegral xs 
  where
    sep = some (oneOf " \t(){},")

pCosts :: C e s m => m [Scientific]
pCosts = do
  let sep = some (oneOf " \t(){},")
      real' = real >>= \r -> optional sep >> return r
  optional sep
  cs <- many real'
  _ <- newline
  return cs

pDenseMatrices :: C e s m => Int -> [Int] -> m [Matrix]
pDenseMatrices m bs = optional sep >> replicateM (fromIntegral m + 1) pDenceMatrix
  where
    sep = some ((spaceChar >> return ()) <|> (oneOf "(){}," >> return ()))
    real' = real >>= \r -> optional sep >> return r
    pDenceMatrix = forM bs $ \b ->
      if b >= 0
      then do
        xs <- replicateM b (replicateM b real')
        return $ denseBlock xs
      else do
        xs <- replicateM (abs b) real'
        return $ diagBlock xs

pSparseMatrices :: C e s m => Int -> [Int] -> m [Matrix]
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
    sep = some (oneOf " \t") >> return ()
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

nat_line :: C e s m => m Integer
nat_line = do
  space
  n <- nat
  _ <- manyTill anyChar newline
  return n

nat :: C e s m => m Integer
nat = Lexer.decimal

int :: C e s m => m Integer
int = Lexer.signed (return ()) Lexer.decimal

real :: forall e s m. C e s m => m Scientific
real = Lexer.signed (return ()) Lexer.number

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
    sepByS [shows c | c <- costs prob] (showString ", ") .
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
                shows e . showChar '\n'
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

renderVec :: [Scientific] -> ShowS
renderVec xs =
  showChar '{' .
  sepByS (map shows xs) (showString ", ") .
  showChar '}'

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

sepByS :: [ShowS] -> ShowS -> ShowS
sepByS xs sep = concatS $ intersperse sep xs
