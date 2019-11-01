{-# LANGUAGE CPP, ConstraintKinds, FlexibleContexts, GADTs, ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Text.SDPFile
-- Copyright   :  (c) Masahiro Sakai 2012,2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
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
    -- * The solution type
  , Solution (..)
  , evalPrimalObjective
  , evalDualObjective

    -- * File I/O
  , readDataFile
  , writeDataFile

    -- * Construction
  , DenseMatrix
  , DenseBlock
  , denseMatrix
  , denseBlock
  , diagBlock
  
    -- * Rendering
  , renderData
  , renderSparseData

    -- * Parsing
  , ParseError
  , parseData
  , parseSparseData
  ) where

import Control.Exception
import Control.Monad
import qualified Data.ByteString.Lazy as BL
import Data.ByteString.Builder (Builder)
import qualified Data.ByteString.Builder as B
import qualified Data.ByteString.Builder.Scientific as B
import Data.Char
import qualified Data.Foldable as F
import Data.List (intersperse)
#if !MIN_VERSION_base(4,11,0)
import Data.Monoid
#endif
import Data.Scientific (Scientific)
#if !MIN_VERSION_megaparsec(5,0,0)
import Data.Scientific (fromFloatDigits)
#endif
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import System.FilePath (takeExtension)
import System.IO
import qualified Text.Megaparsec as MegaParsec
#if MIN_VERSION_megaparsec(6,0,0)
import Data.Word
import Data.Void
import Text.Megaparsec hiding (ParseError, oneOf)
import Text.Megaparsec.Byte hiding (oneOf)
import qualified Text.Megaparsec.Byte as MegaParsec
import qualified Text.Megaparsec.Byte.Lexer as Lexer
#else
import qualified Data.ByteString.Lazy.Char8 as BL8
import Text.Megaparsec hiding (ParseError, oneOf)
import qualified Text.Megaparsec.Lexer as Lexer
import Text.Megaparsec.Prim (MonadParsec ())
#endif

#if MIN_VERSION_megaparsec(7,0,0)
type C e s m = (MonadParsec e s m, Token s ~ Word8)
type ParseError = MegaParsec.ParseErrorBundle BL.ByteString Void
#elif MIN_VERSION_megaparsec(6,0,0)
type C e s m = (MonadParsec e s m, Token s ~ Word8)
type ParseError = MegaParsec.ParseError Word8 Void
#elif MIN_VERSION_megaparsec(5,0,0)
type C e s m = (MonadParsec e s m, Token s ~ Char)
type ParseError = MegaParsec.ParseError Char Dec
#else
type C e s m = (MonadParsec s m Char)
type ParseError = MegaParsec.ParseError
#endif

#if MIN_VERSION_megaparsec(7,0,0)
anyChar :: C e s m => m Word8
anyChar = anySingle
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
-- solution
-- ---------------------------------------------------------------------------

data Solution
  = Solution
  { primalVector :: [Scientific] -- ^ The primal variable vector x
  , primalMatrix :: Matrix -- ^ The primal variable matrix X
  , dualMatrix   :: Matrix -- ^ The dual variable matrix Y
  }
  deriving (Show, Ord, Eq)

evalPrimalObjective :: Problem -> Solution -> Scientific
evalPrimalObjective prob sol = sum $ zipWith (*) (costs prob) (primalVector sol)

evalDualObjective :: Problem -> Solution -> Scientific
evalDualObjective Problem{ matrices = [] } _ = error "evalDualObjective: invalid problem data"
evalDualObjective Problem{ matrices = f0:_ } sol =
  sum $ zipWith (\blk1 blk2 -> F.sum (Map.intersectionWith (*) blk1 blk2)) f0 (dualMatrix sol)

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
-- File I/O
-- ---------------------------------------------------------------------------

-- | Parse a SDPA format file (.dat) or a SDPA sparse format file (.dat-s)..
readDataFile :: FilePath -> IO Problem
readDataFile fname = do
  p <- case map toLower (takeExtension fname) of
    ".dat" -> return pDataFile
    ".dat-s" -> return pSparseDataFile
    ext -> ioError $ userError $ "unknown extension: " ++ ext
  s <- BL.readFile fname
  case parse (p <* eof) fname s of
    Left e -> throw (e :: ParseError)
    Right prob -> return prob

writeDataFile :: FilePath -> Problem -> IO ()
writeDataFile fname prob = do
  isSparse <- case map toLower (takeExtension fname) of
    ".dat" -> return False
    ".dat-s" -> return True
    ext -> ioError $ userError $ "unknown extension: " ++ ext
  withBinaryFile fname WriteMode $ \h -> do
    B.hPutBuilder h $ renderImpl isSparse prob

-- ---------------------------------------------------------------------------
-- parsing
-- ---------------------------------------------------------------------------

-- | Parse a SDPA format (.dat) string.
parseData :: String -> BL.ByteString -> Either ParseError Problem
parseData = parse (pDataFile <* eof)

-- | Parse a SDPA sparse format (.dat-s) string.
parseSparseData :: String -> BL.ByteString -> Either ParseError Problem
parseSparseData = parse (pSparseDataFile <* eof)

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

pComment :: C e s m => m BL.ByteString
pComment = do
  c <- oneOf "*\""
  cs <- manyTill anyChar newline
#if MIN_VERSION_megaparsec(6,0,0)
  return $ BL.pack (c:cs)
#else
  return $ BL8.pack (c:cs)
#endif

pBlockStruct :: C e s m => m [Int]
pBlockStruct = do
  _ <- optional sep
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
  _ <- optional sep
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
      _ <- optional sep
      matno <- nat
      sep
      blkno <- nat
      sep
      i <- nat
      sep
      j <- nat
      sep
      e <- real
      _ <- optional sep
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
#if MIN_VERSION_megaparsec(6,0,0)
real = Lexer.signed (return ()) Lexer.scientific
#elif MIN_VERSION_megaparsec(5,0,0)
real = Lexer.signed (return ()) Lexer.number
#else
real = liftM (either fromInteger fromFloatDigits) $ Lexer.signed (return ()) $ Lexer.number
#endif

#if MIN_VERSION_megaparsec(6,0,0)
oneOf :: C e s m => [Char] -> m Word8
oneOf = MegaParsec.oneOf . map (fromIntegral . fromEnum)
#else
oneOf :: C e s m => [Char] -> m Char
oneOf = MegaParsec.oneOf
#endif

-- ---------------------------------------------------------------------------
-- rendering
-- ---------------------------------------------------------------------------

renderData :: Problem -> Builder
renderData = renderImpl False

renderSparseData :: Problem -> Builder
renderSparseData = renderImpl True

renderImpl :: Bool -> Problem -> Builder
renderImpl sparse prob = mconcat
  [
  -- mDim
    B.intDec (mDim prob) <> " = mDIM\n"

  -- nBlock
  , B.intDec (nBlock prob) <> " = nBlock\n"

  -- blockStruct
  , B.char7 '('
  , sepByS [B.intDec i | i <- blockStruct prob] ", "
  , B.char7 ')'
  , " = bLOCKsTRUCT\n"

  -- costs
  , B.char7 '('
  , sepByS [B.scientificBuilder c | c <- costs prob] ", "
  , ")\n"

  -- matrices
  , if sparse
    then mconcat [renderSparseMatrix matno m | (matno, m) <- zip [0..] (matrices prob)]
    else mconcat $ map renderDenseMatrix (matrices prob)
  ]

  where
    renderSparseMatrix :: Int -> Matrix -> Builder
    renderSparseMatrix matno m =
      mconcat [ B.intDec matno <> B.char7 ' ' <>
                B.intDec blkno <> B.char7 ' ' <>
                B.intDec i <> B.char7 ' ' <>
                B.intDec j <> B.char7 ' ' <>
                B.scientificBuilder e <> B.char7 '\n'
              | (blkno, blk) <- zip [(1::Int)..] m, ((i,j),e) <- Map.toList blk, i <= j ]

    renderDenseMatrix :: Matrix -> Builder
    renderDenseMatrix m = 
      "{\n" <>
      mconcat [renderDenseBlock b s <> "\n" | (b,s) <- zip m (blockStruct prob)] <>
      "}\n"

    renderDenseBlock :: Block -> Int -> Builder
    renderDenseBlock b s
      | s < 0 =
          "  " <> renderVec [blockElem i i b | i <- [1 .. abs s]]
      | otherwise = 
          "  { " <>
          sepByS [renderRow i | i <- [1..s]] ", " <>     
          " }"
      where
        renderRow i = renderVec [blockElem i j b | j <- [1..s]]

renderVec :: [Scientific] -> Builder
renderVec xs =
  B.char7 '{' <>
  sepByS (map B.scientificBuilder xs) ", " <>
  B.char7 '}'

sepByS :: [Builder] -> Builder -> Builder
sepByS xs sep = mconcat $ intersperse sep xs
