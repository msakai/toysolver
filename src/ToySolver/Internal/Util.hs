{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Internal.Util
-- Copyright   :  (c) Masahiro Sakai 2011-2012
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Some utility functions.
--
-----------------------------------------------------------------------------

module ToySolver.Internal.Util where

import Control.Monad
import Data.Ratio
import Data.Set (Set)
import qualified Data.Set as Set
import System.IO
import GHC.IO.Encoding

-- | Combining two @Maybe@ values using given function.
combineMaybe :: (a -> a -> a) -> Maybe a -> Maybe a -> Maybe a
combineMaybe _ Nothing y = y
combineMaybe _ x Nothing = x
combineMaybe f (Just x) (Just y) = Just (f x y)

-- | is the number integral?
--
-- @
--    isInteger x = fromInteger (round x) == x
-- @
isInteger :: RealFrac a => a -> Bool
isInteger x = fromInteger (round x) == x

-- | fractional part
--
-- @
--   fracPart x = x - fromInteger (floor x)
-- @
fracPart :: RealFrac a => a -> a
fracPart x = x - fromInteger (floor x)

showRational :: Bool -> Rational -> String
showRational asRatio v
  | denominator v == 1 = show (numerator v)
  | asRatio            = show (numerator v) ++ "/" ++ show (denominator v)
  | otherwise          = show (fromRational v :: Double)

showRationalAsFiniteDecimal :: Rational -> Maybe String
showRationalAsFiniteDecimal x = do
  let a :: Integer
      (a,b) = properFraction (abs x)
      s1 = if x < 0 then "-" else ""
      s2 = show a
  s3 <- if b == 0
        then return ".0"
        else liftM ("." ++ ) $ loop Set.empty b
  return $ s1 ++ s2 ++ s3
  where
    loop :: Set Rational -> Rational -> Maybe String
    loop _ 0 = return ""
    loop rs r
      | r `Set.member` rs = mzero
      | otherwise = do
          let a :: Integer
              (a,b) = properFraction (r * 10)
          s <- loop (Set.insert r rs) b
          return $ show a ++ s

{-# INLINE revSequence #-}
revSequence :: Monad m => [m a] -> m [a]
revSequence = go []
  where
    go xs [] = return xs
    go xs (m:ms) = do
      x <- m
      go (x:xs) ms

{-# INLINE revMapM #-}
revMapM :: Monad m => (a -> m b) -> ([a] -> m [b])
revMapM f = revSequence . map f

{-# INLINE revForM #-}
revForM :: Monad m => [a] -> (a -> m b) -> m [b]
revForM = flip revMapM

setEncodingChar8 :: IO ()
setEncodingChar8 = do
  setLocaleEncoding char8
  setForeignEncoding char8
  setFileSystemEncoding char8
