{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Encoder.PB.Internal.BCCNF
-- Copyright   :  (c) Masahiro Sakai 2022
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- References
--
-- * 南 雄之 (Yushi Minami), 宋 剛秀 (Takehide Soh), 番原 睦則
--   (Mutsunori Banbara), 田村 直之 (Naoyuki Tamura). ブール基数制約を
--   経由した擬似ブール制約のSAT符号化手法 (A SAT Encoding of
--   Pseudo-Boolean Constraints via Boolean Cardinality Constraints).
--   Computer Software, 2018, volume 35, issue 3, pages 65-78,
--   <https://doi.org/10.11309/jssst.35.3_65>
--
-----------------------------------------------------------------------------
module ToySolver.SAT.Encoder.PB.Internal.BCCNF
  (
  -- * High-level pure encoder
    encode

  -- * Low-level implementation
  , preprocess

  -- ** Prefix sum
  , PrefixSum
  , toPrefixSum
  , encodePrefixSum
  , encodePrefixSumBuggy
  , encodePrefixSumNaive

  -- ** Boolean cardinality constraints
  , BCLit
  , toAtLeast
  , implyBCLit

  -- ** Clause over boolean cardinality constraints
  , BCClause
  , reduceBCClause
  , implyBCClause

  -- ** CNF over boolean cardinality constraints
  , BCCNF
  , reduceBCCNF
  ) where

import Control.Exception (assert)
import Data.Function (on)
import Data.List (sortBy)
import Data.Maybe (listToMaybe)
import Data.Ord (comparing)

import ToySolver.SAT.Types

-- ------------------------------------------------------------------------

type PrefixSum = [(Integer, Int, [Lit])]

toPrefixSum :: PBLinSum -> PrefixSum
toPrefixSum s =
  assert (and [c > 0 | (c, _) <- s] && and (zipWith ((>=) `on` fst) s (tail s))) $
    go 0 [] s
  where
    go :: Int -> [Lit] -> PBLinSum -> PrefixSum
    go _ _ [] = []
    go !i prefix ((c, l) : ts)
      | c > c1 = (c - c1, i + 1, reverse (l : prefix)) : go (i + 1) (l : prefix) ts
      | otherwise = go (i + 1) (l : prefix) ts
      where
        c1 = maybe 0 fst (listToMaybe ts)

-- ------------------------------------------------------------------------

type BCLit = (Int, [Lit], Int)
type BCClause = [BCLit]
type BCCNF = [BCClause]

toAtLeast :: BCLit -> AtLeast
toAtLeast (_, lhs, rhs) = (lhs, rhs)

implyBCLit :: BCLit -> BCLit -> Bool
implyBCLit (i,_,a) (j,_,b)
  | i <= j = a >= b
  | otherwise = i - a <= j - b

reduceBCClause :: BCClause -> BCClause
reduceBCClause lits = assert (isAsc lits2) $ lits2
  where
    isAsc  ls = and [i1 <= i2 | let is = [i | (i,_,_) <- ls], (i1,i2) <- zip is (tail is)]
    isDesc ls = and [i1 >= i2 | let is = [i | (i,_,_) <- ls], (i1,i2) <- zip is (tail is)]

    lits1 = assert (isAsc lits) $ f1 [] minBound lits
    lits2 = assert (isDesc lits1) $ f2 [] maxBound lits1

    f1 r !_ [] = r
    f1 r !jb (l@(i,_,a) : ls)
      | ia > jb = f1 (l : r) ia ls
      | otherwise = f1 r jb ls
      where
        ia = i - a

    f2 r !_ [] = r
    f2 r !b (l@(_,_,a) : ls)
      | a < b = f2 (l : r) a ls
      | otherwise = f2 r b ls

implyBCClause :: BCClause -> BCClause -> Bool
implyBCClause lits1 lits2 = all (\lit1 -> any (implyBCLit lit1) lits2) lits1

reduceBCCNF :: BCCNF -> BCCNF
reduceBCCNF = reduceBCCNF' . map reduceBCClause

reduceBCCNF' :: BCCNF -> BCCNF
reduceBCCNF' = go []
  where
    go r [] = reverse r
    go r (c : cs)
      | any (\c' -> implyBCClause c' c) (r ++ cs) = go r cs
      | otherwise = go (c : r) cs

-- ------------------------------------------------------------------------

encode :: PBLinAtLeast -> [[AtLeast]]
encode constr = map (map toAtLeast) $ reduceBCCNF $ encodePrefixSum (toPrefixSum lhs) rhs
  where
    (lhs, rhs) = preprocess constr

preprocess :: PBLinAtLeast -> PBLinAtLeast
preprocess constr = (lhs2, rhs1)
  where
    (lhs1, rhs1) = normalizePBLinAtLeast constr
    lhs2 = sortBy (flip (comparing fst) <> comparing (abs . snd)) lhs1

-- | Algorithm 2 in the paper but with a bug fixed
encodePrefixSum :: PrefixSum -> Integer -> [[BCLit]]
encodePrefixSum = f 0 0
  where
    f !_ !_ [] !c = if c > 0 then [[]] else []
    f i0 d0 ((0,_,_) : bss) c = f i0 d0 bss c
    f i0 d0 ((b,i,ls) : bss) c =
      [ [(i, ls, maximum ds' + 1)] | not (null ds') ]
      ++
      [ if d+1 > i then theta else (i, ls, d+1) : theta
      | d <- ds, theta <- f i d bss (fromIntegral (c - b * fromIntegral d))
      ]
      where
        bssMax d = bssMin d + sum [b' * fromIntegral (i' - i) | (b', i', _) <- bss]
        bssMin d = sum [b' | (b', _, _) <- bss]  * fromIntegral d
        ds  = [d | d <- [d0 .. d0 + i - i0], let bd = b * fromIntegral d, c - bssMax d <= bd, bd < c - bssMin d]
        ds' = [d | d <- [d0 .. d0 + i - i0], b * fromIntegral d < c - bssMax d]

-- | Algorithm 2 in the paper
encodePrefixSumBuggy :: PrefixSum -> Integer -> [[BCLit]]
encodePrefixSumBuggy = f 0 0
  where
    f !_ !_ [] !c = if c > 0 then [[]] else []
    f i0 d0 ((0,_,_) : bss) c = f i0 d0 bss c
    f i0 d0 ((b,i,ls) : bss) c =
      [ [(i, ls, max (maximum ds' + 1) d0)] | not (null ds') ]
      ++
      [ if d+1 > i then theta else (i, ls, d+1) : theta
      | d <- ds, theta <- f i d bss (fromIntegral (c - b * fromIntegral d))
      ]
      where
        bssMax d = bssMin d + sum [b' * fromIntegral (i' - i) | (b', i', _) <- bss]
        bssMin d = sum [b' | (b', _, _) <- bss]  * fromIntegral d
        ds  = [d | d <- [d0 .. d0 + i - i0], let bd = b * fromIntegral d, c - bssMax d <= bd, bd < c - bssMin d]
        ds' = [d | d <- [0..i], b * fromIntegral d < c - bssMax d]

-- | Algorithm 1 in the paper
encodePrefixSumNaive :: PrefixSum -> Integer -> [[BCLit]]
encodePrefixSumNaive = f
  where
    f [] !c = if c > 0 then [[]] else []
    f ((0,_,_) : bss) c = f bss c
    f ((b,i,ls) : bss) c =
      [ [(i, ls, maximum ds' + 1)] | not (null ds') ]
      ++
      [ if d+1 > i then theta else (i, ls, d+1) : theta
      | d <- ds, theta <- f bss (fromIntegral (c - b * fromIntegral d))
      ]
      where
        bssMax = sum [b' * fromIntegral i' | (b', i', _) <- bss]
        bssMin = 0
        ds  = [d | d <- [0..i], let bd = b * fromIntegral d, c - bssMax <= bd, bd < c - bssMin]
        ds' = [d | d <- [0..i], b * fromIntegral d < c - bssMax]

-- ------------------------------------------------------------------------
