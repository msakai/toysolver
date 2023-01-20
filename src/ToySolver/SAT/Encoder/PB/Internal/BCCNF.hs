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
  -- * Monadic interface
    addPBLinAtLeastBCCNF
  , encodePBLinAtLeastWithPolarityBCCNF

  -- * High-level pure encoder
  , encode

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
import Control.Monad
import Control.Monad.Primitive
import Data.Function (on)
import Data.List (sortBy)
import Data.Maybe (listToMaybe)
import Data.Ord (comparing)

import ToySolver.SAT.Types
import qualified ToySolver.SAT.Encoder.Cardinality as Card
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin

-- ------------------------------------------------------------------------

-- | \(\sum_{j=1}^i b_j s_j = \sum_{j=1}^i b_j (x_1, \ldots, x_j)\) is represented
-- as a list of tuples consisting of \(b_j, j, [x_1, \ldots, x_j]\).
type PrefixSum = [(Integer, Int, [Lit])]

-- | Convert 'PBLinSum' to 'PrefixSum'.
-- The 'PBLinSum' must be 'preprocess'ed before calling the function.
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

-- | A constraint \(s_i \ge c\) where \(s_i = x_1 + \ldots + x_i\) is represnted as
-- a tuple of \(i\), \([x_1, \ldots, x_i]\), and \(c\).
type BCLit = (Int, [Lit], Int)

-- | Disjunction of 'BCLit'
type BCClause = [BCLit]

-- | Conjunction of 'BCClause'
type BCCNF = [BCClause]

-- | Forget \(s_i\) and returns \(x_1 + \ldots + x_i \ge c\).
toAtLeast :: BCLit -> AtLeast
toAtLeast (_, lhs, rhs) = (lhs, rhs)

-- | \((s_i \ge a) \Rightarrow (s_j \ge b)\) is defined as
-- \((i \le j \wedge a \ge b) \vee (i \ge b \wedge i - a \le j - b)\).
implyBCLit :: BCLit -> BCLit -> Bool
implyBCLit (i,_,a) (j,_,b)
  | i <= j = a >= b
  | otherwise = i - a <= j - b

-- | Remove redundant literals based on 'implyBCLit'.
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

-- | \(C \Rightarrow C'\) is defined as \(\forall l\in C \exists l' \in C' (l \Rightarrow l')\).
implyBCClause :: BCClause -> BCClause -> Bool
implyBCClause lits1 lits2 = all (\lit1 -> any (implyBCLit lit1) lits2) lits1

-- | Reduce 'BCCNF' by reducing each clause using 'reduceBCClause' and then
-- remove redundant clauses based on 'implyBCClause'.
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

-- | Encode a given pseudo boolean constraint \(\sum_i a_i x_i \ge c\)
-- into an equilavent formula in the form of
-- \(\bigwedge_j \bigvee_k \sum_{l \in L_{j,k}} l \ge d_{j,k}\).
encode :: PBLinAtLeast -> [[AtLeast]]
encode constr = map (map toAtLeast) $ reduceBCCNF $ encodePrefixSum (toPrefixSum lhs) rhs
  where
    (lhs, rhs) = preprocess constr

-- | Perform 'normalizePBLinAtLeast' and sort the terms in descending order of coefficients
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

addPBLinAtLeastBCCNF :: PrimMonad m => Card.Encoder m -> PBLinAtLeast -> m ()
addPBLinAtLeastBCCNF enc constr = do
  forM_ (encode constr) $ \clause -> do
    addClause enc =<< mapM (Card.encodeAtLeast enc) clause

encodePBLinAtLeastWithPolarityBCCNF :: PrimMonad m => Card.Encoder m -> Tseitin.Polarity -> PBLinAtLeast -> m Lit
encodePBLinAtLeastWithPolarityBCCNF enc polarity constr = do
  let tseitin = Card.getTseitinEncoder enc
  ls <- forM (encode constr) $ \clause -> do
    Tseitin.encodeDisjWithPolarity tseitin polarity =<< mapM (Card.encodeAtLeastWithPolarity enc polarity) clause
  Tseitin.encodeConjWithPolarity tseitin polarity ls

-- ------------------------------------------------------------------------
