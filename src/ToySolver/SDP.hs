{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SDP
-- Copyright   :  (c) Masahiro Sakai 2017
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  exprimental
-- Portability :  portable
--
-- References:
--
-- * Convert Semidefinite program forms - Mathematics Stack Exchange
--   <https://math.stackexchange.com/questions/732658/convert-semidefinite-program-forms>
--
-----------------------------------------------------------------------------

module ToySolver.SDP
  ( dualize
  ) where

import qualified Data.Map.Strict as Map
import Data.Scientific (Scientific)
import qualified ToySolver.Text.SDPFile as SDPFile

-- | Given a primal-dual pair (P), (D), it returns another primal-dual pair (P'), (D')
-- such that (P) is equivalent to (D') and (D) is equivalent to (P').
dualize :: SDPFile.Problem -> SDPFile.Problem
dualize origProb =
  SDPFile.Problem
  { SDPFile.blockStruct = blockStruct
  , SDPFile.costs = d
  , SDPFile.matrices = a0 : as
  }
  where
    {- original:
       (P)
           min Σ_i=1^m c_i x_i
           s.t.
             X = Σ_i=1^m F_i x_i - F_0
             X ⪰ 0
       (D)
           max F_0 • Y
           s.t.
             F_i • Y = c_i  for i ∈ {1,…,m}
             Y ⪰ 0
       where
         x : variable over R^m
         c ∈ R^m
         F_0, F_1, … , F_m ∈ R^(n × n)
    -}
    m :: Int
    m = SDPFile.mDim origProb
    c :: [Scientific]
    c = SDPFile.costs origProb
    f0 :: SDPFile.Matrix
    fs :: [SDPFile.Matrix]
    f0:fs = SDPFile.matrices origProb

    {- transformed
       (P')
           min d^T・z
           s.t.
             Z = Σ_i=1^n Σ_j=i^n A_ij z_ij - A_0
             Z ⪰ 0
       (D')
           max A_0 • W
           s.t.
             A_ij • W = d_ij  for i,j ∈ {1,…,n}, i≤j
             W ⪰ 0
       where
         z : variable over R^{n(n+1)/2}
         d ∈ R^{n(n+1)/2}
         d_ij = - F0 [i,j]              if i=j
              = - (F0 [i,j] + F0 [j,i]) otherwise
         A_0, A_ij ∈ R^((2m+n)×(2m+n)) for i,j∈{1,…,n} i≤j
         A_0  = diag(-c, c, 0_{n×n})
         A_ij = {(k,k)       ↦ - (if i=j then F_k [i,j] else F_k [i,j] + F_k [j,i]) | k∈{1,…,m}}
              ∪ {(m+k,m+k)   ↦   (if i=j then F_k [i,j] else F_k [i,j] + F_k [j,i]) | k∈{1,…,m}}
              ∪ {(2m+i,2m+j) ↦ 1}
              ∪ {(2m+j,2m+i) ↦ 1}

       correspondence:
         diag(W) = (x+, x-, X)
         Y [i,j] = z_ij if i≤j
                 = z_ji otherwise
    -}
    blockStruct :: [Int]
    blockStruct = [-m, -m] ++ SDPFile.blockStruct origProb
    a0 :: SDPFile.Matrix
    a0 =
      [ Map.fromList [((j,j), -cj) | (j,cj) <- zip [1..m] c, cj /= 0]
      , Map.fromList [((j,j),  cj) | (j,cj) <- zip [1..m] c, cj /= 0]
      ] ++
      [ Map.empty | _ <- SDPFile.blockStruct origProb]
    as :: [SDPFile.Matrix]
    as =
      [ [ Map.fromList [ ((k,k), - (if i == j then v else 2*v))
                       | (k,fk) <- zip [1..m] fs, let v = SDPFile.blockElem i j (fk!!b), v /= 0]
        , Map.fromList [ ((k,k),   (if i == j then v else 2*v))
                       | (k,fk) <- zip [1..m] fs, let v = SDPFile.blockElem i j (fk!!b), v /= 0]
        ] ++
        [ if b /= b2 then
            Map.empty
          else if i == j then
            Map.singleton (i,j) 1
          else
            Map.fromList [((i,j),1), ((j,i),1)]
        | (b2, _) <- zip [0..] (SDPFile.blockStruct origProb)
        ]
      | (b,block) <- zip [0..] (SDPFile.blockStruct origProb)
      , (i,j) <- blockIndexes block
      ]
    d =
      [ - (if i == j then v else 2*v)
      | (b,block) <- zip [0..] (SDPFile.blockStruct origProb)
      , (i,j) <- blockIndexes block
      , let v = SDPFile.blockElem i j (f0 !! b)
      ]

blockIndexes :: Int -> [(Int,Int)]
blockIndexes n = if n >= 0 then [(i,j) | i <- [1..n], j <- [i..n]] else [(i,i) | i <- [1..(-n)]]
