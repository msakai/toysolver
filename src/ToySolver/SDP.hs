{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SDP
-- Copyright   :  (c) Masahiro Sakai 2017
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  exprimental
-- Portability :  non-portable
--
-- References:
--
-- * Convert Semidefinite program forms - Mathematics Stack Exchange
--   <https://math.stackexchange.com/questions/732658/convert-semidefinite-program-forms>
--
-----------------------------------------------------------------------------

module ToySolver.SDP
  ( dualize
  , DualizeInfo (..)
  ) where

import qualified Data.Aeson as J
import Data.Aeson ((.=), (.:))
import qualified Data.Map.Strict as Map
import Data.Scientific (Scientific)
import ToySolver.Converter.Base
import ToySolver.Internal.JSON (withTypedObject)
import qualified ToySolver.Text.SDPFile as SDPFile

-- | Given a primal-dual pair (P), (D), it returns another primal-dual pair (P'), (D')
-- such that (P) is equivalent to (D') and (D) is equivalent to (P').
dualize :: SDPFile.Problem -> (SDPFile.Problem, DualizeInfo)
dualize origProb =
  ( SDPFile.Problem
    { SDPFile.blockStruct = blockStruct
    , SDPFile.costs = d
    , SDPFile.matrices = a0 : as
    }
  , DualizeInfo m (SDPFile.blockStruct origProb)
  )
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
             Z = Σ_i=1^n Σ_j=1^i A_ij z_ij - A_0
             Z ⪰ 0
       (D')
           max A_0 • W
           s.t.
             A_ij • W = d_ij  for i ∈ {1,…,n}, j ∈ {1,…,i}
             W ⪰ 0
       where
         z : variable over R^{n(n+1)/2}
         d_ij ∈ R  for i ∈ {1,…,n}, j ∈ {1,…,i}
         d_ij = - F0 [i,j]              if i=j
              = - (F0 [i,j] + F0 [j,i]) otherwise
         A_0  ∈ R^((2m+n)×(2m+n))
         A_0  = diag(-c, c, 0_{n×n})
         A_ij ∈ R^((2m+n)×(2m+n))  for i ∈ {1,…,n}, j ∈ {1,…,i}
         A_ij [   k,   k] = - (if i=j then F_k [i,j] else F_k [i,j] + F_k [j,i]) for k∈{1,…,m}
         A_ij [ m+k, m+k] =   (if i=j then F_k [i,j] else F_k [i,j] + F_k [j,i]) for k∈{1,…,m}
         A_ij [2m+i,2m+j] = 1
         A_ij [2m+j,2m+i] = 1
         A_ij [  _ ,  _ ] = 0

       correspondence:
         W = diag(x+, x-, X)
         Y [i,j] = z_ij if j≤i
                 = z_ji otherwise
         Z = diag(0, 0, Y)
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
blockIndexes n = if n >= 0 then [(i,j) | i <- [1..n], j <- [1..i]] else [(i,i) | i <- [1..(-n)]]

blockIndexesLen :: Int -> Int
blockIndexesLen n = if n >= 0 then n*(n+1) `div` 2 else -n


data DualizeInfo = DualizeInfo Int [Int]
  deriving (Eq, Show, Read)

instance Transformer DualizeInfo where
  type Source DualizeInfo = SDPFile.Solution
  type Target DualizeInfo = SDPFile.Solution

instance ForwardTransformer DualizeInfo where
  transformForward (DualizeInfo _origM origBlockStruct)
    SDPFile.Solution
    { SDPFile.primalVector = xV
    , SDPFile.primalMatrix = xM
    , SDPFile.dualMatrix   = yM
    } =
    SDPFile.Solution
    { SDPFile.primalVector = zV
    , SDPFile.primalMatrix = zM
    , SDPFile.dualMatrix   = wM
    }
    where
      zV = concat [[SDPFile.blockElem i j block | (i,j) <- blockIndexes b] | (b,block) <- zip origBlockStruct yM]
      zM = Map.empty : Map.empty : yM
      wM =
        [ Map.fromList $ zipWith (\i x -> ((i,i), if x >= 0 then   x else 0)) [1..] xV
        , Map.fromList $ zipWith (\i x -> ((i,i), if x <= 0 then  -x else 0)) [1..] xV
        ] ++ xM

instance BackwardTransformer DualizeInfo where
  transformBackward (DualizeInfo origM origBlockStruct)
    SDPFile.Solution
    { SDPFile.primalVector = zV
    , SDPFile.primalMatrix = _zM
    , SDPFile.dualMatrix   = wM
    } =
    case wM of
      (xps:xns:xM) ->
        SDPFile.Solution
        { SDPFile.primalVector = xV
        , SDPFile.primalMatrix = xM
        , SDPFile.dualMatrix   = yM
        }
        where
          xV = [SDPFile.blockElem i i xps - SDPFile.blockElem i i xns | i <- [1..origM]]
          yM = f origBlockStruct zV
            where
              f [] _ = []
              f (block : blocks) zV1 =
                case splitAt (blockIndexesLen block) zV1 of
                  (vals, zV2) -> symblock (zip (blockIndexes block) vals) : f blocks zV2
      _ -> error "ToySolver.SDP.transformSolutionBackward: invalid solution"

instance J.ToJSON DualizeInfo where
  toJSON (DualizeInfo origM origBlockStruct) =
    J.object
    [ "type" .= J.String "DualizeInfo"
    , "num_original_matrices" .= origM
    , "original_block_structure" .= origBlockStruct
    ] 

instance J.FromJSON DualizeInfo where
  parseJSON =
    withTypedObject "DualizeInfo" $ \obj ->
      DualizeInfo
        <$> obj .: "num_original_matrices"
        <*> obj .: "original_block_structure"

symblock :: [((Int,Int), Scientific)] -> SDPFile.Block
symblock es = Map.fromList $ do
  e@((i,j),x) <- es
  if x == 0 then
    []
  else if i == j then
    return e
  else
    [e, ((j,i),x)]
