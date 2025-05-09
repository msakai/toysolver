{-# LANGUAGE TemplateHaskell #-}
module Test.ContiTraverso (ctTestGroup) where

import Control.Monad
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Map as Map
import Data.VectorSpace

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH

import Data.OptDir

import ToySolver.Arith.ContiTraverso

import ToySolver.Data.OrdRel
import qualified ToySolver.Data.LA as LA
import ToySolver.Data.Polynomial (Polynomial)
import qualified ToySolver.Data.Polynomial as P

-- http://madscientist.jp/~ikegami/articles/IntroSequencePolynomial.html
-- optimum is (3,2,0)
case_ikegami = solve P.grlex (IS.fromList vs) OptMin obj cs @?= Just (IM.fromList [(1,3),(2,2),(3,0)])
  where
    vs = [1..3]
    [x,y,z] = map LA.var vs
    cs = [ 2*^x ^+^ 2*^y ^+^ 2*^z .==. LA.constant 10
         , 3*^x ^+^ y ^+^ z .==. LA.constant 11
         , x .>=. LA.constant 0
         , y .>=. LA.constant 0
         , z .>=. LA.constant 0
         ]
    obj = x ^+^ 2*^y ^+^ 3*^z

case_ikegami' = solve' P.grlex (IS.fromList vs) obj cs @?= Just (IM.fromList [(1,3),(2,2),(3,0)])
  where
    vs@[x,y,z] = [1..3]
    cs = [ (LA.fromTerms [(2,x),(2,y),(2,z)], 10)
         , (LA.fromTerms [(3,x),(1,y),(1,z)], 11)
         ]
    obj = LA.fromTerms [(1,x),(2,y),(3,z)]

-- http://posso.dm.unipi.it/users/traverso/conti-traverso-ip.ps
-- optimum is (39, 75, 1, 8, 122)
disabled_case_test1 = solve P.grlex (IS.fromList vs) OptMin obj cs @?= Just (IM.fromList [(1,39), (2,75), (3,1), (4,8), (5,122)])
  where
    vs = [1..5]
    vs2@[x1,x2,x3,x4,x5] = map LA.var vs
    cs = [ 2*^x1 ^+^ 5*^x2 ^-^ 3*^x3 ^+^    x4 ^-^ 2*^x5 .==. LA.constant 214
         ,    x1 ^+^ 7*^x2 ^+^ 2*^x3 ^+^ 3*^x4 ^+^    x5 .==. LA.constant 712
         , 4*^x1 ^-^ 2*^x2 ^-^    x3 ^-^ 5*^x4 ^+^ 3*^x5 .==. LA.constant 331
         ] ++
         [ v .>=. LA.constant 0 | v <- vs2 ]
    obj = x1 ^+^ x2 ^+^ x3 ^+^ x4 ^+^ x5

disabled_case_test1' = solve' P.grlex (IS.fromList vs) obj cs @?= Just (IM.fromList [(1,39), (2,75), (3,1), (4,8), (5,122)])
  where
    vs@[x1,x2,x3,x4,x5] = [1..5]
    cs = [ (LA.fromTerms [(2, x1), ( 5, x2), (-3, x3), ( 1,x4), (-2, x5)], 214)
         , (LA.fromTerms [(1, x1), ( 7, x2), ( 2, x3), ( 3,x4), ( 1, x5)], 712)
         , (LA.fromTerms [(4, x1), (-2, x2), (-1, x3), (-5,x4), ( 3, x5)], 331)
         ]
    obj = LA.fromTerms [(1,x1),(1,x2),(1,x3),(1,x4),(1,x5)]

-- optimum is (0,2,2)
case_test2 = solve P.grlex (IS.fromList vs) OptMin obj cs @?= Just (IM.fromList [(1,0),(2,2),(3,2)])
  where
    vs = [1..3]
    vs2@[x1,x2,x3] = map LA.var vs
    cs = [ 2*^x1 ^+^ 3*^x2 ^-^ x3 .==. LA.constant 4 ] ++
         [ v .>=. LA.constant 0 | v <- vs2 ]
    obj = 2*^x1 ^+^ x2

case_test2' = solve' P.grlex (IS.fromList vs) obj cs @?= Just (IM.fromList [(1,0),(2,2),(3,2)])
  where
    vs@[x1,x2,x3] = [1..3]
    cs = [ (LA.fromTerms [(2, x1), (3, x2), (-1, x3)], 4) ]
    obj = LA.fromTerms [(2,x1),(1,x2)]

-- infeasible
case_test3 = solve P.grlex (IS.fromList vs) OptMin obj cs @?= Nothing
  where
    vs = [1..3]
    vs2@[x1,x2,x3] = map LA.var vs
    cs = [ 2*^x1 ^+^ 2*^x2 ^+^ 2*^x3 .==. LA.constant 3 ] ++
         [ v .>=. LA.constant 0 | v <- vs2 ]
    obj = x1

case_test3' = solve' P.grlex (IS.fromList vs) obj cs @?= Nothing
  where
    vs@[x1,x2,x3] = [1..3]
    cs = [ (LA.fromTerms [(2, x1), (2, x2), (2, x3)], 3) ]
    obj = LA.fromTerms [(1,x1)]

------------------------------------------------------------------------
-- Test harness

ctTestGroup :: TestTree
ctTestGroup = $(testGroupGenerator)
