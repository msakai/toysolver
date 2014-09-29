{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module Main (main) where

import Control.Monad
import Test.HUnit hiding (Test)
import Test.QuickCheck
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.TH
import Test.Framework.Providers.QuickCheck2
import Test.Framework.Providers.HUnit
import qualified ToySolver.Data.Vec as Vec
import ToySolver.Internal.Util
import ToySolver.Internal.TextUtil
import qualified ToySolver.Knapsack as Knapsack

case_showRationalAsDecimal :: IO ()
case_showRationalAsDecimal = do
  showRationalAsFiniteDecimal 0      @?= Just "0.0"
  showRationalAsFiniteDecimal 1      @?= Just "1.0"
  showRationalAsFiniteDecimal (-1)   @?= Just "-1.0"
  showRationalAsFiniteDecimal 0.1    @?= Just "0.1"
  showRationalAsFiniteDecimal (-0.1) @?= Just "-0.1"
  showRationalAsFiniteDecimal 1.1    @?= Just "1.1"
  showRationalAsFiniteDecimal (-1.1) @?= Just "-1.1"
  showRationalAsFiniteDecimal (5/4)  @?= Just "1.25"
  showRationalAsFiniteDecimal (-5/4) @?= Just "-1.25"
  showRationalAsFiniteDecimal (4/3)  @?= Nothing
  showRationalAsFiniteDecimal (-4/3) @?= Nothing

case_readUnsignedInteger_maxBound_bug :: IO ()
case_readUnsignedInteger_maxBound_bug =
  readUnsignedInteger "006666666666666667" @?= 6666666666666667

prop_readUnsignedInteger = 
  forAll (choose (0, 2^128)) $ \i -> 
    readUnsignedInteger (show i) == i

case_knapsack_1 :: IO ()
case_knapsack_1 = Knapsack.solve [(5,4), (6,5), (3,2)] 9 @?= (11, 9, [True,True,False])

case_knapsack_2 :: IO ()
case_knapsack_2 = Knapsack.solve [(16,2), (19,3), (23,4), (28,5)] 7 @?= (44, 7, [True,False,False,True])

case_Vec :: IO ()
case_Vec = do
  (v::Vec.UVec Int) <- Vec.new
  let xs = [0..100]
  forM_ xs $ \i -> Vec.push v i
  ys <- Vec.getElems v
  ys @?= xs

  Vec.resize v 4
  zs <- Vec.getElems v
  zs @?= take 4 xs

  Vec.push v 1
  Vec.push v 2
  Vec.push v 3

  ws <- Vec.getElems v
  ws @?= take 4 xs ++ [1,2,3]

  x3 <- Vec.unsafePop v
  x3 @?= 3
  s <- Vec.getSize v
  s @?= 6
  ws <- Vec.getElems v
  ws @?= take 4 xs ++ [1,2]

case_Vec_clone :: IO ()
case_Vec_clone = do
  (v::Vec.UVec Int) <- Vec.new  
  Vec.push v 0
  v2 <- Vec.clone v
  Vec.write v2 0 1

  a <- Vec.read v 0
  a @?= 0

  b <- Vec.read v2 0
  b @?= 1

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
