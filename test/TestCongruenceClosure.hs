{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
module Main (main) where

import Test.HUnit hiding (Test)
import Test.Framework.TH
import Test.Framework.Providers.HUnit

import Algorithm.CongruenceClosure

------------------------------------------------------------------------
-- Test cases

case_1 :: IO ()
case_1 = do
  solver <- newSolver
  a <- newVar solver
  b <- newVar solver
  c <- newVar solver
  d <- newVar solver

  merge solver (FTConst a, c)
  ret <- areCongruent solver (FTApp a b) (FTApp c d)
  ret @?= False
  
  merge solver (FTConst b, d)
  ret <- areCongruent solver (FTApp a b) (FTApp c d)
  ret @?= True

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
