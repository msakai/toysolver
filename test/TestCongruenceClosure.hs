{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
module Main (main) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import ToySolver.CongruenceClosure

------------------------------------------------------------------------
-- Test cases

case_1 :: IO ()
case_1 = do
  solver <- newSolver
  a <- newVar solver
  b <- newVar solver
  c <- newVar solver
  d <- newVar solver

  merge solver (TApp a []) (TApp c [])
  ret <- areCongruent solver (TApp a [TApp b []]) (TApp c [TApp d []])
  ret @?= False
  
  merge solver (TApp b []) (TApp d [])
  ret <- areCongruent solver (TApp a [TApp b []]) (TApp c [TApp d []])
  ret @?= True

case_1_FlatTerm :: IO ()
case_1_FlatTerm = do
  solver <- newSolver
  a <- newVar solver
  b <- newVar solver
  c <- newVar solver
  d <- newVar solver

  mergeFlatTerm solver (FTConst a, c)
  ret <- areCongruentFlatTerm solver (FTApp a b) (FTApp c d)
  ret @?= False
  
  mergeFlatTerm solver (FTConst b, d)
  ret <- areCongruentFlatTerm solver (FTApp a b) (FTApp c d)
  ret @?= True
      
------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
