{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Arith.FourierMotzkin.Optimization
-- Copyright   :  (c) Masahiro Sakai 2014-2015
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Naïve implementation of Fourier-Motzkin Variable Elimination
-- 
-- Reference:
--
-- * <http://users.cecs.anu.edu.au/~michaeln/pubs/arithmetic-dps.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.Arith.FourierMotzkin.Optimization
  ( optimize
  ) where

import Control.Exception (assert)
import Control.Monad
import Data.Maybe
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.ExtendedReal
import qualified Data.Interval as Interval
import Data.Interval (Interval, (<=..<), (<..<=))
import Data.OptDir

import ToySolver.Data.DNF
import qualified ToySolver.Data.LA as LA
import ToySolver.Data.Var
import ToySolver.Arith.FourierMotzkin.Base

-- | @optimize dir obj φ@ returns @(I, lift)@ where
--
-- * @I@ is convex hull of feasible region, and
--
-- * @lift@ is a function, that takes @x ∈ I@ and returns the feasible solution with objective value /better than or equal to/ @x@.
--
-- Note:
-- 
-- * @'Interval.lowerBound' i@ (resp. @'Interval.upperBound' i@) is the optimal value in case of minimization (resp. maximization).
--
-- * If @I@ is empty, then the problem is INFEASIBLE.
-- 
optimize :: VarSet -> OptDir -> LA.Expr Rational -> [LA.Atom Rational] -> (Interval Rational, Rational -> Model Rational)
optimize vs dir obj cs = (ival, m)
  where
    rs = [projectToObj' vs obj cs' | cs' <- unDNF (constraintsToDNF cs)]
    ival = Interval.hulls (map fst rs)

    m :: Rational -> Model Rational
    m x = fromJust $ msum $ map f rs
      where
        f :: (Interval Rational, Rational -> Model Rational) -> Maybe (Model Rational)
        f (i1,m1) = do
          x' <- Interval.simplestRationalWithin (Interval.intersection i1 ib)
          return (m1 x')

        ib = case dir of
               OptMin -> NegInf <..<= Finite x
               OptMax -> Finite x <=..< PosInf

projectToObj' :: VarSet -> LA.Expr Rational -> [Constr] -> (Interval Rational, Rational -> Model Rational)
projectToObj' vs obj cs = projectTo' vs (eqR (toRat (LA.var z)) (toRat obj) : cs) z
  where
    z = fromMaybe 0 (fmap ((+1) . fst) (IntSet.maxView vs))

projectTo' :: VarSet -> [Constr] -> Var -> (Interval Rational, Rational -> Model Rational)
projectTo' vs cs z = fromMaybe (Interval.empty, \_ -> error "ToySolver.FourierMotzkin.projectTo': should not be called") $ do
  (ys,mt) <- projectN' vs =<< simplify cs
  let (bs,ws) = collectBounds z ys
  assert (null ws) $ return ()
  let ival = evalBounds IntMap.empty bs
  return (ival, \v -> mt (IntMap.singleton z v))
