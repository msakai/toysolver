{-# LANGUAGE ScopedTypeVariables, BangPatterns #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Algorithm.BoundsInference
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables, BangPatterns)
--
-- Tightening variable bounds by constraint propagation.
-- 
-----------------------------------------------------------------------------
module Algorithm.BoundsInference
  ( BoundsEnv
  , inferBounds
  , LA.computeInterval
  ) where

import Control.Monad
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.VectorSpace

import Data.ArithRel
import Data.Interval
import Data.LA (BoundsEnv)
import qualified Data.LA as LA
import Data.Var
import Util (isInteger)

type C r = (RelOp, LA.Expr r)

-- | tightening variable bounds by constraint propagation.
inferBounds :: forall r. (RealFrac r)
  => LA.BoundsEnv r -- ^ initial bounds
  -> [LA.Atom r]    -- ^ constraints
  -> VarSet         -- ^ integral variables
  -> Int            -- ^ limit of iterations
  -> LA.BoundsEnv r
inferBounds bounds constraints ivs limit = loop 0 bounds
  where
    cs :: VarMap [C r]
    cs = IM.fromListWith (++) $ do
      Rel lhs op rhs <- constraints
      let m = LA.coeffMap (lhs ^-^ rhs)
      (v,c) <- IM.toList m
      guard $ v /= LA.unitVar
      let op' = if c < 0 then flipOp op else op
          rhs' = (-1/c) *^ LA.fromCoeffMap (IM.delete v m)
      return (v, [(op', rhs')])

    loop  :: Int -> LA.BoundsEnv r -> LA.BoundsEnv r
    loop !i b = if (limit>=0 && i>=limit) || b==b' then b else loop (i+1) b'
      where
        b' = refine b

    refine :: LA.BoundsEnv r -> LA.BoundsEnv r
    refine b = IM.mapWithKey (\v i -> tighten v $ f b (IM.findWithDefault [] v cs) i) b

    -- tighten bounds of integer variables
    tighten :: Var -> Interval r -> Interval r
    tighten v x =
      if v `IS.notMember` ivs
        then x
        else tightenToInteger x

f :: (Real r, Fractional r) => LA.BoundsEnv r -> [C r] -> Interval r -> Interval r
f b cs i = foldr intersection i $ do
  (op, rhs) <- cs
  let i' = LA.computeInterval b rhs
      lb = lowerBound' i'
      ub = upperBound' i'
  case op of
    Eql -> return i'
    Le -> return $ interval (NegInf, False) ub
    Ge -> return $ interval lb (PosInf, False)
    Lt -> return $ interval (NegInf, False) (strict ub)
    Gt -> return $ interval (strict ub) (PosInf, False)
    NEq -> []

strict :: (EndPoint r, Bool) -> (EndPoint r, Bool)
strict (x, _) = (x, False)

-- | tightening intervals by ceiling lower bounds and flooring upper bounds.
tightenToInteger :: forall r. (RealFrac r) => Interval r -> Interval r
tightenToInteger ival = interval lb2 ub2
  where
    lb@(x1, in1) = lowerBound' ival
    ub@(x2, in2) = upperBound' ival
    lb2 =
      case x1 of
        Finite x ->
          ( if isInteger x && not in1
            then Finite (x + 1)
            else Finite (fromInteger (ceiling x))
          , True
          )
        _ -> lb
    ub2 =
      case x2 of
        Finite x ->
          ( if isInteger x && not in2
            then Finite (x - 1)
            else Finite (fromInteger (floor x))
          , True
          )
        _ -> ub
