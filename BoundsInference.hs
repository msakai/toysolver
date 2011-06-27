{-# LANGUAGE ScopedTypeVariables, BangPatterns #-}
module BoundsInference
  ( Bounds
  , Constraint
  , inferBounds
  , evalToInterval
  ) where

import Control.Monad
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

import Expr
import Formula
import LA
import LC
import Interval
import Util (isInteger)

type C r = (RelOp, LC r)

inferBounds :: forall r. (RealFrac r) => Bounds r -> [Constraint r] -> VarSet -> Int -> Bounds r
inferBounds bounds constraints ivs limit = loop 0 bounds
  where
    cs :: VarMap [C r]
    cs = IM.fromListWith (++) $ do
      LARel lhs op rhs <- constraints
      let LC m = lhs .-. rhs
      (v,c) <- IM.toList m
      guard $ v /= constKey
      let op' = if c < 0 then flipOp op else op
          rhs' = (-1/c) .*. LC (IM.delete v m)
      return (v, [(op', rhs')])

    loop  :: Int -> Bounds r -> Bounds r
    loop !i b = if (limit>=0 && i>=limit) || b==b' then b else loop (i+1) b'
      where
        b' = refine b

    refine :: Bounds r -> Bounds r
    refine b = IM.mapWithKey (\v i -> tighten v $ f b (IM.findWithDefault [] v cs) i) b

    -- tighten bounds of integer variables
    tighten :: Var -> Interval r -> Interval r
    tighten v x@(Interval lb ub) =
      if v `IS.notMember` ivs
        then x
        else interval (fmap tightenLB lb) (fmap tightenUB ub)
      where
        tightenLB (incl,lb) =
          ( True
          , if isInteger lb && not incl
            then lb + 1
            else fromIntegral (ceiling lb :: Integer)
          )
        tightenUB (incl,ub) =
          ( True
          , if isInteger ub && not incl
            then ub - 1
            else fromIntegral (floor ub :: Integer)
          )

f :: (Real r, Fractional r) => Bounds r -> [C r] -> Interval r -> Interval r
f b cs i = foldr intersection i $ do
  (op, rhs) <- cs
  let i'@(Interval lb ub) = evalToInterval b rhs
  case op of
    Eql -> return i'
    Le -> return $ interval Nothing ub
    Ge -> return $ interval lb Nothing
    Lt -> return $ interval Nothing (strict ub)
    Gt -> return $ interval (strict lb) Nothing
    NEq -> []

evalToInterval :: (Real r, Fractional r) => Bounds r -> LC r -> Interval r
evalToInterval b (LC m) = lsum
  [ if v==constKey then singleton c else c .*. (b IM.! v)
  | (v,c) <- IM.toList m ]

strict :: EndPoint r -> EndPoint r
strict Nothing = Nothing
strict (Just (_,val)) = Just (False,val)
