{-# LANGUAGE ScopedTypeVariables #-}
module BoundsInference
  ( Bounds
  , Constraint
  , inferBounds
  , evalToInterval
  ) where

import Control.Monad
import qualified Data.IntMap as IM

import Expr
import Formula
import LC
import Interval

type Bounds r = VarMap (Interval r)

type Constraint r = (LC r, RelOp, LC r)

type C r = (RelOp, LC r)

inferBounds :: forall r. (Real r, Fractional r) => Bounds r -> [Constraint r] -> Bounds r
inferBounds bounds constraints = loop bounds
  where
    cs :: VarMap [C r]
    cs = IM.fromListWith (++) $ do
      (lhs, op, rhs) <- constraints
      let LC m = lhs .-. rhs
      (v,c) <- IM.toList m
      guard $ v /= constKey
      let op' = if c < 0 then flipOp op else op
          rhs' = (-1/c) .*. LC (IM.delete v m)
      return (v, [(op', rhs')])

    loop  :: Bounds r -> Bounds r
    loop b = if b==b' then b else loop b'
      where
        b' = refine b

    refine :: Bounds r -> Bounds r
    refine b = IM.mapWithKey (\v i -> f b (IM.findWithDefault [] v cs) i) b

f :: (Real r, Fractional r) => Bounds r -> [C r] -> Interval r -> Interval r
f b cs i = foldr intersection i $ do
  (op, rhs) <- cs
  let i'@(Interval lb ub) = evalToInterval b rhs
  case op of
    Eql -> return i'
    Le -> return $ Interval Nothing ub
    Ge -> return $ Interval lb Nothing
    Lt -> return $ Interval Nothing (strict ub)
    Gt -> return $ Interval (strict lb) Nothing
    NEq -> []

evalToInterval :: (Real r, Fractional r) => Bounds r -> LC r -> Interval r
evalToInterval b (LC m) = foldr (.+.) zero
  [ if v==constKey then singleton c else c .*. (b IM.! v)
  | (v,c) <- IM.toList m ]

strict :: EndPoint r -> EndPoint r
strict Nothing = Nothing
strict (Just (_,val)) = Just (False,val)
