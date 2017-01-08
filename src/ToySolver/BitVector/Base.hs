{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.BitVector.Base
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------
module ToySolver.BitVector.Base
  (
  -- * BitVector values
    BV
  , bv2nat
  , nat2bv
  , fromAscBits
  , fromDescBits
  , toAscBits
  , toDescBits
  , IsBV (..)

  -- * BitVector language
  , Var (..)
  , Expr (..)
  , Op1 (..)
  , Op2 (..)
  , repeat
  , zeroExtend
  , signExtend
  , Atom (..)
  , BVComparison (..)
  , module ToySolver.Data.OrdRel
  , Model
  , evalExpr
  , evalAtom
  ) where

import Prelude hiding (repeat)
import Data.Bits
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Ord
import qualified Data.Vector as V
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Unboxed as VU
import ToySolver.Data.Boolean
import ToySolver.Data.OrdRel

class Monoid a => IsBV a where
  width :: a -> Int
  extract :: Int -> Int -> a -> a
  fromBV :: BV -> a

  bvnot  :: a -> a
  bvand  :: a -> a -> a
  bvor   :: a -> a -> a
  bvxor  :: a -> a -> a
  bvnand :: a -> a -> a
  bvnor  :: a -> a -> a
  bvxnor :: a -> a -> a

  bvneg  :: a -> a
  bvadd  :: a -> a -> a
  bvsub  :: a -> a -> a
  bvmul  :: a -> a -> a
  bvudiv :: a -> a -> a
  bvurem :: a -> a -> a
  bvsdiv :: a -> a -> a
  bvsrem :: a -> a -> a
  bvsmod :: a -> a -> a
  bvshl  :: a -> a -> a
  bvlshr :: a -> a -> a
  bvashr :: a -> a -> a
  bvcomp :: a -> a -> a

  bvnand s t = bvnot (bvand s t)
  bvnor s t  = bvnot (bvor s t)
  bvxnor s t = bvnot (bvxor s t)

  bvsub s t = bvadd s (bvneg t)

repeat :: Monoid m => Int -> m -> m
repeat i x = mconcat (replicate i x)

zeroExtend :: IsBV a => Int -> a -> a
zeroExtend i s = fromAscBits (replicate i False) <> s

signExtend :: IsBV a => Int -> a -> a
signExtend i s
  | w == 0 = fromAscBits (replicate i False)
  | otherwise = repeat i (extract (w-1) (w-1) s) <> s
  where
    w = width s

class (IsBV a, IsEqRel a (ComparisonResult a), Complement (ComparisonResult a)) => BVComparison a where
  type ComparisonResult a

  bvule, bvult, bvuge, bvugt, bvsle, bvslt, bvsge, bvsgt :: a -> a -> ComparisonResult a

  bvule a b = notB (bvult b a)
  bvult a b = notB (bvule b a)
  bvuge a b = bvule b a
  bvugt a b = bvult b a

  bvsle a b = notB (bvslt b a)
  bvslt a b = notB (bvsle b a)
  bvsge a b = bvsle b a
  bvsgt a b = bvslt b a

  {-# MINIMAL (bvule | bvult), (bvsle | bvslt) #-}

-- ------------------------------------------------------------------------
    
newtype BV = BV (VU.Vector Bool)
  deriving (Eq)

instance Ord BV where
  compare (BV bs1) (BV bs2) =
    (comparing VG.length <> comparing VG.reverse) bs1 bs2

instance Monoid BV where
  mempty = BV VG.empty
  mappend (BV hi) (BV lo) = BV (lo <> hi) 

instance Show BV where
  show bv = "0b" ++ [if b then '1' else '0' | b <- toDescBits bv]

instance Bits BV where
  (.&.) = bvand
  (.|.) = bvor
  xor = bvxor
  complement = bvnot

  shiftL x i
    | i < w = extract (w-1-i) 0 x <> nat2bv i 0
    | otherwise = nat2bv w 0
    where
      w = width x
  shiftR x i
    | i < w = nat2bv i 0 <> extract (w-1) i x
    | otherwise = nat2bv w 0
    where
      w = width x
  rotateL x i
    | w == 0 = x
    | otherwise = extract (w-1-j) 0 x <> extract (w-1) (w-j) x
    where
      w = width x
      j = i `mod` w
  rotateR x i
    | w == 0 = x
    | otherwise = extract (j-1) 0 x <> extract (w-1) j x
    where
      w = width x
      j = i `mod` w

  zeroBits = error "zeroBits is not implemented"

  bit = error "bit is not implemented"

  setBit x@(BV bs) i 
    | 0 <= i && i < w = BV $ bs VG.// [(i,True)]
    | otherwise = x
    where
      w = width x
  clearBit x@(BV bs) i
    | 0 <= i && i < w = BV $ bs VG.// [(i,False)]
    | otherwise = x
    where
      w = width x
  complementBit x@(BV bs) i
    | 0 <= i && i < w = BV $ bs VG.// [(i, not (testBit x i))]
    | otherwise = x
    where
      w = width x
  testBit x@(BV bs) i
    | 0 <= i && i < w = bs VG.! i
    | otherwise = False
    where
      w = width x

  popCount x = sum [1 | b <- toAscBits x, b]

  bitSizeMaybe _ = Nothing
  bitSize _ = error "bitSize is not implemented"
  isSigned _ = False

instance IsBV BV where
  width (BV bs) = VG.length bs
  extract i j (BV bs) = BV $ VG.slice j (i - j + 1) bs
  fromBV = id

  bvnot (BV bs) = BV $ VG.map not bs

  bvand (BV bs1) (BV bs2)
    | VG.length bs1 /= VG.length bs2 = error "width mismatch"
    | otherwise = BV $ VG.zipWith (&&) bs1 bs2
  bvor (BV bs1) (BV bs2)
    | VG.length bs1 /= VG.length bs2 = error "width mismatch"
    | otherwise = BV $ VG.zipWith (||) bs1 bs2
  bvxor (BV bs1) (BV bs2) 
    | VG.length bs1 /= VG.length bs2 = error "width mismatch"
    | otherwise = BV $ VG.zipWith (/=) bs1 bs2

  bvneg x = nat2bv (width x) $ 2 ^ width x - bv2nat x

  bvadd x y
    | width x /= width y = error "invalid width"
    | otherwise = nat2bv (width x) (bv2nat x + bv2nat y)

  bvmul x y
    | width x /= width y = error "invalid width"
    | otherwise = nat2bv (width x) (bv2nat x * bv2nat y)

  bvudiv x y
    | width x /= width y = error "invalid width"
    | y' == 0 = error "division by zero"
    | otherwise = nat2bv (width x) (bv2nat x `div` y')
    where
      y' :: Integer
      y' = bv2nat y

  bvurem x y
    | width x /= width y = error "invalid width"
    | y' == 0 = error "division by zero"
    | otherwise = nat2bv (width x) (bv2nat x `mod` y')
    where
      y' :: Integer
      y' = bv2nat y

  bvsdiv x y
    | width x < 1 || width y < 1 || width x /= width y = error "invalid width"
    | not msb_x && not msb_y = bvudiv x y
    | msb_x && not msb_y = bvneg $ bvudiv (bvneg x) y
    | not msb_x && msb_y = bvneg $ bvudiv x (bvneg y)
    | otherwise = bvudiv (bvneg x) (bvneg y)
    where
      msb_x = testBit x (width x - 1)
      msb_y = testBit y (width y - 1)

  bvsrem x y
    | width x < 1 || width y < 1 || width x /= width y = error "invalid width"
    | not msb_x && not msb_y = bvurem x y
    | msb_x && not msb_y = bvneg $ bvurem (bvneg x) y
    | not msb_x && msb_y = bvurem x (bvneg y)
    | otherwise = bvneg $ bvurem (bvneg x) (bvneg y)
    where
      msb_x = testBit x (width x - 1)
      msb_y = testBit y (width y - 1)

  bvsmod x y
    | width x < 1 || width y < 1 || width x /= width y = error "invalid width"
    | bv2nat u == (0::Integer) = u
    | not msb_x && not msb_y = u
    | msb_x && not msb_y = bvadd (bvneg u) y
    | not msb_x && msb_y = bvadd u y
    | otherwise = bvneg u
    where
      msb_x = testBit x (width x - 1)
      msb_y = testBit y (width y - 1)
      abs_x = if msb_x then bvneg x else x
      abs_y = if msb_y then bvneg y else y
      u = bvurem abs_x abs_y

  bvshl  x y
    | width x /= width y = error "invalid width"
    | otherwise = nat2bv (width x) (bv2nat x `shiftL` bv2nat y)

  bvlshr x y
    | width x /= width y = error "invalid width"
    | otherwise = nat2bv (width x) (bv2nat x `shiftR` bv2nat y)

  bvashr x y
    | width x /= width y = error "invalid width"
    | not msb_x = bvlshr x y
    | otherwise = bvneg $ bvlshr (bvneg x) y
    where
      msb_x = testBit x (width x - 1)

  bvcomp x y
    | width x /= width y = error "invalid width"
    | otherwise = nat2bv 1 (if x==y then 1 else 0)

instance IsEqRel BV Bool where
  (.==.) = (==)
  (./=.) = (/=)

instance BVComparison BV where
  type ComparisonResult BV = Bool

  bvule = (<=)

  bvsle bs1 bs2
    | width bs1 /= width bs2 = error ("length mismatch: " ++ show (width bs1) ++ " and " ++ show (width bs2))
    | w == 0 = true
    | otherwise = bs1_msb && not bs2_msb || (bs1_msb == bs2_msb) && bs1 <= bs2
    where
      w = width bs1
      bs1_msb = testBit bs1 (w-1)
      bs2_msb = testBit bs2 (w-1)

bv2nat :: Integral a => BV -> a
bv2nat (BV bv) = VG.ifoldl' (\r i x -> if x then r+2^i else r) 0 bv

nat2bv :: IsBV a => Int -> Integer -> a
nat2bv m x = fromBV $ BV $ VG.generate m (testBit x)

fromAscBits :: IsBV a => [Bool] -> a
fromAscBits = fromBV . BV . VG.fromList

fromDescBits :: IsBV a => [Bool] -> a
fromDescBits = fromBV . fromAscBits . reverse

toAscBits :: BV -> [Bool]
toAscBits (BV bs) = VG.toList bs

toDescBits :: BV -> [Bool]
toDescBits = reverse . toAscBits

-- ------------------------------------------------------------------------

data Var
  = Var
  { varWidth :: {-# UNPACK #-} !Int
  , varId :: {-# UNPACK #-} !Int
  }
  deriving (Eq, Ord, Show)

data Expr
  = EConst BV
  | EVar Var
  | EOp1 Op1 Expr
  | EOp2 Op2 Expr Expr
  deriving (Eq, Ord, Show)

data Op1
  = OpExtract !Int !Int
  | OpNot
  | OpNeg
  deriving (Eq, Ord, Show)

data Op2
  = OpConcat
  | OpAnd
  | OpOr
  | OpXOr
  | OpComp
  | OpAdd
  | OpMul
  | OpUDiv
  | OpURem
  | OpSDiv
  | OpSRem
  | OpSMod
  | OpShl
  | OpLShr
  | OpAShr
  deriving (Eq, Ord, Enum, Bounded, Show)

instance IsBV Expr where
  width (EConst x) = width x
  width (EVar v) = varWidth v
  width (EOp1 op arg) =
    case op of
      OpExtract i j -> i - j + 1
      _ -> width arg
  width (EOp2 op arg1 arg2) =
    case op of
      OpConcat -> width arg1 + width arg2
      OpComp -> 1
      _ -> width arg1

  extract i j = EOp1 (OpExtract i j)

  fromBV = EConst

  bvnot = EOp1 OpNot
  bvand = EOp2 OpAnd
  bvor  = EOp2 OpOr
  bvxor = EOp2 OpXOr

  bvneg  = EOp1 OpNeg
  bvadd  = EOp2 OpAdd
  bvmul  = EOp2 OpMul
  bvudiv = EOp2 OpUDiv
  bvurem = EOp2 OpURem
  bvsdiv = EOp2 OpSDiv
  bvsrem = EOp2 OpSRem
  bvsmod = EOp2 OpSMod
  bvshl  = EOp2 OpShl
  bvlshr = EOp2 OpLShr
  bvashr = EOp2 OpAShr
  bvcomp = EOp2 OpComp

instance Monoid Expr where
  mempty = EConst mempty
  mappend = EOp2 OpConcat

instance Bits Expr where
  (.&.) = bvand
  (.|.) = bvor
  xor = bvxor
  complement = bvnot
  shiftL x i
    | i < w = extract (w-1-i) 0 x <> nat2bv i 0
    | otherwise = nat2bv w 0
    where
      w = width x
  shiftR x i
    | i < w = nat2bv i 0 <> extract (w-1) i x
    | otherwise = nat2bv w 0
    where
      w = width x
  rotateL x i
    | w == 0 = x
    | otherwise = extract (w-1-j) 0 x <> extract (w-1) (w-j) x
    where
      w = width x
      j = i `mod` w
  rotateR x i
    | w == 0 = x
    | otherwise = extract (j-1) 0 x <> extract (w-1) j x
    where
      w = width x
      j = i `mod` w

  zeroBits = error "zeroBits is not implemented"

  bit = error "bit is not implemented"

  setBit x i
    | 0 <= i && i < w = extract (w-1) (i+1) x <> fromDescBits [True] <> extract (i-1) 0 x
    | otherwise = x
    where
      w = width x

  clearBit x i
    | 0 <= i && i < w = extract (w-1) (i+1) x <> fromDescBits [False] <> extract (i-1) 0 x
    | otherwise = x
    where
      w = width x

  complementBit x i
    | 0 <= i && i < w = extract (w-1) (i+1) x <> bvnot (extract i i x) <> extract (i-1) 0 x
    | otherwise = x
    where
      w = width x

  testBit = error "testBit is not implemented"

  popCount = error "popCount is not implemented"

  bitSizeMaybe _ = Nothing
  bitSize _ = error "bitSize is not implemented"
  isSigned _ = False

data Atom = Rel (OrdRel Expr) Bool
  deriving (Eq, Ord, Show)

instance Complement Atom where
  notB (Rel rel signed) = Rel (notB rel) signed

instance IsEqRel Expr Atom where
  a .==. b = Rel (a .==. b) False
  a ./=. b = Rel (a ./=. b) False

instance BVComparison Expr where
  type ComparisonResult Expr = Atom

  bvule s t = Rel (s .<=. t) False
  bvult s t = Rel (s .<.  t) False
  bvuge s t = Rel (s .>=. t) False
  bvugt s t = Rel (s .>.  t) False
  bvsle s t = Rel (s .<=. t) True
  bvslt s t = Rel (s .<.  t) True
  bvsge s t = Rel (s .>=. t) True
  bvsgt s t = Rel (s .>.  t) True

-- ------------------------------------------------------------------------

type Model = (V.Vector BV, Map BV BV, Map BV BV)

evalExpr :: Model -> Expr -> BV
evalExpr (env, divTable, remTable) = f
  where
    f (EConst bv) = bv
    f (EVar v) = env VG.! varId v
    f (EOp1 op x) = evalOp1 op (f x)
    f (EOp2 op x y) = evalOp2 op (f x) (f y)

    evalOp1 (OpExtract i j) = extract i j
    evalOp1 OpNot = bvnot
    evalOp1 OpNeg = bvneg

    evalOp2 OpConcat a b = a <> b
    evalOp2 OpAnd x y = bvand x y
    evalOp2 OpOr x y = bvor x y
    evalOp2 OpXOr x y = bvxor x y
    evalOp2 OpAdd x y = bvadd x y
    evalOp2 OpMul x y = bvmul x y
    evalOp2 OpUDiv x y
      | y' /= 0 = bvudiv x y
      | otherwise =
          case Map.lookup x divTable of
            Just d -> d
            Nothing -> nat2bv (width x) 0
      where
        y' :: Integer
        y' = bv2nat y
    evalOp2 OpURem x y
      | y' /= 0 = bvurem x y
      | otherwise =
          case Map.lookup x remTable of
            Just r -> r
            Nothing -> nat2bv (width x) 0
      where
        y' :: Integer
        y' = bv2nat y
    evalOp2 OpSDiv x y
      | width x < 1 || width y < 1 || width x /= width y = error "invalid width"
      | not msb_x && not msb_y = evalOp2 OpUDiv x y
      | msb_x && not msb_y = bvneg $ evalOp2 OpUDiv (bvneg x) y
      | not msb_x && msb_y = bvneg $ evalOp2 OpUDiv x (bvneg y)
      | otherwise = evalOp2 OpUDiv (bvneg x) (bvneg y)
      where
        msb_x = testBit x (width x - 1)
        msb_y = testBit y (width y - 1)
    evalOp2 OpSRem x y
      | width x < 1 || width y < 1 || width x /= width y = error "invalid width"
      | not msb_x && not msb_y = evalOp2 OpURem x y
      | msb_x && not msb_y = bvneg $ evalOp2 OpURem (bvneg x) y
      | not msb_x && msb_y = evalOp2 OpURem x (bvneg y)
      | otherwise = bvneg $ evalOp2 OpURem (bvneg x) (bvneg y)
      where
        msb_x = testBit x (width x - 1)
        msb_y = testBit y (width y - 1)
    evalOp2 OpSMod x y
      | width x < 1 || width y < 1 || width x /= width y = error "invalid width"
      | bv2nat u == (0::Integer) = u
      | not msb_x && not msb_y = u
      | msb_x && not msb_y = bvadd (bvneg u) y
      | not msb_x && msb_y = bvadd u y
      | otherwise = bvneg u
      where
        msb_x = testBit x (width x - 1)
        msb_y = testBit y (width y - 1)
        abs_x = if msb_x then bvneg x else x
        abs_y = if msb_y then bvneg y else y
        u = evalOp2 OpURem abs_x abs_y
    evalOp2 OpShl x y = bvshl x y
    evalOp2 OpLShr x y = bvlshr x y
    evalOp2 OpAShr x y = bvashr x y
    evalOp2 OpComp x y = nat2bv 1 (if x==y then 1 else 0)

evalAtom :: Model -> Atom -> Bool
evalAtom m (Rel (OrdRel lhs op rhs) False) = evalOp op (evalExpr m lhs) (evalExpr m rhs)
evalAtom m (Rel (OrdRel lhs op rhs) True) =
  case op of
    Lt -> bvslt lhs' rhs'
    Gt -> bvslt rhs' lhs'
    Le -> bvsle lhs' rhs'
    Ge -> bvsle rhs' lhs'
    Eql -> lhs' == rhs'
    NEq -> lhs' /= rhs'
  where
    lhs' = evalExpr m lhs
    rhs' = evalExpr m rhs
