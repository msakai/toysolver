{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.BitVector
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------
module ToySolver.BitVector
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
  , module ToySolver.Data.OrdRel
  , ule
  , ult
  , uge
  , ugt
  , sle
  , slt
  , sge
  , sgt
  , Model
  , evalExpr
  , evalAtom
  
  -- * BitVector solver
  , Solver
  , newSolver
  , newVar
  , assertAtom
  , check
  , getModel
  , explain
  , pushBacktrackPoint
  , popBacktrackPoint
  ) where

import Prelude hiding (repeat)
import Control.Applicative hiding (Const (..))
import Control.Monad
import Data.Bits
import qualified Data.Foldable as F
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Data.Ord
import qualified Data.Vector as V
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Unboxed as VU
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import ToySolver.Data.BoolExpr
import ToySolver.Data.Boolean
import ToySolver.Data.OrdRel
import qualified ToySolver.Internal.Data.SeqQueue as SQ
import qualified ToySolver.Internal.Data.Vec as Vec
import qualified ToySolver.SAT as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin

class Monoid a => IsBV a where
  width :: a -> Int
  extract :: Int -> Int -> a -> a
  fromBV :: BV -> a

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
  BV bs1 .&. BV bs2
    | VG.length bs1 /= VG.length bs2 = error "width mismatch"
    | otherwise = BV $ VG.zipWith (&&) bs1 bs2
  BV bs1 .|. BV bs2
    | VG.length bs1 /= VG.length bs2 = error "width mismatch"
    | otherwise = BV $ VG.zipWith (||) bs1 bs2
  xor (BV bs1) (BV bs2) 
    | VG.length bs1 /= VG.length bs2 = error "width mismatch"
    | otherwise = BV $ VG.zipWith (/=) bs1 bs2

  complement (BV bs) = BV $ VG.map not bs

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
  | OpNAnd
  | OpNOr
  | OpXNOr
  | OpComp
  | OpAdd
  | OpSub
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

  bvneg  = EOp1 OpNeg
  bvadd  = EOp2 OpAdd
  bvsub  = EOp2 OpSub
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
  (.&.) = EOp2 OpAnd
  (.|.) = EOp2 OpOr
  xor = EOp2 OpXOr
  complement = EOp1 OpNot
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
    | 0 <= i && i < w = extract (w-1) (i+1) x <> complement (extract i i x) <> extract (i-1) 0 x
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

ule, ult, uge, ugt, sle, slt, sge, sgt :: Expr -> Expr -> Atom
ule s t = Rel (s .<=. t) False
ult s t = Rel (s .<.  t) False
uge s t = Rel (s .>=. t) False
ugt s t = Rel (s .>.  t) False
sle s t = Rel (s .<=. t) True
slt s t = Rel (s .<.  t) True
sge s t = Rel (s .>=. t) True
sgt s t = Rel (s .>.  t) True

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
    evalOp1 OpNot = complement
    evalOp1 OpNeg = bvneg

    evalOp2 OpConcat a b = a <> b
    evalOp2 OpAnd x y = x .&. y
    evalOp2 OpOr x y = x .|. y
    evalOp2 OpXOr x y = x `xor` y
    evalOp2 OpNAnd x y = complement (x .&. y)
    evalOp2 OpNOr x y  = complement (x .|. y)
    evalOp2 OpXNOr x y = complement (x `xor` y)
    evalOp2 OpAdd x y = bvadd x y
    evalOp2 OpSub x y = bvsub x y
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
    Lt -> bvslt' lhs' rhs'
    Gt -> bvslt' rhs' lhs'
    Le -> bvsle' lhs' rhs'
    Ge -> bvsle' rhs' lhs'
    Eql -> lhs' == rhs'
    NEq -> lhs' /= rhs'
  where
    lhs' = evalExpr m lhs
    rhs' = evalExpr m rhs

    bvsle' :: BV -> BV -> Bool
    bvsle' bs1 bs2
      | width bs1 /= width bs2 = error ("length mismatch: " ++ show (width bs1) ++ " and " ++ show (width bs2))
      | w == 0 = true
      | otherwise = bs1_msb && not bs2_msb || (bs1_msb == bs2_msb) && bs1 <= bs2
      where
        w = width bs1
        bs1_msb = testBit bs1 (w-1)
        bs2_msb = testBit bs2 (w-1)

    bvslt' :: BV -> BV -> Bool    
    bvslt' bs1 bs2
      | width bs1 /= width bs2 = error ("length mismatch: " ++ show (width bs1) ++ " and " ++ show (width bs2))
      | w == 0 = false
      | otherwise = bs1_msb && not bs2_msb || (bs1_msb == bs2_msb) && bs1 < bs2
      where
        w = width bs1
        bs1_msb = testBit bs1 (w-1)
        bs2_msb = testBit bs2 (w-1)

-- ------------------------------------------------------------------------

data Solver
  = Solver
  { svVars :: Vec.Vec (VU.Vector SAT.Lit)
  , svSATSolver :: SAT.Solver
  , svTseitin :: Tseitin.Encoder IO
  , svEncTable :: IORef (Map Expr (VU.Vector SAT.Lit))
  , svDivRemTable :: IORef [(VU.Vector SAT.Lit, VU.Vector SAT.Lit, VU.Vector SAT.Lit, VU.Vector SAT.Lit)]
  , svContexts :: Vec.Vec (IntMap (Maybe Int))
  }

newSolver :: IO Solver
newSolver = do
  vars <- Vec.new
  sat <- SAT.newSolver
  tseitin <- Tseitin.newEncoder sat
  table <- newIORef Map.empty
  divRemTable <- newIORef []
  contexts <- Vec.new
  Vec.push contexts IntMap.empty
  return $
    Solver
    { svVars = vars
    , svSATSolver = sat
    , svTseitin = tseitin
    , svEncTable = table
    , svDivRemTable = divRemTable
    , svContexts = contexts
    }

newVar :: Solver -> Int -> IO Expr
newVar solver w = do
  bs <- VG.fromList <$> SAT.newVars (svSATSolver solver) w
  v <- Vec.getSize $ svVars solver
  Vec.push (svVars solver) bs
  return $ EVar $ Var{ varWidth = w, varId = v }

assertAtom :: Solver -> Atom -> Maybe Int -> IO ()
assertAtom solver (Rel (OrdRel lhs op rhs) signed) label = do
  s <- encodeExpr solver lhs
  t <- encodeExpr solver rhs
  let f = if signed then
            case op of
              Lt -> isSLT s t
              Gt -> isSLT t s
              Le -> isSLE s t
              Ge -> isSLE t s
              Eql -> isEQ s t
              NEq -> Not (isEQ s t)
          else
            case op of
              Lt -> isLT s t
              Gt -> isLT t s
              Le -> isLE s t
              Ge -> isLE t s
              Eql -> isEQ s t
              NEq -> Not (isEQ s t)
  size <- Vec.getSize (svContexts solver)
  case label of
    Nothing | size == 1 -> do
      Tseitin.addFormula (svTseitin solver) f
    _ -> do
      l <- Tseitin.encodeFormula (svTseitin solver) f
      Vec.modify (svContexts solver) (size - 1) (IntMap.insert l label)

check :: Solver -> IO Bool
check solver = do
  size <- Vec.getSize (svContexts solver)
  m <- Vec.read (svContexts solver) (size - 1)
  b <- SAT.solveWith (svSATSolver solver) (IntMap.keys m)
  return b

getModel :: Solver -> IO Model
getModel solver = do
  m <- SAT.getModel (svSATSolver solver)
  vss <- Vec.getElems (svVars solver)
  let f = BV . VG.map (SAT.evalLit m)
      env = VG.fromList [f vs | vs <- vss]
  xs <- readIORef (svDivRemTable solver)
  let divTable = Map.fromList [(f s, f d) | (s,t,d,_r) <- xs, let BV bs = f t, not (VG.or bs)]
      remTable = Map.fromList [(f s, f r) | (s,t,_d,r) <- xs, let BV bs = f t, not (VG.or bs)]
  return (env, divTable, remTable)

explain :: Solver -> IO IntSet
explain solver = do
  xs <- SAT.getFailedAssumptions (svSATSolver solver)
  size <- Vec.getSize (svContexts solver)
  m <- Vec.read (svContexts solver) (size - 1)
  return $ IntSet.fromList $ catMaybes [m IntMap.! x | x <- xs]

pushBacktrackPoint :: Solver -> IO ()
pushBacktrackPoint solver = do
  size <- Vec.getSize (svContexts solver)
  m <- Vec.read (svContexts solver) (size - 1)
  Vec.push (svContexts solver) m

popBacktrackPoint :: Solver -> IO ()
popBacktrackPoint solver = do
  _ <- Vec.pop (svContexts solver)
  return ()

-- ------------------------------------------------------------------------

type SBV = VU.Vector SAT.Lit

encodeExpr :: Solver -> Expr -> IO SBV
encodeExpr solver = enc
  where
    enc e@(EConst _) = enc' e
    enc e@(EVar _) = enc' e
    enc e = do
      table <- readIORef (svEncTable solver)
      case Map.lookup e table of
        Just vs -> return vs
        Nothing -> do
          vs <- enc' e
          modifyIORef (svEncTable solver) (Map.insert e vs)
          return vs

    enc' (EConst (BV bs)) = do
      VU.forM bs $ \b ->
        if b
        then Tseitin.encodeConj (svTseitin solver) []
        else Tseitin.encodeDisj (svTseitin solver) []
    enc' (EVar v) = Vec.read (svVars solver) (varId v)
    enc' (EOp1 op arg) = do
      arg' <- enc arg
      case op of
        OpExtract i j -> do
          unless (VG.length arg' > i && i >= j && j >= 0) $
            error ("invalid extract " ++ show (i,j) ++ " on bit-vector of length " ++ show (VG.length arg') ++ " : " ++ show arg)
          return $ VG.slice j (i - j + 1) arg'
        OpNot -> return $ VG.map negate arg'
        OpNeg -> encodeNegate (svTseitin solver) arg'
    enc' (EOp2 OpNAnd arg1 arg2) = enc' (EOp1 OpNot (EOp2 OpAnd arg1 arg2))
    enc' (EOp2 OpNOr  arg1 arg2) = enc' (EOp1 OpNot (EOp2 OpOr arg1 arg2))
    enc' (EOp2 OpXNOr arg1 arg2) = enc' (EOp1 OpNot (EOp2 OpXOr arg1 arg2))
    enc' (EOp2 OpSub arg1 arg2) = enc' (EOp2 OpAdd arg1 (EOp1 OpNeg arg2))
    enc' (EOp2 op arg1 arg2) = do
      arg1' <- enc arg1
      arg2' <- enc arg2
      case op of
        OpConcat -> return (arg2' <> arg1')
        OpAnd -> VG.zipWithM (\l1 l2 -> Tseitin.encodeConj (svTseitin solver) [l1,l2]) arg1' arg2'
        OpOr  -> VG.zipWithM (\l1 l2 -> Tseitin.encodeDisj (svTseitin solver) [l1,l2]) arg1' arg2'
        OpXOr -> VG.zipWithM (Tseitin.encodeXOR (svTseitin solver)) arg1' arg2'
        OpComp -> VG.singleton <$> Tseitin.encodeFormula (svTseitin solver) (isEQ arg1' arg2')
        OpAdd -> encodeSum (svTseitin solver) (VG.length arg1') True [arg1', arg2']
        OpMul -> encodeMul (svTseitin solver) True arg1' arg2'
        OpUDiv -> fst <$> encodeDivRem solver arg1' arg2'
        OpURem -> snd <$> encodeDivRem solver arg1' arg2'
        OpSDiv -> encodeSDiv solver arg1' arg2'
        OpSRem -> encodeSRem solver arg1' arg2'
        OpSMod -> encodeSMod solver arg1' arg2'
        OpShl  -> encodeShl (svTseitin solver) arg1' arg2'
        OpLShr -> encodeLShr (svTseitin solver) arg1' arg2'
        OpAShr -> encodeAShr (svTseitin solver) arg1' arg2'

encodeMul :: Tseitin.Encoder IO -> Bool -> SBV -> SBV -> IO SBV
encodeMul enc allowOverflow arg1 arg2 = do
  let w = VG.length arg1
  b0 <- Tseitin.encodeDisj enc [] -- False
  bss <- forM (zip [0..] (VG.toList arg2)) $ \(i,b2) -> do
    let arg1' = if allowOverflow
                then VG.take (w - i) arg1
                else arg1
    bs <- VG.forM arg1' $ \b1 -> do
            Tseitin.encodeConj enc [b1,b2]
    return (VG.replicate i b0 <> bs)
  encodeSum enc w allowOverflow bss

encodeSum :: Tseitin.Encoder IO -> Int -> Bool -> [SBV] -> IO SBV
encodeSum enc w allowOverflow xss = do
  (buckets :: IORef (Seq (SQ.SeqQueue IO SAT.Lit))) <- newIORef Seq.empty
  let insert i x = do
        bs <- readIORef buckets
        let n = Seq.length bs
        q <- if i < n then do
               return $ Seq.index bs i
             else do
               qs <- replicateM (i+1 - n) SQ.newFifo
               let bs' = bs Seq.>< Seq.fromList qs
               writeIORef buckets bs'
               return $ Seq.index bs' i
        SQ.enqueue q x

  forM_ xss $ \xs -> do
    VG.imapM (\i x -> insert i x) xs

  let loop i ret
        | i >= w = do
            unless allowOverflow $ do
              bs <- readIORef buckets
              forM_ (F.toList bs) $ \q -> do
                ls <- SQ.dequeueBatch q
                forM_ ls $ \l -> do
                  SAT.addClause  enc [-l]
            return (reverse ret)
        | otherwise = do
            bs <- readIORef buckets
            let n = Seq.length bs
            if i >= n then do
              b <- Tseitin.encodeDisj enc [] -- False
              loop (i+1) (b : ret)
            else do
              let q = Seq.index bs i
              m <- SQ.queueSize q
              case m of
                0 -> do
                  b <- Tseitin.encodeDisj enc [] -- False
                  loop (i+1) (b : ret)
                1 -> do
                  Just b <- SQ.dequeue q
                  loop (i+1) (b : ret)
                2 -> do
                  Just b1 <- SQ.dequeue q
                  Just b2 <- SQ.dequeue q
                  s <- encodeHASum enc b1 b2
                  c <- encodeHACarry enc b1 b2
                  insert (i+1) c
                  loop (i+1) (s : ret)
                _ -> do
                  Just b1 <- SQ.dequeue q
                  Just b2 <- SQ.dequeue q
                  Just b3 <- SQ.dequeue q
                  s <- Tseitin.encodeFASum enc b1 b2 b3
                  c <- Tseitin.encodeFACarry enc b1 b2 b3
                  insert i s
                  insert (i+1) c
                  loop i ret
  VU.fromList <$> loop 0 []

encodeHASum :: Tseitin.Encoder IO -> SAT.Lit -> SAT.Lit -> IO SAT.Lit
encodeHASum = Tseitin.encodeXOR

encodeHACarry :: Tseitin.Encoder IO -> SAT.Lit -> SAT.Lit -> IO SAT.Lit
encodeHACarry enc a b = Tseitin.encodeConj enc [a,b]

encodeNegate :: Tseitin.Encoder IO -> SBV -> IO SBV
encodeNegate enc s = do
  let f _ [] ret = return $ VU.fromList $ reverse ret
      f b (x:xs) ret = do
        y <- Tseitin.encodeITE enc b (- x) x
        b' <- Tseitin.encodeDisj enc [b, x]
        f b' xs (y : ret)
  b0 <- Tseitin.encodeDisj enc []
  f b0 (VG.toList s) []

encodeAbs :: Tseitin.Encoder IO -> SBV -> IO SBV
encodeAbs enc s = do
  let w = VG.length s
  if w == 0 then
    return VG.empty
  else do
    let msb_s = VG.last s
    r <- VG.fromList <$> SAT.newVars enc w
    t <- encodeNegate enc s
    Tseitin.addFormula enc $
      ite (Atom (-msb_s)) (isEQ r s) (isEQ r t)
    return r

encodeShl :: Tseitin.Encoder IO -> SBV -> SBV -> IO SBV
encodeShl enc s t = do
  let w = VG.length s
  when (w /= VG.length t) $ error "invalid width"
  b0 <- Tseitin.encodeDisj enc [] -- False
  let go bs (i,b) =
        VG.generateM w $ \j -> do
          let k = j - 2^i
              t = if k >= 0 then bs VG.! k else b0
              e = bs VG.! j
          Tseitin.encodeITE enc b t e
  foldM go s (zip [(0::Int)..] (VG.toList t))
  
encodeLShr :: Tseitin.Encoder IO -> SBV -> SBV -> IO SBV
encodeLShr enc s t = do
  let w = VG.length s
  when (w /= VG.length t) $ error "invalid width"
  b0 <- Tseitin.encodeDisj enc [] -- False
  let go bs (i,b) =
        VG.generateM w $ \j -> do
          let k = j + 2^i
              t = if k < VG.length bs then bs VG.! k else b0
              e = bs VG.! j
          Tseitin.encodeITE enc b t e
  foldM go s (zip [(0::Int)..] (VG.toList t))

encodeAShr :: Tseitin.Encoder IO -> SBV -> SBV -> IO SBV
encodeAShr enc s t = do
  let w = VG.length s
  when (w /= VG.length t) $ error "invalid width"
  if w == 0 then
    return VG.empty
  else do
    let msb_s = VG.last s
    r <- VG.fromList <$> SAT.newVars enc w
    a <- encodeLShr enc s t
    b <- VG.map negate <$> encodeLShr enc (VG.map negate s) t
    Tseitin.addFormula enc $
      ite (Atom (-msb_s)) (isEQ r a) (isEQ r b)
    return r

encodeDivRem :: Solver -> SBV -> SBV -> IO (SBV, SBV)
encodeDivRem solver s t = do
  let w = VG.length s
  d <- VG.fromList <$> SAT.newVars (svSATSolver solver) w
  r <- VG.fromList <$> SAT.newVars (svSATSolver solver) w
  c <- do
    tmp <- encodeMul (svTseitin solver) False d t
    encodeSum (svTseitin solver) w False [tmp, r]
  tbl <- readIORef (svDivRemTable solver)
  Tseitin.addFormula (svTseitin solver) $
    ite (isZero t)
        (And [(isEQ s s' .&&. isZero t') .=>. (isEQ d d' .&&. isEQ r r') | (s',t',d',r') <- tbl, w == VG.length s'])
        (isEQ s c .&&. isLT r t)
  modifyIORef (svDivRemTable solver) ((s,t,d,r) :)
  return (d,r)

encodeSDiv :: Solver -> SBV -> SBV -> IO SBV
encodeSDiv solver s t = do
  let w = VG.length s
  when (w /= VG.length t) $ error "invalid width"
  if w == 0 then
    return VG.empty
  else do    
    s' <- encodeNegate (svTseitin solver) s
    t' <- encodeNegate (svTseitin solver) t
    let msb_s = VG.last s
        msb_t = VG.last t
    r <- VG.fromList <$> SAT.newVars (svSATSolver solver) w
    let f x y = fst <$> encodeDivRem solver x y
    a <- f s t
    b <- encodeNegate (svTseitin solver) =<< f s' t
    c <- encodeNegate (svTseitin solver) =<< f s t'
    d <- f s' t'
    Tseitin.addFormula (svTseitin solver) $
      ite (Atom (-msb_s) .&&. Atom (-msb_t)) (isEQ r a) $
      ite (Atom msb_s .&&. Atom (-msb_t)) (isEQ r b) $
      ite (Atom (-msb_s) .&&. Atom msb_t) (isEQ r c) $
      (isEQ r d)
    return r

encodeSRem :: Solver -> SBV -> SBV -> IO SBV
encodeSRem solver s t = do
  let w = VG.length s
  when (w /= VG.length t) $ error "invalid width"
  if w == 0 then
    return VG.empty
  else do
    s' <- encodeNegate (svTseitin solver) s
    t' <- encodeNegate (svTseitin solver) t
    let msb_s = VG.last s
        msb_t = VG.last t
    r <- VG.fromList <$> SAT.newVars (svSATSolver solver) w
    let f x y = snd <$> encodeDivRem solver x y
    a <- f s t
    b <- encodeNegate (svTseitin solver) =<< f s' t
    c <- f s t'
    d <- encodeNegate (svTseitin solver) =<< f s' t'
    Tseitin.addFormula (svTseitin solver) $
      ite (Atom (-msb_s) .&&. Atom (-msb_t)) (isEQ r a) $
      ite (Atom msb_s .&&. Atom (-msb_t)) (isEQ r b) $
      ite (Atom (-msb_s) .&&. Atom msb_t) (isEQ r c) $
      (isEQ r d)
    return r

encodeSMod :: Solver -> SBV -> SBV -> IO SBV
encodeSMod solver s t = do
  let w = VG.length s
  when (w /= VG.length t) $ error "invalid width"
  if w == 0 then
    return VG.empty
  else do
    let msb_s = VG.last s
        msb_t = VG.last t
    r <- VG.fromList <$> SAT.newVars (svSATSolver solver) w
    abs_s <- encodeAbs (svTseitin solver) s
    abs_t <- encodeAbs (svTseitin solver) t
    u <- snd <$> encodeDivRem solver abs_s abs_t
    u' <- encodeNegate (svTseitin solver) u
    a <- encodeSum (svTseitin solver) w True [u', t]
    b <- encodeSum (svTseitin solver) w True [u, t]
    Tseitin.addFormula (svTseitin solver) $
      ite (isZero u .||. (Atom (-msb_s) .&&. Atom (-msb_t))) (isEQ r u) $
      ite (Atom msb_s .&&. Atom (-msb_t)) (isEQ r a) $
      ite (Atom (-msb_s) .&&. Atom msb_t) (isEQ r b) $
      (isEQ r u')
    return r

isZero :: SBV -> Tseitin.Formula
isZero bs = And [Not (Atom b) | b <- VG.toList bs]

isEQ :: SBV -> SBV -> Tseitin.Formula
isEQ bs1 bs2
  | VG.length bs1 /= VG.length bs2 = error ("length mismatch: " ++ show (VG.length bs1) ++ " and " ++ show (VG.length bs2))
  | otherwise = And [Equiv (Atom b1) (Atom b2) | (b1,b2) <- zip (VG.toList bs1) (VG.toList bs2)]

isLE :: SBV -> SBV -> Tseitin.Formula
isLE bs1 bs2 = lexComp true bs1 bs2

isLT :: SBV -> SBV -> Tseitin.Formula
isLT bs1 bs2 = lexComp false bs1 bs2 

isSLE :: SBV -> SBV -> Tseitin.Formula
isSLE bs1 bs2
  | VG.length bs1 /= VG.length bs2 = error ("length mismatch: " ++ show (VG.length bs1) ++ " and " ++ show (VG.length bs2))
  | w == 0 = true
  | otherwise =
      Atom bs1_msb .&&. Not (Atom bs2_msb)
      .||. (Atom bs1_msb .<=>. Atom bs2_msb) .&&. isLE bs1 bs2
  where
    w = VG.length bs1
    bs1_msb = bs1 VG.! (w-1)
    bs2_msb = bs2 VG.! (w-1)

isSLT :: SBV -> SBV -> Tseitin.Formula
isSLT bs1 bs2
  | VG.length bs1 /= VG.length bs2 = error ("length mismatch: " ++ show (VG.length bs1) ++ " and " ++ show (VG.length bs2))
  | w == 0 = false
  | otherwise =
      Atom bs1_msb .&&. Not (Atom bs2_msb)
      .||. (Atom bs1_msb .<=>. Atom bs2_msb) .&&. isLT bs1 bs2
  where
    w = VG.length bs1
    bs1_msb = bs1 VG.! (w-1)
    bs2_msb = bs2 VG.! (w-1)

lexComp :: Tseitin.Formula -> SBV -> SBV -> Tseitin.Formula
lexComp b bs1 bs2
  | VG.length bs1 /= VG.length bs2 = error ("length mismatch: " ++ show (VG.length bs1) ++ " and " ++ show (VG.length bs2))
  | otherwise = f (VG.toList (VG.reverse bs1)) (VG.toList (VG.reverse bs2))
  where
    f [] [] = b
    f (b1:bs1) (b2:bs2) =
      (notB (Atom b1) .&&. Atom b2) .||. ((Atom b1 .=>. Atom b2) .&&. f bs1 bs2)

-- ------------------------------------------------------------------------

test1 = do
  solver <- newSolver
  v1 <- newVar solver 8
  v2 <- newVar solver 8
  assertAtom solver (EOp2 OpMul v1 v2 .==. nat2bv 8 6) Nothing
  print =<< check solver
  m <- getModel solver
  print m

test2 = do
  solver <- newSolver
  v1 <- newVar solver 8
  v2 <- newVar solver 8
  let z = nat2bv 8 0
  assertAtom solver (EOp2 OpUDiv v1 z ./=. EOp2 OpUDiv v2 z) Nothing
  assertAtom solver (v1 .==. v2) Nothing
  print =<< check solver -- False
