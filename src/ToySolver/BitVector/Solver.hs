{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.BitVector.Solver
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
--
-----------------------------------------------------------------------------
module ToySolver.BitVector.Solver
  (    
  -- * BitVector solver
    Solver
  , newSolver
  , newVar
  , newVar'
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

import ToySolver.BitVector.Base

-- ------------------------------------------------------------------------

data Solver
  = Solver
  { svVars :: Vec.Vec (VU.Vector SAT.Lit)
  , svSATSolver :: SAT.Solver
  , svTseitin :: Tseitin.Encoder IO
  , svEncTable :: IORef (Map Expr (VU.Vector SAT.Lit))
  , svDivRemTable :: IORef [(VU.Vector SAT.Lit, VU.Vector SAT.Lit, VU.Vector SAT.Lit, VU.Vector SAT.Lit)]
  , svAtomTable :: IORef (Map NormalizedAtom SAT.Lit)
  , svContexts :: Vec.Vec (IntMap (Maybe Int))
  }

newSolver :: IO Solver
newSolver = do
  vars <- Vec.new
  sat <- SAT.newSolver
  tseitin <- Tseitin.newEncoder sat
  table <- newIORef Map.empty
  divRemTable <- newIORef []
  atomTable <- newIORef Map.empty
  contexts <- Vec.new
  Vec.push contexts IntMap.empty
  return $
    Solver
    { svVars = vars
    , svSATSolver = sat
    , svTseitin = tseitin
    , svEncTable = table
    , svDivRemTable = divRemTable
    , svAtomTable = atomTable
    , svContexts = contexts
    }

newVar :: Solver -> Int -> IO Expr
newVar solver w = EVar <$> newVar' solver w

newVar' :: Solver -> Int -> IO Var
newVar' solver w = do
  bs <- VG.fromList <$> SAT.newVars (svSATSolver solver) w
  v <- Vec.getSize $ svVars solver
  Vec.push (svVars solver) bs
  return $ Var{ varWidth = w, varId = v }

data NormalizedRel = NRSLt | NRULt | NREql
  deriving (Eq, Ord, Enum, Bounded, Show)  

data NormalizedAtom = NormalizedAtom NormalizedRel Expr Expr
  deriving (Eq, Ord, Show)

normalizeAtom :: Atom -> (NormalizedAtom, Bool)
normalizeAtom (Rel (OrdRel lhs op rhs) True) =
  case op of
    Lt -> (NormalizedAtom NRSLt lhs rhs, True)
    Gt -> (NormalizedAtom NRSLt rhs lhs, True)
    Le -> (NormalizedAtom NRSLt rhs lhs, False)
    Ge -> (NormalizedAtom NRSLt lhs rhs, False)
    Eql -> (NormalizedAtom NREql lhs rhs, True)
    NEq -> (NormalizedAtom NREql lhs rhs, False)
normalizeAtom (Rel (OrdRel lhs op rhs) False) =
  case op of
    Lt -> (NormalizedAtom NRULt lhs rhs, True)
    Gt -> (NormalizedAtom NRULt rhs lhs, True)
    Le -> (NormalizedAtom NRULt rhs lhs, False)
    Ge -> (NormalizedAtom NRULt lhs rhs, False)
    Eql -> (NormalizedAtom NREql lhs rhs, True)
    NEq -> (NormalizedAtom NREql lhs rhs, False)

assertAtom :: Solver -> Atom -> Maybe Int -> IO ()
assertAtom solver atom label = do
  let (atom'@(NormalizedAtom op lhs rhs), polarity) = normalizeAtom atom
  table <- readIORef (svAtomTable solver)
  l <- (if polarity then id else negate) <$>
    case Map.lookup atom' table of
      Just lit -> return lit
      Nothing -> do
        s <- encodeExpr solver lhs
        t <- encodeExpr solver rhs
        l <- Tseitin.encodeFormula (svTseitin solver) $
          case op of
            NRULt -> isULT s t
            NRSLt -> isSLT s t
            NREql -> isEQ s t
        writeIORef (svAtomTable solver) $ Map.insert atom' l table
        return l
  size <- Vec.getSize (svContexts solver)
  case label of
    Nothing | size == 1 -> SAT.addClause (svTseitin solver) [l]
    _ -> do
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
  let f = fromAscBits . map (SAT.evalLit m) . VG.toList
      isZero = not . or . toAscBits
      env = VG.fromList [f vs | vs <- vss]
  xs <- readIORef (svDivRemTable solver)
  let divTable = Map.fromList [(f s, f d) | (s,t,d,_r) <- xs, isZero (f t)]
      remTable = Map.fromList [(f s, f r) | (s,t,_d,r) <- xs, isZero (f t)]
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

    enc' (EConst bs) =
      liftM VU.fromList $ forM (toAscBits bs) $ \b ->
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
#if MIN_VERSION_vector(0,11,0)
    VG.imapM insert xs
#else
    VG.mapM (uncurry insert) (VG.indexed xs)
#endif

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
    s' <- encodeNegate enc s
    a <- encodeLShr enc s t
    b <- encodeNegate enc =<< encodeLShr enc s' t
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
        (isEQ s c .&&. isULT r t)
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

isULT :: SBV -> SBV -> Tseitin.Formula
isULT bs1 bs2
  | VG.length bs1 /= VG.length bs2 = error ("length mismatch: " ++ show (VG.length bs1) ++ " and " ++ show (VG.length bs2))
  | otherwise = f (VG.toList (VG.reverse bs1)) (VG.toList (VG.reverse bs2))
  where
    f [] [] = false
    f (b1:bs1) (b2:bs2) =
      (notB (Atom b1) .&&. Atom b2) .||. ((Atom b1 .=>. Atom b2) .&&. f bs1 bs2)
    f _ _ = error "should not happen"

isSLT :: SBV -> SBV -> Tseitin.Formula
isSLT bs1 bs2
  | VG.length bs1 /= VG.length bs2 = error ("length mismatch: " ++ show (VG.length bs1) ++ " and " ++ show (VG.length bs2))
  | w == 0 = false
  | otherwise =
      Atom bs1_msb .&&. Not (Atom bs2_msb)
      .||. (Atom bs1_msb .<=>. Atom bs2_msb) .&&. isULT bs1 bs2
  where
    w = VG.length bs1
    bs1_msb = bs1 VG.! (w-1)
    bs2_msb = bs2 VG.! (w-1)

-- ------------------------------------------------------------------------

test1 :: IO ()
test1 = do
  solver <- newSolver
  v1 <- newVar solver 8
  v2 <- newVar solver 8
  assertAtom solver (EOp2 OpMul v1 v2 .==. nat2bv 8 6) Nothing
  print =<< check solver
  m <- getModel solver
  print m

test2 :: IO ()
test2 = do
  solver <- newSolver
  v1 <- newVar solver 8
  v2 <- newVar solver 8
  let z = nat2bv 8 0
  assertAtom solver (EOp2 OpUDiv v1 z ./=. EOp2 OpUDiv v2 z) Nothing
  assertAtom solver (v1 .==. v2) Nothing
  print =<< check solver -- False
