{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
module Test.BitVector (bitVectorTestGroup) where

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH
import qualified Test.QuickCheck.Monadic as QM

import Control.Monad
import Data.Maybe
#if !MIN_VERSION_base(4,11,0)
import Data.Monoid
#endif

import ToySolver.Data.OrdRel
import qualified ToySolver.BitVector as BV

-- ------------------------------------------------------------------------

prop_BVSolver :: Property
prop_BVSolver = QM.monadicIO $ do
  (vs,cs) <- QM.pick genFormula
  ret <- QM.run $ do
    solver <- BV.newSolver
    forM_ vs $ \v -> do
      v' <- BV.newVar solver (BV.varWidth v)
      unless (v' == BV.EVar v) undefined -- XXX
      return ()
    forM_ cs $ \c -> do
      BV.assertAtom solver c Nothing
    ret <- BV.check solver
    if ret then do
      m <- BV.getModel solver
      return $ Just m
    else
      return Nothing
  case ret of
    Nothing -> return ()
    Just m -> do
      QM.monitor (counterexample $ show m)
      QM.assert $ and [BV.evalAtom m c | c <- cs]

case_division_by_zero_cong :: IO ()
case_division_by_zero_cong = do
  solver <- BV.newSolver
  v1 <- BV.newVar solver 8
  v2 <- BV.newVar solver 8
  let z = BV.nat2bv 8 0
  BV.assertAtom solver (BV.bvudiv v1 z ./=. BV.bvudiv v2 z) Nothing
  ret <- BV.check solver
  ret @?= True
  BV.assertAtom solver (v1 .==. v2) Nothing
  ret2 <- BV.check solver
  ret2 @?= False

-- ------------------------------------------------------------------------
-- Generators

genBVExpr :: [BV.Expr] -> Int -> Int -> Gen BV.Expr
genBVExpr bases = f
  where
    f :: Int -> Int -> Gen BV.Expr
    f w s = do
      let gBase
            | w > 0 && wmax >= w = Just $ do
                e <- elements [e | e <- bases, BV.width e >= w]
                if BV.width e == w then do
                  return e
                else do
                  l <- choose (0, BV.width e - w) -- inclusive range
                  let u = l + w - 1
                  return $ BV.extract u l e
            | otherwise = Nothing
            where
              wmax = maximum (0 : map BV.width bases)
          gConst = do
            bs <- replicateM w arbitrary
            return $ BV.fromDescBits bs
          gConcat = do
            if s <= 0 then do
              w1 <- choose (1,w-1)
              lhs <- f w1 0
              rhs <- f (w - w1) 0
              return $ lhs <> rhs
            else do
              w1 <- choose (0,w)
              s1 <- choose (0,s)
              lhs <- f w1 s1
              rhs <- f (w - w1) (s - s1)
              return $ lhs <> rhs
          gExtract = do
            wd <- choose (0,10)
            e <- f (w + wd) (s - 1)
            l <- choose (0, BV.width e - w) -- inclusive range
            let u = l + w - 1
            return $ BV.extract u l e
          gNormalOp1 = do
            op <- elements [BV.bvnot, BV.bvneg]
            e <- f w (s - 1)
            return $ op e
          gNormalOp2 = do
            op <- elements $
                    [BV.bvand, BV.bvor, BV.bvxor, BV.bvnand, BV.bvnor, BV.bvxnor] ++
                    [BV.bvadd, BV.bvsub, BV.bvmul, BV.bvudiv, BV.bvurem, BV.bvshl, BV.bvlshr, BV.bvashr] ++
                    (if w >= 1 then [BV.bvsdiv, BV.bvsrem, BV.bvsmod] else [])
            s1 <- choose (0,s)
            lhs <- f w s1
            rhs <- f w (s - s1)
            return $ op lhs rhs
          gComp = do
            w1 <- choose (0, wmax*2)
            s1 <- choose (0,s)
            lhs <- f w1 s1
            rhs <- f w1 (s - s1)
            return $ BV.bvcomp lhs rhs
            where
              wmax = maximum (0 : map BV.width bases)
      if s <= 0 then do
        oneof $ maybeToList gBase ++ [gConst] ++ [gConcat | w >= 2]
      else do
        oneof $ maybeToList gBase ++ [gConst, gNormalOp1, gNormalOp2] ++ (if w > 0 then [gConcat, gExtract] else []) ++ [gComp | w == 1]

genBVAtom :: [BV.Expr] -> Int -> Gen BV.Atom
genBVAtom bases size = do
  w <- choose (0,16)
  s1 <- choose (0,size)
  e1 <- genBVExpr bases w s1
  e2 <- genBVExpr bases w (size - s1)
  op  <- elements [Lt, Le, Ge, Gt, Eql, NEq]
  signed <- arbitrary
  return $ BV.Rel (ordRel op e1 e2) signed

genFormula :: Gen ([BV.Var], [BV.Atom])
genFormula = do
  vs <- forM [0..2] $ \v -> do
    w <- choose (1,16)
    return $ BV.Var{ BV.varWidth = w, BV.varId = v }
  let bases = [BV.EVar v | v <- vs]
  nc <- choose (0,3)
  cs <- replicateM nc $ do
    size <- choose (1,8)
    genBVAtom bases size
  return (vs,cs)

-- ------------------------------------------------------------------------
-- Test harness

bitVectorTestGroup :: TestTree
bitVectorTestGroup = $(testGroupGenerator)
