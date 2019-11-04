{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Arith.Simplex.Simple
-- Copyright   :  (c) Masahiro Sakai 2016
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-----------------------------------------------------------------------------
module ToySolver.Arith.Simplex.Simple
  ( Model
  , OptDir (..)
  , OptResult (..)
  , check
  , optimize
  ) where

import Control.Monad
import Control.Monad.ST
import Data.Default.Class
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import qualified ToySolver.Data.LA as LA
import ToySolver.Data.IntVar hiding (Model)
import qualified ToySolver.Arith.Simplex as Simplex
import ToySolver.Arith.Simplex hiding (check, optimize)

check :: VarSet -> [LA.Atom Rational] -> Maybe Model
check vs as = runST $ do
  solver <- Simplex.newSolver
  s <- liftM IntMap.fromAscList $ forM (IntSet.toAscList vs) $ \v -> do
    v2 <- Simplex.newVar solver
    return (v, v2)
  let s' = fmap LA.var s
      mtrans m = fmap (m IntMap.!) s
  forM_ as $ \a -> do
    Simplex.assertAtomEx solver (fmap (LA.applySubst s') a)
  ret <- Simplex.check solver
  if ret then do
    m <- Simplex.getModel solver
    return $ Just $ mtrans m
  else
    return Nothing

optimize :: VarSet -> OptDir -> LA.Expr Rational -> [LA.Atom Rational] -> (OptResult, Maybe Model)
optimize vs dir obj as = runST $ do
  solver <- Simplex.newSolver
  s <- liftM IntMap.fromAscList $ forM (IntSet.toAscList vs) $ \v -> do
    v2 <- Simplex.newVar solver
    return (v, v2)
  let s' = fmap LA.var s
      mtrans m = fmap (m IntMap.!) s
  forM_ as $ \a -> do
    assertAtom solver (fmap (LA.applySubst s') a)
  Simplex.setOptDir solver dir
  Simplex.setObj solver obj
  ret <- Simplex.optimize solver def
  case ret of
    Optimum -> do
      m <- Simplex.getModel solver
      return $ (ret, Just (mtrans m))
    Unsat -> do
      return $ (ret, Nothing)
    Unbounded -> do
      m <- Simplex.getModel solver
      return $ (ret, Just (mtrans m))
    ObjLimit -> do
      error "should not happen"
