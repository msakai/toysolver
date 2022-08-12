{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.Encoder.Cardinality.Internal.Totalizer
-- Copyright   :  (c) Masahiro Sakai 2020
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.SAT.Encoder.Cardinality.Internal.Totalizer
  ( Encoder (..)
  , newEncoder

  , Definitions
  , getDefinitions
  , evalDefinitions

  , addAtLeast
  , encodeAtLeastWithPolarity

  , addCardinality
  , encodeCardinalityWithPolarity

  , encodeSum
  ) where

import Control.Monad.Primitive
import Control.Monad.State.Strict
import qualified Data.IntSet as IntSet
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Primitive.MutVar
import Data.Vector.Unboxed (Vector)
import qualified Data.Vector.Unboxed as V
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Encoder.Tseitin as Tseitin


data Encoder m = Encoder (Tseitin.Encoder m) (MutVar (PrimState m) (Map SAT.LitSet (Vector SAT.Var)))

instance Monad m => SAT.NewVar m (Encoder m) where
  newVar   (Encoder a _) = SAT.newVar a
  newVars  (Encoder a _) = SAT.newVars a
  newVars_ (Encoder a _) = SAT.newVars_ a

instance Monad m => SAT.AddClause m (Encoder m) where
  addClause (Encoder a _) = SAT.addClause a

newEncoder :: PrimMonad m => Tseitin.Encoder m -> m (Encoder m)
newEncoder tseitin = do
  tableRef <- newMutVar Map.empty
  return $ Encoder tseitin tableRef


type Definitions = [(Vector SAT.Var, SAT.LitSet)]

getDefinitions :: PrimMonad m => Encoder m -> m Definitions
getDefinitions (Encoder _ tableRef) = do
  m <- readMutVar tableRef
  return [(vars', lits) | (lits, vars') <- Map.toList m]


evalDefinitions :: SAT.IModel m => m -> Definitions -> [(SAT.Var, Bool)]
evalDefinitions m defs = do
  (vars', lits) <- defs
  let n = length [() | l <- IntSet.toList lits, SAT.evalLit m l]
  (i, v) <- zip [1..] (V.toList vars')
  return (v, i <= n)


addAtLeast :: PrimMonad m => Encoder m -> SAT.AtLeast -> m ()
addAtLeast enc (lhs, rhs) = do
  addCardinality enc lhs (rhs, length lhs)


addCardinality :: PrimMonad m => Encoder m -> [SAT.Lit] -> (Int, Int) -> m ()
addCardinality enc lits (lb, ub) = do
  let n = length lits
  if lb <= 0 && n <= ub then
    return ()
  else if n < lb || ub < 0 then
    SAT.addClause enc []
  else do
    lits' <- encodeSum enc lits
    forM_ (take lb lits') $ \l -> SAT.addClause enc [l]
    forM_ (drop ub lits') $ \l -> SAT.addClause enc [- l]



encodeAtLeastWithPolarity :: PrimMonad m => Encoder m -> Tseitin.Polarity -> SAT.AtLeast -> m SAT.Lit
encodeAtLeastWithPolarity enc polarity (lhs,rhs) = do
  encodeCardinalityWithPolarity enc polarity lhs (rhs, length lhs)


encodeCardinalityWithPolarity :: PrimMonad m => Encoder m -> Tseitin.Polarity -> [SAT.Lit] -> (Int, Int) -> m SAT.Lit
encodeCardinalityWithPolarity enc@(Encoder tseitin _) polarity lits (lb, ub) = do
  let n = length lits
  if lb <= 0 && n <= ub then
    Tseitin.encodeConjWithPolarity tseitin polarity []
  else if n < lb || ub < 0 then
    Tseitin.encodeDisjWithPolarity tseitin polarity []
  else do
    lits' <- encodeSum enc lits
    forM_ (zip lits' (tail lits')) $ \(l1, l2) -> do
      SAT.addClause enc [-l2, l1] -- l2→l1 or equivalently ¬l1→¬l2
    Tseitin.encodeConjWithPolarity tseitin polarity $
      [lits' !! (lb - 1) | lb > 0] ++ [- (lits' !! (ub + 1 - 1)) | ub < n]


encodeSum :: PrimMonad m => Encoder m -> [SAT.Lit] -> m [SAT.Lit]
encodeSum enc = liftM V.toList . encodeSumV enc . V.fromList


encodeSumV :: PrimMonad m => Encoder m -> Vector SAT.Lit -> m (Vector SAT.Lit)
encodeSumV (Encoder enc tableRef) = f
  where
    f lits
      | n <= 1 = return lits
      | otherwise = do
          m <- readMutVar tableRef
          let key = IntSet.fromList (V.toList lits)
          case Map.lookup key m of
            Just vars -> return vars
            Nothing -> do
              rs <- liftM V.fromList $ SAT.newVars enc n
              writeMutVar tableRef (Map.insert key rs m)
              case V.splitAt n1 lits of
                (lits1, lits2) -> do
                  lits1' <- f lits1
                  lits2' <- f lits2
                  forM_ [0 .. n] $ \sigma ->
                    -- a + b = sigma, 0 <= a <= n1, 0 <= b <= n2
                    forM_ [max 0 (sigma - n2) .. min n1 sigma] $ \a -> do
                      let b = sigma - a
                      -- card(lits1) >= a ∧ card(lits2) >= b → card(lits) >= sigma
                      -- ¬(card(lits1) >= a) ∨ ¬(card(lits2) >= b) ∨ card(lits) >= sigma
                      unless (sigma == 0) $ do
                        SAT.addClause enc $
                          [- (lits1' V.! (a - 1)) | a > 0] ++
                          [- (lits2' V.! (b - 1)) | b > 0] ++
                          [rs V.! (sigma - 1)]
                      -- card(lits) > sigma → (card(lits1) > a ∨ card(lits2) > b)
                      -- card(lits) >= sigma+1 → (card(lits1) >= a+1 ∨ card(lits2) >= b+1)
                      -- card(lits1) >= a+1 ∨ card(lits2) >= b+1 ∨ ¬(card(lits) >= sigma+1)
                      unless (sigma + 1 == n + 1) $ do
                        SAT.addClause enc $
                          [lits1' V.! (a + 1 - 1) | a + 1 < n1 + 1] ++
                          [lits2' V.! (b + 1 - 1) | b + 1 < n2 + 1] ++
                          [- (rs V.! (sigma + 1 - 1))]
                  return rs
     where
       n = V.length lits
       n1 = n `div` 2
       n2 = n - n1

