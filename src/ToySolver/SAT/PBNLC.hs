{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.PBNLC
-- Copyright   :  (c) Masahiro Sakai 2015
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
-- 
-----------------------------------------------------------------------------
module ToySolver.SAT.PBNLC
  (
    PBTerm
  , PBSum

  -- * Adding constraints
  , addPBAtLeast
  , addPBAtMost  
  , addPBExactly
  , addPBAtLeastSoft
  , addPBAtMostSoft
  , addPBExactlySoft

  -- * Linearlization
  , linearizePBSum
  , linearizePBSumWithPolarity

  -- * Evaluation
  , evalPBSum
  ) where

import qualified ToySolver.SAT as SAT
import ToySolver.SAT.Types
import ToySolver.SAT.TseitinEncoder
import ToySolver.Internal.Util (revForM)

type PBTerm = (Integer, [Lit])
type PBSum = [PBTerm]

-- | Add a non-linear pseudo boolean constraints /c1*ls1 + c2*ls2 + … ≥ n/.
addPBAtLeast
  :: Encoder
  -> PBSum   -- ^ @[(c1,ls1),(c2,ls2),…]@
  -> Integer -- ^ /n/
  -> IO ()
addPBAtLeast enc lhs rhs = do
  lhs' <- linearizePBSumWithPolarity enc polarityPos lhs
  SAT.addPBAtLeast (encSolver enc) lhs' rhs

-- | Add a non-linear pseudo boolean constraints /c1*ls1 + c2*ls2 + … ≥ n/.
addPBAtMost
  :: Encoder
  -> PBSum   -- ^ @[(c1,ls1),(c2,ls2),…]@
  -> Integer -- ^ /n/
  -> IO ()
addPBAtMost enc lhs rhs =
  addPBAtLeast enc [(-c,ls) | (c,ls) <- lhs] (negate rhs)

-- | Add a non-linear pseudo boolean constraints /c1*ls1 + c2*ls2 + … = n/.
addPBExactly
  :: Encoder
  -> PBSum   -- ^ @[(c1,ls1),(c2,ls2),…]@
  -> Integer -- ^ /n/
  -> IO ()
addPBExactly enc lhs rhs = do
  lhs' <- linearizePBSum enc lhs
  SAT.addPBExactly (encSolver enc) lhs' rhs

-- | Add a soft non-linear pseudo boolean constraints /lit ⇒ c1*ls1 + c2*ls2 + … ≥ n/.
addPBAtLeastSoft
  :: Encoder
  -> Lit     -- ^ indicator @lit@
  -> PBSum   -- ^ @[(c1,ls1),(c2,ls2),…]@
  -> Integer -- ^ /n/
  -> IO ()
addPBAtLeastSoft enc sel lhs rhs = do
  lhs' <- linearizePBSumWithPolarity enc polarityPos lhs
  SAT.addPBAtLeastSoft (encSolver enc) sel lhs' rhs

-- | Add a soft non-linear pseudo boolean constraints /lit ⇒ c1*ls1 + c2*ls2 + … ≤ n/.
addPBAtMostSoft
  :: Encoder
  -> Lit     -- ^ indicator @lit@
  -> PBSum   -- ^ @[(c1,ls1),(c2,ls2),…]@
  -> Integer -- ^ /n/
  -> IO ()
addPBAtMostSoft enc sel lhs rhs =
  addPBAtLeastSoft enc sel [(negate c, lit) | (c,lit) <- lhs] (negate rhs)

-- | Add a soft non-linear pseudo boolean constraints /lit ⇒ c1*ls1 + c2*ls2 + … = n/.
addPBExactlySoft
  :: Encoder
  -> Lit     -- ^ indicator @lit@
  -> PBSum   -- ^ @[(c1,ls1),(c2,ls2),…]@
  -> Integer -- ^ /n/
  -> IO ()
addPBExactlySoft enc sel lhs rhs = do
  lhs' <- linearizePBSum enc lhs
  SAT.addPBExactlySoft (encSolver enc) sel lhs' rhs

-- | Encode a non-linear 'PBSum' into a lienar 'PBLinSum'.
--
-- @linearizePBSum enc s@ is equivalent to @linearizePBSumWithPolarity enc polarityBoth@.
linearizePBSum
  :: Encoder
  -> PBSum
  -> IO PBLinSum
linearizePBSum enc = linearizePBSumWithPolarity enc polarityBoth

-- | Linearize a non-linear 'PBSum' into a lienar 'PBLinSum'.
--
-- The input 'PBSum' is assumed to occur only in specified polarity.
--
-- * If @'polarityPosOccurs' p@, the value of resulting 'PBLinSum' is /greater than/ or /equal to/ the value of original 'PBSum'.
--
-- * If @'polarityNegOccurs' p@, the value of resulting 'PBLinSum' is /lesser than/ or /equal to/ the value of original 'PBSum'.
-- 
linearizePBSumWithPolarity
  :: Encoder
  -> Polarity -- polarity /p/
  -> PBSum
  -> IO PBLinSum
linearizePBSumWithPolarity enc p xs =
  revForM xs $ \(c,ls) -> do
    l <- if c > 0 then
           encodeConjWithPolarity enc p ls
         else
           encodeConjWithPolarity enc (negatePolarity p) ls
    return (c,l)

evalPBSum :: IModel m => m -> PBSum -> Integer
evalPBSum m xs = sum [c | (c,lits) <- xs, all (evalLit m) lits]
