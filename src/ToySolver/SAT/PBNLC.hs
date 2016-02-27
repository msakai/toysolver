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
  , addPBNLAtLeast
  , addPBNLAtMost  
  , addPBNLExactly
  , addPBNLAtLeastSoft
  , addPBNLAtMostSoft
  , addPBNLExactlySoft

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
addPBNLAtLeast
  :: Encoder
  -> PBSum   -- ^ @[(c1,ls1),(c2,ls2),…]@
  -> Integer -- ^ /n/
  -> IO ()
addPBNLAtLeast enc lhs rhs = do
  let c = sum [c | (c,[]) <- lhs]
  lhs' <- linearizePBSumWithPolarity enc polarityPos [(c,ls) | (c,ls) <- lhs, not (null ls)]
  SAT.addPBAtLeast (encSolver enc) lhs' (rhs - c)

-- | Add a non-linear pseudo boolean constraints /c1*ls1 + c2*ls2 + … ≥ n/.
addPBNLAtMost
  :: Encoder
  -> PBSum   -- ^ @[(c1,ls1),(c2,ls2),…]@
  -> Integer -- ^ /n/
  -> IO ()
addPBNLAtMost enc lhs rhs =
  addPBNLAtLeast enc [(-c,ls) | (c,ls) <- lhs] (negate rhs)

-- | Add a non-linear pseudo boolean constraints /c1*ls1 + c2*ls2 + … = n/.
addPBNLExactly
  :: Encoder
  -> PBSum   -- ^ @[(c1,ls1),(c2,ls2),…]@
  -> Integer -- ^ /n/
  -> IO ()
addPBNLExactly enc lhs rhs = do
  let c = sum [c | (c,[]) <- lhs]
  lhs' <- linearizePBSum enc [(c,ls) | (c,ls) <- lhs, not (null ls)]
  SAT.addPBExactly (encSolver enc) lhs' (rhs - c)

-- | Add a soft non-linear pseudo boolean constraints /sel ⇒ c1*ls1 + c2*ls2 + … ≥ n/.
addPBNLAtLeastSoft
  :: Encoder
  -> Lit     -- ^ Selector literal @sel@
  -> PBSum   -- ^ @[(c1,ls1),(c2,ls2),…]@
  -> Integer -- ^ /n/
  -> IO ()
addPBNLAtLeastSoft enc sel lhs rhs = do
  let c = sum [c | (c,[]) <- lhs]
  lhs' <- linearizePBSumWithPolarity enc polarityPos [(c,ls) | (c,ls) <- lhs, not (null ls)]
  SAT.addPBAtLeastSoft (encSolver enc) sel lhs' (rhs - c)

-- | Add a soft non-linear pseudo boolean constraints /sel ⇒ c1*ls1 + c2*ls2 + … ≤ n/.
addPBNLAtMostSoft
  :: Encoder
  -> Lit     -- ^ Selector literal @sel@
  -> PBSum   -- ^ @[(c1,ls1),(c2,ls2),…]@
  -> Integer -- ^ /n/
  -> IO ()
addPBNLAtMostSoft enc sel lhs rhs =
  addPBNLAtLeastSoft enc sel [(negate c, lit) | (c,lit) <- lhs] (negate rhs)

-- | Add a soft non-linear pseudo boolean constraints /lit ⇒ c1*ls1 + c2*ls2 + … = n/.
addPBNLExactlySoft
  :: Encoder
  -> Lit     -- ^ indicator @lit@
  -> PBSum   -- ^ @[(c1,ls1),(c2,ls2),…]@
  -> Integer -- ^ /n/
  -> IO ()
addPBNLExactlySoft enc sel lhs rhs = do
  let c = sum [c | (c,[]) <- lhs]
  lhs' <- linearizePBSum enc [(c,ls) | (c,ls) <- lhs, not (null ls)]
  SAT.addPBExactlySoft (encSolver enc) sel lhs' (rhs - c)

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
