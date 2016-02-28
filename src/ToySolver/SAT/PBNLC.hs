{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ExistentialQuantification, FlexibleContexts, MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.PBNLC
-- Copyright   :  (c) Masahiro Sakai 2015
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ExistentialQuantification, FlexibleContexts, MultiParamTypeClasses)
-- 
-----------------------------------------------------------------------------
module ToySolver.SAT.PBNLC
  (
    PBTerm
  , PBSum
  , Encoder
  , newEncoder
  , getTseitinEncoder

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

import ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.TseitinEncoder as Tseitin
import ToySolver.Internal.Util (revForM)

type PBTerm = (Integer, [Lit])
type PBSum = [PBTerm]

data Encoder
  = forall a. SAT.AddPBLin IO a => Encoder
  { encBase    :: a
  , encTseitin :: Tseitin.Encoder
  }

instance SAT.NewVar IO Encoder where
  newVar Encoder{ encBase = a }   = SAT.newVar a
  newVars Encoder{ encBase = a }  = SAT.newVars a
  newVars_ Encoder{ encBase = a } = SAT.newVars_ a

instance SAT.AddClause IO Encoder where
  addClause Encoder{ encBase = a } = SAT.addClause a

instance SAT.AddCardinality IO Encoder where
  addAtLeast Encoder{ encBase = a } = SAT.addAtLeast a
  addAtMost  Encoder{ encBase = a } = SAT.addAtMost a
  addExactly Encoder{ encBase = a } = SAT.addExactly a

instance SAT.AddPBLin IO Encoder where
  addPBAtLeast Encoder{ encBase = a } = SAT.addPBAtLeast a
  addPBAtMost  Encoder{ encBase = a } = SAT.addPBAtMost a
  addPBExactly Encoder{ encBase = a } = SAT.addPBExactly a
  addPBAtLeastSoft Encoder{ encBase = a } = SAT.addPBAtLeastSoft a
  addPBAtMostSoft  Encoder{ encBase = a } = SAT.addPBAtMostSoft a
  addPBExactlySoft Encoder{ encBase = a } = SAT.addPBExactlySoft a

newEncoder :: SAT.AddPBLin IO a => a -> Tseitin.Encoder -> IO Encoder
newEncoder a tseitin = return $ Encoder a tseitin

getTseitinEncoder :: Encoder -> Tseitin.Encoder
getTseitinEncoder Encoder{ encTseitin = tseitin } = tseitin

-- | Add a non-linear pseudo boolean constraints /c1*ls1 + c2*ls2 + … ≥ n/.
addPBNLAtLeast
  :: Encoder
  -> PBSum   -- ^ @[(c1,ls1),(c2,ls2),…]@
  -> Integer -- ^ /n/
  -> IO ()
addPBNLAtLeast enc lhs rhs = do
  let c = sum [c | (c,[]) <- lhs]
  lhs' <- linearizePBSumWithPolarity enc Tseitin.polarityPos [(c,ls) | (c,ls) <- lhs, not (null ls)]
  SAT.addPBAtLeast enc lhs' (rhs - c)

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
  SAT.addPBExactly enc lhs' (rhs - c)

-- | Add a soft non-linear pseudo boolean constraints /sel ⇒ c1*ls1 + c2*ls2 + … ≥ n/.
addPBNLAtLeastSoft
  :: Encoder
  -> Lit     -- ^ Selector literal @sel@
  -> PBSum   -- ^ @[(c1,ls1),(c2,ls2),…]@
  -> Integer -- ^ /n/
  -> IO ()
addPBNLAtLeastSoft enc sel lhs rhs = do
  let c = sum [c | (c,[]) <- lhs]
  lhs' <- linearizePBSumWithPolarity enc Tseitin.polarityPos [(c,ls) | (c,ls) <- lhs, not (null ls)]
  SAT.addPBAtLeastSoft enc sel lhs' (rhs - c)

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
  SAT.addPBExactlySoft enc sel lhs' (rhs - c)

-- | Encode a non-linear 'PBSum' into a lienar 'PBLinSum'.
--
-- @linearizePBSum enc s@ is equivalent to @linearizePBSumWithPolarity enc polarityBoth@.
linearizePBSum
  :: Encoder
  -> PBSum
  -> IO PBLinSum
linearizePBSum enc = linearizePBSumWithPolarity enc Tseitin.polarityBoth

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
  -> Tseitin.Polarity -- polarity /p/
  -> PBSum
  -> IO PBLinSum
linearizePBSumWithPolarity Encoder{ encTseitin = tseitin } p xs =
  revForM xs $ \(c,ls) -> do
    l <- if c > 0 then
           Tseitin.encodeConjWithPolarity tseitin p ls
         else
           Tseitin.encodeConjWithPolarity tseitin (Tseitin.negatePolarity p) ls
    return (c,l)

evalPBSum :: IModel m => m -> PBSum -> Integer
evalPBSum m xs = sum [c | (c,lits) <- xs, all (evalLit m) lits]
